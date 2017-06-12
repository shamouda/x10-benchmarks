import x10.compiler.Pragma;
import x10.util.Random;
import x10.util.OptionsParser;
import x10.util.Option;
import x10.util.Team;
import x10.util.concurrent.Lock;

import x10.util.resilient.PlaceManager;
import x10.util.resilient.localstore.ResilientNativeMap;
import x10.util.resilient.localstore.Tx;
import x10.util.resilient.localstore.ResilientStore;
import x10.util.resilient.localstore.CloneableLong;
import x10.util.resilient.localstore.TxConfig;
import x10.util.resilient.localstore.LockingTx;
import x10.util.resilient.localstore.LocalTx;
import x10.util.resilient.localstore.AbstractTx;
import x10.util.resilient.localstore.tx.FatalTransactionException;
import x10.util.resilient.localstore.CloneableLong;
import x10.util.resilient.localstore.tx.ConflictException;
import x10.util.ArrayList;
import x10.util.HashMap;

public final class SSCA2Cluster(N:Int) {
    val graph:Graph;
    val verbose:Int;
    val verticesToWorkOn = new Rail[Int](N, (i:Long)=>i as Int);
    val map:ResilientNativeMap[Int];
    val places:Long;
    val verticesPerPlace:Long;
    val random:Random;
    
    // Constructor
    public def this(map:ResilientNativeMap[Int], graph:Graph, places:Long, random:Random, verbose:Int) {
        property(graph.numVertices());
        this.graph = graph;
        this.map = map;
        this.places = places;
        this.verbose = verbose;
        this.verticesPerPlace = Math.ceil((graph.numVertices() as Double)/places) as Long;
        this.random = random;
    }

    static def make(map:ResilientNativeMap[Int], rmat:Rmat, permute:Int, places:Long, random:Random, verbose:Int) {
        val graph = rmat.generate();
        if (verbose > 0 && here.id == 0) {
            Console.OUT.println(graph.toString());
            Console.OUT.println("=========================");
        }
        graph.compress();
        val s = new SSCA2Cluster(map, graph, places, random, verbose);
        if (permute > 0) s.permuteVertices();
        return s;
    }


    /**
     * A function to shuffle the vertices randomly to give better work dist.
     */
    private def permuteVertices() {
        val prng = new Random(1);

        for(var i:Int=0n; i<N; i++) {
            val indexToPick = prng.nextInt(N-i);
            val v = verticesToWorkOn(i);
            verticesToWorkOn(i) = verticesToWorkOn(i+indexToPick);
            verticesToWorkOn(i+indexToPick) = v;
        }
    }

    private def vertexPlace(v:Int) = v / verticesPerPlace;
    
    private def getVertexPlaceMap(v:Int, edgeStart:Int, edgeEnd:Int) {
        val map = new HashMap[Long,ArrayList[Int]]();
        var dest:Long = vertexPlace(v);
        var list:ArrayList[Int] = new ArrayList[Int]();
        list.add(v);
        map.put (dest, list);
        
        // Iterate over all its neighbors
        for(var wIndex:Int=edgeStart; wIndex<edgeEnd; ++wIndex) {
            // Get the target of the current edge.
            val w:Int = graph.getAdjacentVertexFromIndex(wIndex);
            dest = vertexPlace(w);
            
            list = map.getOrElse(dest, null);
            if (list == null) {
                list = new ArrayList[Int]();
                map.put(dest, list);
            }
            list.add(w);
        }
        if (verbose > 0n) {
            printVertexPlaceMap(v, map);
        }
        return map;
    }
    
    private def printVertexPlaceMap(v:Int, map:HashMap[Long,ArrayList[Int]]) {
        var str:String = "vertexMap v=" + v + ":";
        val iter = map.keySet().iterator();
        while (iter.hasNext()) {
            val pl = iter.next();
            str += " place(" + pl + ") {";
            val list = map.getOrThrow(pl);
            for (l in list) {
                str += l + " ";
            }
            str += "}";
        }
        Console.OUT.println(str);
    } 
    
    private def processVertex(v:Int, placeIndex:Long, tx:AbstractTx[Int], clusterSize:Long, accum:Long):Long {
        // Get the start and the end points for the edge list for "v"
        val edgeStart:Int = graph.begin(v);
        val edgeEnd:Int = graph.end(v);
        val edgeCount:Int = edgeEnd-edgeStart ;
    
        var innerCount:Long = 0;
        var outerCount:Long = 0;
        val map = getVertexPlaceMap(v, edgeStart, edgeEnd);
        val iter = map.keySet().iterator();
        while (iter.hasNext()) {
            val dest = iter.next();
            val vertices = map.getOrThrow(dest);
            innerCount += vertices.size();
            tx.asyncAt(dest, () => {
                for (s in vertices) {
                    val cluster = tx.get(s);
                    if (cluster == null)
                        tx.put(s, new CloneableLong(placeIndex));
                    else if ((cluster as CloneableLong).v != placeIndex)
                        throw new ConflictException("vertex " + s + " allocated by place " + (cluster as CloneableLong).v, here);
                }
            });
        }
        
        outerCount = accum + innerCount;
        
        if (edgeCount > 0 && accum + innerCount < clusterSize) {
            val indx = Math.abs(random.nextInt()) % edgeCount;
            val nextV:Int = graph.getAdjacentVertexFromIndex(edgeStart + indx);
            outerCount = processVertex(nextV, placeIndex, tx, clusterSize, accum + innerCount) ;
        }
        
        return outerCount;
    }
    
    private def selectRandomAdjacent(v:Int, edgeStart:Int, edgeEnd:Int) {
        val rnd = random.nextInt();
        
        return 0n;
    }
    
    /**
     * Dump the clusters.
     */
    private def generateClusters(val startVertex:Int, val endVertex:Int, clusterSize:Long) {
        Console.OUT.println(here + " " + startVertex + "-" + endVertex);
        val placeIndex = here.id;
        // Iterate over each of the vertices in my portion.
        for(var vertexIndex:Int=startVertex; vertexIndex<endVertex; ++vertexIndex) { 
            val s:Int = verticesToWorkOn(vertexIndex);
            val dest = vertexPlace(s);

            val closure = (tx:AbstractTx[Int]) => {
                return processVertex(s, placeIndex, tx, clusterSize, 0);
            };
            
            try {
                val result = map.executeTransaction(null, closure, 1, -1);
                if (verbose > 0) Console.OUT.println(here + " vertex["+s+"] cluster succeeded, count=" + result.output);
            }catch (ex:Exception) {
                if (verbose > 0) Console.OUT.println(here + " vertex["+s+"] cluster failed");
            }
        }
    }
    
    /**
     * Dump the clusters.
     */
    private def printClusters() {
        Console.OUT.println("==============  Collecting clusters  ===============");
        val result = map.executeLockingTransaction(new Rail[Long](0),new Rail[Int](0), new Rail[Boolean](0), 0, (tx:LockingTx[Int]) => {
            val map = new HashMap[Long,ArrayList[Int]]();
            for (var tmpP:Long = 0; tmpP < places; tmpP++) {
                val p = tmpP as Int;
                val localMap = tx.evalAt(p, () => {
                    val setIter = tx.keySet().iterator();                    
                    val pMap = new HashMap[Long,ArrayList[Int]]();
                    while (setIter.hasNext()) {
                        val vertex = setIter.next();
                        val cl = tx.get(vertex);                        
                        if (cl != null) {
                            val clusterId = (cl as CloneableLong).v;
                            var tmpList:ArrayList[Int] = pMap.getOrElse(clusterId, null);
                            if (tmpList == null) {
                                tmpList = new ArrayList[Int]();
                                pMap.put (clusterId, tmpList);
                            }
                            tmpList.add(vertex);
                        }
                    }
                    return pMap;
                }) as HashMap[Long,ArrayList[Int]];
                
                val iter = localMap.keySet().iterator();
                while (iter.hasNext()) {
                    val pl = iter.next();
                    var list:ArrayList[Int] = map.getOrElse(pl, null);
                    if (list == null) {
                        list = new ArrayList[Int]();
                        map.put (pl, list);
                    }
                    val localList = localMap.getOrThrow(pl);
                    list.addAll(localList);
                }
            }
            
            return map;
        });
        val mergedMap = result.output as HashMap[Long,ArrayList[Int]];
        
        val iter = mergedMap.keySet().iterator();
        while (iter.hasNext()) {
            val key = iter.next();
            val list = mergedMap.getOrThrow(key);
            var str:String = "";
            for (x in list) {
                str += x + " ";
            }
            Console.OUT.println("Cluster " + key + " = { " + str + " }");
        }
    }

    /**
     * Calls betweeness, prints out the statistics and what not.
     */
    private static def crunchNumbers(map:ResilientNativeMap[Int], rmat:Rmat, permute:Int, clusterSize:Long, places:Long, verbose:Int) {
        var time:Long = System.nanoTime();

        val plh = PlaceLocalHandle.makeFlat[SSCA2Cluster](Place.places(), ()=>SSCA2Cluster.make(map, rmat, permute, places, new Random(here.id), verbose));

        val distTime = (System.nanoTime()-time)/1e9;
        time = System.nanoTime();

        val myGraph = plh().graph;
        val N = myGraph.numVertices();
        val M = myGraph.numEdges();
        Console.OUT.println("Graph details: N=" + N + ", M=" + M);

        val max = places;

        // Loop over all the places and crunch the numbers.
        Place.places().broadcastFlat(()=>{
                val h = here.id as Int;
                plh().generateClusters((N as Long*h/max) as Int, (N as Long*(h+1)/max) as Int, clusterSize);
            });

        time = System.nanoTime() - time;
        val procTime = time/1E9;
        val totalTime = distTime + procTime;
        val procPct = procTime*100.0/totalTime;

        //if(verbose > 2) 
            plh().printClusters();

        Console.OUT.println("Places: " + max + "  N: " + N + "  Setup: " + distTime + "s  Processing: " + procTime + "s  Total: " + totalTime + "s  (proc: " + procPct  +  "%).");
    }

    /**
     * Reads in all the options and calculate betweenness.
     */
    public static def main(args:Rail[String]):void {
        val cmdLineParams = new OptionsParser(args, new Rail[Option](0L), [
            Option("sp", "", "Spare places"),
            Option("cs", "", "Cluster size"),
            Option("s", "", "Seed for the random number"),
            Option("n", "", "Number of vertices = 2^n"),
            Option("a", "", "Probability a"),
            Option("b", "", "Probability b"),
            Option("c", "", "Probability c"),
            Option("d", "", "Probability d"),
            Option("p", "", "Permutation"),
            Option("v", "", "Verbose")]);

        val spare:Long = cmdLineParams("-sp", 0);
        val clusterSize:Long = cmdLineParams("-cs", 10);
        val seed:Long = cmdLineParams("-s", 2);
        val n:Int = cmdLineParams("-n", 2n);
        val a:Double = cmdLineParams("-a", 0.55);
        val b:Double = cmdLineParams("-b", 0.1);
        val c:Double = cmdLineParams("-c", 0.1);
        val d:Double = cmdLineParams("-d", 0.25);
        val permute:Int = cmdLineParams("-p", 1n); // on by default
        val verbose:Int = cmdLineParams("-v", 0n); // off by default

        Console.OUT.println("Running SSCA2 with the following parameters:");
        Console.OUT.println("clusterSize = " + clusterSize);
        Console.OUT.println("seed = " + seed);
        Console.OUT.println("N = " + (1<<n));
        Console.OUT.println("a = " + a);
        Console.OUT.println("b = " + b);
        Console.OUT.println("c = " + c);
        Console.OUT.println("d = " + d);
        
        val mgr = new PlaceManager(spare, false);
        val activePlaces = mgr.activePlaces();
        val immediateRecovery = true;
        val store = ResilientStore.make[Int](activePlaces, immediateRecovery);
        val map = store.makeMap();
        
        Console.OUT.println("spare places = " + spare);
        Console.OUT.println("active places = " + activePlaces.size());
        
        
        crunchNumbers(map, Rmat(seed, n, a, b, c, d), permute, clusterSize, activePlaces.size(), verbose);
    }
}
