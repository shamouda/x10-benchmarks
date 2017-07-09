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
import x10.util.resilient.localstore.TxConfig;
import x10.util.resilient.localstore.LockingTx;
import x10.util.resilient.localstore.LocalTx;
import x10.util.resilient.localstore.AbstractTx;
import x10.util.resilient.localstore.tx.FatalTransactionException;
import x10.util.resilient.localstore.Cloneable;
import x10.util.resilient.localstore.tx.ConflictException;
import x10.util.ArrayList;
import x10.util.HashMap;
import x10.util.HashSet;

public final class SSCA2Cluster(N:Int) {
    val graph:Graph;
    val verbose:Int;
    val verticesToWorkOn = new Rail[Int](N, (i:Long)=>i as Int);
    val map:ResilientNativeMap[Int];
    val places:Long;
    val verticesPerPlace:Long;
    val random:Random;
    
    public static struct Color implements Cloneable {
        public val placeId:Long;
        public val clusterId:Long;
    
        def this(p:Long, c:Long) {
            placeId = p;
            clusterId = c;
        }
        
        public def clone() = new Color(placeId, clusterId);
    };
    
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
    
    private def getAdjacentVertecesPlaces(v:Int, edgeStart:Int, edgeEnd:Int) {
        val map = new HashMap[Long,HashSet[Int]]();
        var dest:Long = vertexPlace(v);
        var set:HashSet[Int] = new HashSet[Int]();
        set.add(v);
        map.put (dest, set);
        
        // Iterate over all its neighbors
        for(var wIndex:Int=edgeStart; wIndex<edgeEnd; ++wIndex) {
            // Get the target of the current edge.
            val w:Int = graph.getAdjacentVertexFromIndex(wIndex);
    		dest = vertexPlace(w);
        
    		set = map.getOrElse(dest, null);
    		if (set == null) {
    			set = new HashSet[Int]();
    			map.put(dest, set);
    		}
    		set.add(w);
        }
        if (verbose > 1n) {
            printVertexPlaceMap(v, map);
        }
        return map;
    }
    
    private def printVertexPlaceMap(v:Int, map:HashMap[Long,HashSet[Int]]) {
        var str:String = "vertexMap v=" + v + ":";
        val iter = map.keySet().iterator();
        while (iter.hasNext()) {
            val pl = iter.next();
            str += " place(" + pl + ") {";
            val set = map.getOrThrow(pl);
            for (l in set) {
                str += l + " ";
            }
            str += "}";
        }
        Console.OUT.println(str);
    } 
    
    private def processVertex(v:Int, placeId:Long, clusterId:Long, tx:AbstractTx[Int], clusterSize:Long, accum:Long):Long {
        // Get the start and the end points for the edge list for "v"
        val edgeStart:Int = graph.begin(v);
        val edgeEnd:Int = graph.end(v);
        val edgeCount:Int = edgeEnd-edgeStart ;
    
        var innerCount:Long = 0;
        var outerCount:Long = 0;
        val map = getAdjacentVertecesPlaces(v, edgeStart, edgeEnd);
        val iter = map.keySet().iterator();
        finish { /*finish is important to prevent concurrent actions on the same transaction at a certain place*/
	        while (iter.hasNext()) {
	            val dest = iter.next();
	            val vertices = map.getOrThrow(dest);
	            innerCount += vertices.size();
	            
	            if (verbose > 1n) Console.OUT.println(here + " tx["+tx.id+"].asyncAt("+dest+") started");
	            tx.asyncAt(dest, () => {
	                for (s in vertices) {
	                    val color = tx.get(s);
	                    if (color == null)
	                        tx.put(s, new Color(placeId, clusterId));
	                    else if (! ((color as Color).placeId == placeId && (color as Color).clusterId == clusterId ) )
	                        throw new ConflictException("Tx[" + tx.id + "] " + here + " vertex " + s + " allocated by place " + (color as Color).placeId, here);
	                }
	            });
	        }
        }
        
        outerCount = accum + innerCount;
        
        if (verbose > 1n) Console.OUT.println(here + " tx["+tx.id+"] edgeCount="+edgeCount + " outerCount["+outerCount+"] < clusterSize["+clusterSize+"]=" + (outerCount < clusterSize));
        if (edgeCount > 0 && outerCount < clusterSize) {
            val indx = Math.abs(random.nextInt()) % edgeCount;
            val nextV:Int = graph.getAdjacentVertexFromIndex(edgeStart + indx);
            outerCount = processVertex(nextV, placeId, clusterId, tx, clusterSize, accum + innerCount) ;
        }
        
        return outerCount;
    }
    
    /**
     * Dump the clusters.
     */
    private def generateClusters(val startVertex:Int, val endVertex:Int, clusterSize:Long, g:Long) {
        Console.OUT.println(here + " " + startVertex + "-" + endVertex);
        val placeId = here.id;
        // Iterate over each of the vertices in my portion.
        var c:Long = 1;
        val vCount = endVertex - startVertex;
        for(var vertexIndex:Int=startVertex; vertexIndex<endVertex; ++vertexIndex, ++c) { 
            val s:Int = verticesToWorkOn(vertexIndex);
            val dest = vertexPlace(s);

            val clusterId = c;
            val closure = (tx:AbstractTx[Int]) => {
                return processVertex(s, placeId, clusterId, tx, clusterSize, 0);
            };
            
            try {
            	if (verbose > 0) Console.OUT.println(here + " vertex["+s+"] cluster started   ["+clusterId+"/"+vCount+"]");
                val result = map.executeTransaction(null, closure, 1, -1);
                if (g > 0 && clusterId%g == 0) Console.OUT.println(here + " vertex["+s+"] cluster succeeded ["+clusterId+"/"+vCount+"], count=" + result.output);
            } catch (ex:Exception) {
                if (verbose > 0) Console.OUT.println(here + " vertex["+s+"] cluster failed    ["+clusterId+"/"+vCount+"]   msg["+ex.getMessage()+"] ");
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
                            val clusterId = ((cl as Color).placeId+1) * 1000000 + (cl as Color).clusterId;
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
    private static def crunchNumbers(map:ResilientNativeMap[Int], rmat:Rmat, permute:Int, clusterSize:Long, places:Long, g:Long, r:Long, verbose:Int) {
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
                plh().generateClusters((N as Long*h/max) as Int, (N as Long*(h+1)/max) as Int, clusterSize, g);
                Console.OUT.println(here + " ... finished ...");
        });

        time = System.nanoTime() - time;
        val procTime = time/1E9;
        val totalTime = distTime + procTime;
        val procPct = procTime*100.0/totalTime;

        if(verbose > 2 || r > 0) 
            plh().printClusters();

        map.printTxStatistics();
        
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
            Option("g", "", "Progress"),
            Option("r", "", "Print resulting clusters"),
            Option("v", "", "Verbose")]);

        val spare:Long = cmdLineParams("-sp", 0);
        val clusterSize:Long = cmdLineParams("-cs", 10);
        val seed:Long = cmdLineParams("-s", 2);
        val n:Int = cmdLineParams("-n", 2n);
        val a:Double = cmdLineParams("-a", 0.55);
        val b:Double = cmdLineParams("-b", 0.1);
        val c:Double = cmdLineParams("-c", 0.1);
        val d:Double = cmdLineParams("-d", 0.25);
        val g:Long = cmdLineParams("-g", -1);
        val r:Long = cmdLineParams("-r", 0);
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
        
        
        crunchNumbers(map, Rmat(seed, n, a, b, c, d), permute, clusterSize, activePlaces.size(), g, r, verbose);
    }
}
