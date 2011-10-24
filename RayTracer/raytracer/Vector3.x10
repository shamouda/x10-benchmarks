package raytracer;

import x10.compiler.Inline;


public struct Vector3(x:Float,y:Float,z:Float) {

    @Inline public operator this + (v:Vector3) = Vector3(x+v.x, y+v.y, z+v.z);
    @Inline public operator this - (v:Vector3) = Vector3(x-v.x, y-v.y, z-v.z);
    @Inline public operator + this = this;
    @Inline public operator - this = Vector3(-x, -y, -z);
    @Inline public operator this * (v:Vector3) = Vector3(x*v.x, y*v.y, z*v.z);
    @Inline public operator this / (v:Vector3) = Vector3(x/v.x, y/v.y, z/v.z);
    @Inline public operator this * (v:Float) = Vector3(x*v, y*v, z*v);
    @Inline public operator (v:Float) * this = Vector3(x*v, y*v, z*v);
    @Inline public operator this / (v:Float) = Vector3(x/v, y/v, z/v);

    @Inline public def length2() = x*x + y*y + z*z;
    @Inline public def length() = Math.sqrtf(length2());
    @Inline public def dot (v:Vector3) = x*v.x + y*v.y + z*v.z;
    @Inline public def cross (v:Vector3) = Vector3(y*v.z - z*v.y,  z*v.x - x*v.z,  x*v.y - y*v.x);
    @Inline public def normalised() = this/length();

    public def toString () = "Vector3("+x+", "+y+", "+z+")";

    @Inline public def maxElement () = Math.max(x, Math.max(y, z));
    @Inline public def minElement () = Math.min(x, Math.min(y, z));

    @Inline public static def max (a:Vector3, b:Vector3) = Vector3(Math.max(a.x, b.x), Math.max(a.y, b.y), Math.max(a.z, b.z));
    @Inline public static def min (a:Vector3, b:Vector3) = Vector3(Math.min(a.x, b.x), Math.min(a.y, b.y), Math.min(a.z, b.z));
    @Inline public def max (o:Vector3) = Vector3(Math.max(x, o.x), Math.max(y, o.y), Math.max(z, o.z));
    @Inline public def min (o:Vector3) = Vector3(Math.min(x, o.x), Math.min(y, o.y), Math.min(z, o.z));

    @Inline public static def lerp (v1:Vector3, v2:Vector3, alpha:Float) = (1-alpha)*v1 + alpha*v2;
    @Inline public static operator (rgb:RGB) as Vector3 = Vector3(rgb.r/255.0f, rgb.g/255.0f, rgb.b/255.0f);

    @Inline public static def reflect (v:Vector3, n:Vector3) {
        val d = v.dot(n);
        return v - 2*d*n;
    }   

    // v and n must be normalised
    @Inline public static def refract (v:Vector3, n:Vector3, n1_n2:Float) {
        // taken from http://www.devmaster.net/articles/raytracing/
        val cosI = v.dot(n); // -1 to 0 for one-sided surfaces
        val c2 = Math.sqrtf(1 - n1_n2*n1_n2*(1 - cosI*cosI)); // 0 if v,n aligned
        return (n1_n2*v + (n1_n2*cosI - c2)*n).normalised();
    }


}

