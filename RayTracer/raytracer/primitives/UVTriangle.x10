package raytracer.primitives;

import raytracer.*;

public final class UVTriangle extends Primitive {
    val p1:Vector3;
    val e1:Vector3, e2:Vector3;
    val n:Vector3;
    val m:Material;
    val tc1:Vector2, tc2:Vector2, tc3:Vector2; // tex coords
    val texSquash:Float;
    public def this (p1:Vector3, tc1:Vector2, p2:Vector3, tc2:Vector2, p3:Vector3, tc3:Vector2, m:Material) {
        this.p1 = p1;
        this.e1 = p2 - p1;
        this.e2 = p3 - p1;
        this.tc1 = tc1;
        this.tc2 = tc2;
        this.tc3 = tc3;
        this.m = m;
        this.n = e1.cross(e2).normalised();
        val space_area = e1.cross(e2).length()*0.5f;
        val uv_e1 = tc2 - tc1;
        val uv_e2 = tc3 - tc1;
        val uv_area = uv_e1.cross(uv_e2)*0.5f;
        texSquash = uv_area / space_area;
    }
    public def getAABB() = AABB(Vector3.min(p1,Vector3.min(p1+e1, p1+e2)), Vector3.max(p1,Vector3.max(p1+e1, p1+e2)));
    public def intersectRay (st:RayState) {
        // from http://www.cs.virginia.edu/~gfx/Courses/2003/ImageSynthesis/papers/Acceleration/Fast%20MinimumStorage%20RayTriangle%20Intersection.pdf
        val h = st.d.cross(e2);
        val a = e1.dot(h);

        if (a < 0.00001) return;

        val s = st.o - p1;
        val E1 = s.dot(h);

        if (E1 < 0.0 || E1 > a) return;

        val q = s.cross(e1);
        val E2 = st.d.dot(q);

        if (E2 < 0.0 || E1 + E2 > a) return;

        val t = e2.dot(q);

        val f = 1/a;

        val t_ = t * f;
        val E1_ = E1 * f;
        val E2_ = E2 * f;

        if (t_ < 0.00001) return;
        if (t_ >= st.t) return;

        st.t = t_;
        st.normal = n;
        st.mat = m;
        st.texCoord = (1-E1_-E2_)*tc1 + E1_*tc2 + E2_*tc3;

        st.texSquash = texSquash / (-st.d.dot(n));
    }
}

