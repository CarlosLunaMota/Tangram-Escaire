#!/usr/bin/python
# -*- coding: utf-8 -*-

from math import sqrt, hypot, sin, cos, atan2, pi
from itertools import permutations, combinations
from pyx import *

from time import time

### BASIC AUXILIARY FUNCTIONS ##################################################

def dist(P, Q):
    """Returns the distance between the 2D points P and Q"""
    
    return hypot(Q[0]-P[0], Q[1]-P[1])

def area(polygon):
    """Returns the signed area of the polygon (positive if counterclockwise)"""
    
    return sum(polygon[i-1][0]*polygon[i][1] - polygon[i-1][1]*polygon[i][0]
               for i in range(len(polygon))) / 2

def angle(P, Q, R):
    """Returns the angle between vector Q->P and vector Q->R"""
    
    a = atan2(R[1]-Q[1], R[0]-Q[0]) - atan2(P[1]-Q[1], P[0]-Q[0])
    if a < 0: return a + 2*pi
    else:     return a 

def cross(P, Q, R):
    """Crossproduct of vector Q->P and R->P"""
    
    return ((Q[0]-P[0]) * (R[1]-P[1])) - ((Q[1]-P[1]) * (R[0]-P[0]))

### AUXILIARY FUNCTIONS FOR POLYGONS ###########################################
    
def simplify(polygon, eps=0.0001):
    """Eliminates redundant (=aligned) consecutive vertices from the polygon"""
    
    P = list(p for p in polygon)
    N = len(polygon)
    i = N-1
    while i >= 0 and N > 3:
        if abs(cross(P[i-2], P[i-1], P[i])) > eps: i -= 1
        else:
            P.pop(i-1)
            N -= 1
            i  = N-1
    return P

def is_convex(polygon, eps=0.0001):
    """
    Tests if the polygon is strictly convex.

    The polygon vertices are assumed to be in counter-clock-wise order.
    """
    
    P = polygon
    return all(cross(P[i-2],P[i-1],P[i]) >= eps for i in range(len(P)))

def is_symmetric(polygon, sym_axial=True, sym_rotational=True, eps=0.0001):

    N = len(polygon)

    if sym_axial:

        M = N//2
        D = [dist(               polygon[i-1], polygon[i]) for i in range(N)]
        A = [angle(polygon[i-2], polygon[i-1], polygon[i]) for i in range(N)]

        for i in range(N):
            DD = D[i:] + D[:i]
            AA = A[i:] + A[:i]

            # Symmetry through a vertex:
            if all((abs(DD[j]-DD[-j-1]) < eps and abs(AA[j]-AA[-j]) < eps)
                    for j in range(0, M+1)): return True

            # Symmetry through an edge:
            if all((abs(DD[j]-DD[-j]) < eps and abs(AA[j+1]-AA[-j]) < eps)
                    for j in range(0, M+1)): return True

    if sym_rotational:
        
        O = (sum(p[0] for p in polygon)/N, sum(p[1] for p in polygon)/N)
        D = [dist(O, polygon[i]) for i in range(N)]
        K = [k for k in range(1, N) if N%k == 0]

        for k in K:
            a = angle(polygon[0], O, polygon[k])
            if all(abs(angle(polygon[i], O, polygon[i+k])-a) < eps and
                   abs(D[i]-D[i+k]) < eps for i in range(-N,1)): return True
        
    return False

def symmetry_angle(polygon, sym_axial=True, sym_rotational=True, eps=0.0001):

    N = len(polygon)

    O = (0,0)
    OO = (1,0)

    if sym_axial:

        M = N//2
        D = [dist(               polygon[i-1], polygon[i]) for i in range(N)]
        A = [angle(polygon[i-2], polygon[i-1], polygon[i]) for i in range(N)]

        for i in range(N):
            
            P  = polygon[i-1]
            Q  = polygon[i]
            PQ = ((P[0]+Q[0])/2, (P[1]+Q[1])/2) 

            R  = polygon[(i-1+M)%N]
            S  = polygon[ i-1-M]
            T  = polygon[ i  -M]
            RS = ((R[0]+S[0])/2, (R[1]+S[1])/2) 
            RT = ((R[0]+T[0])/2, (R[1]+T[1])/2) 
            
            av = pi/2-angle((P[0] +1,P[1] ), P,  RS)
            ae = pi/2-angle((PQ[0]+1,PQ[1]), PQ, RT)
            
            DD = D[i:] + D[:i]
            AA = A[i:] + A[:i]

            # Symmetry through a vertex i-1:
            if all((abs(DD[j]-DD[-j-1]) < eps and abs(AA[j]-AA[-j]) < eps)
                    for j in range(M+1)): return av

            # Symmetry through an edge i-1 -- i:
            if all((abs(DD[j]-DD[-j]) < eps and abs(AA[j+1]-AA[-j]) < eps)
                    for j in range(M+1)): return ae

    if sym_rotational:
        O = (sum(p[0] for p in polygon)/N, sum(p[1] for p in polygon)/N)
        D = [dist(O, polygon[i]) for i in range(N)]
        K = [k for k in range(1, N) if N%k == 0]

        for k in K:
            a = angle(polygon[0], O, polygon[k])
            if all(abs(angle(polygon[i], O, polygon[i+k])-a) < eps and
                   abs(D[i]-D[i+k]) < eps for i in range(-N,1)): return 0
        
    return None

def are_congruent(polygon_1, polygon_2, eps=0.0001):
    """
    Tests if the polygons are congruent.

    The polygons are assumed to be simplified and in counterclockwise order.
    """

    P = polygon_1  
    Q = polygon_2

    if len(P) == len(Q):
        
        N  = len(P)
        Ps = [(dist(P[i],P[i-1]), angle(P[i],P[i-1],P[i-2])) for i in range(N)]
        Qs = [(dist(Q[i],Q[i-1]), angle(Q[i],Q[i-1],Q[i-2])) for i in range(N)]

        for i in range(N):
            if all(abs(p[0]-q[0]) < eps and abs(p[1]-q[1]) < eps
                   for p,q in zip(Ps,Qs[i:]+Qs[:i])): return True

        Q  = [(-q[0], q[1]) for q in reversed(Q)]
        Qs = [(dist(Q[i],Q[i-1]), angle(Q[i],Q[i-1],Q[i-2])) for i in range(N)]

        for i in range(N):
            if all(abs(p[0]-q[0]) < eps and abs(p[1]-q[1]) < eps
                   for p,q in zip(Ps,Qs[i:]+Qs[:i])): return True

    return False

### AUXILIARY FUNCTIONS FOR TRIANGLES ##########################################

def draw(triangles, name, alpha=0):
    """Draws the triangles in a PDF file with the given name"""

    drawing = []
    STYLE = [style.linewidth.THick, style.linestyle.solid,
             style.linecap.round, style.linejoin.round, color.grey.black,
             deco.filled([color.cmyk.Goldenrod])]

    # Draw the triangles:
    c,s = cos(alpha), sin(alpha)
    for triangle in triangles:
        p = triangle[0]
        q = triangle[1]
        r = triangle[2]
        drawing.append((path.path(path.moveto(p[0]*c - p[1]*s, p[0]*s + p[1]*c),
                                  path.lineto(q[0]*c - q[1]*s, q[0]*s + q[1]*c),
                                  path.lineto(r[0]*c - r[1]*s, r[0]*s + r[1]*c),
                                  path.closepath()), STYLE))

    mycanvas = canvas.canvas()
    for (p, s) in drawing: mycanvas.stroke(p, s)
    #mycanvas.writeEPSfile(name)
    mycanvas.writePDFfile(name)

def draw_shape(triangles, name, alpha=0):
    """Draws the triangles in a PDF file with the given name"""

    drawing = []
    STYLE = [style.linewidth.THick, style.linestyle.solid,
             deco.filled([color.grey.black]), color.grey.black,
             style.linecap.round, style.linejoin.round]
             
    # Draw the triangles:
    c,s = cos(alpha), sin(alpha)
    for triangle in triangles:
        p = triangle[0]
        q = triangle[1]
        r = triangle[2]
        drawing.append((path.path(path.moveto(p[0]*c - p[1]*s, p[0]*s + p[1]*c),
                                  path.lineto(q[0]*c - q[1]*s, q[0]*s + q[1]*c),
                                  path.lineto(r[0]*c - r[1]*s, r[0]*s + r[1]*c),
                                  path.closepath()), STYLE))

    mycanvas = canvas.canvas()
    for (p, s) in drawing: mycanvas.stroke(p, s)
    #mycanvas.writeEPSfile(name)
    mycanvas.writePDFfile(name)

def same_triangles(T1, T2, eps=0.0001):
    """Tests if T1 and T2 contain the same triangles in different order"""

    if len(T1) != len(T2): return False

    # Sort by area and edge lengths
    T1 = sorted((area(t), max(dist(t[i-1],t[i]) for i in range(3)), t) for t in T1)
    T2 = sorted((area(t), max(dist(t[i-1],t[i]) for i in range(3)), t) for t in T2)
    
    # Compare with all 3 rotations (both triangles are counterclockwise!)
    for (a1,d1,t1),(a2,d2,t2) in zip(T1,T2):
        if abs(a1-a2) > eps: return False
        T = ((t2[0],t2[1],t2[2]), (t2[1],t2[2],t2[0]), (t2[2],t2[0],t2[1]))
        if not any(all(dist(p,q) < eps for p,q in zip(t1,t)) for t in T):
            return False
        
    return True
    
def dont_collide(triangles, triangle, eps=0.0001):
    """
    Tests if a triangle doesn't collide with any element of the triangles list.

    All triangle vertices are assumed to be in counterclockwise order
    """
    
    A,B,C     = triangle
    triangles = [t for t in triangles]
    return all(any(
              [all(a<eps for a in (area((A,B,X)),area((A,B,Y)),area((A,B,Z)))),
               all(a<eps for a in (area((B,C,X)),area((B,C,Y)),area((B,C,Z)))),
               all(a<eps for a in (area((C,A,X)),area((C,A,Y)),area((C,A,Z)))),
               all(a<eps for a in (area((X,Y,A)),area((X,Y,B)),area((X,Y,C)))),
               all(a<eps for a in (area((Y,Z,A)),area((Y,Z,B)),area((Y,Z,C)))),
               all(a<eps for a in (area((Z,X,A)),area((Z,X,B)),area((Z,X,C))))])
               for X,Y,Z in triangles)

### MAIN FUNCTIONS #############################################################

def explore(boundary, triangles, pieces, eps=0.0001):
    """
    Given a list of triangles (such that each one of them is given in counter-
    clockwise order), its boundary (also given in counterclockwise order) and
    a list of triangular pieces (each one of them given as a list of its edge
    lengths), this recursive function yields the (boundary, triangles) pairs
    of all the figures that can be formed by attaching these pieces to the
    original boundary in any order.

    Each attached piece must have one corner in common and touch side-by-side
    with, at least, one previously placed piece. Pieces may never overlap.    
    """

    if not pieces: yield (boundary, triangles)

    for k,piece in enumerate(pieces):

        new_p = pieces[::]
        new_p.remove(piece)

        for j,(A,B,C) in enumerate(permutations(piece)):

            k1 = (B**2 - C**2 + A**2) / (2*A)
            k2 = sqrt(B**2 - k1**2)

            for i in range(len(boundary)):

                # Glue piece to segment P-Q
                P = boundary[i-1]
                Q = boundary[i]
                D = dist(P,Q)

                # The piece fits perfectly:
                if abs(D-A) < eps:
                    X =  P
                    Y =  Q
                    Z = (X[0] + (Y[0]-X[0])*k1/A + (Y[1]-X[1])*k2/A,
                         X[1] + (Y[1]-X[1])*k1/A - (Y[0]-X[0])*k2/A)

                    if dont_collide(triangles, (Z,Y,X)):
                        new_t = triangles[::] + [(Z,Y,X)]
                        new_b = boundary[:i] + [Z] + boundary[i:]
                        yield from explore(new_b, new_t, new_p)
                    
                else:

                    # Snap piece to P
                    X =  P
                    Y = (P[0] + (Q[0]-P[0])*A/D, P[1] + (Q[1]-P[1])*A/D)
                    Z = (X[0] + (Y[0]-X[0])*k1/A + (Y[1]-X[1])*k2/A,
                         X[1] + (Y[1]-X[1])*k1/A - (Y[0]-X[0])*k2/A)

                    if dont_collide(triangles, (Z,Y,X)):
                        new_t = triangles[::] + [(Z,Y,X)]
                        new_b = boundary[:i] + [Z, Y] + boundary[i:]
                        yield from explore(new_b, new_t, new_p)
                    
                    # Snap piece to Q
                    V = (Q[0]-Y[0], Q[1]-Y[1])
                    X = (X[0]+V[0], X[1]+V[1])
                    Y = (Y[0]+V[0], Y[1]+V[1])
                    Z = (Z[0]+V[0], Z[1]+V[1])

                    if dont_collide(triangles, (Z,Y,X)):
                        new_t = triangles[::] + [(Z,Y,X)]
                        new_b = boundary[:i] + [X, Z] + boundary[i:]
                        yield from explore(new_b, new_t, new_p)

def get_all_figures(debug=True, min_sides=3, max_sides=4,
                    all_convex=True, sym_axial=True, sym_rotational=True):
    """
    Explores all the figures that can be formed with these pieces and:

     * Draws all the polygons in the selected range of sides
     * Draws all convex figures if `all_convex == True`
     * Draws all figures with axial symmetry if `sym_axial == True`
     * Draws all figures with rotational symmetry if `sym_rotational == True`

    If `debug == True` a copy of each figure is drawn as soon as it is found.
    """

    R3 = sqrt(3.0)

    # Get the initial piece:
    boundary, triangles = [(0,0),(2*R3,0),(0,2)], [((0,0),(2*R3,0),(0,2))]
    
    # Get remaining pieces:
    pieces = [(1, 2, sqrt(3)), (3, R3, 2*R3), (2, 2, 2), (2, 2, 2*R3)]

    # Get experiment name:
    name = "Escaire"
    
    ### EXPLORE THE SOLUTION SPACE #############################################

    if debug: print("Exploring the solution space of "+name+":\n")

    C = [None, None, None, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}]  # convex
    P = [None, None, None, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}]  # polygons
    S = [None, None, None, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}]  # symmetric

    for n, (b,t) in enumerate(explore(boundary, triangles, pieces)):

        shape = tuple(simplify(b))
        sides = len(shape)

        # Store polygon:
        if min_sides <= sides <= max_sides:
            found = False
            for s in P[sides]:
                if are_congruent(s, shape):
                    found = True
                    if all(not same_triangles(t, tt) for tt in P[sides][s]):
                        P[sides][s].append(t)
                        if debug: draw(t, "D-"+name+"-P{}-{}".format(sides,n))            
            if not found:
                P[sides][shape] = [t]
                if debug: draw(t, "D-"+name+"-P{}-{}".format(sides,n))
                if debug: draw_shape(t, "D-"+name+"-P{}-{}s".format(sides,n))            

        # Store convex shape:
        if all_convex and is_convex(shape):
            found = False
            for s in C[sides]:
                if are_congruent(s, shape):
                    found = True
                    if all(not same_triangles(t, tt) for tt in C[sides][s]):
                        C[sides][s].append(t)
                        if debug: draw(t, "D-"+name+"-C{}-{}".format(sides,n))
            if not found:
                C[sides][shape] = [t]
                if debug: draw(t, "D-"+name+"-C{}-{}".format(sides,n))
                if debug: draw_shape(t, "D-"+name+"-C{}-{}s".format(sides,n))

        # Store symmetric shape:
        if is_symmetric(shape, sym_axial, sym_rotational):
            found = False
            alpha = symmetry_angle(shape)
            for s in S[sides]:
                if are_congruent(s, shape):
                    found = True
                    if all(not same_triangles(t, tt) for tt in S[sides][s]):
                        S[sides][s].append(t)
                        if debug: draw(t, "D-"+name+"-S{}-{}".format(sides,n), alpha)
            if not found:
                S[sides][shape] = [t]
                if debug: draw(t, "D-"+name+"-S{}-{}".format(sides,n), alpha)
                if debug: draw_shape(t, "D-"+name+"-S{}-{}s".format(sides,n), alpha)

    ### OUTPUT RESULTS #########################################################

    # Print polygons
    for i in range(max(min_sides,3), min(max_sides+1,len(P))):
        for j,shape in enumerate(P[i]):
            draw_shape(P[i][shape][0], name+"-polygon-{:02d}-{:04d}".format(i, j+1))
            for k,t in enumerate(P[i][shape]):
                draw(t, name+"-polygon-{:02d}-{:04d}-{}".format(i, j+1, k+1))
                
    # Print convex shapes
    j = 0
    for i in range(3, len(C)):
        for shape in C[i]:
            j += 1
            draw_shape(C[i][shape][0], name+"-convex-{:02d}-{:04d}".format(i, j))
            for k,t in enumerate(C[i][shape]):
                draw(t, name+"-convex-{:02d}-{:04d}-{}".format(i, j, k+1))

    # Print symmetric shapes
    j = 0
    for i in range(3, len(S)):
        for shape in S[i]:
            j += 1
            alpha = symmetry_angle(shape)
            draw_shape(S[i][shape][0], name+"-symmetric-{:02d}-{:04d}".format(i, j), alpha)
            for k,t in enumerate(S[i][shape]):
                draw(t, name+"-symmetric-{:02d}-{:04d}-{}".format(i, j, k+1), alpha)

### MAIN FUNCTION ##############################################################

if __name__ == "__main__":

    get_all_figures(debug=True, min_sides=3, max_sides=4,
                    all_convex=True, sym_axial=True, sym_rotational=True)

################################################################################
