#!/usr/bin/env python3
"""R2 regime (l1 A=1, s'<l0 A). For the B0'-block cols s'+j (0<j<l1(A[n])) of A[n],
classify each by location: in G'-region (idx < l0 A + l1 A, where elem(A[n])=elem A)
vs bumped region (idx >= l0 A + l1 A). Report the ranges and verify the two
domination facts:
 (G) for s'+j < l0 A + l1 A:  elem A s' m < elem A (s'+j) m   (raw dom in A)
 (B) for s'+j >= l0 A + l1 A: elem(A[n]) s' m < elem(A[n]) (s'+j) m  (bumped)
all for m < t'. A=predecessor, En=A[n]."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,2)(3,3,0)"]
    visited=set(); CAP=3000
    g_ok=g_bad=0; b_ok=b_bad=0
    ncase=0; gcols=0; bcols=0
    bad=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(4):
            frontier=[]
            for Ap in Q:
                l0P=l0(Ap); l1P=l1(Ap); tP=max_parent_level(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    if l1P!=1 or tP is None: continue
                    if not s < l0P: continue
                    ncase+=1
                    bound = l0P + l1P   # l0 A + l1 A
                    for j in range(1, L1):
                        c = s + j
                        for m in range(0, t):
                            if c < bound:
                                gcols+=1 if m==0 else 0
                                if elem(Ap,s,m) < elem(Ap,c,m): g_ok+=1
                                else:
                                    g_bad+=1
                                    if len(bad)<8: bad.append(("G",fmt(Ap),nn,s,c,m,bound))
                            else:
                                bcols+=1 if m==0 else 0
                                if elem(A,s,m) < elem(A,c,m): b_ok+=1
                                else:
                                    b_bad+=1
                                    if len(bad)<8: bad.append(("B",fmt(Ap),nn,s,c,m,bound))
            Q=frontier
            if len(visited)>CAP: break
    print(f"R2 cases: {ncase} | G-region cols counted: {gcols} | bumped cols: {bcols}")
    print(f"(G) elem A s' m < elem A (s'+j) m  [s'+j < l0A+l1A]: OK={g_ok} BAD={g_bad}")
    print(f"(B) elem En s' m < elem En (s'+j) m [s'+j>= l0A+l1A]: OK={b_ok} BAD={b_bad}")
    for x in bad: print("  ",x)
if __name__=='__main__': main()
