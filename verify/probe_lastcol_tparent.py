#!/usr/bin/env python3
"""mpl(A[n])>=mpl A  <=>  last col of A[n] has a parent at level t=mpl A.
Test: when l1(A[n])>=2, is m_parent(A[n]) (mpl A) (last col A[n]) != None?
Also: what is that parent (does it relate to idx_B A n (l1-1)'s structure)?"""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)"]
    visited=set(); CAP=1200
    has_ok=has_bad=0; ncase=0
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(4):
            frontier=[]
            for Ap in Q:
                tP=max_parent_level(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    L1=l1(A)
                    if tP is None or L1<2: continue
                    ncase+=1
                    lc=len(A)-1
                    p=m_parent(A,tP,lc)   # parent at level mpl A
                    if p is not None: has_ok+=1
                    else:
                        has_bad+=1
            Q=frontier
            if len(visited)>CAP: break
    print(f"design-regime (l1(A[n])>=2) cases: {ncase}")
    print(f"last col of A[n] HAS parent at level mpl A: OK={has_ok} BAD={has_bad}")
if __name__=='__main__': main()
