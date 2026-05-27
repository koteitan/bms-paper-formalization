#!/usr/bin/env python3
"""j=0 asc level: where is m_parent(A[n]) k (idx_B n 0)? Classify: G(<l0), or idx_B(c,off).
Find the recursion law. Also test: is it idx_B(n-1, ?) or block n itself or G?"""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def idxB(l0,l1,c,j): return l0+c*l1+j
def cls(p,L0,L1,nn):
    if p is None: return "None"
    if p<L0: return f"G({p})"
    r=p-L0; c=r//L1; off=r%L1
    return f"B(c={c},off={off})"
def main():
    seeds=["(0,0)(1,1)(2,2)","(0,0,0)(1,1,1)","(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)",
           "(0,0)(1,1)(2,0)(3,1)","(0,0,0)(1,1,1)(2,2,0)"]
    visited=set(); CAP=500; shown=0
    from collections import Counter
    kinds=Counter()
    for seed in seeds:
        if len(visited)>CAP or shown>=24: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(3):
            frontier=[]
            for Ap in Q:
                L1=l1(Ap); L0=l0(Ap); tP=max_parent_level(Ap)
                for nn in range(2,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    if L1!=1 or tP is None or tP<2: continue
                    iN=idxB(L0,L1,nn,0)
                    if iN>=len(A): continue
                    for k in range(1,tP):  # asc levels (k<mpl, k>0)
                        pN=m_parent(A,k,iN)
                        c=cls(pN,L0,L1,nn)
                        kinds[c]+=1
                        if shown<24:
                            shown+=1
                            print(f"A'={fmt(Ap)} n={nn} k={k} l0={L0}: m_parent(idxB n 0)={pN} = {c}")
            Q=frontier
            if len(visited)>CAP or shown>=24: break
    print("dist:", dict(kinds))
if __name__=='__main__': main()
