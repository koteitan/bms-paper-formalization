#!/usr/bin/env python3
"""Cross-block landing: when m_parent(A[n]) k (idx_B A 0 j) is outside block 0 (in G, <l0),
what is m_parent(A[n]) k (idx_B A n j)? Test the clause-i transfer hypothesis:
 (T) m_parent(A[n]) k (idx_B A 0 j) = Some g (g<l0) ⟺ m_parent(A[n]) k (idx_B A n j) = Some g (SAME g in G).
i.e. when the block-0 source's parent is in G, the block-n source has the SAME G parent."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def idxB(l0,l1,c,j): return l0+c*l1+j
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)",
           "(0,0)(1,1)(2,0)(3,1)","(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)",
           "(0,0,0)(1,1,1)(2,2,2)(3,3,0)"]
    visited=set(); CAP=900
    T_ok=T_bad=0; ncase=0
    bad=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(3):
            frontier=[]
            for Ap in Q:
                L1=l1(Ap); L0=l0(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A); H=height(A)
                    if L1<1: continue
                    for j in range(0,L1):
                        i0=idxB(L0,L1,0,j); iN=idxB(L0,L1,nn,j)
                        if iN>=len(A): continue
                        for k in range(0,H):
                            p0=m_parent(A,k,i0)
                            # only when block-0 parent in G (<L0)
                            if p0 is None or p0>=L0: continue
                            pN=m_parent(A,k,iN)
                            ncase+=1
                            if pN==p0: T_ok+=1
                            else:
                                T_bad+=1
                                if len(bad)<10: bad.append((fmt(Ap),nn,j,k,p0,pN,L0))
            Q=frontier
            if len(visited)>CAP: break
    print(f"cases (block-0 parent in G): {ncase}")
    print(f"(T) block-n parent == same G col: OK={T_ok} BAD={T_bad}")
    for x in bad: print("  ",x)
if __name__=='__main__': main()
