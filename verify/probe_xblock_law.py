#!/usr/bin/env python3
"""When block-0 source idx_B(0,j) has parent p0 in G (<l0), block-n source idx_B(n,j)
has parent pN. Find the law for pN. Hypotheses:
 (L1) pN = p0 + n*l1  (shifted by n blocks)? 
 (L2) pN = idx_B(n, ?) i.e. in block n?
 (L3) pN relates to p0 via the ancestry chain. 
Also KEY: is m_ancestor(A[n]) k (idx_B(0,j)) i  ⟺  m_ancestor(A[n]) k (idx_B(n,j)) i (clause i, target i in G)?
This is the TRUE clause-i claim — verify it's the 0-violation one."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def idxB(l0,l1,c,j): return l0+c*l1+j
def main():
    seeds=["(0,0)(1,1)(2,2)","(0,0,0)(1,1,1)","(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)",
           "(0,0)(1,1)(2,0)(3,1)","(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)"]
    visited=set(); CAP=700
    ci_ok=ci_bad=0; l1law=l2law=0; ncase=0
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
                    for i in range(0,L0):       # G target
                        for j in range(0,L1):
                            i0=idxB(L0,L1,0,j); iN=idxB(L0,L1,nn,j)
                            if iN>=len(A): continue
                            for k in range(0,H):
                                # clause i (true claim): m_anc to G target i
                                a0=m_anc(A,k,i0,i); aN=m_anc(A,k,iN,i)
                                ncase+=1
                                if a0==aN: ci_ok+=1
                                else:
                                    ci_bad+=1
                                    if len(bad)<8: bad.append((fmt(Ap),nn,i,j,k,a0,aN))
            Q=frontier
            if len(visited)>CAP: break
    print(f"clause-i cases (G target): {ncase}")
    print(f"clause i (m_anc to G target i): block0==blockn: OK={ci_ok} BAD={ci_bad}")
    for x in bad: print("  ",x)
if __name__=='__main__': main()
