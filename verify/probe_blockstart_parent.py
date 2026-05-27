#!/usr/bin/env python3
"""Asc levels (k<mpl A): is m_parent(A[n]) k (idx_B A c 0) = idx_B A (c-1) 0 for 1<=c<=n?
(consecutive block-start parent). If so, by trans induction idx_B A 0 0 is k-anc of idx_B A n 0.
Also test the consequence: m_anc(A[n]) k (idx_B A n 0) (idx_B A 0 0)."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def idxB(l0,l1,c,j): return l0+c*l1+j
def ascends(A,d,m,s,t):
    if m>=t: return False
    return (s+d==s) or m_anc(A,m,s+d,s)
def main():
    seeds=["(0,0)(1,1)(2,2)","(0,0,0)(1,1,1)","(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)",
           "(0,0)(1,1)(2,0)(3,1)","(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)",
           "(0,0,0)(1,1,1)(2,2,2)(3,3,0)"]
    visited=set(); CAP=700
    cp_ok=cp_bad=0; anc_ok=anc_bad=0
    bad=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(3):
            frontier=[]
            for Ap in Q:
                L1=l1(Ap); L0=l0(Ap); tP=max_parent_level(Ap); sP=b0_start(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    if tP is None or sP is None or L1!=1: continue
                    for k in range(0,tP):
                        if not ascends(Ap,0,k,sP,tP): continue
                        for c in range(1,nn+1):
                            ic=idxB(L0,L1,c,0); icm=idxB(L0,L1,c-1,0)
                            if ic>=len(A): continue
                            p=m_parent(A,k,ic)
                            if p==icm: cp_ok+=1
                            else:
                                cp_bad+=1
                                if len(bad)<8: bad.append((fmt(Ap),nn,k,c,p,icm))
                        # consequence
                        iN=idxB(L0,L1,nn,0); i0=idxB(L0,L1,0,0)
                        if iN<len(A):
                            if m_anc(A,k,iN,i0): anc_ok+=1
                            else: anc_bad+=1
            Q=frontier
            if len(visited)>CAP: break
    print(f"m_parent(idxB c 0)=idxB(c-1,0) [asc,1<=c<=n]: OK={cp_ok} BAD={cp_bad}")
    print(f"m_anc(idxB n 0)(idxB 0 0) [asc]: OK={anc_ok} BAD={anc_bad}")
    for x in bad: print("  ",x)
if __name__=='__main__': main()
