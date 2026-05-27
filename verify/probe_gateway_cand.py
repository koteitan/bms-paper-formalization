#!/usr/bin/env python3
"""Gateway: a>0, m_parent(A[n]) m (idx_B A n a)=Some p ⟹ idx_B A n 0 ≤ p.
Sufficient condition: idx_B A n 0 is itself a candidate of idx_B A n a at level m
(elem(A[n]) (idx_B n 0) m < elem(A[n]) (idx_B n a) m ∧ (m=0 ∨ m_anc(A[n])(m-1)(idx_B n a)(idx_B n 0))).
If so, max candidate >= idx_B n 0 (since idx_B n 0 is the largest index < idx_B n a that's a block-n col... no, candidates can be larger). Actually test: is the MAX candidate always >= idx_B n 0?
Test directly: for a>0, when m_parent exists, is it >= idx_B n 0? (gateway). AND is idx_B n 0 a candidate?"""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def idxB(A_l0,A_l1,c,j): return A_l0 + c*A_l1 + j
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0)(1,2,0)(1,1,1)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)","(0,0,0)(1,1,1)(2,2,0)",
           "(0,0,0,0)(1,2,3,4)","(0,0,0)(1,1,1)(2,2,2)(3,3,0)"]
    visited=set(); CAP=900
    gw_ok=gw_bad=0; cand_ok=cand_bad=0
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(3):
            frontier=[]
            for Ap in Q:
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    L1=l1(Ap); L0=l0(Ap)  # of predecessor (for idx_B in A=Ap[nn])
                    if L1<1: continue
                    H=height(A)
                    for a in range(1,L1):
                        ia = idxB(L0,L1,nn,a); i0 = idxB(L0,L1,nn,0)
                        if ia>=len(A): continue
                        for m in range(0,H):
                            p=m_parent(A,m,ia)
                            if p is None: continue
                            # gateway
                            if i0<=p: gw_ok+=1
                            else:
                                gw_bad+=1
                            # is i0 a candidate?
                            ec = elem(A,i0,m)<elem(A,ia,m) and (m==0 or m_anc(A,m-1,ia,i0))
                            if ec: cand_ok+=1
                            else: cand_bad+=1
            Q=frontier
            if len(visited)>CAP: break
    print(f"gateway (i0<=p): OK={gw_ok} BAD={gw_bad}")
    print(f"i0 is candidate: OK={cand_ok} BAD={cand_bad}")
if __name__=='__main__': main()
