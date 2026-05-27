#!/usr/bin/env python3
"""clause i @ j=0, ASC levels (k<mpl A). Is m_parent(A[n]) k (idx_B n 0) == m_parent(A[n]) k (idx_B 0 0)?
(idx_B 0 0 = l0 = s). If equal like not-asc, clause_i_j0_step works for asc too.
If differ, asc needs translation. Also test the TARGET claim: m_anc(A[n]) k (idx_B n 0) i ⟺ m_anc(A[n]) k (idx_B 0 0) i for i<l0 at asc levels (should be 0-viol)."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def idxB(l0,l1,c,j): return l0+c*l1+j
def ascends(A,d,m,s,t):  # ascends A d m: m<t and non_strict_anc A m (s+d) s
    if m>=t: return False
    # non_strict: s+d==s or m_anc
    return (s+d==s) or m_anc(A,m,s+d,s)
def main():
    seeds=["(0,0)(1,1)(2,2)","(0,0,0)(1,1,1)","(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)",
           "(0,0)(1,1)(2,0)(3,1)","(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)"]
    visited=set(); CAP=700
    mpeq_ok=mpeq_bad=0; anc_ok=anc_bad=0
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
                    if L1!=1 or tP is None or sP is None: continue
                    iN=idxB(L0,L1,nn,0); i0=idxB(L0,L1,0,0)
                    if iN>=len(A): continue
                    for k in range(0,tP):  # asc levels k<mpl A
                        if not ascends(Ap,0,k,sP,tP): continue  # only asc
                        pN=m_parent(A,k,iN); p0=m_parent(A,k,i0)
                        if pN==p0: mpeq_ok+=1
                        else: mpeq_bad+=1
                        for i in range(0,L0):
                            if m_anc(A,k,iN,i)==m_anc(A,k,i0,i): anc_ok+=1
                            else: anc_bad+=1
            Q=frontier
            if len(visited)>CAP: break
    print(f"asc-level j=0: m_parent(idxB n 0)==m_parent(idxB 0 0): OK={mpeq_ok} BAD={mpeq_bad}")
    print(f"asc-level j=0: m_anc to G target equal: OK={anc_ok} BAD={anc_bad}")
if __name__=='__main__': main()
