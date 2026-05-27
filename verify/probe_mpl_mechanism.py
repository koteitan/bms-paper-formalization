#!/usr/bin/env python3
"""Why mpl(A[n]) >= mpl A in R2/design regime? Test correlations:
 (M1) mpl(A[n]) >= mpl A  <=>  l1(A[n]) >= 2  (design regime)?
 (M2) among the 115 general-decrease cases, what is l1(A[n])?
 (M3) does mpl(A[n]) >= mpl A hold whenever l1(A[n]) >= 1 and mpl(A[n])>0?
Classify each expand case by (l1En, mpl_ge)."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)"]
    visited=set(); CAP=1500
    # buckets: (l1En>=2, mpl_ge) counts
    from collections import Counter
    buck=Counter()
    decrease_l1=Counter()
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
                    t=max_parent_level(A); L1=l1(A)
                    if t is None or tP is None: continue
                    ge = t>=tP
                    d2 = L1>=2
                    buck[(d2,ge)]+=1
                    if not ge:
                        decrease_l1[L1]+=1
            Q=frontier
            if len(visited)>CAP: break
    print("buckets (l1En>=2, mpl(A[n])>=mpl A): count")
    for k in sorted(buck): print(f"  l1>=2={k[0]}  mpl_ge={k[1]}: {buck[k]}")
    print("among mpl-DECREASE cases, distribution of l1(A[n]):", dict(sorted(decrease_l1.items())))
if __name__=='__main__': main()
