#!/usr/bin/env python3
"""Is mpl(A[n]) >= mpl A in general? (needed: in R2, ascends A 0 t' false => bumped
block-starts all equal elem A sA t', excluded from candidates, so P1 candidate set
restricts to G-region.) Test general + R2-only."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)"]
    visited=set(); CAP=1500
    ge_gen=lt_gen=0; ge_r2=lt_r2=0; ncase=0
    bad=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(4):
            frontier=[]
            for Ap in Q:
                tP=max_parent_level(Ap); l0P=l0(Ap); l1P=l1(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    t=max_parent_level(A)
                    if t is None or tP is None: continue
                    ncase+=1
                    if t>=tP: ge_gen+=1
                    else:
                        lt_gen+=1
                        if len(bad)<8: bad.append(("gen",fmt(Ap),nn,t,tP))
                    s=b0_start(A); L1=l1(A)
                    if s is not None and t>0 and L1>=2 and l1P==1 and s<l0P:
                        if t>=tP: ge_r2+=1
                        else: lt_r2+=1
            Q=frontier
            if len(visited)>CAP: break
    print(f"all expand cases: {ncase}")
    print(f"GENERAL: mpl(A[n])>=mpl A: {ge_gen}  mpl(A[n])<mpl A: {lt_gen}")
    print(f"R2-only: >= {ge_r2}  < {lt_r2}")
    for x in bad: print("  ",x)
if __name__=='__main__': main()
