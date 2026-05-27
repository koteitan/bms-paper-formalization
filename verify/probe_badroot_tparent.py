#!/usr/bin/env python3
"""R2 design (l1 A=1, l1(A[n])>=2): does b0_start A have a (mpl A)-parent in A?
i.e. m_parent A (mpl A) (b0_start A) != None. If so, mpl-bound follows non-circularly
(via clause_i_j0 + candidate q). Test."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def main():
    seeds=["(0,0)(1,1)(2,2)","(0,0,0)(1,1,1)","(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)",
           "(0,0)(1,1)(2,0)(3,1)","(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)",
           "(0,0,0)(1,1,1)(2,2,2)(3,3,0)","(0,0,0,0,0)(1,1,1,1,1)"]
    visited=set(); CAP=900
    ok=bad=0; ncase=0
    badsamp=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(3):
            frontier=[]
            for Ap in Q:
                L1=l1(Ap); tP=max_parent_level(Ap); sP=b0_start(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    if L1!=1 or tP is None or sP is None or l1(A)<2: continue
                    ncase+=1
                    p=m_parent(Ap,tP,sP)  # mpl A - parent of b0_start A, in A (=Ap)
                    if p is not None: ok+=1
                    else:
                        bad+=1
                        if len(badsamp)<8: badsamp.append((fmt(Ap),tP,sP))
            Q=frontier
            if len(visited)>CAP: break
    print(f"R2 design cases: {ncase}")
    print(f"b0_start A has (mpl A)-parent in A: OK={ok} BAD={bad}")
    for x in badsamp: print("  BAD",x)
if __name__=='__main__': main()
