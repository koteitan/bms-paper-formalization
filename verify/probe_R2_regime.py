#!/usr/bin/env python3
"""When does R2 (b0_start(A[n]) < l0 A) occur, and what is l1' in those cases?
A = predecessor, A[n] = expanded. R2: b0_start(A[n]) < l0(A)."""
import re, subprocess
from probe_R2_reduce import parse,fmt,strip,elem,height,m_parent,m_anc,max_parent_level,b0_start,l1,l0,expand
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,2)(3,3,0)"]
    visited=set(); CAP=4000
    r2_by_l1p={}   # l1' -> count of R2 cases
    r2a_ok=r2a_bad=0
    bad=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(4):
            frontier=[]
            for Ap in Q:
                l0P=l0(Ap); l1P=l1(Ap); tP=max_parent_level(Ap); sP=b0_start(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    if sP is None or tP is None: continue
                    if not s < l0P: continue   # R2 only
                    r2_by_l1p[l1P]=r2_by_l1p.get(l1P,0)+1
                    # R2a: s is t-anc in A' of every c, s<c<=l0P
                    for c in range(s+1,l0P+1):
                        if m_anc(Ap,t,c,s): r2a_ok+=1
                        else:
                            r2a_bad+=1
                            if len(bad)<8: bad.append((fmt(Ap),nn,s,c,t,l1P))
            Q=frontier
            if len(visited)>CAP: break
    print("R2 cases by l1'(predecessor):", dict(sorted(r2_by_l1p.items())))
    print(f"R2a (s t-anc A' of c, s<c<=l0', ALL l1'): OK={r2a_ok} BAD={r2a_bad}")
    for x in bad: print("  BAD",x)
if __name__=='__main__': main()
