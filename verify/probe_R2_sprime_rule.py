#!/usr/bin/env python3
"""STRIP-CORRECT. R2 regime (l1 A=1). s'=b0_start(A[n]) is independent of n.
Test what s' IS in terms of A alone:
 (P1) s' == m_parent A t' (l0 A)   [t'-parent of A's own bad root]
 (P2) s' == m_parent A t' (lastcol A)  [t'-parent of A's last col]
 (P3) s' == b0_start chain: t'-ancestor structure of badrootA
Also confirm: s' indep of n; and m_anc A t' (l0 A) s'  (s' is t'-anc of badrootA in A)."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,2)(3,3,0)"]
    visited=set(); CAP=3000
    p1_ok=p1_bad=0; p2_ok=p2_bad=0; sanc_ok=sanc_bad=0
    indep={}  # fmt(A')->set of s'
    bad=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(4):
            frontier=[]
            for Ap in Q:
                l0P=l0(Ap); l1P=l1(Ap); tP=max_parent_level(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    if l1P!=1 or tP is None: continue
                    if not s < l0P: continue
                    indep.setdefault(fmt(Ap),set()).add(s)
                    # P1: s' == m_parent A' t' (l0P) using t'=t (mpl of En)
                    p1=m_parent(Ap,t,l0P)
                    if p1==s: p1_ok+=1
                    else:
                        p1_bad+=1
                        if len(bad)<10: bad.append(("P1",fmt(Ap),nn,s,p1,t,l0P))
                    # P2: s' == m_parent A' t' (last col of A')
                    p2=m_parent(Ap,t,len(Ap)-1)
                    if p2==s: p2_ok+=1
                    else: p2_bad+=1
                    # s' is t'-anc of badrootA=l0P in A'
                    if m_anc(Ap,t,l0P,s): sanc_ok+=1
                    else: sanc_bad+=1
            Q=frontier
            if len(visited)>CAP: break
    bad_indep=[(k,v) for k,v in indep.items() if len(v)>1]
    print(f"s' indep of n? cases-with-multiple-s': {len(bad_indep)} (0=always indep)")
    print(f"P1  s'==m_parent A' t' (l0 A=badrootA): OK={p1_ok} BAD={p1_bad}")
    print(f"P2  s'==m_parent A' t' (lastcol A):     OK={p2_ok} BAD={p2_bad}")
    print(f"    s' is t'-anc A' of badrootA:        OK={sanc_ok} BAD={sanc_bad}")
    for x in bad: print("  ",x)
if __name__=='__main__': main()
