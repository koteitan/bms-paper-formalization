#!/usr/bin/env python3
"""R2 regime (l1 A=1, s'<l0 A). CRITICAL: for G-region cols c (s'<c<=s_A=l0 A) and
levels m with 0<m<t', is c ALWAYS an (m-1)-ancestor of s_A in A? If yes, the
off-chain gap is VACUOUS in R2 and (G) closes via m_anc_Suc_imp_strict_min_on_anc
seeded by P1 (s'=m_parent A t' s_A). If no, R2's m>0 needs the full induction.
Also test directly: is s' an m-ancestor of every such c (the ANC we ultimately need)?"""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,2)(3,3,0)",
           "(0,0,0,0)(1,2,3,4)","(0,0,0,0,0)(1,1,1,1,1)"]
    visited=set(); CAP=1200
    onchain_ok=onchain_bad=0     # c is (m-1)-anc of s_A
    sanc_ok=sanc_bad=0           # s' is m-anc of c
    ncase=0
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
                    ncase+=1
                    sA=l0P  # A's bad root
                    for c in range(s+1, sA+1):
                        for m in range(1, t):   # 0<m<t'
                            # on-chain: c is (m-1)-anc of s_A
                            if c==sA or m_anc(Ap,m-1,sA,c): onchain_ok+=1
                            else:
                                onchain_bad+=1
                                if len(bad)<10: bad.append(("onchain",fmt(Ap),nn,s,c,sA,m,t))
                        for m in range(0, t):
                            if m_anc(Ap,m,c,s): sanc_ok+=1
                            else:
                                sanc_bad+=1
            Q=frontier
            if len(visited)>CAP: break
    print(f"R2 cases: {ncase}")
    print(f"on-chain: c is (m-1)-anc of s_A [0<m<t', s'<c<=s_A]: OK={onchain_ok} BAD={onchain_bad}")
    print(f"s' is m-anc of c [0<=m<t', s'<c<=s_A]:               OK={sanc_ok} BAD={sanc_bad}")
    for x in bad: print("  ",x)
if __name__=='__main__': main()
