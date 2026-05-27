#!/usr/bin/env python3
"""R2 regime. Is m_parent A m' c = c-1 (consecutive) for c in (s', s_A], 0<=m'<t'-?
If so, the m'-chain from s_A is consecutive down to s', giving density cleanly.
Test: (C1) m_parent A m' c == c-1 for s'<c<=s_A, m'<t'.
      (C2) c is m'-anc of s_A (the on-chain fact) for s'<c<s_A, m'<t'-? (m' s.t. relevant)."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)"]
    visited=set(); CAP=1200
    c1_ok=c1_bad=0; ncase=0
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
                    sA=l0P
                    for c in range(s+1, sA+1):
                        for mp in range(0, t):  # m'<t'
                            res=m_parent(Ap,mp,c)
                            if res==c-1: c1_ok+=1
                            else:
                                c1_bad+=1
                                if len(bad)<12: bad.append((fmt(Ap),nn,s,c,mp,res,sA,t))
            Q=frontier
            if len(visited)>CAP: break
    print(f"R2 cases: {ncase}")
    print(f"C1  m_parent A m' c == c-1 [s'<c<=s_A, m'<t']: OK={c1_ok} BAD={c1_bad}")
    for x in bad: print("  ",x)
if __name__=='__main__': main()
