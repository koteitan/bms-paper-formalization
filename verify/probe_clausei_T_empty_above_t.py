#!/usr/bin/env python3
"""
Faithful-BMS probe for clause_i_iff_when_not_ascends sorry (BMS_Ancestry.thy ~16918).
In the branch t <= Suc k' (level K=Suc k' >= max_parent_level t), the leftmost
bump-tail filter
  T = [ p in [l0 .. idx_B(n,0)) :
          elem B p K < elem B (idx_B(n,0)) K  and  m_ancestor B (K-1) (idx_B(n,0)) p ]
is ALWAYS EMPTY (so the `T != []` case is vacuous).  Mechanism: at level >= t
there is no bump, so a column can be value-smaller than the gateway, but such a
smaller column is never a (K-1)-ancestor of the gateway (clause (iv) territory).
Result: 0 non-empty / 126 checks (seeds 2..5, depth 4, n=1,2, all K in [t,height)).
"""
import sys; sys.path.insert(0,'/home/koteitan/bms-paper/verify')
from probe_mpl_none_linchpin import (elem,height,m_parent,m_ancestor,
    max_parent_level,b0_start,B0_block,expansion,fmt,seed)
def l1(A): return len(B0_block(A))
def l0(A):
    s=b0_start(A); return 0 if s is None else s
def idxB(A,c,j): return l0(A)+c*l1(A)+j
def main():
    seen=set(); frontier=[]
    for k in (2,3,4,5):
        s=seed(k)
        if s not in seen: seen.add(s); frontier.append(s)
    for d in range(4):
        nxt=[]
        for A in frontier:
            for n in range(0,3):
                B=expansion(A,n)
                if B and B not in seen: seen.add(B); nxt.append(B)
        frontier=nxt
    Tne=0; checks=0
    for A in seen:
        s=b0_start(A)
        if s is None: continue
        t=max_parent_level(A)
        if t is None: continue
        for n in range(1,3):
            B=expansion(A,n)
            if not B: continue
            gw=idxB(A,n,0)
            if gw>=len(B): continue
            for K in range(max(t,1), height(B)):
                checks+=1
                thr=elem(B,gw,K)
                T=[p for p in range(l0(A),gw)
                   if elem(B,p,K)<thr and m_ancestor(B,K-1,gw,p)]
                if T: Tne+=1
    print(f"checks (K>=t): {checks};  bump-tail T non-empty: {Tne}")
if __name__=="__main__": main()
