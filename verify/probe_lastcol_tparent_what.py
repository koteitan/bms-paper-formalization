#!/usr/bin/env python3
"""design regime (l1(A[n])>=2): WHAT is m_parent(A[n]) (mpl A) (last col A[n])?
Identify the witness column to construct the proof. Classify: is it
idx_B A n (l1-2) (the previous col in block n)? or idx_B A (n) j for some j?
or a G/earlier-block col? last col = idx_B A n (l1-1)."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def classify(A,p,l0A,l1A,n):
    if p is None: return "None"
    if p < l0A: return f"G(<l0={l0A})"
    # p = l0A + c*l1A + j
    rel = p - l0A
    c = rel // l1A; j = rel % l1A
    return f"idx_B(c={c},j={j}) [n={n},l1={l1A}]"
def main():
    seeds=["(0,0,0)(1,1,1)(2,2,2)(3,3,0)","(0,0,0,0)(1,2,3,4)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0,0)(1,1,1,1,1)"]
    visited=set(); CAP=800; shown=0
    from collections import Counter
    kinds=Counter()
    for seed in seeds:
        if len(visited)>CAP or shown>=20: break
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
                    L1=l1(A); l0A=l0(A)
                    if tP is None or L1<2: continue
                    lc=len(A)-1
                    p=m_parent(A,tP,lc)
                    rel_to_last = (lc - p) if p is not None else -1
                    kinds[f"last-p={rel_to_last}"]+=1
                    if shown<20:
                        shown+=1
                        print(f"A'={fmt(Ap)} n={nn} tP={tP} | last={lc} parent={p} (last-p={rel_to_last}) l1En={L1} l0En={l0A}")
            Q=frontier
            if len(visited)>CAP or shown>=20: break
    print("distribution last_col - parent:", dict(sorted(kinds.items())))
if __name__=='__main__': main()
