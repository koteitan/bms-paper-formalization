#!/usr/bin/env python3
"""STRIP-CORRECT. R2 regime (l1 A=1). Trace the m_parent(A[n]) t' chain from the
last column C down to s'=b0_start(A[n]), to reveal the mechanism by which s' is a
t-ancestor (in A) of b0_start A = l0 A. A=predecessor, En=A[n]=expanded.
Report for each R2 case: l0 A, b0_start A, last_col_idx, s'(=b0_start En), t', and
the full t'-parent chain in En from C. Mark which chain nodes are < l0 A (G-region),
== l0 A (= A's bad root image), or in bumped region."""
import re, subprocess
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def chain(A,m,i):
    out=[]; p=m_parent(A,m,i); seen=set()
    while p is not None and p not in seen:
        seen.add(p); out.append(p); p=m_parent(A,m,p)
    return out
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)"]
    visited=set(); CAP=2000; shown=0
    for seed in seeds:
        if len(visited)>CAP or shown>=18: break
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
                    if shown>=18: break
                    shown+=1
                    C=len(A)-1
                    ch=chain(A,t,C)
                    annot=[]
                    for c in ch:
                        if c<l0P: annot.append(f"{c}(G<{l0P})")
                        elif c==l0P: annot.append(f"{c}(=badrootA)")
                        else: annot.append(f"{c}(bump)")
                    print(f"A'={fmt(Ap)} n={nn} | l0A={l0P} badrootA={l0P} lastA={len(Ap)-1} | s'={s} t'={t} l0+l1A={l0P+l1P}")
                    print(f"   En t'-chain from C={C}: {' -> '.join(annot)}")
            Q=frontier
            if len(visited)>CAP or shown>=18: break
if __name__=='__main__': main()
