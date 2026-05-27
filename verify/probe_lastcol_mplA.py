#!/usr/bin/env python3
"""R2 regime (l1 A=1, l1(A[n])>=2): does idx_B A n 0 (= last col of A[n]) have a
parent at level t=mpl A? And what is mpl(A[n]) vs mpl A? Find witness at level t."""
import re
from probe_R2_reduce import (parse,fmt,strip,elem,height,m_parent,m_anc,
                             max_parent_level,b0_start,l1,l0,expand)
def idxB(l0,l1,c,j): return l0+c*l1+j
def main():
    seeds=["(0,0)(1,1)(2,2)","(0,0,0)(1,1,1)","(0,0,0)(1,2,0)(1,1,1)","(0,0)(1,1)(2,0)",
           "(0,0)(1,1)(2,0)(3,1)","(0,0,0)(1,1,1)(2,2,0)","(0,0,0,0)(1,2,3,4)",
           "(0,0,0)(1,1,1)(2,2,2)(3,3,0)"]
    visited=set(); CAP=700
    has_ok=has_bad=0; ncase=0; shown=0
    from collections import Counter
    pwit=Counter()
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(3):
            frontier=[]
            for Ap in Q:
                L1=l1(Ap); L0=l0(Ap); tP=max_parent_level(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    if L1!=1 or tP is None or l1(A)<2: continue
                    lc=idxB(L0,L1,nn,0)  # = idx_B A n 0 = last col (l1=1)
                    if lc!=len(A)-1: continue  # confirm it's the last col
                    ncase+=1
                    p=m_parent(A,tP,lc)  # parent at level mpl A
                    if p is not None:
                        has_ok+=1
                        rel = lc - p
                        pwit[rel]+=1
                    else: has_bad+=1
                    if shown<10:
                        shown+=1
                        print(f"A'={fmt(Ap)} n={nn} tP={tP} mplEn={max_parent_level(A)} last={lc} m_parent@tP={p}")
            Q=frontier
            if len(visited)>CAP: break
    print(f"R2 design (l1 A=1, l1En>=2): {ncase}")
    print(f"idx_B A n 0 has parent at level mpl A: OK={has_ok} BAD={has_bad}")
    print(f"witness (last - parent) dist: {dict(pwit)}")
if __name__=='__main__': main()
