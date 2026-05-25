#!/usr/bin/env python3
"""Relate t'=mpl(A[n]) to t=mpl(A), and l1' to l1, in R1 (block-start) vs R2 (in-G)
design-regime cases. Determines whether dom_transfer_R1's m<t (predecessor)
hypothesis is implied by DOM(A[n])'s m<t'."""
import re, subprocess
from collections import Counter
import importlib.util
spec=importlib.util.spec_from_file_location("p","/home/koteitan/bms-paper/verify/probe_elem_lt_below_t_induct.py")
P=importlib.util.module_from_spec(spec); spec.loader.exec_module(P)

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0)(1,1)(2,0)","(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)",
           "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)"]
    arrays=[A for A in P.collect(seeds,350,3) if len(A)<=26]
    tprime_le_t=Counter(); tprime_gt_t=0
    r1_tle=r1_tgt=r2_tle=r2_tgt=0
    ex=[]
    for A in arrays:
        sA=P.b0(A); tA=P.mpl(A); l0A=P.l0(A); l1A=P.l1(A)
        if sA is None or tA is None or l1A<1: continue
        for n in range(1,4):
            E=P.expand(P.fmt(A),n)
            if E is None: continue
            sE=P.b0(E); tE=P.mpl(E); l1E=P.l1(E); l0E=P.l0(E)
            if sE is None or tE is None or tE<2 or l1E<2: continue
            R2 = sE<l0A
            if tE<=tA:
                if R2: r2_tle+=1
                else: r1_tle+=1
            else:
                tprime_gt_t+=1
                if R2: r2_tgt+=1
                else: r1_tgt+=1
                if len(ex)<8: ex.append((P.fmt(A),n,'R2' if R2 else 'R1',tA,tE,l1A,l1E))
    print(f"t'<=t: R1={r1_tle} R2={r2_tle}    t'>t: R1={r1_tgt} R2={r2_tgt}  (total t'>t={tprime_gt_t})")
    for e in ex: print("  t'>t example:",e)

if __name__=='__main__': main()
