#!/usr/bin/env python3
"""
!!! STILL UNRELIABLE (coverage gap) — use verify/probe_location_correct.py. !!!
This fixed the bucket-discard bug but kept (a) a shallow BFS (depth 7, hand seeds)
and (b) the WRONG guard (mpl>=1 only, not l1(A[n])>=2). Its "('>=2','>=1') R3=0,
R2=0" conclusion is a COVERAGE-GAP false positive: with a deeper BFS and the
correct design guard (l1(A[n])>=2 AND mpl(A[n])>=1), b0_start(A[n]) is R1 (block-
start) OR R2 (in-G') — R2 occurs for l1(A)>=2 too (2025 cases). Only R3 (mid-block)
is genuinely 0 in the design-relevant regime. See probe_location_correct.py.

CORRECTED location probe (the earlier probe_location_predictor.py had a BUG:
it discarded the mid-block case `r=2: continue` BEFORE counting, giving a false
"l1>=2 => 100% block-start"). Here we count ALL three buckets and never discard:
  R1 = block-start : s' >= l0A and (s'-l0A) % l1A == 0
  R2 = in-G'       : s' < l0A
  R3 = mid-block   : s' >= l0A and (s'-l0A) % l1A != 0   <-- the discarded case

loc_R1 (l1A>=2 => block-start) is already REFUTED at mpl(A[n])=0
(A=(0)(1)(2)(1)(0)(1)(2)(1), b0(A[1])=8 mid-block). But the joint-induction design
only USES the location when domination is non-vacuous, i.e. mpl(A[n]) >= 1.
KEY QUESTION: does R3 (mid-block) still occur when l1 A >= 2 AND mpl(A[n]) >= 1?
Break the R1/R2/R3 counts down by (l1A==1 vs >=2) x (mpl(E)==0 vs >=1).
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand, height)
from collections import defaultdict

def main():
    seeds = [
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0)(1,1)(2,0)(3,1)","(0,0)(1,1)(2,0)(3,0)",
      "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,1,0)(2,2,1)","(0,0,0)(1,1,1)(2,2,0)(3,3,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,1,0)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,0)","(0,0,0,0,0)(1,1,1,1,1)(2,2,2,1,0)",
    ]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=2500; depth=7
    # (l1cls, mplcls) -> [R1,R2,R3]
    cells=defaultdict(lambda:[0,0,0])
    r3_examples=[]
    for d in range(depth):
        fr=[]
        for A in Q:
            set_array(A); sA=b0(A); lA=l1(A); l0A=sA
            if sA is not None and lA>=1 and len(A)<=30:
                for n in range(1,4):
                    E=expand(fmt(A),n)
                    if E is None: continue
                    set_array(E); sp=b0(E); tp=mpl(E)
                    set_array(A)
                    if sp is None: continue
                    if sp < l0A: r=1
                    elif (sp-l0A)%lA==0: r=0
                    else: r=2   # mid-block R3 -- COUNTED, not discarded
                    l1cls = '>=2' if lA>=2 else '1'
                    mplcls = '>=1' if (tp is not None and tp>=1) else '0/None'
                    cells[(l1cls,mplcls)][r]+=1
                    if r==2 and lA>=2 and tp is not None and tp>=1 and len(r3_examples)<10:
                        r3_examples.append((fmt(A),n,sp,sA,lA,tp))
            for n in range(1,4):
                if len(A)>25: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        if len(seen)>CAP: break
    print("cell (l1A, mpl(A[n])) -> [R1 block-start, R2 in-G', R3 MID-BLOCK]")
    for key in sorted(cells):
        print(f"   {key}: {cells[key]}")
    print(f"\nKEY CELL ('>=2','>=1') R3(mid-block) count = {cells[('>=2','>=1')][2]}")
    print("  (if 0: guarded loc_R1 [l1>=2 & mpl(A[n])>=1 => block-start] is empirically TRUE)")
    print("  (if >0: even the guarded design's main case has mid-block; design needs rework)")
    for e in r3_examples: print("   R3 @ l1>=2,mpl>=1 (A,n,s',l0A,l1A,mpl):", e)

if __name__=='__main__': main()
