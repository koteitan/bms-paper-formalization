#!/usr/bin/env python3
"""
DESIGN-VERIFICATION probe for the joint-induction reconstruction.

The remaining technical blocker is locating b0_start(A[n]): it is always either
R1 (a block-start: s' = l0 A + c*l1 A) or R2 (in G': s' < l0 A), never mid-block.
For the joint (i)-(v) k-induction to close domination by a decidable R1/R2
case-split, we need: WHICH decidable condition on A (and n) predicts R1 vs R2?
(The simple "l0 A = 0 -> R1 / l0 A > 0 -> R2" rule was REFUTED.)

For each genuine BMS A and n in 1..3, classify s'=b0_start(A[n]) as R1/R2 and
record candidate predictor features of A, then report, for each feature value,
the R1/R2 split. A feature that perfectly separates R1 from R2 is the case-split
the induction should use.

Features of A recorded:
  l0A      = l0 A (= b0_start A = sA)
  l0A==0   = whether G-block empty
  tA       = mpl A
  lA       = l1 A
  Cpar_inG = whether the mpl-parent of A's last col (=b0_start A) is in G' of A,
             i.e. sA < l0A  (always false for A itself: sA = l0A) -- instead use:
  lastasc  = whether A's last B0 col (offset lA-1) "ascends" at level tA-1
  tA_even  = parity (long shot)
  n        = expansion count
Also: t' = mpl(A[n]) vs tA, to see if t' relation correlates with R1/R2.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand, height)
from collections import defaultdict

def ascends(A, j, m, sA, tA):
    if tA is None or m >= tA: return False
    if j == 0: return True
    return m_anc(A, m, sA + j, sA)

def main():
    seeds = [
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0)(1,1)(2,0)(3,1)","(0,0)(1,1)(2,0)(3,0)",
      "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,1,0)(2,2,1)","(0,0,0)(1,1,1)(2,2,0)(3,3,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,1,0)","(0,0,0,0)(1,1,1,1)(2,2,1,1)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,0)","(0,0,0,0,0)(1,1,1,1,1)(2,2,2,1,0)",
    ]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=2500; depth=7
    # per-feature -> Counter of R1/R2
    feats = defaultdict(lambda: defaultdict(lambda: [0,0]))  # featname -> value -> [R1,R2]
    total=[0,0]
    for d in range(depth):
        fr=[]
        for A in Q:
            set_array(A); sA=b0(A); tA=mpl(A); lA=l1(A); l0A=sA
            if sA is not None and tA is not None and lA>=1 and len(A)<=30:
                lastasc = ascends(A, lA-1, tA-1, sA, tA) if (tA>=1 and lA>=1) else False
                C_has_Gparent = (m_parent(A, tA, len(A)-1) is not None and m_parent(A,tA,len(A)-1) < l0A) if tA is not None else False
                for n in range(1,4):
                    E=expand(fmt(A), n)
                    if E is None: continue
                    set_array(E); sp=b0(E); tp=mpl(E)
                    set_array(A)
                    if sp is None: continue
                    if sp < l0A: r=1  # R2 index
                    elif lA>0 and (sp-l0A)%lA==0: r=0  # R1
                    else: r=2  # OTHER (should not happen)
                    if r==2:
                        continue
                    total[r]+=1
                    def rec(fn,val): feats[fn][val][r]+=1
                    rec('l0A==0', l0A==0)
                    rec('lA', lA)
                    rec('tA', tA)
                    rec('lastasc', lastasc)
                    rec('C_has_Gparent_inA', C_has_Gparent)
                    rec('n', n)
                    rec('tprime_vs_tA', (None if tp is None else ('t-1' if tp==tA-1 else 't' if tp==tA else 't+1' if tp==tA+1 else 'other')))
                    rec('l0A==0 & n', (l0A==0, n))
            for n in range(1,4):
                if len(A)>25: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        if len(seen)>CAP: break
    print(f"TOTAL: R1(block-start)={total[0]}  R2(in-G')={total[1]}")
    print("\nFor each feature value: [R1, R2] counts. A feature that perfectly separates (one column 0) is the predictor.")
    for fn in feats:
        print(f"\n== {fn} ==")
        for val in sorted(feats[fn], key=lambda x:str(x)):
            r1,r2 = feats[fn][val]
            sep = "  <-- pure R1" if r2==0 and r1>0 else ("  <-- pure R2" if r1==0 and r2>0 else "")
            print(f"   {val!r:>14}: R1={r1:5d} R2={r2:5d}{sep}")

if __name__=='__main__': main()
