#!/usr/bin/env python3
"""
Complete the joint-induction DESIGN by resolving the l1(A)=1 sub-case.

When l1 A = 1, DOM(A) is vacuous (single B0 column, no interior), so DOM(A[n'])
cannot come from the IH DOM(A). Hypothesis: A[n']'s B-region columns are bumped
COPIES of the single B0 column, with elem(idx_B c 0) m = (A!s)!m + (asc? c*delta),
hence MONOTONE in block index c (delta>=0). So DOM(A[n']) on the B-region part
is pure bump-monotonicity (no DOM(A) needed). R2 (b0_start in G') additionally
involves G' columns.

For genuine BMS A with l1 A = 1 and n' in 1..3, E = A[n']:
 - classify s'=b0_start(E): R1 (block-start) / R2 (in-G' < l0 A)
 - DOM(E) holds? (sanity, must be 0 viol)
 - For each interior column s'+j of E (0<j<l1 E), m < mpl E: is s'+j in the
   B-region (>= l0 A) [bumped copy] or in G' (< l0 A) [verbatim]? Report counts.
 - B-region monotonicity check: for B-region interior columns, is the domination
   elem(E,s',m) < elem(E,s'+j,m) consistent with "monotone in block index"
   (i.e. s' has the smallest block index among E's B0' block)?
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand, height)

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
    nA=0; domviol=0
    r1=r2=0
    breg=0; greg=0          # interior columns in B-region vs G'
    r1_all_breg=0; r1_cases=0
    for d in range(depth):
        fr=[]
        for A in Q:
            set_array(A); sA=b0(A); tA=mpl(A); lA=l1(A); l0A=sA
            if sA is not None and tA is not None and lA==1 and len(A)<=30:
                nA+=1
                for n in range(1,4):
                    E=expand(fmt(A),n)
                    if E is None: continue
                    set_array(E); sp=b0(E); tp=mpl(E); lp=l1(E)
                    if sp is None or tp is None:
                        set_array(A); continue
                    isR1 = (sp>=l0A and (sp-l0A)%lA==0)  # lA=1 so always block-aligned if >=l0A
                    if sp<l0A: r2+=1; thisR1=False
                    elif isR1: r1+=1; thisR1=True
                    else:
                        set_array(A); continue
                    all_breg=True
                    for j in range(1,lp):
                        col=sp+j
                        if col>=l0A: breg+=1
                        else: greg+=1; all_breg=False
                        for m in range(0,tp):
                            if not (elem(E,sp,m)<elem(E,col,m)):
                                domviol+=1
                    if thisR1:
                        r1_cases+=1
                        if all_breg: r1_all_breg+=1
                set_array(A)
            for n in range(1,4):
                if len(A)>25: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        if len(seen)>CAP: break
    print(f"l1(A)=1 arrays checked: {nA}")
    print(f"b0_start(A[n']) split:  R1(block-start)={r1}  R2(in-G')={r2}")
    print(f"DOM(A[n']) violations:  {domviol}  (must be 0)")
    print(f"interior columns of E's B0': B-region(bumped copy)={breg}  G'(verbatim)={greg}")
    print(f"R1 cases where ALL interior are B-region (pure bump-monotone): {r1_all_breg}/{r1_cases}")

if __name__=='__main__': main()
