#!/usr/bin/env python3
"""
THIRD, careful location verification. Two prior probes were wrong:
 (1) probe_location_predictor.py: bucket bug (discarded mid-block).
 (2) probe_location_3way.py: guarded by mpl>=1 only + shallow BFS (depth 7) ->
     coverage gap; missed the counterexample A=(0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,1)
     whose A[1] has b0_start=8 (mid-block) with mpl=1 BUT l1(A[1])=1.

KEY REALIZATION: the joint-induction design uses the location of b0_start(A[n])
ONLY when DOM(A[n]) is NON-VACUOUS, i.e. l1(A[n]) >= 2 (need interior 0<j<l1)
AND mpl(A[n]) >= 1 (need a level m<mpl). The above counterexample has l1(A[1])=1
so DOM(A[1]) is vacuous -> NOT design-relevant.

So the design-relevant question: under  l1(A[n]) >= 2 AND mpl(A[n]) >= 1,
is b0_start(A[n]) ALWAYS a block-start (R1)?  MECE 3-way buckets, NO discard,
DEEPER BFS (depth 10, incl. 3-row seeds that reach the prior counterexample).
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand, height)

def main():
    seeds = [
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0,0)(1,1,1)(2,2,2)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,0)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,1,0)(2,2,1)",
      # seeds near the known counterexample (3-row -> stripped 2-row staircases)
      "(0,0)(1,1)(2,2)","(0,0)(1,1)(2,2)(3,1)","(0,0)(1,1)(2,2)(3,3)",
    ]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=6000; depth=11
    # buckets for the DESIGN-RELEVANT cell: l1(E)>=2 AND mpl(E)>=1
    R1=R2=R3=0
    r3_ex=[]
    other_cells=0
    checked_E=0
    for d in range(depth):
        fr=[]
        for A in Q:
            set_array(A); sA=b0(A); lA=l1(A); l0A=sA
            if sA is not None and lA>=1 and len(A)<=40:
                for n in range(1,4):
                    E=expand(fmt(A),n)
                    if E is None: continue
                    set_array(E); sp=b0(E); tp=mpl(E); lp=l1(E)
                    set_array(A)
                    if sp is None or tp is None: continue
                    checked_E+=1
                    # DESIGN-RELEVANT guard: l1(E)>=2 AND mpl(E)>=1
                    if not (lp>=2 and tp>=1):
                        other_cells+=1; continue
                    if sp < l0A: R2+=1
                    elif lA>0 and (sp-l0A)%lA==0: R1+=1
                    else:
                        R3+=1
                        if len(r3_ex)<12: r3_ex.append((fmt(A),n,fmt(E),sp,l0A,lA,tp,lp))
            for n in range(1,4):
                if len(A)>35: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"  depth {d}: visited={len(seen)} checkedE={checked_E} | design-cell R1={R1} R2={R2} R3={R3} (off-cell={other_cells})",flush=True)
        if len(seen)>CAP: break
    print(f"\nDESIGN-RELEVANT cell (l1(A[n])>=2 AND mpl(A[n])>=1):")
    print(f"  R1 block-start={R1}  R2 in-G'={R2}  R3 MID-BLOCK={R3}")
    if R3==0 and R2==0:
        print("  => b0_start(A[n]) is ALWAYS a block-start in the design-relevant regime. loc lemma holds (guard: l1(A[n])>=2 & mpl(A[n])>=1).")
    else:
        print("  => block-start is NOT guaranteed even design-relevant; design must handle R2/R3.")
    for e in r3_ex: print("   R3 (A,n,E,s',l0A,l1A,mpl_E,l1_E):", e)

if __name__=='__main__': main()
