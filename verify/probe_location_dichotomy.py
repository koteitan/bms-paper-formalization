#!/usr/bin/env python3
"""
Test the LOCATION DICHOTOMY hypothesis for b0_start(A[n]):

  H_loc:  for A in BMS, n>=1, E=A[n], sA=b0_start A, l0A=l0 A=sA, lA=l1 A,
          s'=b0_start E:
    (R1)  if l0A = 0  then  s' is a block-start in A-coords:
              (s' - l0A) mod lA == 0   [s' = l0A + c*lA for some c>=0]
    (R2)  if l0A > 0  then  s' < l0A   [s' sits in A's G-prefix]

If H_loc holds (0 violations), the BMS.induct expansion case for
elem_lt_below_t splits cleanly into two regimes keyed on l0 A = 0 vs > 0,
which prior sessions believed had "no clean closed form".

Also records, within R1, the block index c = (s'-l0A)/lA vs n, and t'=mpl E
vs tA, to see if a finer closed form exists.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand, height)
from collections import Counter

def l0(A):
    s = b0(A)
    return None if s is None else s   # b0_start = l0 (G-block length) for A in BMS

def main():
    seeds = [
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0,0,0,0,0)(1,1,1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0)(1,1)(2,0)(3,1)","(0,0)(1,1)(2,0)(3,0)",
      "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,1,1)(2,0,0)",
      "(0,0,0)(1,1,0)(2,2,1)","(0,0,0)(1,1,1)(2,2,0)(3,3,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,2)","(0,0,0,0)(1,1,1,1)(2,2,1,0)",
      "(0,0,0,0)(1,1,1,1)(2,2,1,1)","(0,0,0,0)(1,1,1,1)(2,1,1,0)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,0)","(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,1)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,1,0)",
    ]
    seen = set(); Q = []
    for sd in seeds:
        A = strip(parse(sd)); k = fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP = 2500; depth = 7
    checked = 0; viol = 0
    r1_c_vs_n = Counter(); t_rel = Counter()
    for d in range(depth):
        fr = []
        for A in Q:
            set_array(A)
            sA = b0(A); tA = mpl(A); lA = l1(A); l0A = sA
            if sA is not None and tA is not None and len(A) <= 30:
                for n in range(1, 4):
                    E = expand(fmt(A), n)
                    if E is None: continue
                    set_array(E)
                    sp = b0(E); tp = mpl(E)
                    set_array(A)
                    if sp is None: continue
                    checked += 1
                    if l0A == 0:
                        # R1 expected: (sp - l0A) mod lA == 0
                        ok = (lA > 0 and (sp - l0A) % lA == 0)
                        if ok:
                            c = (sp - l0A) // lA
                            r1_c_vs_n[(n, c)] += 1
                        else:
                            viol += 1
                            if viol <= 25:
                                print(f"  R1-VIOL A={fmt(A)} n={n} sA={sA} l0A={l0A} lA={lA} s'={sp}", flush=True)
                    else:
                        # R2 expected: s' < l0A
                        ok = (sp < l0A)
                        if not ok:
                            viol += 1
                            if viol <= 25:
                                print(f"  R2-VIOL A={fmt(A)} n={n} sA={sA} l0A={l0A} lA={lA} s'={sp}", flush=True)
                    if tp is not None and tA is not None:
                        t_rel[(tA, tp)] += 1
            for n in range(1, 4):
                if len(A) > 25: continue
                E = expand(fmt(A), n)
                if E is None: continue
                key = fmt(E)
                if key in seen or len(seen) > CAP: continue
                seen.add(key); fr.append(E)
        Q = fr
        print(f"  depth {d}: visited={len(seen)} checked={checked} viol={viol}", flush=True)
        if len(seen) > CAP: break
    print(f"FINAL checked={checked} DICHOTOMY-VIOLATIONS={viol}", flush=True)
    print(f"  R1 (l0A=0) block c vs n: {dict(sorted(r1_c_vs_n.items()))}", flush=True)
    print(f"  t' vs tA: {dict(sorted(t_rel.items()))}", flush=True)

if __name__ == '__main__': main()
