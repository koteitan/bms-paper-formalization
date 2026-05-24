#!/usr/bin/env python3
"""
DECISIVE test for the faithful Hunter case-B reconstruction (avoids elem_lt).

Hunter's (ii) case-B: j-th B0 column does NOT ascend at level m=Suc k' (m<t).
Claim he uses: "in Bn there cannot be any k-ancestors of j that aren't copies
of k-ancestors of j in B0" -> the (Suc k')-parent CANDIDATE SET of column j
corresponds 1:1 between block 0 and block n (restricted to x<j).

We test, on E=A[n] (stripped), for sA=b0(A), tA=mpl(A), l1A=l1(A),
column index  idx_B(c,x) = sA + c*l1A + x:

  cand_c(x)  :=  elem(E, idx_B(c,x), m) < elem(E, idx_B(c,j), m)
                 AND m_anc(E, m-1, idx_B(c,j), idx_B(c,x))      (m=Suc k')

CORRESP:  for not-ascending j and all x<j:  cand_0(x) <=> cand_n(x).
If 0 violations, the candidate sets match WITHOUT nasc_chain0, so the parent
(= last candidate, block-shifted) matches, giving (ii) directly.

We ALSO log, for any violation, whether the offending x ascends (to see if
the failure is exactly the ascending-but-candidate case, i.e. whether some
weaker hypothesis than nasc_chain0 is needed).
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand, height)

def ascends(A, j, m, sA, tA):
    # ascends A j m  <=>  m < t  and  (j==0 or m_anc(A,m,sA+j,sA))
    if m >= tA: return False
    if j == 0: return True
    return m_anc(A, m, sA + j, sA)

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
    CAP = 1800; depth = 7
    checked = 0; viol = 0; viol_asc = 0
    for d in range(depth):
        fr = []
        for A in Q:
            set_array(A)
            sA = b0(A); tA = mpl(A); L1 = l1(A)
            if sA is not None and tA is not None and tA >= 2 and L1 >= 2 and len(A) <= 30:
                for n in range(1, 4):
                    E = expand(fmt(A), n)
                    if E is None: continue
                    set_array(E)
                    def idxB(c, x): return sA + c * L1 + x
                    H = height(E)
                    for j in range(1, L1):
                        for m in range(1, tA):          # m = Suc k', 1 <= m < t
                            if ascends(A, j, m, sA, tA): continue   # case-B only
                            if m >= H: continue
                            # candidate correspondence x<j
                            for x in range(0, j):
                                i0j = idxB(0, j); i0x = idxB(0, x)
                                inj = idxB(n, j); inx = idxB(n, x)
                                c0 = (elem(E, i0x, m) < elem(E, i0j, m)) and m_anc(E, m-1, i0j, i0x)
                                cn = (elem(E, inx, m) < elem(E, inj, m)) and m_anc(E, m-1, inj, inx)
                                checked += 1
                                if c0 != cn:
                                    viol += 1
                                    xa = ascends(A, x, m, sA, tA)
                                    if xa: viol_asc += 1
                                    if viol <= 25:
                                        print(f"  CORRESP-VIOL A={fmt(A)} n={n} j={j} m={m} x={x}"
                                              f" c0={c0} cn={cn} x_ascends={xa}", flush=True)
                    set_array(A)
            for n in range(1, 4):
                if len(A) > 25: continue
                E = expand(fmt(A), n)
                if E is None: continue
                key = fmt(E)
                if key in seen or len(seen) > CAP: continue
                seen.add(key); fr.append(E)
        Q = fr
        print(f"  depth {d}: visited={len(seen)} checked={checked} viol={viol} (of which x_ascends={viol_asc})", flush=True)
        if len(seen) > CAP: break
    print(f"FINAL checked={checked} CORRESP-VIOLATIONS={viol} (x_ascends among them={viol_asc})", flush=True)

if __name__ == '__main__': main()
