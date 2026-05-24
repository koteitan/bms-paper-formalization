#!/usr/bin/env python3
"""
Decide whether the FULL premise combination of
`clause_iv_intermediate_B_t_impossible_chain_through_Bn_first` (the consumer of
the false T2 lemma) is realizable on genuine BMS arrays — STRIP-CORRECT
(the earlier "0 of 441" claim used un-stripped indices = false confidence).

Consumer premises (it concludes False, i.e. the config must be impossible):
  A in BMS, s=b0_start A, l1 A > 0, 0 < i < l1, k > 0,
  E = A[n],
  m_parent(E) k (idx_B(n,i)) = idx_B(t,j)  with  t < n, j < l1   [k-parent in intermediate block t]
  no_G_parent: NOT exists k'<k. m_parent(E) k' (idx_B(n,i)) is a G-column (< l0 A)
  chain_through_Bn0: for all k'<k. idx_B(n,0) is a k'-ancestor of idx_B(n,i)

idx_B(c,x) = l0 A + c*l1 A + x = s + c*l1 + x  (column index, strip-invariant).

If REALIZED count = 0 -> consumer is vacuously sound; T2 can be restated with the
consumer's hypotheses (true vacuously). If > 0 -> genuine unsoundness in clause (iv).
Reports realized count + first witnesses.
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
      "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,1,0)","(0,0,0,0)(1,1,1,1)(2,2,1,1)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,0)","(0,0,0,0,0)(1,1,1,1,1)(2,2,2,1,0)",
    ]
    seen = set(); Q = []
    for sd in seeds:
        A = strip(parse(sd)); key = fmt(A)
        if key not in seen: seen.add(key); Q.append(A)
    CAP = 2500; depth = 7
    checked = 0; realized = 0; wit = []
    for d in range(depth):
        fr = []
        for A in Q:
            set_array(A)
            sA = b0(A); L1 = l1(A)
            if sA is not None and L1 >= 1 and len(A) <= 30:
                def idxB(c, x): return sA + c * L1 + x
                for n in range(1, 4):
                    E = expand(fmt(A), n)
                    if E is None: continue
                    set_array(E); H = height(E)
                    for i in range(1, L1):              # 0 < i < l1
                        ini = idxB(n, i)
                        if ini >= len(E): continue
                        for k in range(1, H):            # k > 0
                            checked += 1
                            p = m_parent(E, k, ini)
                            if p is None: continue
                            # k-parent in an intermediate block t<n ?
                            if p < sA: continue          # in G, not intermediate
                            off = p - sA
                            t, j = divmod(off, L1)
                            if not (t < n and j < L1): continue
                            # no_G_parent: no k'<k parent is a G-column
                            if any((lambda q: q is not None and q < sA)(m_parent(E, kp, ini))
                                   for kp in range(0, k)): continue
                            # chain_through_Bn0: idx_B(n,0) is k'-ancestor of ini for all k'<k
                            b0n = idxB(n, 0)
                            if not all(m_anc(E, kp, ini, b0n) for kp in range(0, k)): continue
                            realized += 1
                            if len(wit) < 15:
                                wit.append((fmt(A), n, i, k, t, j, p))
                    set_array(A)
            for n in range(1, 4):
                if len(A) > 25: continue
                E = expand(fmt(A), n)
                if E is None: continue
                key = fmt(E)
                if key in seen or len(seen) > CAP: continue
                seen.add(key); fr.append(E)
        Q = fr
        print(f"  depth {d}: visited={len(seen)} checked={checked} REALIZED={realized}", flush=True)
        if len(seen) > CAP: break
    print(f"FINAL checked={checked}  consumer-premise REALIZED={realized}", flush=True)
    for w in wit: print("   witness (A,n,i,k,t,j,p):", w)

if __name__ == '__main__': main()
