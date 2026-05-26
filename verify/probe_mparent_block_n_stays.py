#!/usr/bin/env python3
"""
STRIP-CORRECT genuine-seed probe of the gateway lever
`m_parent_block_n_stays_until_zero`:

  A in BMS, s=b0_start A, l1 A > 0, 0 < a < l1, E = A[n],
  m_parent(E, m, idx_B(n,a)) = Some p   ==>   idx_B(n,0) <= p

idx_B(c,x) = s + c*l1 + x  (column index, strip-invariant).

GENUINE seeds ONLY: 2-column [replicate k 0, replicate k 1], BFS via expand,
strip-correct (3+-col hand seeds are NON-BMS -> false violations).

If VIOLATIONS = 0 -> lever is empirically sound; report count + witnesses.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, m_parent,
    set_array, expand, height, b0, l1)

def main():
    # GENUINE 2-column seeds only (per verification pitfalls doc).
    seeds = [
      "(0,0)(1,1)", "(0,0,0)(1,1,1)", "(0,0,0,0)(1,1,1,1)",
      "(0,0,0,0,0)(1,1,1,1,1)", "(0,0,0,0,0,0)(1,1,1,1,1,1)",
    ]
    seen = set(); Q = []
    for sd in seeds:
        A = strip(parse(sd)); key = fmt(A)
        if key not in seen: seen.add(key); Q.append(A)
    CAP = 2600; depth = 8
    checked = 0; viol = 0; wit = []
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
                    b0n = idxB(n, 0)
                    for a in range(1, L1):            # 0 < a < l1
                        col = idxB(n, a)
                        if col >= len(E): continue
                        for m in range(0, H):
                            checked += 1
                            p = m_parent(E, m, col)
                            if p is None: continue
                            if p < b0n:                # VIOLATION: parent below gateway
                                viol += 1
                                if len(wit) < 15:
                                    wit.append((fmt(A), n, a, m, p, b0n))
                    set_array(A)
            for n in range(1, 4):
                if len(A) > 25: continue
                E = expand(fmt(A), n)
                if E is None: continue
                key = fmt(E)
                if key in seen or len(seen) > CAP: continue
                seen.add(key); fr.append(E)
        Q = fr
        print(f"  depth {d}: visited={len(seen)} checked={checked} VIOL={viol}", flush=True)
        if len(seen) > CAP: break
    print(f"FINAL checked={checked}  m_parent_block_n_stays VIOLATIONS={viol}", flush=True)
    for w in wit: print("   violation (A,n,a,m,p,b0n):", w)

if __name__ == '__main__': main()
