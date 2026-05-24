#!/usr/bin/env python3
"""
Verify the elem_increase reframing of elem_lt_below_t.

Two claims (eval-faithful; reuse probe_vacuity_refute functions):

C-INSTANCE (the telescoping bridge):  A in BMS, mpl A = Some t (t>=1),
  s = b0_start A, C = last_col_idx.  Then for every y with s < y <= C and
  every level k < t:   elem A (y-1) k < elem A y k.
  (Telescoping this from s to s+j gives elem_lt_below_t directly, unifying
   m=0 / on-chain / off-chain.)

GENERAL elem_increase (the self-propagating statement for BMS.induct):
  A in BMS, q < length A, p = m_parent A (Suc t') q = Some p,
  Suc t' <= mpl A.  Then for every y with p < y <= q and every k <= t':
    elem A (y-1) k < elem A y k.

We hunt hard (many seeds, deep BFS, targeted) and report first violations.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand, height)

def last(A): return len(A) - 1

def check_C_instance(A):
    t = mpl(A); s = b0(A)
    if t is None or s is None or t < 1: return []
    C = last(A); out = []
    for y in range(s + 1, C + 1):
        for k in range(0, t):           # k < t
            if not (elem(A, y - 1, k) < elem(A, y, k)):
                out.append(('C', y, k, elem(A, y-1, k), elem(A, y, k)))
    return out

def check_general(A):
    M = mpl(A)
    if M is None: return []
    out = []
    N = len(A)
    for q in range(0, N):
        for tt in range(0, M):          # Suc t' = tt+1 <= M  => t' = tt
            p = m_parent(A, tt + 1, q)
            if p is None: continue
            for y in range(p + 1, q + 1):
                for k in range(0, tt + 1):   # k <= t' = tt
                    if not (elem(A, y - 1, k) < elem(A, y, k)):
                        out.append(('G', q, tt+1, p, y, k,
                                    elem(A, y-1, k), elem(A, y, k)))
    return out

def main():
    seeds = [
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0,0,0,0,0)(1,1,1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0)(1,1)(2,0)(3,1)","(0,0)(1,1)(2,0)(3,0)",
      "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,1,1)(2,0,0)","(0,0,0)(1,2,0)(1,1,1)",
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
    cC = cG = 0; vC = vG = 0
    for d in range(depth):
        fr = []
        for A in Q:
            set_array(A)
            if len(A) <= 40:
                if mpl(A) is not None and mpl(A) >= 1 and l1(A) >= 2:
                    cC += 1
                    r = check_C_instance(A)
                    if r:
                        vC += 1
                        if vC <= 20:
                            print(f"  C-VIOL A={fmt(A)} t={mpl(A)} s={b0(A)} {r[:6]}", flush=True)
                if mpl(A) is not None:
                    cG += 1
                    r = check_general(A)
                    if r:
                        vG += 1
                        if vG <= 20:
                            print(f"  G-VIOL A={fmt(A)} mpl={mpl(A)} {r[:6]}", flush=True)
            for n in range(1, 4):
                if len(A) > 30: continue
                E = expand(fmt(A), n)
                if E is None: continue
                key = fmt(E)
                if key in seen or len(seen) > CAP: continue
                seen.add(key); fr.append(E)
        Q = fr
        print(f"  depth {d}: visited={len(seen)} cC={cC} vC={vC} cG={cG} vG={vG}", flush=True)
        if len(seen) > CAP: break
    print(f"FINAL visited={len(seen)}", flush=True)
    print(f"  C-instance (telescoping bridge): checked={cC} VIOLATIONS={vC}", flush=True)
    print(f"  general elem_increase:           checked={cG} VIOLATIONS={vG}", flush=True)

if __name__ == '__main__': main()
