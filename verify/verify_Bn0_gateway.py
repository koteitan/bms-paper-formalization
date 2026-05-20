#!/usr/bin/env python3
"""
Empirical verification of the "B_n[0] gateway" sub-helper for the
chain_breaks branch of clause_iv_intermediate_B_t_impossible.

Claim (gateway):
  Let A be a BMS, l1 A > 0, t < n, j < l1, 0 < i < l1.
  If  m_ancestor (A[n]) m (idx_B(n,i)) (idx_B(t,j))
  then m_ancestor (A[n]) m (idx_B(n,i)) (idx_B(n,0)).

Rationale: idx_B(n,0) is the leftmost block-n column; it is the unique
"gateway" through which the upward m-ancestor chain of any block-n column
must pass before it can land on an earlier-block (t<n) column. So whenever
an earlier-block column is reached as an ancestor, idx_B(n,0) is reached too.

If this holds for all m (in particular for the chain_breaks witness k'),
then in the chain_breaks branch idx_B(n,0) would be an ancestor at *every*
level <= k_0, contradicting the existence of a breaking witness <= k_0.

Search: BFS over BMS, enumerate (n,m,i) configurations where the antecedent
        holds, and check the consequent. Any failure => REFUTATION.

Usage: python3 verify_Bn0_gateway.py
"""

import re
import subprocess

YA_BMS = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"


def parse_bms(text):
    cols = []
    for m in re.finditer(r'\(([^)]*)\)', text):
        nums = [int(x) for x in m.group(1).split(',') if x.strip()]
        cols.append(tuple(nums))
    return cols


def height(A):
    return max(len(c) for c in A) if A else 0


def elem(A, p, r):
    if p >= len(A): return 0
    if r >= len(A[p]): return 0
    return A[p][r]


def m_parent(A, m, i):
    target = elem(A, i, m)
    for p in range(i - 1, -1, -1):
        if elem(A, p, m) >= target: continue
        if m > 0:
            if not m_ancestor(A, m - 1, i, p): continue
        return p
    return None


def m_ancestor(A, m, i, j):
    if j >= i: return False
    p = m_parent(A, m, i)
    while p is not None:
        if p == j: return True
        if p < j: return False
        p = m_parent(A, m, p)
    return False


def last_col_idx(A): return len(A) - 1


def max_parent_level(A):
    last = last_col_idx(A)
    if last < 0: return None
    for m in range(height(A) - 1, -1, -1):
        if m_parent(A, m, last) is not None:
            return m
    return None


def b0_start(A):
    m0 = max_parent_level(A)
    if m0 is None: return None
    return m_parent(A, m0, last_col_idx(A))


def l0(A):
    s = b0_start(A)
    return s if s is not None else len(A)


def l1(A):
    s = b0_start(A)
    if s is None: return 0
    return last_col_idx(A) - s


def idx_B(A, t, j):
    return l0(A) + t * l1(A) + j


def is_G(A, p):
    return p < l0(A)


def decompose_B(A, p):
    L1 = l1(A)
    if L1 == 0: return None
    off = p - l0(A)
    if off < 0: return None
    return (off // L1, off % L1)


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True,
                              text=True, timeout=20).stdout.strip()
    except Exception:
        return None


def check_gateway(A_text, max_n=3):
    A_outer = parse_bms(A_text)
    s = b0_start(A_outer)
    if s is None: return []
    L1 = l1(A_outer)
    if L1 < 1: return []

    failures = []
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        H_An = height(An)
        B_n_0 = idx_B(A_outer, n, 0)
        if B_n_0 >= len(An): continue
        for m in range(0, H_An):
            for i in range(1, L1):
                tgt = idx_B(A_outer, n, i)
                if tgt >= len(An): continue
                # find ancestors of tgt that are earlier-block columns
                for t_par in range(0, n):
                    for j_par in range(0, L1):
                        anc = idx_B(A_outer, t_par, j_par)
                        if anc >= tgt: continue
                        if not m_ancestor(An, m, tgt, anc): continue
                        # antecedent holds: earlier-block ancestor at level m
                        # consequent: idx_B(n,0) is ALSO ancestor at level m
                        if not m_ancestor(An, m, tgt, B_n_0):
                            failures.append((n, m, i, t_par, j_par, An_text))
    return failures


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0,0)(1,1,1,1,1)",
        "(0,0)(1,1)(2,1)",
        "(0,0,0)(1,1,1)(2,2,1)",
        "(0,0,0)(1,1,1)(2,1,0)",
        "(0,0,0)(1,1,1)(2,2,2)",
    ]
    visited = set(seeds)
    total_fail = 0
    tested = 0

    print("=== BFS checking B_n[0] gateway property ===")
    for seed in seeds:
        queue = [seed]
        for depth in range(4):
            next_queue = []
            for bms_text in queue:
                for n in range(1, 4):
                    expanded = expand(bms_text, n)
                    if expanded and expanded not in visited:
                        visited.add(expanded)
                        next_queue.append(expanded)
                        fs = check_gateway(expanded, max_n=2)
                        tested += 1
                        if fs:
                            total_fail += len(fs)
                            print(f"  GATEWAY FAILS on {expanded}")
                            for f in fs[:3]:
                                print(f"    n={f[0]}, m={f[1]}, i={f[2]}, "
                                      f"t_par={f[3]}, j_par={f[4]}")
                            if total_fail > 5:
                                break
                if total_fail > 5:
                    break
            queue = next_queue
            if total_fail > 5:
                break
        if total_fail > 5:
            break

    for seed in seeds:
        fs = check_gateway(seed, max_n=3)
        tested += 1
        if fs:
            total_fail += len(fs)
            print(f"\n  SEED FAILURE on {seed}")
            for f in fs[:3]:
                print(f"    n={f[0]}, m={f[1]}, i={f[2]}, t_par={f[3]}, j_par={f[4]}")

    print(f"\n=== TOTAL: tested {tested} BMSs, {total_fail} gateway failures ===")
    if total_fail == 0:
        print("GATEWAY HOLDS empirically.")
    else:
        print("GATEWAY REFUTED empirically.")


if __name__ == '__main__':
    main()
