#!/usr/bin/env python3
"""
Empirical verification of iii_block_shift_bridge_n_ge_2 (Lemma 2.5 Stage 3, n ≥ 2 case).

Claim:
  For BMS A, b0_start = s, max_parent_level = Some m_0, k < m_0, n >= 2,
  i < l1 A:
    m_ancestor (A[n]) k (idx_B(A, 1, 0)) (idx_B(A, 0, i))
      <-->
    m_ancestor (A[n]) k (idx_B(A, n, 0)) (idx_B(A, n-1, i))

  where idx_B(A, t, j) = l0(A) + t * l1(A) + j.

This is Hunter's "trivial extension" of (ii) — the (n-1)-block-translation
bridge used to discharge the substantive case of lemma_2_5_iii_clause_step
when n >= 2.

Counter-example search: BFS expand from multiple seeds, test each (n, k, i) tuple.

Usage: python3 verify_iii_block_shift_bridge_n_ge_2.py
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


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"],
                              capture_output=True, text=True, timeout=10).stdout.strip()
    except Exception:
        return None


def check_iii_bridge(A_text, max_n=4, verbose=False):
    """Check the (iii) n>=2 bridge on A.
       Returns list of (n, k, i, lhs, rhs) violations."""
    A = parse_bms(A_text)
    s = b0_start(A)
    if s is None: return []
    m0 = max_parent_level(A)
    if m0 is None: return []
    L1 = l1(A)
    if L1 < 1: return []

    violations = []
    for n in range(2, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        for k in range(m0):
            for i in range(L1):
                lhs_src = idx_B(A, 1, 0)
                lhs_tgt = idx_B(A, 0, i)
                rhs_src = idx_B(A, n, 0)
                rhs_tgt = idx_B(A, n - 1, i)
                if max(lhs_src, rhs_src, lhs_tgt, rhs_tgt) >= len(An):
                    continue
                lhs = m_ancestor(An, k, lhs_src, lhs_tgt)
                rhs = m_ancestor(An, k, rhs_src, rhs_tgt)
                if lhs != rhs:
                    violations.append((n, k, i, lhs, rhs))
                    if verbose:
                        print(f"  VIOLATION A={A_text}, n={n}, k={k}, i={i}")
                        print(f"    A[{n}] = {An_text}")
                        print(f"    LHS: m_anc {k} idx_B(1,0)={lhs_src} idx_B(0,{i})={lhs_tgt} = {lhs}")
                        print(f"    RHS: m_anc {k} idx_B({n},0)={rhs_src} idx_B({n-1},{i})={rhs_tgt} = {rhs}")
    return violations


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0,0)(1,1,1,1,1)",
    ]
    visited = set(seeds)
    total_violations = 0
    tested = 0
    counter_examples = []

    print("=== BFS checking iii_block_shift_bridge_n_ge_2 ===")
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
                        vs = check_iii_bridge(expanded, max_n=3)
                        tested += 1
                        if vs:
                            counter_examples.append((expanded, vs))
                            total_violations += len(vs)
                            print(f"  VIOLATION FOUND on {expanded}")
                            for v in vs[:3]:
                                print(f"    n={v[0]}, k={v[1]}, i={v[2]}, lhs={v[3]}, rhs={v[4]}")
                            if len(counter_examples) > 5:
                                break
                if len(counter_examples) > 5:
                    break
            queue = next_queue
            if len(counter_examples) > 5:
                break
        if len(counter_examples) > 5:
            break

    for seed in seeds:
        vs = check_iii_bridge(seed, max_n=3)
        tested += 1
        if vs:
            counter_examples.append((seed, vs))
            total_violations += len(vs)
            print(f"\n  SEED VIOLATION on {seed}")
            for v in vs[:3]:
                print(f"    n={v[0]}, k={v[1]}, i={v[2]}, lhs={v[3]}, rhs={v[4]}")

    print(f"\n=== TOTAL: tested {tested} BMSs, {total_violations} violations ===")
    if total_violations == 0:
        print("iii_block_shift_bridge_n_ge_2 holds empirically: NO counter-example.")
    else:
        print("iii_block_shift_bridge_n_ge_2 EMPIRICALLY REFUTED.")


if __name__ == '__main__':
    main()
