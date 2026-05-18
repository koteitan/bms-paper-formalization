#!/usr/bin/env python3
"""
Empirical verification of lemma_2_5_ii_clause_step_v2_at_zero_when_t_pos.

Claim under test:
  Given a BMS A, b0_start A = s, max_parent_level A = t, t > 0, n > 0.
  For i, j with i < j < l1 A:
    m_ancestor (A[n]) 0 (idx_B(A, 0, j)) (idx_B(A, 0, i))
      <-->
    m_ancestor (A[n]) 0 (idx_B(A, n, j)) (idx_B(A, n, i))

  where idx_B(A, t, j) = l0(A) + t * l1(A) + j

This is the (ii) clause at k=0 when t > 0 (the non-trivial base case).

Counter-example search: BFS expand from seed, check each pair (i,j) for each n.

Usage: python3 verify_clause_ii_at_zero_when_t_pos.py
"""

import re
import sys
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
    if p >= len(A):
        return 0
    if r >= len(A[p]):
        return 0
    return A[p][r]


def m_parent(A, m, i):
    target = elem(A, i, m)
    for p in range(i - 1, -1, -1):
        if elem(A, p, m) >= target:
            continue
        if m > 0:
            if not m_ancestor(A, m - 1, i, p):
                continue
        return p
    return None


def m_ancestor(A, m, i, j):
    p = m_parent(A, m, i)
    while p is not None:
        if p == j:
            return True
        if p < j:
            return False
        p = m_parent(A, m, p)
    return False


def last_col_idx(A):
    return len(A) - 1


def max_parent_level(A):
    last = last_col_idx(A)
    if last < 0:
        return None
    for m in range(height(A) - 1, -1, -1):
        if m_parent(A, m, last) is not None:
            return m
    return None


def b0_start(A):
    m0 = max_parent_level(A)
    if m0 is None:
        return None
    return m_parent(A, m0, last_col_idx(A))


def l0(A):
    """G length = first index of B_0 = b0_start(A)."""
    s = b0_start(A)
    return s if s is not None else len(A)


def l1(A):
    s = b0_start(A)
    if s is None:
        return 0
    return last_col_idx(A) - s


def idx_B(A, t, j):
    return l0(A) + t * l1(A) + j


def expand(bms_text, n):
    bracket_text = f"{bms_text}[{n}]"
    try:
        result = subprocess.run([YA_BMS, bracket_text], capture_output=True, text=True, timeout=10)
        out = result.stdout.strip()
        return out
    except Exception:
        return None


def check_lemma(A_text, max_n=3, verbose=False):
    """Check claim on A. Returns list of (n, i, j, lhs, rhs) violations."""
    A = parse_bms(A_text)
    s = b0_start(A)
    m0 = max_parent_level(A)
    if s is None or m0 is None or m0 == 0:
        return []  # need t > 0
    L1 = l1(A)
    L0 = l0(A)
    if L1 < 2:
        return []  # need i < j < l1

    violations = []
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text:
            continue
        An = parse_bms(An_text)
        for i in range(L1):
            for j in range(i + 1, L1):
                lhs_src = idx_B(A, 0, j)
                lhs_tgt = idx_B(A, 0, i)
                rhs_src = idx_B(A, n, j)
                rhs_tgt = idx_B(A, n, i)
                lhs = m_ancestor(An, 0, lhs_src, lhs_tgt)
                rhs = m_ancestor(An, 0, rhs_src, rhs_tgt)
                if lhs != rhs:
                    violations.append((n, i, j, lhs, rhs))
                    if verbose:
                        print(f"  VIOLATION on A={A_text}, n={n}, i={i}, j={j}")
                        print(f"    A[{n}] = {An_text}")
                        print(f"    LHS: m_anc 0 {lhs_src} {lhs_tgt} = {lhs}")
                        print(f"    RHS: m_anc 0 {rhs_src} {rhs_tgt} = {rhs}")
    return violations


def main():
    # Seed list (known BMSs with t > 0)
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0)(1,1,1)(2,2,2)",
        "(0,0,0)(1,1,1)(2,1,0)",
        "(0,0,0)(1,1,1)(2,1,0)(1,1,1)",
        "(0,0,0)(1,1,1)(2,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0)(1,1,1,1)(2,2,2,2)",
    ]

    total_violations = 0
    for bms_text in seeds:
        A = parse_bms(bms_text)
        print(f"\n=== A = {bms_text} ===")
        s = b0_start(A)
        m0 = max_parent_level(A)
        L1 = l1(A)
        L0 = l0(A)
        print(f"  s={s}, t={m0}, l0={L0}, l1={L1}")
        if s is None or m0 is None or m0 == 0:
            print(f"  Skipping (t=0 or no b0)")
            continue
        vs = check_lemma(bms_text, max_n=3, verbose=True)
        print(f"  Violations: {len(vs)}")
        total_violations += len(vs)

    # BFS expansion
    print("\n\n=== BFS expansion from seed (0,0,0)(1,1,1) ===")
    seed = "(0,0,0)(1,1,1)"
    queue = [seed]
    visited = {seed}
    max_depth = 5
    tested = 0
    for depth in range(max_depth):
        next_queue = []
        for bms_text in queue:
            for n in range(1, 4):
                expanded = expand(bms_text, n)
                if expanded and expanded not in visited:
                    visited.add(expanded)
                    next_queue.append(expanded)
                    vs = check_lemma(expanded, max_n=2)
                    tested += 1
                    if vs:
                        print(f"  VIOLATION FOUND on {expanded}:")
                        for v in vs:
                            print(f"    n={v[0]}, i={v[1]}, j={v[2]}, lhs={v[3]}, rhs={v[4]}")
                        total_violations += len(vs)
        queue = next_queue
        print(f"  depth={depth+1}: {len(queue)} new BMSs, tested so far: {tested}, total violations: {total_violations}")

    print(f"\n=== TOTAL VIOLATIONS: {total_violations} (tested {tested} BFS-expanded BMSs + {len(seeds)} seeds) ===")
    if total_violations == 0:
        print("EMPIRICALLY CONSISTENT: no counter-example found.")
    else:
        print("EMPIRICALLY REFUTED: counter-examples exist.")


if __name__ == '__main__':
    main()
