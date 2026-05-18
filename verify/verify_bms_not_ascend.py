#!/usr/bin/env python3
"""
Empirical verification of bms_not_ascend_propagates_to_chain_ancestor.

Claim under test:
  Given a BMS A, b0_start A = s, max_parent_level A = t, k < t (so Suc k <= t).
  For columns j, x with 0 < x < j < l1 (length of B_0):
    NOT ascends A j (Suc k)
    AND m_ancestor A k (s+j) (s+x)
    ==> NOT ascends A x (Suc k)

Counter-example search: looks for (A, j, k, x) violating the implication.

Includes x=0 case separately (where ascends A 0 (Suc k) is True trivially
when Suc k < t, so violation is automatic IF chain m_anc A k (s+j) s holds).

Usage: python3 verify_bms_not_ascend.py
"""

import re
import sys
import subprocess

YA_BMS = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"


def parse_bms(text):
    """Parse '(0,0,0)(1,1,1)...' into list of cols (each a tuple of ints)."""
    cols = []
    for m in re.finditer(r'\(([^)]*)\)', text):
        nums = [int(x) for x in m.group(1).split(',') if x.strip()]
        cols.append(tuple(nums))
    return cols


def height(A):
    return max(len(c) for c in A) if A else 0


def elem(A, p, r):
    """row r of column p; 0 if out of range."""
    if p >= len(A):
        return 0
    if r >= len(A[p]):
        return 0
    return A[p][r]


def m_parent(A, m, i):
    """Greatest p < i satisfying elem A p m < elem A i m AND m_ancestor A (m-1) i p (if m > 0).
       Returns None if no such p."""
    cands = []
    target = elem(A, i, m)
    for p in range(i):
        if elem(A, p, m) >= target:
            continue
        if m > 0:
            if not m_ancestor(A, m - 1, i, p):
                continue
        cands.append(p)
    return cands[-1] if cands else None


def m_ancestor(A, m, i, j):
    """True iff there's an m-parent chain from i reaching j."""
    p = m_parent(A, m, i)
    while p is not None:
        if p == j:
            return True
        p = m_parent(A, m, p)
    return False


def last_col_idx(A):
    return len(A) - 1


def max_parent_level(A):
    """Highest m such that m_parent A m (last_col_idx A) exists. None if no parent."""
    last = last_col_idx(A)
    if last < 0:
        return None
    best = None
    for m in range(height(A) - 1, -1, -1):
        if m_parent(A, m, last) is not None:
            return m
    return None


def b0_start(A):
    """If max_parent_level = Some m_0, return m_parent A m_0 (last). Else None."""
    m0 = max_parent_level(A)
    if m0 is None:
        return None
    return m_parent(A, m0, last_col_idx(A))


def ascends(A, j, m):
    """ascends per the Isabelle definition: m < m_0 AND non_strict_ancestor A m (s+j) s.
       Returns True/False or None if no b0/m_0."""
    m0 = max_parent_level(A)
    s = b0_start(A)
    if m0 is None or s is None:
        return False
    if m >= m0:
        return False
    # non_strict_ancestor: (s+j) == s OR m_ancestor A m (s+j) s
    pos = s + j
    if pos == s:
        return True  # reflexive
    return m_ancestor(A, m, pos, s)


def l1(A):
    """Length of B_0 = arr_len - b0_start, where b0_start = s."""
    s = b0_start(A)
    if s is None:
        return 0
    return last_col_idx(A) - s  # cols [s, last-1] are B_0; last col is C


def check_bms_not_ascend(A, verbose=False):
    """Search for (j, k, x) violating the claim. Returns list of violations.

    Violations: (j, k, x) where:
      x_pos: 0 < x < j (we also test x = 0 separately)
      j < l1
      NOT ascends A j (Suc k)
      m_ancestor A k (s+j) (s+x)
      AND ascends A x (Suc k)  [the conclusion fails]
    """
    s = b0_start(A)
    m0 = max_parent_level(A)
    if s is None or m0 is None or m0 == 0:
        return []

    L1 = l1(A)
    if L1 < 2:
        return []

    violations = []
    for j in range(1, L1):
        for k in range(m0):  # k < m_0 = max_parent_level
            Sk = k + 1
            if Sk >= m0:
                continue  # ascends at Suc k is auto False
            if ascends(A, j, Sk):
                continue  # need NOT asc_j (Suc k)
            for x in range(j):
                if not m_ancestor(A, k, s + j, s + x):
                    continue
                if ascends(A, x, Sk):
                    violations.append((j, k, x))
                    if verbose:
                        print(f"  VIOLATION: A={A}, j={j}, k={k}, x={x}")
                        print(f"    s={s}, m_0={m0}, l1={L1}")
                        print(f"    NOT ascends(j,Suc k=)={ascends(A,j,Sk)}")
                        print(f"    chain m_anc(k=)={m_ancestor(A,k,s+j,s+x)}")
                        print(f"    ascends(x,Suc k=)={ascends(A,x,Sk)}")
    return violations


def expand(bms_text, n=1):
    """Use yaBMS C to expand a BMS."""
    bracket_text = f"{bms_text}[{n}]"
    try:
        result = subprocess.run([YA_BMS, bracket_text], capture_output=True, text=True, timeout=10)
        out = result.stdout.strip()
        return out
    except Exception as e:
        return None


def is_standard(bms_text):
    """Use yaBMS C to check standard form."""
    try:
        result = subprocess.run([YA_BMS, "-s", bms_text], capture_output=True, text=True, timeout=10)
        return "Standard" in result.stdout or "standard" in result.stdout.lower()
    except Exception:
        return False


def main():
    # Test cases: known BMSs
    test_bms = [
        "(0,0,0)(1,1,1)(2,0,0)(1,1,1)",  # the known counterexample BMS
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0)(1,1,1)(2,2,2)",
        "(0,0,0)(1,1,1)(2,1,0)",
        "(0,0,0)(1,1,1)(2,1,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0)(1,1,1,1)(2,2,2,2)",
    ]

    total_violations = 0
    for bms_text in test_bms:
        A = parse_bms(bms_text)
        print(f"\n=== A = {bms_text} ===")
        s = b0_start(A)
        m0 = max_parent_level(A)
        L1 = l1(A)
        print(f"  s={s}, m_0={m0}, l1={L1}")
        if s is None or m0 is None:
            print(f"  Skipping (no b0)")
            continue
        vs = check_bms_not_ascend(A, verbose=True)
        print(f"  Violations: {len(vs)}")
        total_violations += len(vs)

    # Test the BFS expansion sequence
    print("\n\n=== BFS expansion from seed ===")
    seed = "(0,0,0)(1,1,1)"
    queue = [seed]
    visited = set()
    visited.add(seed)
    max_depth = 6
    depth = 0
    while queue and depth < max_depth:
        next_queue = []
        for bms_text in queue:
            for n in range(3):
                expanded = expand(bms_text, n)
                if expanded and expanded not in visited:
                    visited.add(expanded)
                    next_queue.append(expanded)
                    A = parse_bms(expanded)
                    vs = check_bms_not_ascend(A)
                    if vs:
                        print(f"  VIOLATION FOUND: {expanded}")
                        for j, k, x in vs:
                            print(f"    j={j}, k={k}, x={x}")
                        total_violations += len(vs)
        queue = next_queue
        depth += 1
        print(f"  depth={depth}: tested {len(queue)} new BMSs, total violations so far: {total_violations}")

    print(f"\n=== TOTAL VIOLATIONS: {total_violations} ===")


if __name__ == '__main__':
    main()
