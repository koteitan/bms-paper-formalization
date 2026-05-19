#!/usr/bin/env python3
"""
Empirical check for the lex-side reformulation of (*):

  bms_b0_col_clex_lt: for BMS A with t = max_parent_level > 0 and s = b0_start,
    for every j in [1, l1-1],
       (A ! s) <_clex (A ! (s + j))
  where <_clex is column-level lexicographic less-than (positionwise nat <).

This is logically equivalent to (*) under the BMS rectangular-shape
invariant (BMS_Lex.thy: BMS_is_array), because under same-height columns
elem A s 0 < elem A (s+j) 0 iff (A ! s) <_clex (A ! (s+j)) via
col_lt_via_row0 (when the first-diff row is row 0).

This script verifies that (*) and bms_b0_col_clex_lt agree on
BFS-explored BMSs, providing the empirical grounding for the lex-side
attack scaffolded in BMS_Lex.thy.
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


def elem(A, p, r):
    if p >= len(A): return 0
    if r >= len(A[p]): return 0
    return A[p][r]


def height(A):
    return max(len(c) for c in A) if A else 0


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


def l1(A):
    s = b0_start(A)
    if s is None: return 0
    return last_col_idx(A) - s


def col_lt(c, cp):
    """Column-level lex: c <_clex cp iff (c, cp) is in lex order of nat <."""
    n = min(len(c), len(cp))
    for i in range(n):
        if c[i] < cp[i]: return True
        if c[i] > cp[i]: return False
    return len(c) < len(cp)


def expand(bms_text, n):
    try:
        return subprocess.run(
            [YA_BMS, f"{bms_text}[{n}]"], capture_output=True, text=True, timeout=10
        ).stdout.strip()
    except Exception:
        return None


def check_clex(A):
    """For each j in [1, l1-1], check (A!s) <_clex (A!(s+j)).
    Returns list of bad j; None if hypothesis vacuous."""
    t = max_parent_level(A)
    s = b0_start(A)
    if t is None or t == 0 or s is None:
        return None
    L1 = l1(A)
    if L1 < 2:
        return []
    c_s = A[s]
    bad = []
    for j in range(1, L1):
        c_sj = A[s + j]
        if not col_lt(c_s, c_sj):
            bad.append((j, c_s, c_sj))
    return bad


def check_consistency(A):
    """Cross-check: (*) holds iff bms_b0_col_clex_lt holds (with first-diff at row 0)."""
    t = max_parent_level(A)
    s = b0_start(A)
    if t is None or t == 0 or s is None:
        return None
    L1 = l1(A)
    mismatches = []
    for j in range(1, L1):
        star_holds = elem(A, s + j, 0) > elem(A, s, 0)
        clex_holds = col_lt(A[s], A[s + j])
        if star_holds != clex_holds:
            mismatches.append((j, star_holds, clex_holds))
    return mismatches


def main():
    seeds = [
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0)(1,1,1)(2,0,0)(1,1,1)",
        "(0,0)(1,1)",
        "(0,0,0,0)(1,1,1,2)",
        "(0,0,0,0)(1,2,3,4)",
        "(0,0,0,0,0)(1,1,1,1,1)",
        "(0,0,0)(1,2,0)(1,1,1)",
    ]
    visited = set(seeds)
    counter_clex = []
    consistency_fail = []
    tested = 0
    for seed in seeds:
        queue = [seed]
        for depth in range(4):
            next_queue = []
            for bms_text in queue:
                for n in range(1, 4):
                    ex = expand(bms_text, n)
                    if ex and ex not in visited:
                        visited.add(ex)
                        next_queue.append(ex)
                        A = parse_bms(ex)
                        bad_clex = check_clex(A)
                        mismatch = check_consistency(A)
                        tested += 1
                        if bad_clex:
                            counter_clex.append((ex, bad_clex))
                            print(f"  COUNTER (clex): {ex}")
                            print(f"    bad: {bad_clex}")
                        if mismatch:
                            consistency_fail.append((ex, mismatch))
                            print(f"  INCONSISTENT (clex vs (*)): {ex}")
                            print(f"    mismatch: {mismatch}")
            queue = next_queue
    print(f"Tested {tested} BMSs.")
    print(f"  bms_b0_col_clex_lt counter-examples: {len(counter_clex)}")
    print(f"  (*) vs clex inconsistencies: {len(consistency_fail)}")
    if counter_clex:
        print("bms_b0_col_clex_lt FAILS empirically; lex-side reformulation invalid.")
    else:
        print("bms_b0_col_clex_lt holds empirically; lex-side reformulation valid.")
    if not consistency_fail:
        print("(*) and bms_b0_col_clex_lt agree on every tested BMS")
        print("(empirically validating the lex-side attack route).")


if __name__ == '__main__':
    main()
