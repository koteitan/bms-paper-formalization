#!/usr/bin/env python3
"""
Empirical check: when t > 0, does ascends A j 0 hold for all j < l1 A?

If YES, then at_zero_when_t_pos's case B (j doesn't ascend at row 0) is
vacuous and the proof only needs case A.

If NO, we need a case-B proof too.
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


def l1(A):
    s = b0_start(A)
    if s is None:
        return 0
    return last_col_idx(A) - s


def ascends(A, j, m):
    m0 = max_parent_level(A)
    s = b0_start(A)
    if m0 is None or s is None:
        return False
    if m >= m0:
        return False
    pos = s + j
    if pos == s:
        return True
    return m_ancestor(A, m, pos, s)


def expand(bms_text, n):
    try:
        result = subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True, text=True, timeout=10)
        return result.stdout.strip()
    except Exception:
        return None


def check_t_pos_all_ascend_row0(A):
    """Returns list of j where ascends A j 0 is False (counterexamples)."""
    t = max_parent_level(A)
    s = b0_start(A)
    if t is None or t == 0 or s is None:
        return []
    L1 = l1(A)
    bad = []
    for j in range(L1):
        if not ascends(A, j, 0):
            bad.append(j)
    return bad


def main():
    counter_examples = []

    print("=== BFS expansion from multiple seeds ===")
    seeds_for_bfs = [
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0)(1,1,1)(2,0,0)(1,1,1)",
        "(0,0)(1,1)",
        "(0,0,0,0)(1,1,1,2)",
        "(0,0,0,0)(1,2,3,4)",
        "(0,0,0,0,0)(1,1,1,1,1)",
        "(0,0,0)(1,2,0)(1,1,1)",
    ]
    visited = set(seeds_for_bfs)
    tested = 0
    for seed in seeds_for_bfs:
        queue = [seed]
        for depth in range(4):
            next_queue = []
            for bms_text in queue:
                for n in range(1, 4):
                    expanded = expand(bms_text, n)
                    if expanded and expanded not in visited:
                        visited.add(expanded)
                        next_queue.append(expanded)
                        A = parse_bms(expanded)
                        bad = check_t_pos_all_ascend_row0(A)
                        tested += 1
                        if bad:
                            counter_examples.append((expanded, bad))
                            print(f"  COUNTER-EXAMPLE: {expanded}")
                            print(f"    t={max_parent_level(A)}, cols {bad} don't ascend at row 0")
            queue = next_queue
        # also check seed itself
        A_seed = parse_bms(seed)
        bad = check_t_pos_all_ascend_row0(A_seed)
        if bad:
            counter_examples.append((seed, bad))
            print(f"  SEED COUNTER-EXAMPLE: {seed}: cols {bad} don't ascend at row 0")
    print(f"  Tested {tested} expanded BMSs from {len(seeds_for_bfs)} seeds")

    # Also seeds for variety
    for seed_text in ["(0,0,0)(1,1,1)(2,0,0)(1,1,1)",
                       "(0,0,0,0)(1,1,1,1)",
                       "(0,0,0,0)(1,1,1,1)(2,2,2,2)",
                       "(0,0,0,0)(1,2,3,4)",
                       "(0,0,0)(1,2,0)(1,1,1)",
                       "(0,0,0,0)(1,0,1,1)(2,1,2,1)"]:
        A = parse_bms(seed_text)
        t = max_parent_level(A)
        if t is None or t == 0:
            print(f"\n=== {seed_text} t={t} (skipped) ===")
            continue
        bad = check_t_pos_all_ascend_row0(A)
        print(f"\n=== {seed_text} t={t}, l1={l1(A)} ===")
        if bad:
            print(f"  Cols not ascending at row 0: {bad}")
            counter_examples.append((seed_text, bad))
        else:
            print(f"  All cols ascend at row 0")

    print(f"\n=== TOTAL: {len(counter_examples)} BMSs where some col in B_0 doesn't ascend at row 0 (with t>0) ===")
    if counter_examples:
        print("HYPOTHESIS FALSE: case B at row 0 CAN occur.")
    else:
        print("HYPOTHESIS HOLDS empirically: when t>0, all cols in B_0 ascend at row 0.")
        print("=> case B is vacuous in at_zero_when_t_pos; only case A needed.")


if __name__ == '__main__':
    main()
