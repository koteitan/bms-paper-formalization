#!/usr/bin/env python3
"""
Empirical check (*): for BMS A with t = max_parent_level > 0 and s = b0_start,
does elem A (s+j) 0 > elem A s 0 hold for all j in [1, l1-1]?

If YES, this enables proving (H): t>0 => all B_0 cols ascend at row 0
via induction on j.
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


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True, text=True, timeout=10).stdout.strip()
    except Exception: return None


def check_star(A):
    """For each j in [1, l1-1], check elem(s+j, 0) > elem(s, 0). Returns list of bad j."""
    t = max_parent_level(A)
    s = b0_start(A)
    if t is None or t == 0 or s is None:
        return None  # skipped
    L1 = l1(A)
    if L1 < 2: return []
    base = elem(A, s, 0)
    bad = []
    for j in range(1, L1):
        if not (elem(A, s + j, 0) > base):
            bad.append((j, elem(A, s + j, 0), base))
    return bad


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
    counter = []
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
                        bad = check_star(A)
                        tested += 1
                        if bad:
                            counter.append((ex, bad))
                            print(f"  COUNTER: {ex}")
                            print(f"    bad: {bad}")
            queue = next_queue
    print(f"Tested {tested} BMSs. Counter-examples: {len(counter)}")
    if counter:
        print("(*) FAILS empirically")
    else:
        print("(*) holds empirically: elem(s+j,0) > elem(s,0) for all j in [1,l1-1] when t>0")


if __name__ == '__main__':
    main()
