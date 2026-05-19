#!/usr/bin/env python3
"""
Empirical verification of clause_iv_intermediate_B_t_impossible_at_zero:

For A in BMS with b0_start = Some s, l1 > 0, n in BFS reach, i in [1, l1),
if m_parent (A[n]) 0 (idx_B(n, i)) = Some p, then p is NOT in any block
idx_B(t, j) with t < n, j < l1.

Equivalently: the level-0 m-parent of any non-first column in B_n lies in
G_block (p < l0) or in B_n itself (idx_B(n, 0) <= p < idx_B(n, i)),
but never in an earlier B_t (l0 <= p < idx_B(n, 0)).
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


def height(A): return max(len(c) for c in A) if A else 0


def elem(A, p, r):
    if p >= len(A): return 0
    if r >= len(A[p]): return 0
    return A[p][r]


def m_parent(A, m, i):
    target = elem(A, i, m)
    for p in range(i - 1, -1, -1):
        if elem(A, p, m) >= target: continue
        if m > 0 and not m_ancestor(A, m - 1, i, p): continue
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
        if m_parent(A, m, last) is not None: return m
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


def idx_B(A, t, j): return l0(A) + t * l1(A) + j


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True, text=True, timeout=10).stdout.strip()
    except Exception:
        return None


def check_iv_at_zero(A_text, max_n=3, verbose=False):
    A = parse_bms(A_text)
    s = b0_start(A)
    if s is None: return []
    L1 = l1(A)
    L0 = l0(A)
    if L1 < 2: return []  # need i_pos with i < L1

    violations = []
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        for i in range(1, L1):  # i_pos and i < L1
            target = idx_B(A, n, i)
            if target >= len(An): continue
            p = m_parent(An, 0, target)
            if p is None: continue
            # Check if p is in some earlier B_t (t < n)
            if p < L0:
                # In G_block, OK
                continue
            # p >= L0, find which block
            block_offset = p - L0
            t = block_offset // L1
            j = block_offset % L1
            if t < n:
                # Violation: p in B_t with t < n
                violations.append((n, i, p, t, j, target))
                if verbose:
                    print(f"  VIOLATION: A={A_text}, n={n}, i={i}, p={p}=idx_B({t},{j}), target={target}")
    return violations


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0,0)(1,1,1,1,1)",
        "(0)(1)",
        "(0,0)(1,0)",  # m0 = 0 case
        "(0,0)(1,2)",
    ]
    visited = set(seeds)
    total_violations = 0
    tested = 0

    print("=== BFS from seeds, check (iv) at k=0: no parent in earlier B_t ===")
    for seed in seeds:
        queue = [seed]
        for depth in range(5):
            next_queue = []
            for bms_text in queue:
                for n in range(1, 4):
                    ex = expand(bms_text, n)
                    if ex and ex not in visited:
                        visited.add(ex)
                        next_queue.append(ex)
                        vs = check_iv_at_zero(ex, max_n=3)
                        tested += 1
                        if vs:
                            total_violations += len(vs)
                            print(f"  VIOLATION on {ex}: {len(vs)} cases")
                            for v in vs[:3]:
                                print(f"    n={v[0]}, i={v[1]}, p={v[2]}=idx_B({v[3]},{v[4]}), target={v[5]}")
            queue = next_queue

    # Also test seeds themselves
    for s in seeds:
        vs = check_iv_at_zero(s, max_n=3, verbose=True)
        tested += 1
        if vs:
            total_violations += len(vs)

    print(f"\n=== TOTAL: {tested} BMSs tested, {total_violations} violations ===")
    if total_violations == 0:
        print("Claim HOLDS: at k=0, m_parent never lands in an earlier B_t.")
    else:
        print("Claim REFUTED.")


if __name__ == '__main__':
    main()
