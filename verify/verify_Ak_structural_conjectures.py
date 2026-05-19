#!/usr/bin/env python3
"""
Empirical verification of A[k] structural conjectures needed for BMS.induct
expand case in lemmas like bms_b0_row0_gt_s and bms_S_empty_case_B_at_block_0.

Conjectures (for A ∈ BMS, A ≠ [], b0_start A = Some s, max_parent_level A = Some t):
  C1: max_parent_level (A[k]) = Some t  (same t)
  C2: b0_start (A[k]) = Some (l_0(A) + k * l_1(A))  (start of block k in A[k])
  C3: l_1 (A[k]) = l_1(A)
  C4: last_col_idx (A[k]) = l_0(A) + (k+1) * l_1(A) - 1
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


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True, text=True, timeout=10).stdout.strip()
    except Exception:
        return None


def check_conjectures(A_text, max_n=3, verbose=False, require_t_pos=True,
                       require_An_t_pos=True):
    A = parse_bms(A_text)
    s_A = b0_start(A)
    t_A = max_parent_level(A)
    if s_A is None or t_A is None: return []
    if require_t_pos and t_A == 0: return []

    L0_A = l0(A)
    L1_A = l1(A)

    violations = []
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        s_An = b0_start(An)
        t_An = max_parent_level(An)
        L0_An = l0(An)
        L1_An = l1(An)
        last_An = last_col_idx(An)

        # If A[n] has no parent or t_An == 0, (*) is vacuous on A[n] side.
        # Filter to only cases where A[n] is "non-trivial".
        if require_An_t_pos and (t_An is None or t_An == 0):
            continue

        # C1: max_parent_level (A[n]) = Some t_A
        if t_An != t_A:
            violations.append(('C1', n, t_An, t_A, A_text))

        # C2: b0_start (A[n]) = Some (l_0(A) + n * l_1(A))
        expected_s_An = L0_A + n * L1_A
        if s_An != expected_s_An:
            violations.append(('C2', n, s_An, expected_s_An, A_text))

        # C3: l_1 (A[n]) = l_1(A)
        if L1_An != L1_A:
            violations.append(('C3', n, L1_An, L1_A, A_text))

        # C4: last_col_idx (A[n]) = L0_A + (n+1) * L1_A - 1
        expected_last_An = L0_A + (n + 1) * L1_A - 1
        if last_An != expected_last_An:
            violations.append(('C4', n, last_An, expected_last_An, A_text))

        if verbose and violations:
            for v in violations[-4:]:
                print(f"  VIOLATION ({v[0]}): n={v[1]}, got={v[2]}, expected={v[3]} on {v[4]}")

    return violations


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0,0)(1,1,1,1,1)",
    ]
    visited = set(seeds)
    total_violations_by_type = {'C1': 0, 'C2': 0, 'C3': 0, 'C4': 0}
    tested = 0

    print("=== BFS from Hunter seeds, check A[k] structural conjectures ===")
    print("  C1: max_parent_level (A[k]) = max_parent_level A")
    print("  C2: b0_start (A[k]) = l_0(A) + k * l_1(A)")
    print("  C3: l_1 (A[k]) = l_1(A)")
    print("  C4: last_col_idx (A[k]) = l_0(A) + (k+1) * l_1(A) - 1")
    print()
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
                        vs = check_conjectures(ex, max_n=2)
                        tested += 1
                        for v in vs:
                            total_violations_by_type[v[0]] += 1
                        if vs:
                            for v in vs[:3]:
                                print(f"  VIOLATION ({v[0]}): n={v[1]}, got={v[2]}, expected={v[3]} on {v[4]}")
            queue = next_queue

    print(f"\n=== TOTAL: {tested} BMSs tested ===")
    for key, count in total_violations_by_type.items():
        status = "HOLDS" if count == 0 else f"REFUTED ({count} violations)"
        print(f"  {key}: {status}")


if __name__ == '__main__':
    main()
