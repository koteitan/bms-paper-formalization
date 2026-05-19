#!/usr/bin/env python3
"""
Empirical: in case-B (¬ ascends A j (Suc k')) with j > 0, is the candidate
set ?S (used in the case-B helper) always empty?

?S = [x ∈ [0, j). elem (A[n]) (idx_B(0,x)) (Suc k') < elem (A[n]) (idx_B(0,j)) (Suc k')
                  ∧ m_anc (A[n]) k' (idx_B(0,j)) (idx_B(0,x))]

If YES, then we can prove case-B by directly using
m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t_not_asc with the empty ?S,
bypassing not_asc_chain (which would only be needed for non-empty ?S).
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


def ascends(A, j, m):
    m0 = max_parent_level(A)
    s = b0_start(A)
    if m0 is None or s is None: return False
    if m >= m0: return False
    pos = s + j
    if pos == s: return True
    return m_ancestor(A, m, pos, s)


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True, text=True, timeout=10).stdout.strip()
    except Exception:
        return None


def check_S_empty(A_text, max_n=3, verbose=False):
    A = parse_bms(A_text)
    s = b0_start(A)
    t = max_parent_level(A)
    if s is None or t is None or t == 0: return []
    L1 = l1(A)
    if L1 < 2: return []

    violations = []
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        for k_prime in range(t):
            Sk = k_prime + 1
            if Sk >= t: continue
            for j in range(1, L1):
                if ascends(A, j, Sk): continue
                # Build ?S (using A[n] block 0)
                idx_j_0 = idx_B(A, 0, j)
                if idx_j_0 >= len(An): continue
                v_j = elem(An, idx_j_0, Sk)
                S_members = []
                for x in range(j):
                    idx_x_0 = idx_B(A, 0, x)
                    if idx_x_0 >= len(An): continue
                    v_x = elem(An, idx_x_0, Sk)
                    if v_x < v_j and m_ancestor(An, k_prime, idx_j_0, idx_x_0):
                        S_members.append(x)
                if S_members:
                    violations.append((n, k_prime, j, S_members))
                    if verbose:
                        print(f"  VIOLATION: {A_text}, n={n}, k'={k_prime}, j={j}, S={S_members}")
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

    print("=== BFS from Hunter seeds, check ?S = [] in case-B ===")
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
                        vs = check_S_empty(ex, max_n=2)
                        tested += 1
                        if vs:
                            total_violations += len(vs)
                            print(f"  VIOLATION on {ex}: {len(vs)} cases")
                            for v in vs[:3]:
                                print(f"    n={v[0]}, k'={v[1]}, j={v[2]}, S={v[3]}")
            queue = next_queue

    print(f"\n=== TOTAL: {tested} BMSs, {total_violations} violations ===")
    if total_violations == 0:
        print("Claim HOLDS: in case-B, ?S = [].")
        print("=> case-B can use the 'S_empty' branch only.")
    else:
        print("Claim REFUTED: ?S can be nonempty in case-B.")


if __name__ == '__main__':
    main()
