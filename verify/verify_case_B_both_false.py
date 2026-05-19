#!/usr/bin/env python3
"""
Empirical check: in lemma_2_5_ii_clause_step_v2 case B
(¬ ascends A j (Suc k')), is m_anc (A[n]) (Suc k') (idx_B(c, j)) (idx_B(c, i))
False for all c ∈ {0, n}, i < j < l1?

If YES, the case-B branch can be proven via "both sides False" without
needing the Hunter helper or not_asc_chain.
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


def check_case_B(A_text, max_n=3, verbose=False):
    """For Hunter BMS A, check case-B conjecture for all j, k', i in range."""
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
        # Try each k' < t-1 (so Suc k' < t)
        for k_prime in range(t):  # k' < t means Suc k' ≤ t
            Sk = k_prime + 1
            if Sk >= t: continue
            for j in range(L1):
                # Case B trigger: j doesn't ascend at Suc k'
                if ascends(A, j, Sk): continue
                # For each c ∈ {0, n}, each i < j, check m_anc at Suc k' = False
                for c in [0, n]:
                    for i in range(j):
                        src = idx_B(A, c, j)
                        tgt = idx_B(A, c, i)
                        if max(src, tgt) >= len(An): continue
                        if m_ancestor(An, Sk, src, tgt):
                            violations.append((n, k_prime, c, i, j, src, tgt))
                            if verbose:
                                print(f"  VIOLATION: A={A_text}, n={n}, k'={k_prime}, c={c}, i={i}, j={j}")
                                print(f"    m_anc (A[{n}]) {Sk} {src} {tgt} = True (expected False)")
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

    print("=== BFS from Hunter seeds, check case-B 'both False' ===")
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
                        vs = check_case_B(ex, max_n=2)
                        tested += 1
                        if vs:
                            total_violations += len(vs)
                            print(f"  VIOLATION on {ex}: {len(vs)} cases")
                            for v in vs[:2]:
                                print(f"    n={v[0]}, k'={v[1]}, c={v[2]}, i={v[3]}, j={v[4]}")
            queue = next_queue

    print(f"\n=== TOTAL: {tested} BMSs, {total_violations} violations ===")
    if total_violations == 0:
        print("Conjecture HOLDS: in case B, m_anc Suc k' is False for both c=0 and c=n.")
        print("=> case-B can be proven by showing both sides False.")
    else:
        print("Conjecture REFUTED: case B requires Hunter helper / not_asc_chain.")


if __name__ == '__main__':
    main()
