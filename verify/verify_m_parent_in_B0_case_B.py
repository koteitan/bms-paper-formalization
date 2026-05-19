#!/usr/bin/env python3
"""
Empirical: in case-B (¬ ascends A j (Suc k')) with j > 0, is m_parent A (Suc k')
(s+j) always None or < s (i.e., outside B_0)?

If YES, then both LHS m_anc (A[n]) (Suc k') (idx_B(0,j)) (idx_B(0,i)) and RHS
m_anc (A[n]) (Suc k') (idx_B(n,j)) (idx_B(n,i)) are vacuously False for i < j,
and case-B can be proven by this structural pattern.

Also tests c=n side: m_parent (A[n]) (Suc k') (idx_B(n,j)) is None or
< idx_B(n,0).
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


def check_m_parent(A_text, max_n=3, verbose=False):
    """For Hunter BMS A, check the structural claim."""
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
                # c=0: m_parent A (Suc k') (s+j) should be None or < s
                p_A = m_parent(A, Sk, s + j)
                if p_A is not None and p_A >= s:
                    violations.append(('A', n, k_prime, j, p_A, s))
                    if verbose:
                        print(f"  VIOLATION (A): {A_text}, n={n}, k'={k_prime}, j={j}, m_parent={p_A}, s={s}")
                # c=n: m_parent (A[n]) (Suc k') (idx_B(n,j)) should be None or < idx_B(n,0)
                src_n = idx_B(A, n, j)
                start_n = idx_B(A, n, 0)
                if src_n < len(An):
                    p_An = m_parent(An, Sk, src_n)
                    if p_An is not None and p_An >= start_n:
                        violations.append(('An', n, k_prime, j, p_An, start_n))
                        if verbose:
                            print(f"  VIOLATION (An): {A_text}, n={n}, k'={k_prime}, j={j}, m_parent={p_An}, idx_B(n,0)={start_n}")
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

    print("=== BFS from Hunter seeds, check m_parent in case-B is outside B_0/B_n ===")
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
                        vs = check_m_parent(ex, max_n=2)
                        tested += 1
                        if vs:
                            total_violations += len(vs)
                            print(f"  VIOLATION on {ex}: {len(vs)} cases")
                            for v in vs[:3]:
                                print(f"    {v}")
            queue = next_queue

    print(f"\n=== TOTAL: {tested} BMSs, {total_violations} violations ===")
    if total_violations == 0:
        print("Claim HOLDS: in case-B, m_parent A (Suc k') (s+j) is None or < s.")
        print("=> case-B can be proven via 'm_parent outside B_0' structural fact.")
    else:
        print("Claim REFUTED: m_parent in case-B can be inside B_0.")


if __name__ == '__main__':
    main()
