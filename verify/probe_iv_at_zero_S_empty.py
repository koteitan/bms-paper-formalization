#!/usr/bin/env python3
"""
Probe: in the S_empty case for clause (iv) at k=0, what is the m_parent? Is it always in G_block or None?
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


def probe(A_text, max_n=3):
    A = parse_bms(A_text)
    s = b0_start(A)
    if s is None: return
    L0 = l0(A); L1 = l1(A)
    if L1 < 2: return
    m0 = max_parent_level(A)
    print(f"A={A_text}, s={s}, l0={L0}, l1={L1}, m0={m0}")
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        for i in range(1, L1):
            target = idx_B(A, n, i)
            if target >= len(An): continue
            row0_target = elem(An, target, 0)
            # Compute S
            S = []
            for j_prime in range(i):
                v = elem(An, idx_B(A, 0, j_prime), 0)
                if v < row0_target:
                    S.append(j_prime)
            p = m_parent(An, 0, target)
            if S:
                cls = "S_ne"
            else:
                cls = "S_empty"
            p_desc = "None" if p is None else (
                f"G(p={p})" if p < L0 else f"B({(p-L0)//L1},{(p-L0)%L1})"
            )
            print(f"  n={n}, i={i}, target={target}, row0={row0_target}, {cls}, S={S}, p={p_desc}")


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0)(1)",  # m0=0, l1=1
        "(0,0)(1,0)",  # m0=0 candidate
        "(0,0)(1,2)",
        "(0,0)(1,1)(2,1)",
    ]
    for s in seeds:
        probe(s, max_n=2)
        print()


if __name__ == '__main__':
    main()
