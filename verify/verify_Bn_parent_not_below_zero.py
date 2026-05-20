#!/usr/bin/env python3
"""
Empirical verification of the sharper sub-obligation underlying the
"B_n[0] gateway" lemma (idx_B_n_zero_gateway_for_earlier_block_ancestor).

Sub-claim (m_parent_block_n_stays_until_zero):
  Let A be a BMS, l1 A > 0, n >= 1, 0 < a < l1.
  If  m_parent (A[n]) m (idx_B(n,a)) = Some p   then   p >= idx_B(n,0).

  i.e. the *immediate* m-parent of any block-n column idx_B(n,a) with a>0
  never lands strictly below the leftmost block-n column idx_B(n,0).
  (It stays within block n at a smaller offset, or equals idx_B(n,0).)

Why this matters: it is the single inductive step of the gateway lemma.
From it, the upward parent chain of idx_B(n,i) (i>0) descends through
block-n offsets a = i, a', ..., until reaching offset 0 = idx_B(n,0),
and only then can it exit block n to the left toward an earlier block.
Hence any earlier-block (t<n) ancestor of idx_B(n,i) is reached only
*after* idx_B(n,0), so idx_B(n,0) is itself an ancestor.

Any failure => REFUTATION of the chosen reduction.

Usage: python3 verify_Bn_parent_not_below_zero.py
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
    if p >= len(A): return 0
    if r >= len(A[p]): return 0
    return A[p][r]


def m_parent(A, m, i):
    target = elem(A, i, m)
    for p in range(i - 1, -1, -1):
        if elem(A, p, m) >= target: continue
        if m > 0:
            if not m_ancestor(A, m - 1, i, p): continue
        return p
    return None


def m_ancestor(A, m, i, j):
    if j >= i: return False
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


def l0(A):
    s = b0_start(A)
    return s if s is not None else len(A)


def l1(A):
    s = b0_start(A)
    if s is None: return 0
    return last_col_idx(A) - s


def idx_B(A, t, j):
    return l0(A) + t * l1(A) + j


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True,
                              text=True, timeout=20).stdout.strip()
    except Exception:
        return None


def check(A_text, max_n=3):
    A_outer = parse_bms(A_text)
    s = b0_start(A_outer)
    if s is None: return []
    L1 = l1(A_outer)
    if L1 < 1: return []

    failures = []
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        H_An = height(An)
        B_n_0 = idx_B(A_outer, n, 0)
        if B_n_0 >= len(An): continue
        for m in range(0, H_An):
            for a in range(1, L1):
                col = idx_B(A_outer, n, a)
                if col >= len(An): continue
                p = m_parent(An, m, col)
                if p is None: continue
                if p < B_n_0:
                    failures.append((n, m, a, p, B_n_0, An_text))
    return failures


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0,0)(1,1,1,1,1)",
        "(0,0)(1,1)(2,1)",
        "(0,0,0)(1,1,1)(2,2,1)",
        "(0,0,0)(1,1,1)(2,1,0)",
        "(0,0,0)(1,1,1)(2,2,2)",
    ]
    visited = set(seeds)
    total_fail = 0
    tested = 0

    print("=== BFS checking: B_n[a] (a>0) parent never below B_n[0] ===")
    for seed in seeds:
        queue = [seed]
        for depth in range(4):
            next_queue = []
            for bms_text in queue:
                for n in range(1, 4):
                    expanded = expand(bms_text, n)
                    if expanded and expanded not in visited:
                        visited.add(expanded)
                        next_queue.append(expanded)
                        fs = check(expanded, max_n=2)
                        tested += 1
                        if fs:
                            total_fail += len(fs)
                            print(f"  FAILS on {expanded}")
                            for f in fs[:3]:
                                print(f"    n={f[0]}, m={f[1]}, a={f[2]}, "
                                      f"p={f[3]}, B_n_0={f[4]}")
                            if total_fail > 5:
                                break
                if total_fail > 5:
                    break
            queue = next_queue
            if total_fail > 5:
                break
        if total_fail > 5:
            break

    for seed in seeds:
        fs = check(seed, max_n=3)
        tested += 1
        if fs:
            total_fail += len(fs)
            print(f"\n  SEED FAILURE on {seed}")
            for f in fs[:3]:
                print(f"    n={f[0]}, m={f[1]}, a={f[2]}, p={f[3]}, B_n_0={f[4]}")

    print(f"\n=== TOTAL: tested {tested} BMSs, {total_fail} failures ===")
    if total_fail == 0:
        print("SUB-OBLIGATION HOLDS empirically.")
    else:
        print("SUB-OBLIGATION REFUTED empirically.")


if __name__ == '__main__':
    main()
