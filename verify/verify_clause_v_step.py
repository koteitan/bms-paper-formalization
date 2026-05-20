#!/usr/bin/env python3
"""
Empirical verification of Hunter Lemma 2.5 clause (v) -- the n_1 -> n_1+1 step.

Claim (lemma_2_5_v_clause):
  For BMS A, b0_start = s. For all n, all k, all i, j < l1 A,
  all n_0 < n_1 < n:
    m_ancestor (A[n]) k (idx_B(n_1, j)) (idx_B(n_0, i))
      <-->
    m_ancestor (A[n]) k (idx_B(n_1 + 1, j)) (idx_B(n_0, i))

  where idx_B(t, j) = l0(A) + t * l1(A) + j

This mirrors verify_clause_ii_all_k.py but for the intermediate-copy
block-shift step of clause (v). A counter-example here would refute the
proposition; absence supports attempting a proof.

Usage: python3 verify_clause_v_step.py
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
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"],
                              capture_output=True, text=True, timeout=10).stdout.strip()
    except Exception:
        return None


def check_clause_v(A_text, max_n=4, verbose=False):
    """Check (v) step on A across all k, all (i,j) < l1, all n0<n1<n, n<=max_n.
       Returns list of (n, k, i, j, n0, n1, lhs, rhs) violations."""
    A = parse_bms(A_text)
    s = b0_start(A)
    if s is None: return []
    L1 = l1(A)
    if L1 < 1: return []

    violations = []
    for n in range(3, max_n + 1):           # need n_0 < n_1 < n, so n >= 3
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        H_An = height(An)
        for n1 in range(1, n - 1):           # n1 < n, and n1 >= 1 (n0 < n1)
            for n0 in range(0, n1):
                for k in range(H_An):
                    for i in range(L1):
                        for j in range(L1):
                            lhs_src = idx_B(A, n1, j)
                            lhs_tgt = idx_B(A, n0, i)
                            rhs_src = idx_B(A, n1 + 1, j)
                            rhs_tgt = idx_B(A, n0, i)
                            if max(lhs_src, rhs_src, lhs_tgt) >= len(An):
                                continue
                            lhs = m_ancestor(An, k, lhs_src, lhs_tgt)
                            rhs = m_ancestor(An, k, rhs_src, rhs_tgt)
                            if lhs != rhs:
                                violations.append((n, k, i, j, n0, n1, lhs, rhs))
                                if verbose:
                                    print(f"  VIOLATION A={A_text}, n={n}, k={k}, "
                                          f"i={i}, j={j}, n0={n0}, n1={n1}")
                                    print(f"    A[{n}] = {An_text}")
                                    print(f"    LHS: m_anc {k} {lhs_src} {lhs_tgt} = {lhs}")
                                    print(f"    RHS: m_anc {k} {rhs_src} {rhs_tgt} = {rhs}")
    return violations


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0,0)(1,1,1,1,1)",
        "(0,0)(1,1)(2,2)",
        "(0,0,0)(1,1,1)(2,2,2)",
    ]
    visited = set(seeds)
    total_violations = 0
    tested = 0
    counter_examples = []

    print("=== BFS expansion checking clause (v) step for all k ===")
    for seed in seeds:
        queue = [seed]
        for depth in range(3):
            next_queue = []
            for bms_text in queue:
                for n in range(1, 4):
                    expanded = expand(bms_text, n)
                    if expanded and expanded not in visited:
                        visited.add(expanded)
                        next_queue.append(expanded)
                        vs = check_clause_v(expanded, max_n=4)
                        tested += 1
                        if vs:
                            counter_examples.append((expanded, vs))
                            total_violations += len(vs)
                            print(f"  VIOLATION FOUND on {expanded}")
                            for v in vs[:3]:
                                print(f"    n={v[0]}, k={v[1]}, i={v[2]}, j={v[3]}, "
                                      f"n0={v[4]}, n1={v[5]}, lhs={v[6]}, rhs={v[7]}")
                            if len(counter_examples) > 5:
                                break
                if len(counter_examples) > 5:
                    break
            queue = next_queue
            if len(counter_examples) > 5:
                break
        if len(counter_examples) > 5:
            break

    for seed in seeds:
        vs = check_clause_v(seed, max_n=5, verbose=True)
        tested += 1
        if vs:
            counter_examples.append((seed, vs))
            total_violations += len(vs)
            print(f"\n  SEED VIOLATION on {seed}")
            for v in vs[:3]:
                print(f"    n={v[0]}, k={v[1]}, i={v[2]}, j={v[3]}, "
                      f"n0={v[4]}, n1={v[5]}, lhs={v[6]}, rhs={v[7]}")

    print(f"\n=== TOTAL: tested {tested} BMSs, {total_violations} violations ===")
    if total_violations == 0:
        print("Clause (v) step holds empirically: NO counter-example.")
    else:
        print("Clause (v) step EMPIRICALLY REFUTED.")


if __name__ == '__main__':
    main()
