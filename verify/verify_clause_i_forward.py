#!/usr/bin/env python3
"""
Empirical verification of Hunter Lemma 2.5 clause (i) — forward direction (all k).

Claim:
  For BMS A, b0_start = s (assumes exists), for all n > 0, all k,
  all i < l0 A, all j < l1 A:
    m_ancestor (A[n]) k (idx_B(0, j)) (idx_G(i))
      -->   (forward)
    m_ancestor (A[n]) k (idx_B(n, j)) (idx_G(i))
  and the full iff (both directions) is also tested.

  idx_G(i) = i
  idx_B(t, j) = l0(A) + t * l1(A) + j

Counter-example search: BFS expand from seeds, test each (n, k, i, j).

Usage: python3 verify_clause_i_forward.py
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


def idx_G(A, i):
    return i


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True, text=True, timeout=10).stdout.strip()
    except Exception:
        return None


def check_clause_i(A_text, max_n=3, verbose=False):
    """Check (i) forward+iff on A across all k, i<l0, j<l1, n in [1,max_n].
       Returns list of (n, k, i, j, lhs, rhs, dir) violations.
       dir='fwd' means forward implication failed; 'bwd' backward failed."""
    A = parse_bms(A_text)
    s = b0_start(A)
    if s is None: return []
    L0 = l0(A)
    L1 = l1(A)
    if L1 < 1 or L0 < 1: return []

    violations = []
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        H_An = height(An)
        for k in range(H_An):
            for i in range(L0):
                for j in range(L1):
                    src0 = idx_B(A, 0, j)
                    srcn = idx_B(A, n, j)
                    tgt = idx_G(A, i)
                    if max(src0, srcn) >= len(An): continue
                    lhs = m_ancestor(An, k, src0, tgt)
                    rhs = m_ancestor(An, k, srcn, tgt)
                    if lhs and not rhs:
                        violations.append((n, k, i, j, lhs, rhs, 'fwd'))
                        if verbose:
                            print(f"  FWD VIOLATION A={A_text} n={n} k={k} i={i} j={j}")
                            print(f"    A[{n}]={An_text}")
                            print(f"    LHS m_anc {k} {src0} {tgt}={lhs}  RHS m_anc {k} {srcn} {tgt}={rhs}")
                    if rhs and not lhs:
                        violations.append((n, k, i, j, lhs, rhs, 'bwd'))
                        if verbose:
                            print(f"  BWD VIOLATION A={A_text} n={n} k={k} i={i} j={j}")
    return violations


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0,0)(1,1,1,1,1)",
    ]
    visited = set(seeds)
    total = 0
    tested = 0
    fwd_v = 0
    bwd_v = 0
    examples = []

    print("=== BFS expansion checking clause (i) forward+iff for all k ===")
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
                        vs = check_clause_i(expanded, max_n=2)
                        tested += 1
                        if vs:
                            examples.append((expanded, vs))
                            total += len(vs)
                            fwd_v += sum(1 for v in vs if v[6] == 'fwd')
                            bwd_v += sum(1 for v in vs if v[6] == 'bwd')
                            print(f"  VIOLATION FOUND on {expanded}")
                            for v in vs[:5]:
                                print(f"    n={v[0]} k={v[1]} i={v[2]} j={v[3]} lhs={v[4]} rhs={v[5]} dir={v[6]}")
            queue = next_queue
            if len(examples) > 8:
                break
        if len(examples) > 8:
            break

    for seed in seeds:
        vs = check_clause_i(seed, max_n=3)
        tested += 1
        if vs:
            examples.append((seed, vs))
            total += len(vs)
            fwd_v += sum(1 for v in vs if v[6] == 'fwd')
            bwd_v += sum(1 for v in vs if v[6] == 'bwd')
            print(f"\n  SEED VIOLATION on {seed}")
            for v in vs[:5]:
                print(f"    n={v[0]} k={v[1]} i={v[2]} j={v[3]} lhs={v[4]} rhs={v[5]} dir={v[6]}")

    print(f"\n=== TOTAL: tested {tested} BMSs, {total} violations (fwd={fwd_v}, bwd={bwd_v}) ===")
    if total == 0:
        print("Clause (i) holds empirically: NO counter-example (forward AND backward).")
    else:
        print("Clause (i) EMPIRICALLY REFUTED.")


if __name__ == '__main__':
    main()
