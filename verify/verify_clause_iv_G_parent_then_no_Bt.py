#!/usr/bin/env python3
"""
Empirical verification of clause_iv_intermediate_B_t_impossible_when_G_parent_exists.

Claim (False target):
  Let A in BMS, b0_start = Some s, 0 < l1, k > 0.
  Let 0 < i < l1.
  Suppose m_parent (A[n]) k (idx_B(n, i)) = Some p
    and  p = idx_B(t, j) with t < n and j < l1.
  Suppose also that exists k' < k with
    m_parent (A[n]) k' (idx_B(n, i)) = Some q
    and q = idx_G(g) with g < l0.

  Then we should derive False.

i.e., we should NEVER see a witness configuration where:
  - p in some B_t (t < n)  AND
  - some k' < k yields a G parent.

If the claim is true, BFS finds 0 such witnesses.  If false, we get a counter-example.

Usage: python3 verify_clause_iv_G_parent_then_no_Bt.py
"""

import re
import subprocess

YA_BMS = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"


def parse_bms(text):
    cols = []
    for m in re.finditer(r"\(([^)]*)\)", text):
        nums = [int(x) for x in m.group(1).split(",") if x.strip()]
        cols.append(tuple(nums))
    return cols


def height(A):
    return max(len(c) for c in A) if A else 0


def elem(A, p, r):
    if p >= len(A):
        return 0
    if r >= len(A[p]):
        return 0
    return A[p][r]


def m_parent(A, m, i):
    target = elem(A, i, m)
    for p in range(i - 1, -1, -1):
        if elem(A, p, m) >= target:
            continue
        if m > 0:
            if not m_ancestor(A, m - 1, i, p):
                continue
        return p
    return None


def m_ancestor(A, m, i, j):
    p = m_parent(A, m, i)
    while p is not None:
        if p == j:
            return True
        if p < j:
            return False
        p = m_parent(A, m, p)
    return False


def last_col_idx(A):
    return len(A) - 1


def max_parent_level(A):
    last = last_col_idx(A)
    if last < 0:
        return None
    for m in range(height(A) - 1, -1, -1):
        if m_parent(A, m, last) is not None:
            return m
    return None


def b0_start(A):
    m0 = max_parent_level(A)
    if m0 is None:
        return None
    return m_parent(A, m0, last_col_idx(A))


def l0(A):
    s = b0_start(A)
    return s if s is not None else len(A)


def l1(A):
    s = b0_start(A)
    if s is None:
        return 0
    return last_col_idx(A) - s


def idx_B(A, t, j):
    return l0(A) + t * l1(A) + j


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True, text=True, timeout=10).stdout.strip()
    except Exception:
        return None


def classify_parent(An, p, L0_orig, L1_orig, n_expand):
    """Return ('G', g) if p < L0_orig, ('B', t, j) if p = L0_orig + t*L1_orig + j with t <= n_expand, j < L1_orig.
       Else ('OTHER',)."""
    if p < L0_orig:
        return ("G", p)
    rel = p - L0_orig
    if L1_orig == 0:
        return ("OTHER",)
    t, j = divmod(rel, L1_orig)
    if j < L1_orig and t <= n_expand:
        return ("B", t, j)
    return ("OTHER",)


def check_one(A_text, max_n=3, max_k=None, verbose=False):
    """Search for witness violating the claim."""
    A = parse_bms(A_text)
    s = b0_start(A)
    if s is None:
        return []
    L1 = l1(A)
    L0 = l0(A)
    if L1 < 2:
        return []
    witnesses = []
    for n_expand in range(1, max_n + 1):
        An_text = expand(A_text, n_expand)
        if not An_text:
            continue
        An = parse_bms(An_text)
        H_An = height(An)
        upto_k = max_k if max_k is not None else H_An
        for i in range(1, L1):
            src = idx_B(A, n_expand, i)
            if src >= len(An):
                continue
            # find k -> p in some B_t with t < n_expand
            for k in range(1, upto_k):
                p = m_parent(An, k, src)
                if p is None:
                    continue
                cls = classify_parent(An, p, L0, L1, n_expand)
                if cls[0] != "B":
                    continue
                t, j = cls[1], cls[2]
                if t >= n_expand:
                    continue
                # check exists k' < k with G parent
                for kp in range(k):
                    q = m_parent(An, kp, src)
                    if q is None:
                        continue
                    qcls = classify_parent(An, q, L0, L1, n_expand)
                    if qcls[0] != "G":
                        continue
                    witnesses.append((n_expand, k, i, kp, t, j, p, q))
                    if verbose:
                        print(f"  WITNESS A={A_text}, n={n_expand}, k={k}, i={i}, kp={kp}")
                        print(f"    A[{n_expand}] = {An_text}")
                        print(f"    p = {p} = idx_B({t}, {j})")
                        print(f"    q = {q} = idx_G({q})")
    return witnesses


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0,0)(1,1,1,1,1)",
        "(0,0,0,0,0,0)(1,1,1,1,1,1)",
    ]
    visited = set(seeds)
    total = 0
    tested = 0
    counter_examples = []

    print("=== BFS expansion checking clause_iv_intermediate_B_t_impossible_when_G_parent_exists ===")
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
                        w = check_one(expanded, max_n=2)
                        tested += 1
                        if w:
                            counter_examples.append((expanded, w))
                            total += len(w)
                            print(f"  WITNESS FOUND on {expanded}")
                            for v in w[:3]:
                                print(f"    n={v[0]}, k={v[1]}, i={v[2]}, kp={v[3]}, t={v[4]}, j={v[5]}")
                            if len(counter_examples) > 5:
                                break
                if len(counter_examples) > 5:
                    break
            queue = next_queue
            if len(counter_examples) > 5:
                break
        if len(counter_examples) > 5:
            break

    # Also check seeds themselves
    for seed in seeds:
        w = check_one(seed, max_n=3)
        tested += 1
        if w:
            counter_examples.append((seed, w))
            total += len(w)
            print(f"\n  SEED WITNESS on {seed}")
            for v in w[:3]:
                print(f"    n={v[0]}, k={v[1]}, i={v[2]}, kp={v[3]}, t={v[4]}, j={v[5]}")

    print(f"\n=== TOTAL: tested {tested} BMSs, {total} witnesses ===")
    if total == 0:
        print("Claim holds empirically: NO witness of (G-parent at some k' < k AND B_t-parent at k).")
    else:
        print("Claim EMPIRICALLY REFUTED: witnesses exist (see above).")


if __name__ == "__main__":
    main()
