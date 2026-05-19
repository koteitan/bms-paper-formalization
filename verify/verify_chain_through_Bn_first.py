#!/usr/bin/env python3
"""
Empirical verification of clause_iv_intermediate_B_t_impossible_chain_through_Bn_first.

Claim (Hunter Lemma 2.5 (iv), Suc k_0 sub-case):
  Let A be a BMS, A != [], b0_start A = Some s, l1 A > 0.
  Let k > 0, i with 0 < i < l1 A, and assume
    m_parent (A[n]) k (idx_B(n,i)) = Some p,
  with p = idx_B(t,j), t < n, j < l1.
  Assume:
    no_G_parent: there is no k' < k and q s.t.
       m_parent (A[n]) k' (idx_B(n,i)) = Some q
       AND q is a G-column.
    chain_through_Bn0:
       for every k' < k,
         m_ancestor (A[n]) k' (idx_B(n,i)) (idx_B(n,0)).
  Conclusion: contradiction (i.e. this scenario never happens).

Search: BFS over BMS, for each (n, k, i), check whether the configuration
        (intermediate-B_t parent with chain through B_n[0] at every k' < k
         and no G-parent at any k' < k) can actually occur.
        If so, the claim is empirically FALSE and we must reject.

Usage: python3 verify_chain_through_Bn_first.py
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


def is_G(A, p):
    return p < l0(A)


def decompose_B(A, p):
    """Given p >= l0(A), return (t, j) with p = l0 + t*L1 + j, j < L1."""
    L1 = l1(A)
    if L1 == 0: return None
    off = p - l0(A)
    if off < 0: return None
    return (off // L1, off % L1)


def expand(bms_text, n):
    try:
        return subprocess.run([YA_BMS, f"{bms_text}[{n}]"], capture_output=True, text=True, timeout=20).stdout.strip()
    except Exception:
        return None


def check_chain_through_Bn0(A_text, max_n=3, verbose=False):
    """Returns list of witnesses where the *premise combination* of the
    chain-through-Bn0 lemma is actually satisfied (i.e. the lemma would
    have a real obligation to discharge)."""
    A_outer = parse_bms(A_text)
    s = b0_start(A_outer)
    if s is None: return []
    L1 = l1(A_outer)
    if L1 < 1: return []

    witnesses = []
    refuters = []  # cases where premises hold AND conclusion (False) is not derivable -> counter-ex
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        H_An = height(An)
        for k in range(1, H_An):  # k > 0
            for i in range(1, L1):
                tgt = idx_B(A_outer, n, i)
                if tgt >= len(An): continue
                mp = m_parent(An, k, tgt)
                if mp is None: continue
                if is_G(A_outer, mp): continue  # G-parent at level k is a different branch
                dec = decompose_B(A_outer, mp)
                if dec is None: continue
                t_par, j_par = dec
                if t_par >= n: continue   # we need t < n (intermediate B_t)
                # no_G_parent at any k' < k
                no_G = True
                for kp in range(k):
                    q = m_parent(An, kp, tgt)
                    if q is None: continue
                    if is_G(A_outer, q):
                        no_G = False
                        break
                if not no_G: continue
                # chain_through_Bn0: for every k' < k, m_ancestor (A[n]) k' tgt (idx_B(n,0))
                B_n_0 = idx_B(A_outer, n, 0)
                if B_n_0 >= len(An): continue
                chain_through = True
                for kp in range(k):
                    if not m_ancestor(An, kp, tgt, B_n_0):
                        chain_through = False
                        break
                if not chain_through: continue
                # all premises satisfied -> the lemma claims False (impossible)
                # so any witness means EMPIRICAL REFUTATION
                refuters.append((n, k, i, t_par, j_par, mp, An_text))
                if verbose:
                    print(f"  PREMISES HOLD on A={A_text}, n={n}, k={k}, i={i}, parent=idx_B({t_par},{j_par})")
                    print(f"    A[{n}] = {An_text}")
    return refuters


def main():
    seeds = [
        "(0,0)(1,1)",
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0,0,0)(1,1,1,1,1)",
    ]
    visited = set(seeds)
    total_refuters = 0
    tested = 0
    refuters_all = []

    print("=== BFS checking clause_iv chain-through-Bn0 sub-case ===")
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
                        rs = check_chain_through_Bn0(expanded, max_n=2)
                        tested += 1
                        if rs:
                            refuters_all.append((expanded, rs))
                            total_refuters += len(rs)
                            print(f"  PREMISES SATISFIED on {expanded}")
                            for r in rs[:3]:
                                print(f"    n={r[0]}, k={r[1]}, i={r[2]}, t_par={r[3]}, j_par={r[4]}")
                            if total_refuters > 5:
                                break
                if total_refuters > 5:
                    break
            queue = next_queue
            if total_refuters > 5:
                break
        if total_refuters > 5:
            break

    for seed in seeds:
        rs = check_chain_through_Bn0(seed, max_n=3)
        tested += 1
        if rs:
            refuters_all.append((seed, rs))
            total_refuters += len(rs)
            print(f"\n  SEED REFUTER on {seed}")
            for r in rs[:3]:
                print(f"    n={r[0]}, k={r[1]}, i={r[2]}, t_par={r[3]}, j_par={r[4]}")

    print(f"\n=== TOTAL: tested {tested} BMSs, {total_refuters} configurations where lemma premises hold ===")
    if total_refuters == 0:
        print("CLAIM HOLDS empirically: premise combination is unsatisfiable -> lemma vacuously true.")
    else:
        print("CLAIM REFUTED empirically: premise combination is realizable with intermediate B_t parent.")


if __name__ == '__main__':
    main()
