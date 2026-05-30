"""Strategy test for m>0 G-prefix domination in R2 (l1 A=1):
If every mid column p in (s', sA) is an m-ancestor of sA at level m (m<t'),
then m_ancestor_chain_linear (two m-ancestors of sA are linearly ordered) plus
's' is m-ancestor of sA' yields 's' is m-ancestor of p' (since s'<p rules out
the other branch), hence elem A s' m < elem A p m via m_ancestor_elem_lt.

Probe: for p in (s',sA), m in [0,t'): does m_anc A m sA p hold?
Also need s' is m-anc of sA at the SAME m: m_anc A m sA s'.
Tally violations of each; also the conjunction needed for chain_linear.
"""
import sys, collections
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)

seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 9)]
seen = set(); Q = []
for sd in seeds:
    A = strip(parse(sd)); kk = fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP = 8000; depth = 12
R2 = 0
mid_anc_sA = collections.Counter()      # p is m-anc of sA?
sp_anc_sA_m = collections.Counter()     # s' is m-anc of sA at level m?
both = collections.Counter()            # both hold (chain_linear applicable)
ex = []
for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); sA = b0(A); lA = l1(A); l0A = sA; tA = mpl(A)
        if sA is not None and tA is not None and lA >= 1 and len(A) <= 40:
            for n in range(1, 4):
                E = expand(fmt(A), n)
                if E is None: continue
                set_array(E); sp = b0(E); tp = mpl(E); lp = l1(E)
                set_array(A)
                if sp is None or tp is None: continue
                if not (lp >= 2 and tp >= 1 and sp < l0A and lA == 1): continue
                R2 += 1
                for p in range(sp+1, sA):
                    for m in range(1, tp):
                        if m >= len(A[sp]) or m >= len(A[p]) or m >= len(A[sA]): continue
                        a_p = m_anc(A, m, sA, p)     # p anc of sA
                        a_s = m_anc(A, m, sA, sp)    # s' anc of sA at level m
                        mid_anc_sA[a_p] += 1
                        sp_anc_sA_m[a_s] += 1
                        both[(a_p and a_s)] += 1
                        if not a_p and len(ex) < 12:
                            ex.append((fmt(A), 'sp', sp, 'sA', sA, 'p', p, 'm', m, 'tp', tp,
                                       'p_anc_sA', a_p, 's_anc_sA', a_s,
                                       's_anc_p', m_anc(A, m, p, sp)))
        for n in range(1, 3):
            if len(A) > 34: continue
            E = expand(fmt(A), n)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} R2={R2} mid_anc_sA={dict(mid_anc_sA)} s_anc_sA={dict(sp_anc_sA_m)}", flush=True)
    if len(seen) > CAP: break
print(f"\n=== R2 chain_linear strategy test (l1 A=1, R2={R2}) ===")
print(f"mid p is m-anc of sA: {dict(mid_anc_sA)}")
print(f"s' is m-anc of sA (same m): {dict(sp_anc_sA_m)}")
print(f"both hold (chain_linear applicable): {dict(both)}")
for e in ex: print("  mid-NOT-anc-sA:", e)
