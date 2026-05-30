"""G-prefix domination proof route: s'=m_parent A (mpl(A[n])) sA in R2 (l1 A=1).
For mid columns p in (s', sA):
  (Q1) is s' an m-ancestor of p in A?  m_anc A m p s'  (for m<t'=mpl(A[n]))
       -> if yes uniformly, m_ancestor_elem_lt gives s' dominates p directly.
  (Q2) failing that, is p an m-ancestor of sA? (p on the chain above s'?)
Also confirm s' is t'-ancestor of sA: m_anc A t' sA s'.
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
sp_anc_p = collections.Counter()
p_anc_sA = collections.Counter()
sp_anc_sA = collections.Counter()
midchecks = 0
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
                sp_anc_sA[m_anc(A, tp, sA, sp)] += 1
                for p in range(sp+1, sA):
                    for m in range(0, tp):
                        if m >= len(A[sp]) or m >= len(A[p]): continue
                        midchecks += 1
                        a1 = m_anc(A, m, p, sp)
                        sp_anc_p[a1] += 1
                        if not a1:
                            p_anc_sA[m_anc(A, m, sA, p)] += 1
                            if len(ex) < 10:
                                ex.append((fmt(A), 'sp', sp, 'sA', sA, 'p', p, 'm', m, 'tp', tp,
                                           'dom', elem(A, sp, m) < elem(A, p, m)))
        for n in range(1, 3):
            if len(A) > 34: continue
            E = expand(fmt(A), n)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} R2={R2} mid={midchecks} sp_anc_p={dict(sp_anc_p)}", flush=True)
    if len(seen) > CAP: break
print(f"\n=== R2 mid-column structure (l1 A=1, R2={R2}, midchecks={midchecks}) ===")
print(f"s' is m-anc of mid p [m_anc A m p s']: {dict(sp_anc_p)}")
print(f"  (when NOT) p is m-anc of sA: {dict(p_anc_sA)}")
print(f"s' is tp-anc of sA [m_anc A tp sA s']: {dict(sp_anc_sA)}")
for e in ex: print("  NONanc-ex:", e)
