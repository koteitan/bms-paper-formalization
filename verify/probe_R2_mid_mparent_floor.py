"""INTERVAL-ANC proof strategy: strong induction on q in (s', sA) via m_parent.
For q in (s', sA), level m in (0, t''], let p = m_parent A m q.
  - if p exists and p >= s': induction closes (s' dom p by IH, p dom q by m_parent_elem_lt).
  - if p exists and p < s': OBSTRUCTION 1.
  - if p = None: OBSTRUCTION 2.
Tally: how often p>=s' (Some), p<s' (Some, BAD), None (BAD).
s' = m_parent A (Suc t'') sA in R2 (l1 A=1).  m in [1, t''] (= [1, tp-1], tp=mpl(A[n])).
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
cls = collections.Counter()
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
                # tp = mpl(A[n]) = Suc t'', so t'' = tp-1; m in [1, t'']
                for q in range(sp+1, sA):
                    for m in range(1, tp):       # 0 < m <= t'' = tp-1
                        if m >= len(A[q]): continue
                        p = m_parent(A, m, q)
                        if p is None:
                            cls['None'] += 1
                            if len(ex) < 12: ex.append(('None', fmt(A), 'sp', sp, 'sA', sA, 'q', q, 'm', m, 'tp', tp))
                        elif p >= sp:
                            cls['p>=s'] += 1
                        else:
                            cls['p<s(BAD)'] += 1
                            if len(ex) < 12: ex.append(('p<s', fmt(A), 'sp', sp, 'sA', sA, 'q', q, 'm', m, 'p', p, 'tp', tp))
        for n in range(1, 3):
            if len(A) > 34: continue
            E = expand(fmt(A), n)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} R2={R2} cls={dict(cls)}", flush=True)
    if len(seen) > CAP: break
print(f"\n=== R2 mid-column m_parent floor test (l1 A=1, R2={R2}) ===")
print(f"m_parent A m q classification (q in (s',sA), 0<m<=t''): {dict(cls)}")
for e in ex: print("  ex:", e)
