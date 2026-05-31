"""For the adjacent_value_monotone expand case: A[n] (E) expands predecessor A.
The B-region columns of E are bumped copies; their bump is active only when
ascends A c_off m (i.e. m < t_A = mpl A). The goal range is m < t'-1
(t' = mpl E). So we need m < t'-1  ==>  m < t_A, i.e.  t' - 1 <= t_A,
i.e. mpl(E) <= mpl(A) + 1.

Probe over genuine 2-row-seed BMS: for predecessor A and E=A[n] (design regime
l1(E)>=2, mpl(E)>=1), tally whether mpl(E) <= mpl(A)+1, and the distribution of
mpl(E)-mpl(A). If mpl(E) <= mpl(A)+1 always, the cross-block bump argument is
valid on the whole goal range.
"""
import sys, collections
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)

seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 9)]
seen = set(); Q = []
for sd in seeds:
    A = strip(parse(sd)); kk = fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP = 8000; depth = 13
diff = collections.Counter()
viol = 0; tot = 0
exv = []
for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); tA = mpl(A)
        if tA is not None and len(A) <= 44:
            for n in range(1, 4):
                E = expand(fmt(A), n)
                if E is None: continue
                set_array(E); tE = mpl(E); lE = l1(E)
                set_array(A)
                if tE is None: continue
                if not (lE >= 2 and tE >= 1): continue
                tot += 1
                diff[tE - tA] += 1
                if tE > tA + 1:
                    viol += 1
                    if len(exv) < 10: exv.append((fmt(A), 'n', n, 'tA', tA, 'tE', tE))
        for nn in range(1, 3):
            if len(A) > 38: continue
            E = expand(fmt(A), nn)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} tot={tot} viol(tE>tA+1)={viol} diff={dict(sorted(diff.items()))}", flush=True)
    if len(seen) > CAP: break
print(f"\n=== mpl(E) vs mpl(A)+1 (E=A[n] design regime) ===")
print(f"total={tot}, violations (mpl(E) > mpl(A)+1) = {viol}")
print(f"distribution mpl(E)-mpl(A): {dict(sorted(diff.items()))}")
for e in exv: print("  VIOL:", e)
