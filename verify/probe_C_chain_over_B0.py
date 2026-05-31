"""Find the proof idea for interior_B0_anc_of_C: for A in BMS (t>=2,l1>=2),
level m' < t-1, what is m_parent A m' c for c in (s, C] ?
Classify the parent location to reveal the chain shape over B0:
  - c-1 (consecutive / onestep)
  - == s (jumps to bad root)
  - other in (s, c-1)
  - < s (into G) / None
If consecutive dominates, interior_B0_anc_of_C follows by transitivity of the
C-down chain. Also directly check: is m_parent A m' C always in B0 (>s)?
"""
import sys, collections
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)

seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 9)]
seen = set(); Q = []
for sd in seeds:
    A = strip(parse(sd)); kk = fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP = 7000; depth = 12
cls = collections.Counter()
nBMS = 0
for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); s = b0(A); t = mpl(A); lA = l1(A)
        if s is not None and t is not None and t >= 2 and lA >= 2 and len(A) <= 42:
            nBMS += 1
            C = len(A) - 1
            for c in range(s+1, C+1):          # B0 interior columns and C
                for mp_ in range(0, t-1):      # m' < t-1
                    if mp_ >= len(A[c]): continue
                    p = m_parent(A, mp_, c)
                    if p is None: cls['None'] += 1
                    elif p == c-1: cls['c-1(consec)'] += 1
                    elif p == s: cls['==s'] += 1
                    elif p > s: cls['other in(s,c-1)'] += 1
                    else: cls['<s(G)'] += 1
        for n in range(1, 3):
            if len(A) > 36: continue
            E = expand(fmt(A), n)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} BMS={nBMS} {dict(cls)}", flush=True)
    if len(seen) > CAP: break
print(f"\n=== m_parent A m' c for c in (s,C], m'<t-1 (genuine BMS) ===")
tot = sum(cls.values())
for k,v in cls.most_common(): print(f"  {k}: {v}  ({100*v/tot:.1f}%)")
