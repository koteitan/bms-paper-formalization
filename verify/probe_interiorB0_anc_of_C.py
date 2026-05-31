"""Target lemma for closing elem_lt_below_t off-chain:
For A in BMS (genuine), s=b0_start A, t=mpl A, C=last_col_idx A, interior B0
column s+j (0<j<l1 A), level m': is  m_ancestor A m' C (s+j)  (s+j is an
m'-ancestor of C)?  If 0 violations, the off-chain (NOT m'-ancestor of C)
branch of elem_lt_below_t is unreachable -> closed vacuously.

Probe over genuine 2-row-seed BMS arrays. Tally violations for:
  (a) m' in [0, t-1)   (= the m'=m-1 range arising in elem_lt_below_t, m<t)
  (b) m' in [0, t)     (full sub-mpl range)
Also record, when it IS an ancestor, whether s+j is on C's m'-parent chain
to see the chain structure.
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
nBMS = 0
viol_a = 0; chk_a = 0   # m' in [0, t-1)
viol_b = 0; chk_b = 0   # m' in [0, t)
ex_a = []
for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); s = b0(A); t = mpl(A); lA = l1(A)
        if s is not None and t is not None and t >= 2 and lA >= 2 and len(A) <= 44:
            nBMS += 1
            C = len(A) - 1
            for j in range(1, lA):
                sj = s + j
                if sj >= C: break
                for mp_ in range(0, t):
                    if mp_ >= len(A[C]) or mp_ >= len(A[sj]): continue
                    anc = m_anc(A, mp_, C, sj)
                    chk_b += 1
                    if not anc: viol_b += 1
                    if mp_ < t - 1:
                        chk_a += 1
                        if not anc:
                            viol_a += 1
                            if len(ex_a) < 12:
                                ex_a.append((fmt(A), 's', s, 't', t, 'j', j, "m'", mp_))
        for n in range(1, 3):
            if len(A) > 38: continue
            E = expand(fmt(A), n)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} BMS={nBMS} viol_a={viol_a}/{chk_a} viol_b={viol_b}/{chk_b}", flush=True)
    if len(seen) > CAP: break
print(f"\n=== interior B0 col is m'-ancestor of C (genuine BMS, t>=2, l1>=2) ===")
print(f"(a) m' in [0,t-1): {viol_a} viol / {chk_a} checks")
print(f"(b) m' in [0,t):   {viol_b} viol / {chk_b} checks")
for e in ex_a: print("  VIOL(a):", e)
