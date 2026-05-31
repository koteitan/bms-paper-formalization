"""Lean gate: full ancestry-restriction lemma + basic ancestor_monotone, unbuffered."""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent,
                                          mpl, b0, l1, set_array, expand)

def ancs(A, m, i):
    out = []; p = m_parent(A, m, i); seen = set()
    while p is not None:
        if p in seen: break
        seen.add(p); out.append(p); p = m_parent(A, m, p)
    return out

seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 8)]
seen = set(); Q = []
for sd in seeds:
    A = strip(parse(sd)); kk = fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP = 1400; depth = 9
inv_c = inv_v = ar_c = ar_v = 0; ar_ex = []; inv_ex = []
for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); s = b0(A); t = mpl(A)
        if s is not None and t is not None and t >= 2 and len(A) <= 36:
            C = len(A) - 1
            for m in range(0, t-1):
                for q in [s] + ancs(A, m, s):
                    for c in range(q+1, C+1):
                        inv_c += 1
                        if not (elem(A, c-1, m) < elem(A, c, m)):
                            inv_v += 1
                            if len(inv_ex) < 5: inv_ex.append((fmt(A), m, q, c))
        l0A = s
        for n in range(1, 4):
            E = expand(fmt(A), n)
            if E is None: continue
            set_array(E); sE = b0(E); tE = mpl(E)
            if sE is not None and tE is not None and tE >= 1 and l0A is not None and sE < l0A:
                for m in range(0, max(tE-1, 0)):
                    for qp in ancs(E, m, sE):
                        if qp < l0A:
                            ar_c += 1
                            set_array(A); ok = (qp == s or m_anc(A, m, s, qp)); set_array(E)
                            if not ok:
                                ar_v += 1
                                if len(ar_ex) < 8: ar_ex.append((fmt(A), 'n', n, 'm', m, 'sE', sE, 'qp', qp, 's', s))
                set_array(A)
        for nn in range(1, 3):
            if len(A) > 32: continue
            E = expand(fmt(A), nn)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} inv={inv_c}/{inv_v} ar={ar_c}/{ar_v}", flush=True)
    if len(seen) > CAP: break
print("=== DONE ===")
print(f"basic ancestor_monotone: {inv_c} checked, {inv_v} viol")
for e in inv_ex: print("  INV-VIOL", e)
print(f"ancestry-restriction FULL: {ar_c} checked, {ar_v} viol")
for e in ar_ex: print("  AR-VIOL", e)
