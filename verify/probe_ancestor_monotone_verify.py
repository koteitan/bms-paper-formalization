"""Independent trust-but-verify of the workflow's chosen invariant `ancestor_monotone`
and its self-transfer's missing lemma (ancestry-restriction-to-G-prefix), in FULL
(not just the q'=s' base instance the workflow probed).

ancestor_monotone(A) := for s=b0_start, t=mpl, C=last_col_idx:
   ∀ m<t-1. ∀ q. (q==s ∨ m_anc A m s q) → ∀ c∈(q,C]: elem A (c-1) m < elem A c m

Ancestry-restriction lemma (the formal residual, tested in FULL here):
   for E=A[n], s'=b0_start E, q'<l0 A (G-block) with m_anc E m s' q'  (any chain depth)
       ⟹ m_anc A m s q'   (q' is also an m-ancestor of A's OWN bad root s)
Also test the localization premise that underlies it:
   m_parent E m q' == m_parent A m q'   for q' in the G-block (q' < l0 A).
"""
import sys, collections
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent,
                                          mpl, b0, l1, set_array, expand)

def ancestors_of(A, m, i):
    """all q with m_anc A m i q (the full ancestor chain of i at level m)."""
    out = []
    p = m_parent(A, m, i); seen = set()
    while p is not None:
        if p in seen: break
        seen.add(p); out.append(p)
        p = m_parent(A, m, p)
    return out

seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 9)]
seen = set(); Q = []
for sd in seeds:
    A = strip(parse(sd)); kk = fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP = 7000; depth = 13

# (1) basic invariant
inv_chk = 0; inv_viol = 0; inv_ex = []
# (2) ancestry-restriction lemma in FULL
ar_chk = 0; ar_viol = 0; ar_ex = []
# (3) m_parent localization to G-prefix
loc_chk = 0; loc_viol = 0; loc_ex = []

for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); s = b0(A); t = mpl(A)
        if s is not None and t is not None and t >= 2 and len(A) <= 40:
            C = len(A) - 1
            # (1) basic ancestor_monotone
            for m in range(0, t-1):
                qs = [s] + ancestors_of(A, m, s)
                for q in qs:
                    for c in range(q+1, C+1):
                        inv_chk += 1
                        if not (elem(A, c-1, m) < elem(A, c, m)):
                            inv_viol += 1
                            if len(inv_ex) < 6:
                                inv_ex.append((fmt(A), 'm', m, 'q', q, 'c', c))
        # expansions: test ancestry-restriction + localization
        l0A = s if s is not None else None
        for n in range(1, 4):
            E = expand(fmt(A), n)
            if E is None: continue
            set_array(E); sE = b0(E); tE = mpl(E)
            if sE is not None and tE is not None and tE >= 1 and l0A is not None:
                # only meaningful when E reaches into A's G-block (R2-flavored): sE < l0A
                for m in range(0, max(tE-1, 0)):
                    qs = ancestors_of(E, m, sE)  # full chain of ancestors of s' in E
                    for qp in qs:
                        if qp < l0A:   # G-block ancestor
                            ar_chk += 1
                            set_array(A)
                            ok = (m_anc(A, m, s, qp) or qp == s)
                            set_array(E)
                            if not ok:
                                ar_viol += 1
                                if len(ar_ex) < 8:
                                    ar_ex.append((fmt(A), 'n', n, 'm', m, 'sE', sE, 'qp', qp, 's', s))
                # (3) localization: m_parent E m q' == m_parent A m q' for q'<l0A
                for m in range(0, max(tE, 1)):
                    for qp in range(1, l0A):
                        set_array(E); pE = m_parent(E, m, qp)
                        set_array(A); pA = m_parent(A, m, qp)
                        loc_chk += 1
                        if pE != pA:
                            loc_viol += 1
                            if len(loc_ex) < 8:
                                loc_ex.append((fmt(A), 'n', n, 'm', m, 'qp', qp, 'pE', pE, 'pA', pA))
                set_array(A)
        for nn in range(1, 3):
            if len(A) > 34: continue
            E = expand(fmt(A), nn)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} inv={inv_chk}/{inv_viol} ar={ar_chk}/{ar_viol} loc={loc_chk}/{loc_viol}", flush=True)
    if len(seen) > CAP: break

print("\n=== RESULTS ===")
print(f"(1) ancestor_monotone basic:  checked {inv_chk}, violations {inv_viol}")
for e in inv_ex: print("   INV-VIOL:", e)
print(f"(2) ancestry-restriction (FULL chain, G-block q' of s' => m_anc A m s q'): checked {ar_chk}, violations {ar_viol}")
for e in ar_ex: print("   AR-VIOL:", e)
print(f"(3) m_parent localization to G-prefix (E vs A for q'<l0A): checked {loc_chk}, violations {loc_viol}")
for e in loc_ex: print("   LOC-VIOL:", e)
