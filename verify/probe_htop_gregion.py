"""Htop (top-level leaf) reachability + truth probe.

ancestor_monotone_expand's leaf obligation `Htop` fires exactly when
  l1(A) = 1  and  m = tA - 1  and  m < tE - 1   (i.e. tE > tA).
There the obligation is, for E = A[n], m = tA-1:
  forall q (q==sE or m_anc(E,m,sE,q)) -> forall c in (q, CE]:
      elem(E, c-1, m) < elem(E, c, m).

Split each reachable (q,c) by location:
  - B-region  (c >  l0 A):  covered by the proven lemma b_region_adj_increase_l1_eq_1
  - G-region  (c <= l0 A):  the OPEN residual (A's G-prefix monotone at level tA-1)

We report:
  greg_reached : how many (q,c) land in the G-region (is it vacuous?)
  greg_viol    : G-region obligation failures (should be 0 if the residual is TRUE)
  breg_viol    : B-region failures (sanity: must be 0, the lemma is proven)
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent,
                                          mpl, b0, l1, set_array, expand)

def ancestors_of(A, m, i):
    out = []; p = m_parent(A, m, i); seen = set()
    while p is not None:
        if p in seen: break
        seen.add(p); out.append(p); p = m_parent(A, m, p)
    return out

seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 9)]
seen = set(); Q = []
for sd in seeds:
    A = strip(parse(sd)); kk = fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP = 9000; depth = 14

leaf_cases = 0          # how many (A,n) trigger the leaf (l1=1, tE>tA)
greg_reached = 0; greg_viol = 0; greg_ex = []
breg_reached = 0; breg_viol = 0; breg_ex = []

for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); s = b0(A); t = mpl(A)
        if s is None or t is None or t < 1 or l1(A) != 1 or len(A) > 44:
            pass
        else:
            l0A = s
            for n in range(1, 5):
                E = expand(fmt(A), n)
                if E is None: continue
                set_array(E); sE = b0(E); tE = mpl(E)
                if sE is None or tE is None:
                    set_array(A); continue
                if tE <= t:
                    set_array(A); continue   # leaf does not fire
                m = t - 1                    # the leaf level
                if not (m < tE - 1):
                    set_array(A); continue
                leaf_cases += 1
                CE = len(E) - 1
                qs = [sE] + ancestors_of(E, m, sE)
                for q in qs:
                    for c in range(q+1, CE+1):
                        ok = (elem(E, c-1, m) < elem(E, c, m))
                        if c <= l0A:
                            greg_reached += 1
                            if not ok:
                                greg_viol += 1
                                if len(greg_ex) < 8:
                                    greg_ex.append((fmt(A),'n',n,'m',m,'q',q,'c',c,'sE',sE,'l0',l0A,'tE',tE))
                        else:
                            breg_reached += 1
                            if not ok:
                                breg_viol += 1
                                if len(breg_ex) < 8:
                                    breg_ex.append((fmt(A),'n',n,'m',m,'q',q,'c',c))
                set_array(A)
        # frontier growth
        for nn in range(1, 3):
            if len(A) > 38: continue
            E = expand(fmt(A), nn)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} leaf={leaf_cases} greg={greg_reached}/{greg_viol} breg={breg_reached}/{breg_viol}", flush=True)
    if len(seen) > CAP: break

print("\n=== RESULTS ===")
print(f"leaf cases (l1A=1, tE>tA, m=tA-1<tE-1): {leaf_cases}")
print(f"G-region reached {greg_reached}, violations {greg_viol}")
for e in greg_ex: print("   GREG-VIOL:", e)
print(f"B-region reached {breg_reached}, violations {breg_viol}  (must be 0; lemma proven)")
for e in breg_ex: print("   BREG-VIOL:", e)
