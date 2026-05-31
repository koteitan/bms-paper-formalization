"""Key sub-fact for consecutive-parent (=> interior_B0_anc_of_C => off-chain closed):
value monotonicity of ADJACENT columns over B0 at sub-(t-1) levels.
For A in BMS (t>=2, l1>=2), c in (s, C], m' < t-1:
   is  elem A (c-1) m' < elem A c m'  ?
This is a direct value comparison (no ancestry) -> potentially non-circular.
Also probe m'=t-1 separately (where consecutive-parent failed) to see if
monotonicity also fails there (consistency check), and the full m'<t range.
Reconcile with the old 'plateau-refuted' note: check where plateaus occur.
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
v_lt = 0; v_eq = 0; v_gt = 0; chk = 0          # m' < t-1
top_lt = 0; top_eq = 0; top_gt = 0             # m' == t-1
ex_bad = []
for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); s = b0(A); t = mpl(A); lA = l1(A)
        if s is not None and t is not None and t >= 2 and lA >= 2 and len(A) <= 42:
            C = len(A) - 1
            for c in range(s+1, C+1):
                for mp_ in range(0, t):
                    if mp_ >= len(A[c]) or mp_ >= len(A[c-1]): continue
                    a = elem(A, c-1, mp_); b = elem(A, c, mp_)
                    if mp_ < t-1:
                        chk += 1
                        if a < b: v_lt += 1
                        elif a == b:
                            v_eq += 1
                            if len(ex_bad) < 10: ex_bad.append(('EQ', fmt(A), 'c', c, "m'", mp_, 't', t, 'a', a, 'b', b))
                        else:
                            v_gt += 1
                            if len(ex_bad) < 10: ex_bad.append(('GT', fmt(A), 'c', c, "m'", mp_, 't', t, 'a', a, 'b', b))
                    elif mp_ == t-1:
                        if a < b: top_lt += 1
                        elif a == b: top_eq += 1
                        else: top_gt += 1
        for n in range(1, 3):
            if len(A) > 36: continue
            E = expand(fmt(A), n)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    print(f"d{d}: vis={len(seen)} m'<t-1: lt={v_lt} eq={v_eq} gt={v_gt} | m'=t-1: lt={top_lt} eq={top_eq} gt={top_gt}", flush=True)
    if len(seen) > CAP: break
print(f"\n=== adjacent value monotonicity elem A (c-1) m' < elem A c m', c in (s,C] ===")
print(f"m' < t-1 : lt={v_lt} eq={v_eq} gt={v_gt}  (total {chk})  -> violations(eq+gt)={v_eq+v_gt}")
print(f"m' = t-1 : lt={top_lt} eq={top_eq} gt={top_gt}")
for e in ex_bad: print("  BAD:", e)
