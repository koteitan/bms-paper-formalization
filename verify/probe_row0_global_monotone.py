"""Is row-0 (level 0) GLOBALLY strictly increasing over adjacent columns for
genuine BMS?  elem A (c-1) 0 < elem A c 0 for ALL 1 <= c < Lng A.
If globally true (0 viol), it's a clean global invariant -> BMS.induct without
region-mismatch, and is the base case for adjacent_value_monotone at m'=0.
Also check the (s, C] restriction separately, and whether higher rows m' are
globally monotone (to see if a global statement holds at all levels, or only
the (s,C] / m'<t-1 restriction).
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
g0_lt=0; g0_bad=0          # global row0 over all adjacent cols
ex0=[]
gm_bad=collections.Counter()   # global row-m strict-incr violations by m (m>=1)
gm_chk=collections.Counter()
nBMS=0
for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); s=b0(A); t=mpl(A);
        if len(A)>=2 and len(A)<=44:
            nBMS+=1
            L=len(A)
            for c in range(1, L):
                # row 0 global
                if len(A[c])>0 and len(A[c-1])>0:
                    a=elem(A,c-1,0); b=elem(A,c,0)
                    if a<b: g0_lt+=1
                    else:
                        g0_bad+=1
                        if len(ex0)<10: ex0.append((fmt(A),'c',c,'a',a,'b',b))
                # higher rows global (m=1..3)
                for m in range(1,4):
                    if m<len(A[c]) and m<len(A[c-1]):
                        gm_chk[m]+=1
                        if not (elem(A,c-1,m)<elem(A,c,m)): gm_bad[m]+=1
        for n in range(1,3):
            if len(A)>38: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} BMS={nBMS} g0_bad={g0_bad}/{g0_lt+g0_bad} gm_bad={dict(gm_bad)}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== GLOBAL adjacent monotonicity (genuine BMS) ===")
print(f"row 0: {g0_bad} viol / {g0_lt+g0_bad}")
print(f"row m>=1 violations: {dict(gm_bad)} / checks {dict(gm_chk)}")
for e in ex0: print("  ROW0-BAD:",e)
