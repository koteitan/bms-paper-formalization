"""Is A's G-prefix strictly monotone at the top level t-1 (and all 1<=m<t)?

Pure statement about A in BMS (no expansion):
  s = b0_start A, t = mpl A.
  (U) unrestricted G-prefix at top level:  forall 0<c<=s: elem A (c-1)(t-1) < elem A c (t-1)
  (M) all mid levels 1<=m<=t-1:            forall 0<c<=s: elem A (c-1) m     < elem A c m
  (M0) include level 0:                    forall 0<c<=s: elem A (c-1) 0      < elem A c 0
Also record where the G-prefix value plateaus/decreases, to see the true boundary.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, mpl, b0, l1, set_array, expand)

seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 9)]
seen = set(); Q = []
for sd in seeds:
    A = strip(parse(sd)); kk = fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP = 12000; depth = 15

U_chk=0; U_viol=0; U_ex=[]
M_chk=0; M_viol=0; M_ex=[]
M0_chk=0; M0_viol=0; M0_ex=[]

for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); s=b0(A); t=mpl(A)
        if s is not None and t is not None and t>=1 and s>=1 and len(A)<=46:
            # (U) top level
            mtop=t-1
            for c in range(1, s+1):
                U_chk+=1
                if not (elem(A,c-1,mtop) < elem(A,c,mtop)):
                    U_viol+=1
                    if len(U_ex)<8: U_ex.append((fmt(A),'s',s,'t',t,'m',mtop,'c',c))
            # (M) all 1<=m<=t-1
            for m in range(1, t):
                for c in range(1, s+1):
                    M_chk+=1
                    if not (elem(A,c-1,m) < elem(A,c,m)):
                        M_viol+=1
                        if len(M_ex)<8: M_ex.append((fmt(A),'s',s,'t',t,'m',m,'c',c))
            # (M0) level 0
            for c in range(1, s+1):
                M0_chk+=1
                if not (elem(A,c-1,0) < elem(A,c,0)):
                    M0_viol+=1
                    if len(M0_ex)<8: M0_ex.append((fmt(A),'s',s,'t',t,'c',c))
        for nn in range(1,3):
            if len(A)>40: continue
            E=expand(fmt(A),nn)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} U={U_chk}/{U_viol} M={M_chk}/{M_viol} M0={M0_chk}/{M0_viol}", flush=True)
    if len(seen)>CAP: break

print("\n=== RESULTS ===")
print(f"(U) top-level t-1, 0<c<=s:  checked {U_chk}, violations {U_viol}")
for e in U_ex: print("   U-VIOL:", e)
print(f"(M) all 1<=m<=t-1:          checked {M_chk}, violations {M_viol}")
for e in M_ex: print("   M-VIOL:", e)
print(f"(M0) level 0:               checked {M0_chk}, violations {M0_viol}")
for e in M0_ex: print("   M0-VIOL:", e)
