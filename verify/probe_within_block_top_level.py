"""R1 within-block at the subtle top level. For E=A[n] (design regime), the
within-block adjacent pair in E is idx_B(A,blk,off-1), idx_B(A,blk,off). Their
E-values bump by (ascends A (off-1) m ? blk*d : 0) and (ascends A off m ? blk*d : 0)
over base (A!(s+off-1))!m and (A!(s+off))!m.  When the BASE plateaus
(elem A (s+off-1) m == elem A (s+off) m) the strict increase in E must come from
DIFFERENTIAL ascend (off ascends, off-1 doesn't).  Probe at the critical level
m = t_A - 1 (only reachable in goal range when mpl(E)=t_A+1):
  count within-block adjacent (blk>=1, 1<=off<l1A) cases where base plateaus,
  and among those whether E strictly increases AND ascends differ.
"""
import sys, collections
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)

def ascends_base(A, off, m, sA, tA):
    # ascends A off m  <->  m<tA and (off==0 or m_anc A m (sA+off) sA)
    if m >= tA: return False
    if off == 0: return True
    return m_anc(A, m, sA+off, sA)

seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 9)]
seen = set(); Q = []
for sd in seeds:
    A = strip(parse(sd)); kk = fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP = 7000; depth = 12
wb_tot=0; base_plateau=0; plateau_E_strict=0; plateau_diff_asc=0; plateau_E_notstrict=0
exbad=[]
for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); sA=b0(A); tA=mpl(A); lA=l1(A)
        if sA is not None and tA is not None and tA>=1 and lA>=1 and len(A)<=40:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E); tE=mpl(E); lE=l1(E); sE=b0(E)
                lenE=len(E)
                set_array(A)
                if tE is None or sE is None: continue
                if not (lE>=2 and tE>=1): continue
                if tE != tA+1: continue   # diff=1 only
                m = tA - 1
                if m < 0: continue
                # within-block pairs: blk in 1..n, off in 1..lA-1
                l0A = sA
                for blk in range(1, n+1):
                    for off in range(1, lA):
                        i_prev = l0A + blk*lA + (off-1)
                        i_cur  = l0A + blk*lA + off
                        if i_cur >= lenE: continue
                        if m>=len(E[i_prev]) or m>=len(E[i_cur]): continue
                        # only count if both in E's B0' region (sE < i_prev)
                        if not (sE < i_prev): continue
                        wb_tot+=1
                        # base values
                        if m>=len(A[sA+off-1]) or m>=len(A[sA+off]): continue
                        bp = elem(A,sA+off-1,m); bc = elem(A,sA+off,m)
                        if bp == bc:
                            base_plateau+=1
                            Estrict = elem(E,i_prev,m) < elem(E,i_cur,m)
                            ap = ascends_base(A,off-1,m,sA,tA); ac = ascends_base(A,off,m,sA,tA)
                            if Estrict: plateau_E_strict+=1
                            else:
                                plateau_E_notstrict+=1
                                if len(exbad)<8: exbad.append((fmt(A),'n',n,'blk',blk,'off',off,'m',m))
                            if ap!=ac: plateau_diff_asc+=1
        for nn in range(1,3):
            if len(A)>34: continue
            E=expand(fmt(A),nn)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} wb={wb_tot} base_plateau={base_plateau} E_strict={plateau_E_strict} E_notstrict={plateau_E_notstrict} diff_asc={plateau_diff_asc}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== within-block at m=t_A-1 (diff=1) ===")
print(f"within-block pairs: {wb_tot}, base plateau: {base_plateau}")
print(f"  of plateau: E strict-incr: {plateau_E_strict}, E NOT strict: {plateau_E_notstrict}, ascends differ: {plateau_diff_asc}")
for e in exbad: print("  E-NOT-STRICT (would violate!):", e)
