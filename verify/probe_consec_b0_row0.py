"""Is the B0 row-0 consecutiveness crux `consec` true for all A in BMS?

  consec(A):  s=b0_start A.  forall 0<=j<=l1 A:  elem A (s+j) 0 = elem A s 0 + j
This is the hypothesis of chainlen0_bumped_tiling / consec_run_expansion_row0;
discharging it unblocks the expansion row-0 invariant.  Test on genuine BMS.

Also test the weaker/related `no_skip`:  on [s, s+l1], row-0 has no repeats and
increases by exactly 1 each step.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, mpl, b0, l1, set_array, expand)

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=14000; depth=15

C_chk=0;C_viol=0;C_ex=[]

for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); s=b0(A)
        if s is not None and len(A)<=48:
            L=l1(A); base=elem(A,s,0)
            for j in range(0, L+1):
                if s+j >= len(A): break
                C_chk+=1
                if elem(A,s+j,0) != base + j:
                    C_viol+=1
                    if len(C_ex)<12:
                        C_ex.append((fmt(A),'s',s,'l1',L,'j',j,'got',elem(A,s+j,0),'want',base+j))
        for nn in range(1,3):
            if len(A)>42: continue
            E=expand(fmt(A),nn)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} consec={C_chk}/{C_viol}", flush=True)
    if len(seen)>CAP: break

print("\n=== RESULTS ===")
print(f"consec (B0 row-0 = s + j on [s, s+l1]): checked {C_chk}, violations {C_viol}")
for e in C_ex: print("   CONSEC-VIOL:", e)
