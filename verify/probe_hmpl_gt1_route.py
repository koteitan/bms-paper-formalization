"""Hmpl_gt1 proof route: is no-parent@tA+1 (l1>1, in-bounds) a VALUE fact or ANCESTRY fact?

For genuine BMS A, l1(A)>1, E=A[n], height(E)=tA+2 (so row tA+1 in-bounds), C=last col:
  Among p<C, count those with elem(E,p,tA+1) < elem(E,C,tA+1)  [value-smaller candidates].
  - If ZERO value-smaller columns exist  -> pure VALUE argument (no candidate at all).
  - If some exist but parent is None      -> the tA-ancestor GUARD kills them.
Report the distribution of (#value-smaller) when parent@tA+1 is None.
Also: is elem(E,C,tA+1) itself 0? (if 0, nothing is strictly below -> value-trivial.)
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent, mpl, b0, l1, set_array, expand)

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=9000; depth=13

nval=collections.Counter(); cval0=collections.Counter()

for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); sA=b0(A); tA=mpl(A)
        if sA is not None and tA is not None and l1(A)>1 and len(A)<=44:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E); sE=b0(E); tE=mpl(E)
                if sE is None or tE is None:
                    set_array(A); continue
                H=len(E[0]) if len(E)>0 else 0
                if H!=tA+2:
                    set_array(A); continue
                C=len(E)-1
                m=tA+1
                vC=elem(E,C,m)
                cnt=sum(1 for p in range(C) if elem(E,p,m)<vC)
                nval[cnt]+=1
                cval0['C=0' if vC==0 else 'C>0']+=1
                set_array(A)
        for nn in range(1,3):
            if len(A)>38: continue
            E=expand(fmt(A),nn)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    if len(seen)>CAP: break

print("l1>1, H=tA+2: #(value-smaller cols below C at row tA+1) :", dict(sorted(nval.items())))
print("l1>1, H=tA+2: elem(E,C,tA+1) zero? :", dict(cval0))
