"""Pin down the real route for the mpl upper bound (gate 2).

For genuine BMS A and E=A[n]:
  tA = mpl(A), tE = mpl(E), keep = height(E), l1=l1(A).
Record:
  (1) tE - tA distribution, split by l1==1 vs l1>1  (claim: tE<=tA+1; l1>1 => tE<=tA)
  (2) keep - tA  (is height(E) a tight bound? i.e. is keep small?)
  (3) does the LAST column of E have a parent at level tA+1 / tA+2? (the no-parent target)
"""
import sys, collections
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent, mpl, b0, l1, set_array, expand)

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=9000; depth=13

diff_l1eq1=collections.Counter(); diff_l1gt1=collections.Counter()
keepdiff=collections.Counter()
# no-parent at tA+1, tA+2 for last col
par_tAp1=collections.Counter(); par_tAp2=collections.Counter()

for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); sA=b0(A); tA=mpl(A)
        if sA is not None and tA is not None and len(A)<=44:
            L=l1(A)
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E); sE=b0(E); tE=mpl(E)
                if sE is None or tE is None:
                    set_array(A); continue
                dd=tE-tA
                if L==1: diff_l1eq1[dd]+=1
                else: diff_l1gt1[dd]+=1
                kp=len(E[0]) if E and E[0] else 0  # height = rows = len of a column
                # height(E): number of rows
                H=len(E[0]) if len(E)>0 else 0
                keepdiff[H-tA]+=1
                C=len(E)-1
                p1=m_parent(E,tA+1,C); par_tAp1['some' if p1 is not None else 'none']+=1
                p2=m_parent(E,tA+2,C); par_tAp2['some' if p2 is not None else 'none']+=1
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

print("tE-tA, l1==1 :", dict(sorted(diff_l1eq1.items())))
print("tE-tA, l1>1  :", dict(sorted(diff_l1gt1.items())))
print("height(E)-tA :", dict(sorted(keepdiff.items())))
print("parent of last col at tA+1:", dict(par_tAp1))
print("parent of last col at tA+2:", dict(par_tAp2))
