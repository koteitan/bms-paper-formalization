"""gate-2 second half (Hmpl_gt1): for l1(A)>1, is tE <= tA, and what's the clean no-parent route?

For genuine BMS A with l1(A)>1, E=A[n]:
  tA=mpl(A), tE=mpl(E), H=height(E).
Record (l1>1 only):
  (1) tE-tA distribution         (claim: <= 0)
  (2) H-tA distribution          (1 => row tA+1 OOB => trivial no-parent@tA+1)
  (3) when H-tA==2 (row tA+1 in-bounds): does last col have a parent at tA+1?  (claim: none)
  (4) cross-check: parent of last col at tA+1 overall (l1>1).
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent, mpl, b0, l1, set_array, expand)

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=10000; depth=13

tediff=collections.Counter(); hdiff=collections.Counter()
par_when_H2=collections.Counter(); par_all=collections.Counter()
viol=[]

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
                tediff[tE-tA]+=1
                if tE-tA>0 and len(viol)<8: viol.append((fmt(A),'tA',tA,'tE',tE,'l1',l1(A),'n',n))
                H=len(E[0]) if len(E)>0 else 0
                hdiff[H-tA]+=1
                C=len(E)-1
                p=m_parent(E,tA+1,C)
                par_all['some' if p is not None else 'none']+=1
                if H-tA==2:
                    par_when_H2['some' if p is not None else 'none']+=1
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

print("l1>1: tE-tA       :", dict(sorted(tediff.items())))
print("l1>1: height(E)-tA :", dict(sorted(hdiff.items())))
print("l1>1: parent@tA+1 (all)      :", dict(par_all))
print("l1>1: parent@tA+1 when H=tA+2 :", dict(par_when_H2))
for v in viol: print("  tE>tA VIOL:", v)
