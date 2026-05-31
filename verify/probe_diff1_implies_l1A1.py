import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,mpl,b0,l1,set_array,expand)
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=8000;depth=13
tab=collections.Counter()  # (diff, l1A>1)
viol=0
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); tA=mpl(A); lA=l1(A)
        if tA is not None and lA is not None and len(A)<=44:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E); tE=mpl(E); lE=l1(E)
                set_array(A)
                if tE is None: continue
                if not (lE>=2 and tE>=1): continue
                diff=tE-tA
                tab[(diff, lA)]+=1
                if diff==1 and lA!=1: viol+=1
        for nn in range(1,3):
            if len(A)>38: continue
            E=expand(fmt(A),nn)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    if len(seen)>CAP: break
print("(diff, l1A) -> count:", dict(sorted(tab.items())))
print("diff=1 AND l1A!=1 violations:", viol)
