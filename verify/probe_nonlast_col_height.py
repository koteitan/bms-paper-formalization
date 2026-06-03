"""gate-2 reduction target: are non-last columns zero at rows >= tA+2 ?

For A in BMS (stripped), tA=mpl(A), C=last col.  Compute
  M = max{ m : exists c < C with elem A c m != 0 }   (the tallest non-last column row)
and compare to tA.  Claim (for keep(A[n]) <= tA+2):  M <= tA+1, i.e. M - tA <= 1.
Also report height(A)-tA and (M of ALL cols incl last) - tA.
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, mpl, b0, l1, set_array, expand)

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=12000; depth=14

nonlast=collections.Counter(); allcol=collections.Counter()
viol=[]

for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); s=b0(A); t=mpl(A)
        if s is not None and t is not None and len(A)<=46:
            C=len(A)-1
            H=len(A[0]) if len(A)>0 else 0
            # tallest non-last column nonzero row
            Mnl=-1; Mall=-1
            for c in range(len(A)):
                col=A[c]
                for m in range(len(col)-1,-1,-1):
                    if col[m]!=0:
                        if c<C and m>Mnl: Mnl=m
                        if m>Mall: Mall=m
                        break
            nonlast[Mnl-t]+=1
            allcol[Mall-t]+=1
            if Mnl - t > 1 and len(viol)<10:
                viol.append((fmt(A),'t',t,'C',C,'Mnl',Mnl,'H',H))
        for nn in range(1,3):
            if len(A)>40: continue
            E=expand(fmt(A),nn)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    if len(seen)>CAP: break

print("M(non-last) - tA :", dict(sorted(nonlast.items())))
print("M(all cols) - tA :", dict(sorted(allcol.items())))
for v in viol: print("  NONLAST>tA+1:", v)
