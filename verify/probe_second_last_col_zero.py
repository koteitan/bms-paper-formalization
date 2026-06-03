import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, mpl, b0, l1, set_array, expand)
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=11000; depth=13
res=collections.Counter(); ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); s=b0(A); t=mpl(A)
        if s is not None and t is not None and l1(A)>1 and len(A)<=46:
            C=len(A)-1
            # A's second-to-last column = C-1; value at row t+1
            col=A[C-1]
            v = col[t+1] if t+1 < len(col) else 0
            res['zero' if v==0 else 'NONZERO']+=1
            if v!=0 and len(ex)<8: ex.append((fmt(A),'t',t,'C',C,'val',v,'l1',l1(A)))
        for nn in range(1,3):
            if len(A)>40: continue
            E=expand(fmt(A),nn)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    if len(seen)>CAP: break
print("l1>1: A's 2nd-to-last col (C-1) at row mpl+1:", dict(res))
for e in ex: print("  NONZERO:",e)
