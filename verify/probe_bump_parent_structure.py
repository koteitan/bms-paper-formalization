"""Characterize bump-parent cases for clause (i) leftmost gateway.

Setup: among (A, n, k, idx_B(n,0)) parent triples (k >= t, column 0
non-ascending level), focus on the cases where pn := m_parent(E, k, idx_B(n,0))
falls strictly inside the bump region [l0, idx_B(n,0)).

For each such case decompose pn = l0 + c' * l1A + x'  (0 <= x' < l1A)
and tabulate (c', x') distribution.  Hypotheses to check:
  H1: c' = n - 1 always?
  H2: x' = 0 always?
  H3: (c', x') = (n-1, 0) always?
Also bucket by k vs t (k == t, k == t+1, k >= t+2).
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,m_parent,mpl,b0,l1,set_array,expand)

def idxB(c,j,l0A,l1A): return l0A + c*l1A + j

# Genuine 2-row seeds only.
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=7000;depth=11

bump_dist=collections.Counter()      # (c',x') -> count
bucket_by_k=collections.Counter()    # 'k=t','k=t+1','k>=t+2'
c_is_nm1=0; x_is_0=0; both_match=0; bump_total=0
examples=[]                          # up to 30 sample tuples

for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); sA=b0(A); lA=l1(A); l0A=sA
        if sA is not None and lA>=1 and len(A)<=40:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E); tp=mpl(E)
                if tp is None: set_array(A); continue
                lenE=len(E)
                inn=idxB(n,0,l0A,lA)
                if inn>=lenE: set_array(A); continue
                hmax=len(E[inn])
                for k in range(tp,hmax):
                    pn=m_parent(E,k,inn)
                    if pn is None: continue
                    if pn<l0A: continue
                    if pn>=inn: continue
                    # bump-region parent
                    cp=(pn-l0A)//lA
                    xp=(pn-l0A)%lA
                    bump_dist[(cp,xp)]+=1
                    bump_total+=1
                    if cp==n-1: c_is_nm1+=1
                    if xp==0:   x_is_0+=1
                    if cp==n-1 and xp==0: both_match+=1
                    if k==tp:       bucket_by_k['k=t']+=1
                    elif k==tp+1:   bucket_by_k['k=t+1']+=1
                    else:           bucket_by_k['k>=t+2']+=1
                    if len(examples)<30:
                        examples.append((cp,xp,lA,n,k,tp,fmt(A)))
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} bump_total={bump_total}",flush=True)
    if len(seen)>CAP: break

print(f"\n=== bump parent total: {bump_total} ===")
print("(c', x') frequency (top 30):")
for kv,ct in bump_dist.most_common(30):
    print(f"  {kv}: {ct}")
print(f"\nhypothesis checks (out of {bump_total}):")
print(f"  H1  c' = n-1       : {c_is_nm1}/{bump_total}  -> {'YES' if c_is_nm1==bump_total else 'NO'}")
print(f"  H2  x' = 0         : {x_is_0}/{bump_total}    -> {'YES' if x_is_0==bump_total else 'NO'}")
print(f"  H3  (c',x')=(n-1,0): {both_match}/{bump_total}-> {'YES' if both_match==bump_total else 'NO'}")
print(f"\nbucket by k vs t:")
for k,v in bucket_by_k.items():
    print(f"  {k}: {v}")
print(f"\nexamples (c', x', l1A, n, k, t, A):")
for e in examples:
    print(" ",e)
