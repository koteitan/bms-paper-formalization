"""Re-verify: among bump-parent cases, restrict to l0>0 (= non-vacuous gateway).

Same setup as probe_bump_parent_structure.py but filter l0A > 0 so the
gateway biconditional is genuinely about reaching a G-target (i < l0).
Also tally bump cases by l0 to see how many are vacuous.
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,m_parent,mpl,b0,l1,set_array,expand)

def idxB(c,j,l0A,l1A): return l0A + c*l1A + j

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=7000;depth=11

bump_dist_l0pos=collections.Counter()
bump_dist_l0zero=collections.Counter()
bucket_l0pos=collections.Counter()
c_is_nm1_l0pos=0; x_is_0_l0pos=0; both_l0pos=0; total_l0pos=0
total_l0zero=0
ex_l0pos=[]; ex_l0zero=[]

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
                    if pn is None or pn<l0A or pn>=inn: continue
                    cp=(pn-l0A)//lA; xp=(pn-l0A)%lA
                    if l0A>0:
                        bump_dist_l0pos[(cp,xp)]+=1
                        total_l0pos+=1
                        if cp==n-1: c_is_nm1_l0pos+=1
                        if xp==0:   x_is_0_l0pos+=1
                        if cp==n-1 and xp==0: both_l0pos+=1
                        if k==tp:       bucket_l0pos['k=t']+=1
                        elif k==tp+1:   bucket_l0pos['k=t+1']+=1
                        else:           bucket_l0pos['k>=t+2']+=1
                        if len(ex_l0pos)<20:
                            ex_l0pos.append((cp,xp,l0A,lA,n,k,tp,fmt(A)))
                    else:
                        bump_dist_l0zero[(cp,xp)]+=1
                        total_l0zero+=1
                        if len(ex_l0zero)<5:
                            ex_l0zero.append((cp,xp,l0A,lA,n,k,tp,fmt(A)))
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} bump[l0>0]={total_l0pos} bump[l0=0]={total_l0zero}",flush=True)
    if len(seen)>CAP: break

print(f"\n=== bump-parent with l0>0 (non-vacuous gateway): {total_l0pos} ===")
print("(c', x') frequency (top 30):")
for kv,ct in bump_dist_l0pos.most_common(30):
    print(f"  {kv}: {ct}")
if total_l0pos>0:
    print(f"\nhypothesis checks (out of {total_l0pos}):")
    print(f"  H1  c' = n-1       : {c_is_nm1_l0pos}/{total_l0pos}")
    print(f"  H2  x' = 0         : {x_is_0_l0pos}/{total_l0pos}")
    print(f"  H3  (c',x')=(n-1,0): {both_l0pos}/{total_l0pos}")
    print(f"\nbucket by k vs t:")
    for k,v in bucket_l0pos.items():
        print(f"  {k}: {v}")
    print(f"\nexamples (c', x', l0A, l1A, n, k, t, A):")
    for e in ex_l0pos: print(" ",e)

print(f"\n=== bump-parent with l0=0 (vacuous gateway): {total_l0zero} ===")
print("(c', x') frequency (top 10):")
for kv,ct in bump_dist_l0zero.most_common(10):
    print(f"  {kv}: {ct}")
print("examples:")
for e in ex_l0zero: print(" ",e)
