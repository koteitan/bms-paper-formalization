"""In R2 (s'=b0_start(A[n])<l0A, l1(E)>=2, mpl(E)>=1):
  (Q1) is l1 A (PREDECESSOR's l1) always == 1?  (P1_from_struct needs l1 A=1)
  (Q2) is mpl(A[n]) == mpl(A)?  (location lemma s'=m_parent A (mpl A) sA needs t'=tA)
  (Q3) is mpl(A[n]) == Suc t' for the P1 'Suc t'' form, i.e. mpl(A[n])>=1 and = tA?
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,mpl,b0,l1,set_array,expand)

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=9000;depth=13
R2=0; l1A_cnt=collections.Counter(); mpl_eq=collections.Counter(); l1E_cnt=collections.Counter()
ex_l1Agt1=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA;tA=mpl(A)
        if sA is not None and tA is not None and lA>=1 and len(A)<=42:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);sp=b0(E);tp=mpl(E);lp=l1(E)
                set_array(A)
                if sp is None or tp is None: continue
                if not (lp>=2 and tp>=1 and sp<l0A): continue
                R2+=1
                l1A_cnt[lA]+=1
                l1E_cnt[lp]+=1
                mpl_eq[('tp==tA',tp==tA)]+=1
                if lA>1 and len(ex_l1Agt1)<10:
                    ex_l1Agt1.append((fmt(A),'n',n,'lA',lA,'sA',sA,'sp',sp,'tp',tp,'tA',tA))
        for n in range(1,3):
            if len(A)>36: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} R2={R2} l1A={dict(l1A_cnt)} tp==tA={mpl_eq}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== R2 (R2={R2}) ===")
print(f"l1 A (predecessor) distribution: {dict(l1A_cnt)}")
print(f"l1 (A[n]) distribution: {dict(l1E_cnt)}")
print(f"mpl(A[n])==mpl(A): {dict(mpl_eq)}")
for e in ex_l1Agt1: print("  l1A>1:",e)
