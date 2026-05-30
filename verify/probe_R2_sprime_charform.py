"""Characterize s'=b0_start(A[n]) in R2 (s'<sA) in closed form over A.
Test hypotheses:
  H1: s' = m_parent A t' sA          (t'=mpl(A[n]); s' is A-parent of sA at level t')
  H2: s' = m_parent A tA sA          (A-parent of sA at A's own mpl)
  H3: s' = m_parent A t' (last_col_idx A)   (A-parent of C at level t')
  H4: s' = b0_start(G_block A ++ [last_col A])  (bad root of G+C sub-array)
  H5: s' is the LEAST p<sA with elem A p (something) ... (skip)
Tally exact-match counts for each hypothesis among R2 instances.
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,mpl,b0,l1,set_array,expand)

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=8000;depth=12

R2=0
H=collections.Counter(); tot=collections.Counter()
ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA;tA=mpl(A);CA=len(A)-1
        if sA is not None and tA is not None and lA>=1 and len(A)<=40:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);sp=b0(E);tp=mpl(E);lp=l1(E)
                set_array(A)
                if sp is None or tp is None: continue
                if not (lp>=2 and tp>=1 and sp<l0A): continue
                R2+=1
                # H1
                tot['H1']+=1
                if tp<len(A[CA]):  # ensure level valid-ish; m_parent handles
                    h1=m_parent(A,tp,sA)
                    if h1==sp: H['H1']+=1
                # H2
                tot['H2']+=1
                h2=m_parent(A,tA,sA)
                if h2==sp: H['H2']+=1
                # H3
                tot['H3']+=1
                h3=m_parent(A,tp,CA)
                if h3==sp: H['H3']+=1
                # H4: bad root of G_block(A) ++ [C]
                tot['H4']+=1
                GA=[col[:] for col in A[:sA]]+[A[CA][:]]
                set_array(GA); h4=b0(GA); set_array(A)
                if h4==sp: H['H4']+=1
                if len(ex)<8:
                    ex.append((fmt(A),'n',n,'sp',sp,'sA',sA,'tp',tp,'tA',tA,
                               'h1',m_parent(A,tp,sA),'h3',m_parent(A,tp,CA)))
        for n in range(1,3):
            if len(A)>34: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} R2={R2} "+" ".join(f"{k}={H[k]}/{tot[k]}" for k in ['H1','H2','H3','H4']),flush=True)
    if len(seen)>CAP: break

print(f"\n=== s' characterization (R2={R2}) ===")
for k in ['H1','H2','H3','H4']:
    print(f"  {k}: {H[k]}/{tot[k]} match")
for e in ex: print("  ex:",e)
