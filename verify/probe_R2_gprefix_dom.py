"""R2 irreducible sub-fact: the expanded bad root s'=b0_start(A[n]) sits in
A's G-prefix (s'<l0A).  For columns p with s'<p<l0A (still G-prefix, verbatim
A columns), does s' dominate at base array A: elem A s' m < elem A p m, m<t'?

Also characterize s' relative to A's own bad root sA and structure:
  - is s' == sA? s' < sA? s' related to A's t-parent chain?
  - is s' the m'-parent of sA for some m'?  (s' an ancestor of sA in A?)
Goal: find the closed-form characterization of s' and confirm G-prefix
domination is a clean genuine-BMS fact (the missing DOM A => DOM(A[n]) R2 link).
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

R2_inst=0
gpref_chk=0; gpref_viol=0
sp_vs_sA=collections.Counter()
sp_anc_sA=collections.Counter()   # is s' an m_anc of sA in A (some level)?
ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA;tA=mpl(A)
        if sA is not None and tA is not None and lA>=1 and len(A)<=42:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);sp=b0(E);tp=mpl(E);lp=l1(E)
                set_array(A)  # back to A for base-array facts
                if sp is None or tp is None: continue
                if not (lp>=2 and tp>=1 and sp<l0A):  # R2
                    continue
                R2_inst+=1
                # characterize s' vs sA
                if sp==sA: sp_vs_sA['==sA']+=1
                elif sp<sA: sp_vs_sA['<sA']+=1
                else: sp_vs_sA['>sA']+=1
                # is s' an ancestor of sA in A at some level < tA?
                anc=False
                for mm in range(0,tA):
                    if m_anc(A,mm,sA,sp): anc=True;break
                sp_anc_sA[anc]+=1
                # G-prefix domination at base A: s'<p<l0A, m<tp
                for p in range(sp+1,l0A):
                    for m in range(0,tp):
                        if m>=len(A[sp]) or m>=len(A[p]): continue
                        gpref_chk+=1
                        if not (elem(A,sp,m)<elem(A,p,m)):
                            gpref_viol+=1
                            if len(ex)<12:
                                ex.append((fmt(A),'n',n,'sp',sp,'sA',sA,'p',p,'m',m,'tp',tp))
        for n in range(1,3):
            if len(A)>36: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} R2={R2_inst} gpref={gpref_viol}/{gpref_chk}",flush=True)
    if len(seen)>CAP: break

print(f"\n=== R2 G-prefix domination at base A (s'<p<l0A, m<t') ===")
print(f"R2 instances: {R2_inst}")
print(f"G-prefix s' domination viol: {gpref_viol} / {gpref_chk}")
print(f"s' vs sA: {dict(sp_vs_sA)}")
print(f"s' is an m_anc of sA in A (m<tA): {dict(sp_anc_sA)}")
for e in ex: print("  GPREF-VIOL:",e)
