"""R2 crux: at the EXPANDED array A[n] with bad root s' in G' (R2 regime),
does s' RAW-interval-dominate, i.e. elem(A[n]) s' m < elem(A[n]) p m for ALL
s' < p <= s'+j and ALL m < t'=mpl(A[n])?

If raw domination holds at A[n] in R2 (despite failing at base A off-chain),
then m_anc_build_Suc closes R2 ancestry non-circularly (stratified <= raw),
breaking the elem_lt_below_t circularity at the expansion level.

Genuine 2-row seeds only. For each R2 instance (s'<l0A, l1(E)>=2, mpl(E)>=1),
tally raw-domination violations over the full interval and over the
strict-min-at-row-m sub-claim.
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
raw_checks=0; raw_viol=0
anc_checks=0; anc_viol=0   # m_anc(E,m,s'+j,s') holds?
ex_raw=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA
        if sA is not None and lA>=1 and len(A)<=42:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);sp=b0(E);tp=mpl(E);lp=l1(E)
                if sp is None or tp is None: set_array(A); continue
                if not (lp>=2 and tp>=1 and sp<l0A):  # R2 regime only
                    set_array(A); continue
                R2_inst+=1
                # B0'(E) interior columns: sp+1 .. sp+lp-1
                for j in range(1,lp):
                    tgt=sp+j
                    if tgt>=len(E): break
                    for m in range(0,tp):  # m < t'
                        if m>=len(E[sp]) or m>=len(E[tgt]): continue
                        # ancestry (the goal)
                        anc_checks+=1
                        if not m_anc(E,m,tgt,sp): anc_viol+=1
                    # raw interval domination: s' < p <= s'+j
                    for p in range(sp+1,tgt+1):
                        for m in range(0,tp):
                            if m>=len(E[sp]) or m>=len(E[p]): continue
                            raw_checks+=1
                            if not (elem(E,sp,m)<elem(E,p,m)):
                                raw_viol+=1
                                if len(ex_raw)<12:
                                    ex_raw.append((fmt(A),'n',n,'sp',sp,'p',p,'m',m,'tp',tp,
                                                   'es',elem(E,sp,m),'ep',elem(E,p,m)))
                set_array(A)
        for n in range(1,3):
            if len(A)>36: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} R2={R2_inst} raw_chk={raw_checks} raw_viol={raw_viol} anc_viol={anc_viol}/{anc_checks}",flush=True)
    if len(seen)>CAP: break

print(f"\n=== R2 raw-interval domination at A[n] (s'<l0A, l1(E)>=2, m<t') ===")
print(f"R2 instances: {R2_inst}")
print(f"raw-interval s'<p<=s'+j domination: {raw_viol} viol / {raw_checks} checks")
print(f"R2 ancestry m_anc(E,m,s'+j,s'): {anc_viol} viol / {anc_checks} checks")
for e in ex_raw: print("  RAW-VIOL:",e)
