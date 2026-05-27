import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,mpl,b0,l1,set_array,expand,height)
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));k=fmt(A)
    if k not in seen: seen.add(k);Q.append(A)
CAP=9000;depth=12
# CLAIM D: m_anc A M sA sp  ==> for all m'<=M, all x in (sp,sA): elem A sp m' < elem A x m'
# (deep ancestor sp dominates its whole open interval at every level <= M)
# test directly on (sp=b0(E), sA=b0(A)=l0A) pairs in R2, M = t'-1 region... actually test general:
# pick any pair (anc, desc) with m_anc A M desc anc; check interval domination at all m'<=M.
nD=0; vD=0; ex=[]
# also test the offset-induction parent-stays: m_parent A m c >= sp for c in (sp,sA], m<tp
nPar=0; vPar=0
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA
        if sA is not None and lA>=1 and len(A)<=45:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);sp=b0(E);tp=mpl(E);lp=l1(E);set_array(A)
                if sp is None or tp is None: continue
                if not (lp>=2 and tp>=1 and sp<l0A): continue
                # sp = m_parent A t' sA presumably; M ranges m<tp
                for M in range(0,tp):
                    if M>=len(A[sp]) or M>=len(A[sA]): continue
                    if not m_anc(A,M,sA,sp): continue  # need sp anc of sA at level M
                    # claim D: dominate (sp,sA) at all m'<=M
                    for mp_ in range(0,M+1):
                        for x in range(sp+1,sA):
                            if x>=len(A) or mp_>=len(A[x]) or mp_>=len(A[sp]): continue
                            nD+=1
                            if not (elem(A,sp,mp_)<elem(A,x,mp_)):
                                vD+=1
                                if len(ex)<8: ex.append(('D',fmt(A),'sp',sp,'sA',sA,'x',x,'M',M,'mp',mp_))
                # parent-stays check
                for c in range(sp+1,sA+1):
                    if c>=len(A): break
                    for m in range(0,tp):
                        if m>=len(A[c]): continue
                        pp=m_parent(A,m,c)
                        if pp is None: continue
                        nPar+=1
                        if pp<sp: vPar+=1
        for n in range(1,4):
            if len(A)>40: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} D={nD}/v{vD} Par={nPar}/v{vPar}",flush=True)
    if len(seen)>CAP: break
print(f"\nCLAIM D (deep anc dominates interval at all levels<=M): violations={vD}/{nD}")
print(f"parent-stays (m_parent A m c >= sp): violations={vPar}/{nPar}")
for e in ex: print("  ",e)
