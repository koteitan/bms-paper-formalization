import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,mpl,b0,l1,set_array,expand,height)
# GENUINE BMS seeds ONLY: seed k = [replicate k 0, replicate k 1] = 2 columns
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
print("genuine seeds:",seeds)
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));k=fmt(A)
    if k not in seen: seen.add(k);Q.append(A)
CAP=12000;depth=14
checks=0;Pv=0;PQv=0;ex=[]
acc_seen=False
ACC=fmt(strip(parse("(0,0,0)(1,1,1)(2,0,0)(1,1,1)(2,0,0)")))
for d in range(depth):
    fr=[]
    for A in Q:
        if fmt(A)==ACC: acc_seen=True
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA
        if sA is not None and lA>=1 and len(A)<=45:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);sp=b0(E);tp=mpl(E);lp=l1(E);set_array(A)
                if sp is None or tp is None: continue
                if not (lp>=2 and tp>=1 and sp<l0A): continue
                for col in range(sp+1,l0A):
                    j=col-sp
                    if j>=lp: continue
                    if col>=l0A+lA: continue
                    if col>=len(A): break
                    for m in range(0,tp):
                        if m>=len(A[sp]) or m>=len(A[col]): continue
                        checks+=1
                        P=elem(A,sp,m)<elem(A,col,m)
                        if not P:
                            Pv+=1
                            if len(ex)<8: ex.append(('P',fmt(A),n,sp,col,m,'lp',lp))
                            continue
                        if not m_anc(A,m,col,sp):
                            PQv+=1
                            if len(ex)<12: ex.append(('PQ',fmt(A),n,sp,col,m))
        for n in range(1,4):
            if len(A)>40: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    print(f"depth {d}: visited={len(seen)} checks={checks} Pviol={Pv} PQviol={PQv} acc_seen={acc_seen}",flush=True)
    if len(seen)>CAP: break
print(f"\nGENUINE-seed BMS: checks={checks} Pviol={Pv} PQviol={PQv}  Acc-reached={acc_seen}")
for e in ex: print("  ",e)
