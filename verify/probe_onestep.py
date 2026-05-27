import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,mpl,b0,l1,set_array,expand,height)
def idxB(c,j,l0A,l1A): return l0A + c*l1A + j
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=7000;depth=11
# bumped(=ascends&delta>0) one-step: idxB(c-1,j) is k-anc of idxB(c,j)? and what IS m_parent(idxB(c,j),k)?
nS=0;vS=0; parent_is_prevblock=0; parent_total=0; ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA
        if sA is not None and lA>=1 and len(A)<=40:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);tp=mpl(E)
                if tp is None: set_array(A); continue
                lenE=len(E)
                for j in range(0,lA):
                    for c in range(1,n+1):
                        ic=idxB(c,j,l0A,lA); icm=idxB(c-1,j,l0A,lA)
                        if ic>=lenE: continue
                        for k in range(0,tp+1):
                            if k>=len(E[ic]) or k>=len(E[icm]): continue
                            if elem(E,ic,k) > elem(E,icm,k):   # strictly bumped (asc)
                                nS+=1
                                if not m_anc(E,k,ic,icm):
                                    vS+=1
                                    if len(ex)<6: ex.append(('S',fmt(A),n,'j',j,'c',c,'k',k,'lA',lA))
                                pp=m_parent(E,k,ic); parent_total+=1
                                if pp==icm: parent_is_prevblock+=1
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} onestep={nS}/v{vS} parent==prevblock={parent_is_prevblock}/{parent_total}",flush=True)
    if len(seen)>CAP: break
print(f"\none-step anc (idxB(c-1,j) is k-anc of idxB(c,j) when bumped): viol={vS}/{nS}")
print(f"m_parent(idxB(c,j),k)==idxB(c-1,j): {parent_is_prevblock}/{parent_total}")
for e in ex: print("  ",e)
