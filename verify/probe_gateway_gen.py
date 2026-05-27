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
# gateway: m_parent(A[n]) k (idxB(c,0)) == idxB(c-1, l1-1) ? for 1<=c<=n, ascending(k<mpl A region)
# restrict to bumped block-start (idxB(c,0) value > idxB(c-1,0) value), i.e. ascending offset 0
nG=0;vG=0; ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA; tA=mpl(A)
        if sA is not None and lA>=1 and tA is not None and len(A)<=42:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);tp=mpl(E)
                if tp is None: continue
                lenE=len(E)
                for c in range(1,n+1):
                    ic0=idxB(c,0,l0A,lA); pred=idxB(c-1,lA-1,l0A,lA)
                    if ic0>=lenE: continue
                    for k in range(0,tA):  # k < mpl A (ascending region for offset 0)
                        if k>=len(E[ic0]): continue
                        # only when block-start is bumped (asc, delta>0)
                        if elem(E,ic0,k) > elem(E,idxB(c-1,0,l0A,lA),k):
                            pp=m_parent(E,k,ic0)
                            nG+=1
                            if pp!=pred:
                                vG+=1
                                if len(ex)<10: ex.append((fmt(A),'n',n,'c',c,'k',k,'got',pp,'want',pred,'l0',l0A,'l1',lA))
                set_array(A)
        for n in range(1,4):
            if len(A)>38: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} gateway_cases={nG} viol={vG}",flush=True)
    if len(seen)>CAP: break
print(f"\ngateway (m_parent(idxB(c,0),k)==idxB(c-1,l1-1)): viol={vG}/{nG}")
for e in ex[:10]: print("  ",e)
