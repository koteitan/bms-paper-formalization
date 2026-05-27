import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,mpl,b0,l1,set_array,expand,height)
def idxB(c,j,l0A,l1A): return l0A + c*l1A + j
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=6000;depth=10
# bumped one-step, broken by j==0 vs j>0
n0=0;v0=0; nj=0;vj=0; ex=[]
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
                            if elem(E,ic,k)>elem(E,icm,k):
                                ok=m_anc(E,k,ic,icm)
                                if j==0:
                                    n0+=1
                                    if not ok: v0+=1
                                else:
                                    nj+=1
                                    if not ok:
                                        vj+=1
                                        if len(ex)<8: ex.append((fmt(A),n,'j',j,'c',c,'k',k))
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} j0={n0}/v{v0} jpos={nj}/v{vj}",flush=True)
    if len(seen)>CAP: break
print(f"\nbumped onestep: j==0: viol={v0}/{n0}   j>0: viol={vj}/{nj}")
for e in ex: print("  ",e)
