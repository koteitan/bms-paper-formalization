import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,mpl,b0,l1,set_array,expand,height)
def idxB(c,j,l0A,l1A): return l0A + c*l1A + j
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=7000;depth=11
# one-step ALL j (no ascending filter): idxB(c-1,j) k-anc of idxB(c,j)?
# split by whether bumped (asc) or equal (not-asc)
nA=0;vA=0; nN=0;vN=0; ex=[]
# also: full clause(v) iff directly
nV=0;vV=0
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
                            anc=m_anc(E,k,ic,icm)
                            if elem(E,ic,k)>elem(E,icm,k):
                                nA+=1
                                if not anc: vA+=1
                            elif elem(E,ic,k)==elem(E,icm,k):
                                nN+=1
                                if not anc:
                                    vN+=1
                                    if len(ex)<8: ex.append(('N-notanc',fmt(A),n,'j',j,'c',c,'k',k))
                # full clause v iff
                for i in range(0,lA):
                    for j in range(0,lA):
                        for n0 in range(0,n):
                            for n1 in range(n0+1,n):
                                if n1+1>n: continue
                                A0=idxB(n0,i,l0A,lA); S1=idxB(n1,j,l0A,lA); S2=idxB(n1+1,j,l0A,lA)
                                if S2>=lenE or A0>=lenE: continue
                                for k in range(0,tp+1):
                                    if k>=len(E[S1]) or k>=len(E[S2]) or k>=len(E[A0]): continue
                                    nV+=1
                                    if m_anc(E,k,S1,A0)!=m_anc(E,k,S2,A0): vV+=1
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} asc={nA}/v{vA} eq={nN}/v{vN} vIFF={nV}/v{vV}",flush=True)
    if len(seen)>CAP: break
print(f"\nonestep bumped: v{vA}/{nA}  onestep equal(not-asc): v{vN}/{nN}  clause-v-iff: v{vV}/{nV}")
for e in ex: print("  ",e)
