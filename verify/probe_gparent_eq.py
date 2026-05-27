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
# When parent of idx_B(0,j) is in G (< l0), compare with parent of idx_B(n,j).
nEq=0;vEq=0; nGn=0; ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA
        if sA is not None and lA>=1 and len(A)<=42:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);tp=mpl(E)
                if tp is None: continue
                lenE=len(E)
                for j in range(0,lA):
                    i0=idxB(0,j,l0A,lA); iN=idxB(n,j,l0A,lA)
                    if iN>=lenE: continue
                    for k in range(0,tp+1):
                        if k>=len(E[iN]): continue
                        p0=m_parent(E,k,i0); pN=m_parent(E,k,iN)
                        # case: p0 in G (< l0A)
                        if p0 is not None and p0 < l0A:
                            nEq+=1
                            if pN!=p0:
                                vEq+=1
                                if len(ex)<10: ex.append((fmt(A),'n',n,'j',j,'k',k,'p0',p0,'pN',pN,'l0',l0A,'l1',lA))
                        # also count: is pN in G when p0 in G?
                        if p0 is not None and p0<l0A and pN is not None and pN<l0A: nGn+=1
                set_array(A)
        for n in range(1,4):
            if len(A)>38: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} p0inG_cases={nEq} pN!=p0={vEq} bothG={nGn}",flush=True)
    if len(seen)>CAP: break
print(f"\np0 in G: {nEq} cases, p0!=pN: {vEq}, both-in-G: {nGn}")
for e in ex: print("  ",e)
