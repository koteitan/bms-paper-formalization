import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,mpl,b0,l1,set_array,expand,height)
# ascends A j k semantics: need the probe's ascends. Reconstruct: ascends A j k <=> non_strict_ancestor A j (s+j) ... 
# Simpler: use the value test. ascends A j k true iff bump applies. From elem_AEn_cross_block: ascends A j k <=> k < (level where col s+j stops ascending). The probe lib may have it; check by m_parent semantics is hard.
# Use direct: a column s+j 'ascends at k' iff elem grows across blocks. Test claim via idx_B values:
# Claim BC: for k, j<l1A, if elem(E, idxB(n,j), k) > elem(E, idxB(0,j), k) [strictly bumped => ascends],
#   then m_anc(E, k, idxB(n,j), idxB(0,j)).
def idxB(A,c,j,l0A,l1A): return l0A + c*l1A + j
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=8000;depth=11
nBC=0;vBC=0; ex=[]
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
                    i0=idxB(A,0,j,l0A,lA); iN=idxB(A,n,j,l0A,lA)
                    if iN>=lenE or i0>=lenE: continue
                    for k in range(0, tp+1):
                        if k>=len(E[i0]) or k>=len(E[iN]): continue
                        # "ascends at k" proxy: block-n copy strictly bumped above block-0 copy
                        if elem(E,iN,k) > elem(E,i0,k):
                            nBC+=1
                            if not m_anc(E,k,iN,i0):
                                vBC+=1
                                if len(ex)<8: ex.append(('BC',fmt(A),n,'j',j,'k',k,'i0',i0,'iN',iN,'lA',lA))
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} BC={nBC}/v{vBC}",flush=True)
    if len(seen)>CAP: break
print(f"\nblock-copy-anc (bumped => idxB(0,j) is k-anc of idxB(n,j)): viol={vBC}/{nBC}")
for e in ex: print("  ",e)
