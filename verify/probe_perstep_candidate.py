"""Verify the per-step candidate sub-facts for the onestep engine.

Target lemma: m_parent (A[n]) (Suc k') (idx_B c j) = idx_B(c, j-1) for
ascending j>0. Via the within-block characterization this reduces to
"idx_B(0,j-1) is the LAST within-block candidate of idx_B(0,j)", i.e.:
  (a) elem(A[n]) (idx_B 0 (j-1)) (Suc k') < elem(A[n]) (idx_B 0 j) (Suc k')
  (b) m_ancestor (A[n]) k' (idx_B 0 j) (idx_B 0 (j-1))
hold whenever j ascends at Suc k'.  Tally violations of (a), (b), and of
"last S = j-1" directly.  Also check: does (a) hold for ALL x<j in S, or
only x=j-1?  (We only need j-1 to be the max candidate.)
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,mpl,b0,l1,set_array,expand)
def idxB(c,j,l0A,l1A): return l0A + c*l1A + j

def ascends_E(E,s,m0,didx,m):
    # ascends in expansion base sense: m<m0 and non-strict-ancestor of s
    if m>=m0: return False
    col=s+didx
    return col==s or m_anc(E,m,col,s)

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=6000;depth=10

tot=0
a_viol=0; b_viol=0; lastS_viol=0
ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA
        if sA is not None and lA>=2 and len(A)<=40:
            E0=A  # base for ascends ref via expansion
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);tp=mpl(E)
                if tp is None: set_array(A); continue
                lenE=len(E)
                # ascends defined on base A: use A's b0/mpl
                set_array(A); sB=b0(A); m0B=mpl(A); set_array(E)
                if sB is None or m0B is None: set_array(A); continue
                for j in range(1,lA):
                    i0j=idxB(0,j,l0A,lA)
                    if i0j>=lenE: continue
                    for kk2 in range(0,tp):    # Suc k' = kk2, so k' = kk2-1; need kk2>=1
                        if kk2<1: continue
                        Sk=kk2; kp=kk2-1
                        if Sk>=len(E[i0j]): continue
                        # ascending j at Suc k'? (base A ascends)
                        set_array(A)
                        asc = (Sk<m0B) and (sB+j==sB or m_anc(A,Sk,sB+j,sB))
                        set_array(E)
                        if not asc: continue
                        # within-block candidate set S (block 0)
                        S=[x for x in range(0,j)
                           if elem(E,idxB(0,x,l0A,lA),Sk)<elem(E,i0j,Sk)
                           and m_anc(E,kp,i0j,idxB(0,x,l0A,lA))]
                        tot+=1
                        # (a) j-1 value-smaller
                        a_ok = elem(E,idxB(0,j-1,l0A,lA),Sk)<elem(E,i0j,Sk)
                        # (b) j-1 is kp-ancestor
                        b_ok = m_anc(E,kp,i0j,idxB(0,j-1,l0A,lA))
                        if not a_ok: a_viol+=1
                        if not b_ok: b_viol+=1
                        if (not S) or S[-1]!=j-1:
                            lastS_viol+=1
                            if len(ex)<10: ex.append((fmt(A),'n',n,'j',j,'Sk',Sk,'S',S,'lA',lA))
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} tot={tot} a_viol={a_viol} b_viol={b_viol} lastS_viol={lastS_viol}",flush=True)
    if len(seen)>CAP: break

print(f"\n=== per-step candidate sub-facts (ascending j>0, block 0, l1>=2) ===")
print(f"total ascending instances: {tot}")
print(f"(a) elem(j-1)<elem(j) violations: {a_viol}")
print(f"(b) m_anc k' (idx_B 0 j)(idx_B 0 (j-1)) violations: {b_viol}")
print(f"last S = j-1 violations: {lastS_viol}")
for e in ex: print("  LASTS-VIOL:",e)
