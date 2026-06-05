"""For c1 expand-case on a BUMPED column idx_B(c,j): suppose its row0 value is 0.
row0 bumped = dcol(0) + (asc(j,0)? c*delta(0):0).  =0  =>  dcol(0)=0 and term0=0.
Q(A): when dcol(0) = (A!(s+j))!0 = 0, for the column s+j:
  (Q-asc) does s+j EVER ascend (asc(j,m) for some m)? If never => bump=0 => col = dcol
          which is all-0 by IH(c1). CLEAN.
  If it CAN ascend, then need delta(m)=0 at those m, OR dcol still dominates.
Test: among bumped cols with dcol(0)=0, count how many have asc(j,m)=True for some m,
and among those whether delta(m)=0 there. (s+j ascends at m <=> m<m0 & nsa(s+j,s)).
nsa(s+j,s): s+j==s (j=0) or m_anc(s+j,s). If j=0 => col IS s => dcol(0)=elem(s,0).
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)
def delta(A,s,C,m): return elem(A,C,m)-elem(A,s,m)
def nsa(A,m,i,j): return i==j or m_anc(A,m,i,j)
def asc(A,s,m0,j,m): return (m<m0) and nsa(A,m,s+j,s)
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=7000; depth=13
tot=0; ascever=0; ascever_deltapos=0; ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        if 2<=len(A)<=42:
            set_array(A); s=b0(A); m0=mpl(A)
            if s is not None and m0 is not None:
                C=len(A)-1
                L1=C-s
                for j in range(L1):  # B0 cols are s..C-1, index j
                    col=A[s+j]
                    if len(col)>0 and elem(A,s+j,0)==0:
                        tot+=1
                        # does it ever ascend?
                        ascends_any=False; deltapos_at_asc=False
                        for m in range(len(col)):
                            if asc(A,s,m0,j,m):
                                ascends_any=True
                                if delta(A,s,C,m)>0: deltapos_at_asc=True
                        if ascends_any:
                            ascever+=1
                            if deltapos_at_asc:
                                ascever_deltapos+=1
                                if len(ex)<10: ex.append((fmt(A),'s',s,'j',j,'m0',m0))
        for n in range(1,3):
            if len(A)>36: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} dcol0=0 cols={tot} everAsc={ascever} asc&deltapos={ascever_deltapos}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== B0 cols with dcol(0)=0: {tot}; ever ascend: {ascever}; ascend AND delta>0 there: {ascever_deltapos} ===")
for e in ex: print("  EX:",e)
