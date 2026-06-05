"""Why dropC>=drops on [0,m0)?  s is m-ancestor of C for all m<m0 (m_anc A m C s
via m_ancestor_mono from m0-parent). Test some candidate explanations:
 (E1) Is s row constant on [0,m0)? sm == s0 for all m<m0?
 (E2) Is C-s difference (integer) actually >= the difference at next level via
      the GENERAL fact: for ANY two columns x,y with y an m-ancestor of x at all
      levels < L, is (x - y) antitone on [0,L)? Test on arbitrary ancestor pairs.
 (E3) Maybe simpler: delta itself antitone might follow from delta(m) counting
      something. Print delta sequence shape for a few arrays.
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=6000; depth=13
e1_bad=0; e1_chk=0
# E2: general ancestor pair drop test
e2_bad=0; e2_chk=0; e2ex=[]
printed=0
for d in range(depth):
    fr=[]
    for A in Q:
        if 2<=len(A)<=44:
            set_array(A); s=b0(A); t=mpl(A)
            if s is not None and t is not None:
                C=len(A)-1; m0=t
                # E1
                for m in range(0,m0):
                    e1_chk+=1
                    if elem(A,s,m)!=elem(A,s,0): e1_bad+=1
                if printed<6:
                    dseq=[elem(A,C,m)-elem(A,s,m) for m in range(m0)]
                    sseq=[elem(A,s,m) for m in range(m0)]
                    Cseq=[elem(A,C,m) for m in range(m0)]
                    print("  EX",fmt(A)[:60],"m0",m0,"s",s,"delta",dseq,"s",sseq,"C",Cseq)
                    printed+=1
                # E2: for every pair (x,y) with y m-ancestor of x at level m and m+1,
                # test (xm-ym)>=(x(m+1)-y(m+1))
                for x in range(len(A)):
                    for m in range(min(len(A[x]),20)-1):
                        if m_anc(A,m,x, None) if False else True:
                            pass
        for n in range(1,3):
            if len(A)>38: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} e1_bad(s const)={e1_bad}/{e1_chk}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== s constant on [0,m0): {e1_bad} viol / {e1_chk} ===")
