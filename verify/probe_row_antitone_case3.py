"""Verify elem A i (Suc m) <= elem A i m for all genuine BMS arrays, all i,m.
Then dig into the expand case-3 crux: for a bumped column at idx_B(c,j),
when BOTH m and Suc m ascend, check the inequality
  dcol(Suc m)+c*delta(Suc m) <= dcol(m)+c*delta(m)
where dcol(m)=(A!(s+j))!m. Report whether it ever fails (it shouldn't),
and gather structural facts: at ascending levels, is delta(m) >= delta(Suc m)?
and dcol(m) >= dcol(Suc m) (IH)? Find the load-bearing inequality.
"""
import sys, collections
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)

seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=9000; depth=14
viol=0; chk=0; ex=[]
# case3 structural counters
c3_chk=0; c3_delta_noninc=0; c3_delta_inc=0
c3_ex=[]
nBMS=0
for d in range(depth):
    fr=[]
    for A in Q:
        if not (2<=len(A)<=44): 
            pass
        else:
            set_array(A)
            nBMS+=1
            L=len(A)
            for i in range(L):
                col=A[i]
                for m in range(len(col)-1):
                    chk+=1
                    if elem(A,i,m+1) > elem(A,i,m):
                        viol+=1
                        if len(ex)<10: ex.append((fmt(A),'i',i,'m',m))
        for n in range(1,3):
            if len(A)>38: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} BMS={nBMS} viol={viol}/{chk}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== elem antitone: {viol} viol / {chk} ===")
for e in ex: print("  BAD:",e)
