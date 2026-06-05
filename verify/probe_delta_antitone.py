"""Structural crux for case3. For genuine BMS A with b0=Some s, mpl=Some m0:
 (Q1) Is delta antitone where BOTH m, Suc m ascend (for some B0 col j)?
      i.e. delta(Suc m) <= delta(m)?   [c3_delta]
 (Q2) Simpler: is delta antitone for all m with Suc m < m0 (both ascend at the
      first B0 col, which is ancestor-of-itself)? delta(m)=elem A C m - elem A s m.
 (Q3) Even simpler GLOBAL: is delta(Suc m) <= delta(m) for ALL m < m0-1
      i.e. is the function m -> (elem A C m - elem A s m) antitone on [0,m0)?
 Print violation counts. delta antitone on ascending range => case3 trivial.
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)

def delta(A,s,C,m):
    return elem(A,C,m)-elem(A,s,m)

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=9000; depth=14
q3_chk=0; q3_bad=0; q3ex=[]
nB=0
for d in range(depth):
    fr=[]
    for A in Q:
        if 2<=len(A)<=44:
            set_array(A); s=b0(A); t=mpl(A)
            if s is not None and t is not None:
                C=len(A)-1; m0=t
                for m in range(0, m0-1):
                    # need m+1 < m0 ; both in ascending range for first col
                    q3_chk+=1
                    dm=delta(A,s,C,m); dm1=delta(A,s,C,m+1)
                    if dm1> dm:
                        q3_bad+=1
                        if len(q3ex)<12: q3ex.append((fmt(A),'s',s,'C',C,'m',m,'dm',dm,'dm1',dm1))
            nB+=1
        for n in range(1,3):
            if len(A)>38: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} q3_bad={q3_bad}/{q3_chk}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== delta antitone on [0,m0): {q3_bad} viol / {q3_chk} ===")
for e in q3ex: print("  DELTA-BAD:",e)
