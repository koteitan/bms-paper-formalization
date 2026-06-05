"""c1: elem A i 0 = 0 ==> elem A i m = 0 (whole column zero if row0 zero).
This is the row-antitone consequence. Test independent EASIER routes:
 (R-seed/expand) c1 by BMS.induct directly:
   - seed: col0 = replicate n 0 (row0=0 => all 0 OK), col1 = replicate n 1 (row0=1, vacuous).
   - expand: column of A[n] is strip-truncation of a P-column. P-col is G-col(=A col)
     or bumped B-col. If its row0 is 0...
 Test: for a BUMPED column at idx_B(c,j), if row0 value is 0, is the whole column 0?
   bumped row0 = dcol(0) + (asc? c*delta(0):0). If =0 then dcol(0)=0 AND bump term=0.
   dcol(0)=0 => by IH(c1 on A) dcol(m)=0 all m. And if asc at 0 then... does asc at m
   imply delta term? Need: when dcol(0)=0, is the column genuinely all-zero?
 Just verify c1 holds and check the bumped-col implication empirically.
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=9000; depth=14
c1_bad=0; c1_chk=0; ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        if 2<=len(A)<=44:
            set_array(A)
            for i in range(len(A)):
                if len(A[i])>0 and elem(A,i,0)==0:
                    c1_chk+=1
                    for m in range(len(A[i])):
                        if elem(A,i,m)!=0:
                            c1_bad+=1
                            if len(ex)<10: ex.append((fmt(A),'i',i,'m',m)); 
                            break
        for n in range(1,3):
            if len(A)>38: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} c1_bad={c1_bad}/{c1_chk}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== c1 (row0=0 => col all 0): {c1_bad} viol / {c1_chk} cols-with-row0-zero ===")
for e in ex: print("  C1-BAD:",e)
