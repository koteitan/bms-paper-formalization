"""WHY is delta antitone on [0,m0)? delta(m)=elem A C m - elem A s m (nat sub).
delta(m)>=delta(Suc m) i.e. (Cm - sm) >= (C(m+1) - s(m+1)) in NAT.
Hypotheses to test (for m, m+1 < m0, s=b0, C=last):
 H_int:  Cm>=sm AND C(m+1)>=s(m+1)  (delta_pos: both true since m,m+1<m0)
 Then over integers delta_int(m)=Cm-sm >=0. Test integer antitone:
   (Cm-sm) - (C(m+1)-s(m+1)) >= 0  as INTEGER  <=> (Cm-C(m+1)) >= (sm-s(m+1)).
 i.e. C drops at least as much as s, per level, on [0,m0).  [dropC >= drops]
Report: integer delta antitone bad count, and dropC>=drops bad count.
Also: are Cm>=sm strictly (>) for m<m0? (delta_pos says yes).
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
dint_bad=0; drop_bad=0; pos_bad=0; chk=0; ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        if 2<=len(A)<=44:
            set_array(A); s=b0(A); t=mpl(A)
            if s is not None and t is not None:
                C=len(A)-1; m0=t
                for m in range(0, m0):
                    Cm=elem(A,C,m); sm=elem(A,s,m)
                    if not (Cm>sm): pos_bad+=1
                for m in range(0, m0-1):
                    chk+=1
                    Cm=elem(A,C,m); sm=elem(A,s,m)
                    C1=elem(A,C,m+1); s1=elem(A,s,m+1)
                    # integer delta antitone
                    if (Cm-sm) < (C1-s1): dint_bad+=1
                    # dropC>=drops
                    if (Cm-C1) < (sm-s1):
                        drop_bad+=1
                        if len(ex)<12: ex.append((fmt(A),'m',m,'Cm',Cm,'C1',C1,'sm',sm,'s1',s1))
        for n in range(1,3):
            if len(A)>38: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} dint_bad={dint_bad} drop_bad={drop_bad} pos_bad={pos_bad} /{chk}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== integer delta antitone bad={dint_bad}, dropC>=drops bad={drop_bad}, Cm>sm bad={pos_bad} / chk {chk} ===")
for e in ex: print("  DROP-BAD:",e)
