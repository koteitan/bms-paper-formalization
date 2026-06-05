"""GENERAL fact (the real structural reason for delta-antitone):
For genuine BMS A, columns x,y with y an m-ancestor of x at BOTH levels m and m+1:
   (elem A x m - elem A y m) >= (elem A x (m+1) - elem A y (m+1))   [INTEGER]
If 0 viol, delta-antitone is a special case (x=C, y=s, both m-anc by m0-parent).
ALSO test the WEAKER hypothesis that suffices and may be easier:
   y is (m+1)-ancestor of x  ==>  diff antitone from m to m+1
(since ascends needs m+1<m0, and s is (m+1)-ancestor of C? no, s is m0-parent).
Actually for delta we have: s is m0-ancestor of C, hence m-anc for ALL m<=m0.
Test BOTH: (G) m-anc at m and m+1 ; (G2) (m+1)-anc of x.
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_anc, m_parent, mpl, b0, l1, set_array, expand)
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
seen=set(); Q=[]
for sd in seeds:
    A=strip(parse(sd)); kk=fmt(A)
    if kk not in seen: seen.add(kk); Q.append(A)
CAP=5000; depth=12
g_bad=0; g_chk=0; gex=[]
g2_bad=0; g2_chk=0; g2ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        if 2<=len(A)<=40:
            set_array(A)
            L=len(A); H=len(A[0]) if A else 0
            for x in range(L):
                hx=len(A[x])
                for y in range(x):
                    for m in range(min(hx,len(A[y]))-1):
                        anc_m  = m_anc(A,m,  x,y)
                        anc_m1 = m_anc(A,m+1,x,y)
                        if anc_m and anc_m1:
                            g_chk+=1
                            diff_m  = elem(A,x,m)  - elem(A,y,m)
                            diff_m1 = elem(A,x,m+1)- elem(A,y,m+1)
                            if diff_m < diff_m1:
                                g_bad+=1
                                if len(gex)<8: gex.append((fmt(A),'x',x,'y',y,'m',m))
                        if anc_m1:
                            g2_chk+=1
                            diff_m  = elem(A,x,m)  - elem(A,y,m)
                            diff_m1 = elem(A,x,m+1)- elem(A,y,m+1)
                            if diff_m < diff_m1:
                                g2_bad+=1
                                if len(g2ex)<8: g2ex.append((fmt(A),'x',x,'y',y,'m',m))
        for n in range(1,3):
            if len(A)>34: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"d{d}: vis={len(seen)} G(anc m&m+1)bad={g_bad}/{g_chk}  G2(anc m+1)bad={g2_bad}/{g2_chk}",flush=True)
    if len(seen)>CAP: break
print(f"\n=== G: m-anc at m AND m+1 => diff antitone: {g_bad}/{g_chk}")
print(f"=== G2: m-anc at m+1 => diff antitone: {g2_bad}/{g2_chk}")
for e in gex: print("  G-BAD:",e)
for e in g2ex: print("  G2-BAD:",e)
