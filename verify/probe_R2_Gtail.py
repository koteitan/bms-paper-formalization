#!/usr/bin/env python3
"""
DESIGN probe for CORE-B / the R2 branch of the joint induction (careful, per
doc/verification_pitfalls.md: strip via expand; MECE; deep BFS; genuine seeds;
yaBMS=Hunter eval-confirmed).

R2 case: b0_start(A[n]) = s' < l0(A) (in the G-prefix). Design-regime guard:
l1(A[n]) >= 2 AND mpl(A[n]) = t' >= 1. The needed DOM(A[n]) over the G'-tail
columns (s' < s'+j < l0 A, verbatim A G-columns by M1) is, after M1 rewrite,
   elem A s' m < elem A (s'+j) m   for m < t'.    [G'-tail domination, claim P]
QUESTION: is P EXPLAINED by  m_ancestor A m (s'+j) s'  (s' is an A-m-ancestor of
the later A-G-column s'+j) [claim Q]? If Q holds wherever P is needed, then
R2/G'-tail reduces to the ancestry fact Q (m_ancestor_elem_lt then gives P),
which may be clause-(i)/gateway-derivable. Report violations of P and of (P=>Q).
Also report whether s' relates to b0_start(A) (is s' itself a known bad-root?).
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand, height)

def main():
    seeds = [
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0,0)(1,1,1)(2,2,2)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,0)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,1,0)(2,2,1)",
      "(0,0)(1,1)(2,2)","(0,0)(1,1)(2,2)(3,1)","(0,0)(1,1)(2,2)(3,3)",
    ]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=6000; depth=11
    r2_cases=0; checks=0
    P_viol=0; PQ_viol=0   # P=domination fails; P holds but Q(ancestry) fails
    sprime_is_b0A=0; sprime_total=0
    ex=[]
    for d in range(depth):
        fr=[]
        for A in Q:
            set_array(A); sA=b0(A); lA=l1(A); l0A=sA
            if sA is not None and lA>=1 and len(A)<=40:
                for n in range(1,4):
                    E=expand(fmt(A),n);
                    if E is None: continue
                    set_array(E); sp=b0(E); tp=mpl(E); lp=l1(E)
                    set_array(A)
                    if sp is None or tp is None: continue
                    # design-regime R2: l1(E)>=2, mpl(E)>=1, b0(E) in G' (< l0A)
                    if not (lp>=2 and tp>=1 and sp<l0A): continue
                    r2_cases+=1; sprime_total+=1
                    if sp==sA: sprime_is_b0A+=1
                    # G'-tail interior columns: sp < sp+j < l0A (verbatim A G-cols)
                    for col in range(sp+1, l0A):
                        j=col-sp
                        if col>=len(A): break
                        for m in range(0,tp):
                            if m>=len(A[sp]) or m>=len(A[col]): continue
                            checks+=1
                            P = elem(A,sp,m) < elem(A,col,m)
                            if not P:
                                P_viol+=1
                                if len(ex)<8: ex.append(('P',fmt(A),n,sp,col,m))
                                continue
                            Qok = m_anc(A,m,col,sp)
                            if not Qok:
                                PQ_viol+=1
                                if len(ex)<12: ex.append(('PQ',fmt(A),n,sp,col,m))
            for n in range(1,4):
                if len(A)>35: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"  depth {d}: visited={len(seen)} R2cases={r2_cases} checks={checks} Pviol={P_viol} PQviol={PQ_viol}",flush=True)
        if len(seen)>CAP: break
    print(f"\nR2 design-regime cases={r2_cases}  G'-tail checks={checks}")
    print(f"  P (G'-tail domination elem A s' m < elem A (s'+j) m) violations = {P_viol}")
    print(f"  P-holds-but-Q-fails (s' NOT an A-m-ancestor of s'+j) = {PQviol if False else PQ_viol}")
    print(f"  s'==b0_start(A): {sprime_is_b0A}/{sprime_total}")
    print("  (P_viol=0 => G'-tail domination always holds; PQ_viol=0 => it reduces to ancestry Q)")
    for e in ex: print("   ",e)

if __name__=='__main__': main()
