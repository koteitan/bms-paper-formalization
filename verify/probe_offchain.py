#!/usr/bin/env python3
"""
Characterize the OFF-CHAIN interior columns (the residual gap of
elem_lt_below_t at m>0): interior s+j (0<j<l1), level m with 0<m<t, such that
s+j is NOT an (m-1)-ancestor of C (last column).  For these, elem_lt holds
(vacuity) but SM(i=C) doesn't apply.  We ask whether there's a clean handle:

  - is elem A s m == 0  (s degenerate/minimal at level m)?  [trivial handle]
  - is elem A s m == min over all columns at level m?
  - does s+j become an (m-1')-ancestor of C at some OTHER level m-1' ?
  - is s+j an m'-ancestor of C's m-parent chain at level m (not m-1)?

Report counts + samples of genuine off-chain cases.
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,height,m_parent,
    m_anc,mpl,b0,l1,set_array,expand)

def last(A): return len(A)-1

def main():
    seeds=["(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
           "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
           "(0,0,0,0)(1,1,1,1)(2,2,1,0)","(0,0,0)(1,2,0)(1,1,1)",
           "(0,0,0)(1,2,1)(2,1,1)","(0,0,0,0)(1,1,1,1)(2,2,1,1)"]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    offchain=0; s_zero=0; s_globalmin=0; sj_anc_other_lvl=0; samples=[]
    CAP=900
    for d in range(4):
        fr=[]
        for A in Q:
            set_array(A); s=b0(A); t=mpl(A); L1=l1(A); C=last(A)
            if s is not None and t is not None and t>=2 and L1>=2:
                for j in range(1,L1):
                    col=s+j
                    for m in range(1,t):
                        if m_anc(A,m-1,C,col): continue   # on-chain (SM covers)
                        # genuine off-chain (and elem_lt must hold by vacuity)
                        if not (elem(A,s,m)<elem(A,col,m)):
                            continue  # shouldn't happen
                        offchain+=1
                        if elem(A,s,m)==0: s_zero+=1
                        colmin=min(elem(A,cc,m) for cc in range(len(A)))
                        if elem(A,s,m)==colmin: s_globalmin+=1
                        # does col become (m-1')-ancestor of C at some other level?
                        other=any(m_anc(A,mm,C,col) for mm in range(0,t))
                        if other: sj_anc_other_lvl+=1
                        if len(samples)<20:
                            samples.append((fmt(A),s,t,j,m,elem(A,s,m),elem(A,col,m),
                                            f"szero={elem(A,s,m)==0}",f"gmin={elem(A,s,m)==colmin}",
                                            f"ancOther={other}"))
            set_array(A)
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        if len(seen)>CAP: break
    print(f"genuine off-chain instances: {offchain}")
    print(f"  of which s degenerate (elem A s m == 0): {s_zero}")
    print(f"  of which s is global col-min at level m: {s_globalmin}")
    print(f"  of which s+j is m''-ancestor of C at SOME level: {sj_anc_other_lvl}")
    print("samples (A,s,t,j,m,elem_s,elem_sj,...):")
    for x in samples: print("  ",x)

if __name__=='__main__': main()
