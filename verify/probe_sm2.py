#!/usr/bin/env python3
"""
Test candidate SM2 (would close off-chain if true):
  s is m'-ancestor of x (s<x)  ==>  elem A s (Suc m') < elem A x (Suc m')
i.e. m'-ancestry implies strict domination at the NEXT level Suc m'.
(General A in BMS; s,x arbitrary columns, not just bad-root/interior.)

Also test the RESTRICTED form that's actually needed for off-chain:
  SM2r: A in BMS, s=b0_start, t=mpl, Suc m' < t, x interior (s<x<C=s+l1),
        m_ancestor A m' x s  ==>  elem A s (Suc m') < elem A x (Suc m').
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_parent,
    m_anc,mpl,b0,l1,set_array,expand)

def last(A): return len(A)-1

def main():
    seeds=["(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
           "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,1,1,1)(2,2,1,0)"]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    sm2_ok=sm2_bad=0; sm2r_ok=sm2r_bad=0; ex2=[]; ex2r=[]
    CAP=600
    for d in range(4):
        fr=[]
        for A in Q:
            set_array(A); H=max((len(c) for c in A),default=0); N=len(A)
            # SM2 general: for all s<x, all m' with Suc m'<H, if m_anc A m' x s then check
            for x in range(N):
                for s in range(x):
                    for mp_ in range(0, H-1):  # m'=mp_, Suc m'=mp_+1 < H
                        if m_anc(A,mp_,x,s):
                            if elem(A,s,mp_+1) < elem(A,x,mp_+1): sm2_ok+=1
                            else:
                                sm2_bad+=1
                                if len(ex2)<8: ex2.append((fmt(A),s,x,mp_,elem(A,s,mp_+1),elem(A,x,mp_+1)))
            # SM2r restricted to bad-root/interior
            s=b0(A); t=mpl(A); L1=l1(A); C=last(A)
            if s is not None and t is not None and t>=2 and L1>=2:
                for j in range(1,L1):
                    x=s+j
                    for mp_ in range(0,t-1):  # Suc m'=mp_+1 < t
                        if m_anc(A,mp_,x,s):
                            if elem(A,s,mp_+1) < elem(A,x,mp_+1): sm2r_ok+=1
                            else:
                                sm2r_bad+=1
                                if len(ex2r)<8: ex2r.append((fmt(A),s,x,mp_,elem(A,s,mp_+1),elem(A,x,mp_+1)))
            set_array(A)
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        if len(seen)>CAP: break
    print(f"SM2 general (m'-anc => dominate at Suc m'): ok={sm2_ok} bad={sm2_bad}")
    for e in ex2: print("   SM2 bad (A,s,x,m',elem_s_Sm,elem_x_Sm):",e)
    print(f"SM2r restricted (bad-root, interior, Suc m'<t): ok={sm2r_ok} bad={sm2r_bad}")
    for e in ex2r: print("   SM2r bad:",e)

if __name__=='__main__': main()
