#!/usr/bin/env python3
"""
Verify the STRICT-BELOW-t domination (the proposed clean foundation for the
case-B leaf of Lemma 2.5 (ii)):

  D(A):  A in BMS, max_parent_level A = Some t, s=b0_start A,
         0<j<l1(A), m<t   ==>   elem A s m < elem A (s+j) m.

This is the m<t (STRICT) restriction of the machine-checked-FALSE elem_lt
(which was m<=t and fails at m=t; cex E=(0,0)(1,1)(2,0)(1,1)(1,1), t=1,
violation at m=t=1).  We test whether the m<t version is genuinely true.

Also verify the equivalent ancestry form V(A) (vacuity of case-B):
  m_ancestor A m (s+j) s  for 0<j<l1, m<t.

Section-10 discipline: deep+wide BFS over many seeds AND structurally
targeted plateau / elem_lt-cex-family candidates.  Report ANY violation.
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_caseB_vacuity import (parse,fmt,strip,elem,height,m_parent,
    m_anc,max_parent_level,b0_start,l1,nsanc,ascends,expand,collect)

def viol_D(A):
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or s is None: return []
    out=[]
    for j in range(1,L1):
        for m in range(0,t):
            if not (elem(A,s,m) < elem(A,s+j,m)): out.append(('D',j,m,elem(A,s,m),elem(A,s+j,m)))
    return out

def viol_V(A):
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or s is None: return []
    out=[]
    for j in range(1,L1):
        for m in range(0,t):
            if not m_anc(A,m,s+j,s): out.append(('V',j,m))
    return out

def run(arrays,label):
    cD=cV=nD=nV=0; exD=[]; exV=[]
    for A in arrays:
        if len(A)>34: continue
        t=max_parent_level(A)
        if t is None or t<2: continue
        nD+=1; nV+=1
        vd=viol_D(A); vv=viol_V(A)
        if vd: cD+=1;  exD.append((fmt(A),t,b0_start(A),l1(A),vd[:5])) if len(exD)<12 else None
        if vv: cV+=1;  exV.append((fmt(A),t,b0_start(A),l1(A),vv[:5])) if len(exV)<12 else None
    print(f"[{label}] t>=2 arrays={nD}  D-violations={cD}  V-violations={cV}",flush=True)
    for e in exD: print("   D VIOL:",e)
    for e in exV: print("   V VIOL:",e)

def main():
    targets=["(0,0)(1,1)(2,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(1,1)(1,1)",
             "(0,0,0)(1,1,1)(2,2,0)(1,1,1)(2,2,0)",
             "(0,0,0)(1,1,1)(2,2,0)(3,3,1)(4,4,0)",
             "(0,0,0)(1,1,1)(2,2,2)(3,3,0)(4,4,1)",
             "(0,0,0)(1,2,1)(2,1,1)(3,3,0)",
             "(0,0,0)(1,1,1)(2,2,1)(3,1,0)",
             "(0,0,0,0)(1,1,1,1)(2,2,2,0)(3,3,3,1)(4,4,4,0)",
             "(0,0,0,0)(1,1,1,1)(2,2,2,2)(3,3,3,0)(4,4,4,1)"]
    cand=set()
    for tg in targets:
        cand.add(fmt(strip(parse(tg))))
        for n in range(1,4):
            E=expand(tg,n)
            if E is not None: cand.add(fmt(E))
    run([strip(parse(c)) for c in sorted(cand)],"targeted")

    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0,0,0)(1,1,1,1,1)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,2)",
           "(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,2,0)(1,1,1)",
           "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,2)"]
    run(collect(seeds,CAP=700,depth=4),"BFS")

if __name__=='__main__': main()
