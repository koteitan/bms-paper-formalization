#!/usr/bin/env python3
"""
Bigger/deeper hunt for OFF-CHAIN interior columns to test the conjecture:
  off-chain (interior s+j, 0<m<t, s+j NOT (m-1)-ancestor of C)
     ==>  elem A s m = 0   AND   elem A (s+j) m > 0.
Report ALL off-chain instances with the full s-column and (s+j)-column.
Use memoized m_parent; many diverse seeds; deeper BFS.
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,height,m_parent,
    m_anc,mpl,b0,l1,set_array,expand)

def last(A): return len(A)-1

def main():
    seeds=[
      "(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0,0,0,0,0)(1,1,1,1,1,1)",
      "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,1,1)(2,0,0)","(0,0,0)(1,2,0)(1,1,1)",
      "(0,0,0)(1,2,1)(2,1,1)","(0,0,0)(1,1,0)(2,2,1)","(0,0,0)(1,2,2)(2,1,0)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,1,0)","(0,0,0,0)(1,1,1,1)(2,2,1,1)",
      "(0,0,0,0)(1,1,1,1)(2,1,1,0)","(0,0,0,0)(1,2,0,0)(1,1,1,1)",
      "(0,0,0,0)(1,2,3,0)(2,1,1,1)","(0,0,0,0)(1,1,1,1)(2,3,2,0)(3,2,1,1)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,0)","(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,1)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,1,0)",
    ]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    off=0; conj_ok=0; conj_bad=0; ex=[]
    CAP=2500
    for d in range(6):
        fr=[]
        for A in Q:
            set_array(A); s=b0(A); t=mpl(A); L1=l1(A); C=last(A)
            if s is not None and t is not None and t>=2 and L1>=2 and len(A)<=40:
                for j in range(1,L1):
                    col=s+j
                    for m in range(1,t):
                        if m_anc(A,m-1,C,col): continue
                        off+=1
                        es=elem(A,s,m); ec=elem(A,col,m)
                        if es==0 and ec>0: conj_ok+=1
                        else:
                            conj_bad+=1
                            if len(ex)<20: ex.append((fmt(A),s,t,j,m,es,ec,A[s],A[col]))
            set_array(A)
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"  depth {d}: visited={len(seen)} off-chain={off} conj_ok={conj_ok} conj_bad={conj_bad}",flush=True)
        if len(seen)>CAP: break
    print(f"FINAL off-chain={off}  (es=0 & ec>0)_ok={conj_ok}  conj_bad={conj_bad}",flush=True)
    for e in ex: print("  conj BAD (A,s,t,j,m,elem_s,elem_sj,col_s,col_sj):",e)

if __name__=='__main__': main()
