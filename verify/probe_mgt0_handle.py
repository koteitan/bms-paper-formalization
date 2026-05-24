#!/usr/bin/env python3
"""
Hunt for a NON-CIRCULAR handle on elem_lt_below_t at m>0.

For A in BMS, s=b0_start, t=mpl (t>=2), interior s+j (0<j<l1), level m (0<m<t):
test candidate structural properties that, combined with a (provable)
strict-min-over-ancestors lemma, could yield elem A s m < elem A (s+j) m
WITHOUT the level-m ancestor<->elem circularity:

  P_a: m_ancestor A (m-1) C (s+j)        [interior col is (m-1)-ancestor of C]
  P_a0: m_ancestor A 0 C (s+j)           [interior col is 0-ancestor of C]
  P_b: m_parent A m (s+j) is not None and >= s   [m-parent of s+j >= s]
  P_chainC: s+j lies on the m-parent chain of C (i.e. m_ancestor A m C (s+j))

Also test the candidate strict-min-over-(m-1)-ancestors lemma:
  SM: m_ancestor A m C s  AND  m_ancestor A (m-1) C c  AND s<c<C
      ==>  elem A s m < elem A c m
(this is the level-m analog of m_anc_zero_imp_strict_min, restricted to
 (m-1)-ancestors of C).  If SM holds AND P_a holds, m>0 closes.
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
           "(0,0,0,0)(1,1,1,1)(2,2,1,0)","(0,0,0)(1,2,0)(1,1,1)"]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    pa_ok=pa_bad=0; pa0_ok=pa0_bad=0; pb_ok=pb_bad=0; chain_ok=chain_bad=0
    sm_ok=sm_bad=0; sm_checked=0
    pa_bad_ex=[]; sm_bad_ex=[]
    CAP=700
    for d in range(4):
        fr=[]
        for A in Q:
            set_array(A); s=b0(A); t=mpl(A); L1=l1(A); C=last(A)
            if s is not None and t is not None and t>=2 and L1>=2:
                for j in range(1,L1):
                    col=s+j
                    for m in range(1,t):
                        # P_a
                        if m_anc(A,m-1,C,col): pa_ok+=1
                        else:
                            pa_bad+=1
                            if len(pa_bad_ex)<6: pa_bad_ex.append((fmt(A),s,t,col,m))
                        # P_a0
                        if m_anc(A,0,C,col): pa0_ok+=1
                        else: pa0_bad+=1
                        # P_b
                        p=m_parent(A,m,col)
                        if p is not None and p>=s: pb_ok+=1
                        else: pb_bad+=1
                        # P_chainC
                        if m_anc(A,m,C,col): chain_ok+=1
                        else: chain_bad+=1
                # SM test: for s m-ancestor of C, c an (m-1)-ancestor of C in (s,C)
                for m in range(1,t):
                    if not m_anc(A,m,C,s): continue
                    for c in range(s+1,C):
                        if m_anc(A,m-1,C,c):
                            sm_checked+=1
                            if elem(A,s,m)<elem(A,c,m): sm_ok+=1
                            else:
                                sm_bad+=1
                                if len(sm_bad_ex)<6: sm_bad_ex.append((fmt(A),s,m,c,elem(A,s,m),elem(A,c,m)))
            set_array(A)
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        if len(seen)>CAP: break
    print(f"P_a (interior is (m-1)-anc of C): ok={pa_ok} bad={pa_bad}")
    for e in pa_bad_ex: print("   P_a bad (A,s,t,col,m):",e)
    print(f"P_a0 (interior is 0-anc of C): ok={pa0_ok} bad={pa0_bad}")
    print(f"P_b (m-parent of s+j >= s): ok={pb_ok} bad={pb_bad}")
    print(f"P_chainC (s+j is m-anc of C): ok={chain_ok} bad={chain_bad}")
    print(f"SM (s dominates (m-1)-ancestors of C at level m): checked={sm_checked} ok={sm_ok} bad={sm_bad}")
    for e in sm_bad_ex: print("   SM bad (A,s,m,c,elem_s,elem_c):",e)

if __name__=='__main__': main()
