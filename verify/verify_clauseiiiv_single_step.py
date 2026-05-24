#!/usr/bin/env python3
"""
Eval-faithful empirical verification of the TWO target single-step sorries:

TARGET 1: iii_single_step_t_to_Suc_t  (diagonal block shift, src 1 block ahead of tgt)
  For BMS A, s=b0_start, m0=mpl, k<m0, i<l1, t+1<n:
    m_anc (A[n]) k (idx_B(t+1,0)) (idx_B(t,i))
      <-->
    m_anc (A[n]) k (idx_B(t+2,0)) (idx_B(t+1,i))

TARGET 2: lemma_2_5_v_clause_step_iff  (source bump n1->n1+1, target fixed at n0)
  For BMS A, s=b0_start, n>=2, k (all rows), i<l1, j<l1, n0<n1, n1<n:
    m_anc (A[n]) k (idx_B(n1,j)) (idx_B(n0,i))
      <-->
    m_anc (A[n]) k (idx_B(n1+1,j)) (idx_B(n0,i))

idx_B(t,j) = l0 + t*l1 + j  (l0 = s = b0_start).

Uses the SAME eval-faithful primitives as probe_vacuity_refute.py:
m_parent returns LARGEST valid p (= last cands), m_anc walks down by parent.
ALWAYS strip before computing b0/mpl/l1.

BFS over genuine-BMS expansions; reports violation counts with first cases.
"""
import re, subprocess
from collections import Counter
YA = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"

def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)', s)]
def fmt(A): return ''.join('('+','.join(str(x) for x in c)+')' for c in A)
def strip(A):
    if not A: return A
    h=max((len(c) for c in A),default=0)
    while h>0 and all((c[h-1] if h-1<len(c) else 0)==0 for c in A): h-=1
    return [tuple(c[:h]) for c in A]
def height(A): return max((len(c) for c in A),default=0)
def elem(A,p,r):
    if p<0 or p>=len(A): return 0
    if r<0 or r>=len(A[p]): return 0
    return A[p][r]
_MPC={}; _MISS=object()
def set_array(A): _MPC.clear()
def m_parent(A,m,i):
    key=(m,i)
    c=_MPC.get(key,_MISS)
    if c is not _MISS: return c
    res=None
    for pp in range(0,i):
        if elem(A,pp,m)>=elem(A,i,m): continue
        if m>0 and not m_anc(A,m-1,i,pp): continue
        res=pp                       # keep last => largest valid p
    _MPC[key]=res; return res
def m_anc(A,m,i,j):
    p=m_parent(A,m,i); seen=set()
    while p is not None:
        if p in seen: return False
        seen.add(p)
        if p==j: return True
        if p<j: return False
        p=m_parent(A,m,p)
    return False
def mpl(A):
    last=len(A)-1
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0(A):
    t=mpl(A)
    return None if t is None else m_parent(A,t,len(A)-1)
def l1(A):
    s=b0(A); return 0 if s is None else len(A)-1-s
def ascends(A,j,k):
    # row k of source col s+j ascends: elem A s k < elem A (s+j) k  (s=b0)
    s=b0(A)
    return elem(A,s,k) < elem(A,s+j,k)
def idxB(s,L1,t,j): return s + t*L1 + j

_ec={}
def expand(text,n):
    key=(text,n)
    if key in _ec: return _ec[key]
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        v=strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: v=None
    _ec[key]=v; return v

def is_genuine_bms(A):
    """A genuine (Bashicu standard form) BMS expands with NON-NEGATIVE entries.
       yaBMS emits negative values when the input is not in standard form /
       not a reachable BMS. Reject such arrays (they are NOT in our BMS set)."""
    if any(any(x<0 for x in c) for c in A): return False
    E=expand(fmt(A),2)
    if E is None: return False
    if any(any(x<0 for x in c) for c in E): return False
    E1=expand(fmt(A),1)
    if E1 is None or any(any(x<0 for x in c) for c in E1): return False
    return True

def check_iii(A_orig, max_n=4):
    """A_orig is the ORIGINAL (pre-expansion) BMS, stripped."""
    set_array(A_orig)
    s=b0(A_orig); m0=mpl(A_orig); L1=l1(A_orig)
    if s is None or m0 is None or L1<1: return []
    viol=[]
    for n in range(2,max_n+1):
        E=expand(fmt(A_orig),n)
        if E is None: continue
        set_array(E)
        for k in range(m0):
            for i in range(L1):
                for t in range(0,n):
                    if not (t+1<n): continue
                    src1=idxB(s,L1,t+1,0); tgt1=idxB(s,L1,t,i)
                    src2=idxB(s,L1,t+2,0); tgt2=idxB(s,L1,t+1,i)
                    if max(src1,tgt1,src2,tgt2)>=len(E): continue
                    set_array(E)
                    lhs=m_anc(E,k,src1,tgt1)
                    rhs=m_anc(E,k,src2,tgt2)
                    if lhs!=rhs:
                        viol.append(("iii",fmt(A_orig),n,k,i,t,lhs,rhs))
    return viol

def check_v(A_orig, max_n=4):
    set_array(A_orig)
    s=b0(A_orig); L1=l1(A_orig); H=height(A_orig)
    if s is None or L1<1: return []
    viol=[]
    for n in range(2,max_n+1):
        E=expand(fmt(A_orig),n)
        if E is None: continue
        # k ranges over all rows present in E (clause v has no k<m0 restriction)
        HE=height(E)
        for k in range(HE+1):
            for i in range(L1):
                for j in range(L1):
                    for n1 in range(0,n):
                        for n0 in range(0,n1):
                            if not (n0<n1 and n1<n): continue
                            src1=idxB(s,L1,n1,j); src2=idxB(s,L1,n1+1,j)
                            tgt=idxB(s,L1,n0,i)
                            if max(src1,src2,tgt)>=len(E): continue
                            set_array(E)
                            lhs=m_anc(E,k,src1,tgt)
                            rhs=m_anc(E,k,src2,tgt)
                            if lhs!=rhs:
                                viol.append(("v",fmt(A_orig),n,k,i,j,n0,n1,lhs,rhs))
    return viol

def main():
    seeds=[
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0)(1,1)(2,0)(3,1)","(0,0)(1,1)(2,0)(3,0)",
      "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,1,1)(2,0,0)","(0,0,0)(1,2,0)(1,1,1)",
      "(0,0,0)(1,1,0)(2,2,1)","(0,0,0)(1,1,1)(2,2,0)(3,3,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,1,0)","(0,0,0,0)(1,1,1,1)(2,1,1,0)",
      "(0,0)(1,1)(2,0)(1,1)","(0,0)(1,1)(2,0)(1,1)(2,0)",
      "(0,0,0)(1,1,1)(2,2,2)(3,3,0)","(0,0,0)(1,1,1)(2,2,2)(3,3,1)",
      "(0,0,0)(1,1,1)(2,2,2)(3,3,2)",
      # wide / tall / irregular seeds
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,0)","(0,0,0,0,0)(1,1,1,1,1)(2,2,2,1,0)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,1,1,0)","(0,0,0,0,0)(1,1,1,1,1)(2,1,1,1,0)",
      "(0,0)(1,1)(2,2)(3,0)","(0,0)(1,1)(2,2)(3,1)","(0,0)(1,1)(2,2)(3,3)",
      "(0,0,0)(1,1,1)(2,2,1)(3,3,0)","(0,0,0)(1,1,1)(2,2,1)(3,3,1)",
      "(0,0,0)(1,1,1)(2,2,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,0)(2,2,0)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,2)(3,3,3,0)","(0,0,0,0)(1,1,1,1)(2,2,2,2)(3,3,3,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,2)(3,3,3,2)","(0,0,0,0)(1,1,1,1)(2,2,2,2)(3,3,3,3)",
      "(0,0,0)(1,2,3)(2,3,1)","(0,0,0)(1,1,1)(2,3,1)(3,2,2)",
      "(0,0)(1,1)(0,1)(1,1)","(0,0,0)(1,1,1)(1,2,1)(2,2,2)",
    ]
    seen=set(); Q=[]; v_iii=0; v_v=0; tested=0; CAP=1600; depth=7
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    first_iii=[]; first_v=[]
    for d in range(depth):
        fr=[]
        for A in Q:
            if len(A)<=22 and is_genuine_bms(A):
                tested+=1
                vi=check_iii(A,max_n=4)
                if vi:
                    v_iii+=len(vi)
                    for x in vi[:3]:
                        if len(first_iii)<10: first_iii.append(x)
                vv=check_v(A,max_n=4)
                if vv:
                    v_v+=len(vv)
                    for x in vv[:3]:
                        if len(first_v)<10: first_v.append(x)
            for n in range(1,4):
                if len(A)>18: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"depth {d}: visited={len(seen)} tested={tested} viol_iii={v_iii} viol_v={v_v}",flush=True)
        if len(seen)>CAP: break
    print("=== TARGET 1 (iii_single_step) ===")
    print(f"  violations: {v_iii}")
    for x in first_iii: print("   ",x)
    print("=== TARGET 2 (v_clause_step_iff) ===")
    print(f"  violations: {v_v}")
    for x in first_v: print("   ",x)
    print(f"FINAL visited={len(seen)} tested={tested} viol_iii={v_iii} viol_v={v_v}")

if __name__=='__main__': main()
