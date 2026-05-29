#!/usr/bin/env python3
"""
Probe for the candidate lemma m_parent_AEn_idx_B_col0_block_shift.

Claim (to verify exact c-range):
  for A in BMS, A!=[], b0_start A = Some s, 0 < l1 A, Suc c <= n,
      k < keep_of(G@Bs):
    m_parent (A[n]) k (idx_B(Suc c, 0))
      = (case m_parent (A[n]) k (idx_B(c,0)) of
           None  => None
         | Some q => if q < l0 then Some q else Some (q + l1))
  where idx_B(t,j) = l0 + t*l1 + j, l0 = s (= b0_start).

Eval-faithful primitives copied from verify_clauseiiiv_single_step.py.
GENUINE 2-col seeds + BFS via expand; strip-correct.
Reports: violations per (c, k-regime), total tested triples.
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
        res=pp
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
def idxB(s,L1,t,j): return s + t*L1 + j

# keep_of model: strip cutoff = number of rows kept = height(strip(P)).
# Since our expand() already strips, keep_of of the pre-strip P equals
# height(E) where E = expand-stripped. We test k < height(E).

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
    if any(any(x<0 for x in c) for c in A): return False
    E=expand(fmt(A),2)
    if E is None: return False
    if any(any(x<0 for x in c) for c in E): return False
    E1=expand(fmt(A),1)
    if E1 is None or any(any(x<0 for x in c) for c in E1): return False
    return True

def check(A_orig, max_n=4):
    set_array(A_orig)
    s=b0(A_orig)            # = l0
    L1=l1(A_orig)
    m0=mpl(A_orig)
    if s is None or L1<1: return Counter(), Counter(), []
    l0=s
    tested=Counter(); viol=Counter(); examples=[]
    for n in range(1,max_n+1):
        E=expand(fmt(A_orig),n)
        if E is None: continue
        HE=height(E)
        for c in range(0,n):          # Suc c <= n  <=>  c <= n-1  <=>  c < n
            srcC=idxB(l0,L1,c,0)
            srcS=idxB(l0,L1,c+1,0)
            if max(srcC,srcS)>=len(E): continue
            for k in range(0,HE):     # k < keep_of ~ k < height(E)
                set_array(E)
                pc=m_parent(E,k,srcC)
                ps=m_parent(E,k,srcS)
                # predicted
                if pc is None:
                    pred=None
                elif pc<l0:
                    pred=pc
                else:
                    pred=pc+L1
                regime=("c0" if c==0 else "cge1")+("/G" if (pc is not None and pc<l0) else ("/B" if pc is not None else "/None"))
                tested[regime]+=1
                if ps!=pred:
                    viol[regime]+=1
                    if len(examples)<12:
                        examples.append((fmt(A_orig),n,c,k,pc,ps,pred,l0,L1))
    return tested, viol, examples

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
    seen=set(); Q=[]; tested=Counter(); viol=Counter(); examples=[]; ntested=0
    CAP=1600; depth=7
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    for d in range(depth):
        fr=[]
        for A in Q:
            if len(A)<=22 and is_genuine_bms(A):
                ntested+=1
                t,v,ex=check(A,max_n=4)
                tested+=t; viol+=v
                for x in ex:
                    if len(examples)<12: examples.append(x)
            for n in range(1,4):
                if len(A)>18: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"depth {d}: visited={len(seen)} tested={ntested} totviol={sum(viol.values())}",flush=True)
        if len(seen)>CAP: break
    print("=== col0_block_shift probe ===")
    print("tested per regime:", dict(tested))
    print("viol   per regime:", dict(viol))
    print("first violation examples (A,n,c,k,pc,ps,pred,l0,L1):")
    for x in examples: print("   ",x)
    print(f"FINAL visited={len(seen)} arrays_tested={ntested} total_triples={sum(tested.values())} total_viol={sum(viol.values())}")

if __name__=='__main__': main()
