#!/usr/bin/env python3
"""
AGGRESSIVE refutation hunt for the vacuity / elem_lt_below_t claim:

  V(A): A in BMS, mpl A = Some t (t>=2), s=b0_start, 0<j<l1, m<t
        ==> ascends A j m  (equivalently m_ancestor A m (s+j) s,
                            equivalently elem A s m < elem A (s+j) m).

Hunter treats case-B (k<m0, j does NOT ascend) as a REAL case in the
Lemma 2.5 (ii) proof, which suggests V might be FALSE (a section-10
coverage-gap false-positive in the earlier 246-BMS check).  We hunt hard:
many seeds (incl. wide/tall and irregular ones), deep BFS, large arrays,
and report the FIRST violations with full detail.
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
def elem(A,p,r):
    if p<0 or p>=len(A): return 0
    if r<0 or r>=len(A[p]): return 0
    return A[p][r]
def height(A): return max((len(c) for c in A),default=0)
_MPC={}; _MISS=object()  # per-array m_parent cache; reset via set_array
def set_array(A):
    _MPC.clear()
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
_ec={}
def expand(text,n):
    k=(text,n)
    if k in _ec: return _ec[k]
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        v=strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: v=None
    _ec[k]=v; return v

def check(A):
    set_array(A)
    t=mpl(A); s=b0(A); L1=l1(A)
    if t is None or s is None or t<2 or L1<2: return []
    out=[]
    for j in range(1,L1):
        for m in range(0,t):
            if not (elem(A,s,m) < elem(A,s+j,m)):
                out.append((j,m,elem(A,s,m),elem(A,s+j,m), m_anc(A,m,s+j,s)))
    return out

def main():
    seeds=[
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0,0,0,0,0)(1,1,1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0)(1,1)(2,0)(3,1)","(0,0)(1,1)(2,0)(3,0)",
      "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,1,1)(2,0,0)","(0,0,0)(1,2,0)(1,1,1)",
      "(0,0,0)(1,1,0)(2,2,1)","(0,0,0)(1,1,1)(2,2,0)(3,3,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,2)","(0,0,0,0)(1,1,1,1)(2,2,1,0)",
      "(0,0,0,0)(1,1,1,1)(2,2,1,1)","(0,0,0,0)(1,1,1,1)(2,1,1,0)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,0)","(0,0,0,0,0)(1,1,1,1,1)(2,2,2,2,1)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,1,0)",
    ]
    seen=set(); tge2=0; viol=0
    Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=2000; depth=7
    for d in range(depth):
        fr=[]
        for A in Q:
            set_array(A)
            if len(A)<=40 and mpl(A) is not None and mpl(A)>=2 and l1(A)>=2:
                tge2+=1
                vs=check(A)
                if vs:
                    viol+=1
                    if viol<=25:
                        print(f"  VIOL A={fmt(A)} t={mpl(A)} s={b0(A)} l1={l1(A)} {vs[:8]}",flush=True)
            for n in range(1,4):
                if len(A)>30: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"  depth {d}: visited={len(seen)} checked={tge2} viol={viol}",flush=True)
        if len(seen)>CAP: break
    print(f"FINAL visited={len(seen)} checked(t>=2,l1>=2)={tge2} VIOLATIONS={viol}",flush=True)

if __name__=='__main__': main()
