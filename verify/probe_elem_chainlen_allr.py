#!/usr/bin/env python3
"""Probe: does elem A i r = Suc(elem A p r) where p = m_parent A r i hold for r>0?
(The row-0 invariant bms_row0_eq_chainlen0 generalized to all rows.)
Strip-correct. If TRUE universally it'd be a BMS.induct-friendly invariant
that directly yields elem A s r < elem A (s+j) r whenever s is an r-ancestor.
Also probe a WEAKER fact actually needed:
  (M) for r<=t, s=b0_start, 0<j<l1:  elem A s r < elem A (s+j) r  (the goal)
and separately whether the *raw* monotonicity elem A (s+j) r as function of j
is nondecreasing for r<=t (would combine with last-col fact).
"""
import re, subprocess
YA = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"
def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)', s)]
def fmt(A):
    return ''.join('('+','.join(str(x) for x in c)+')' for c in A)
def strip(A):
    if not A: return A
    h = max((len(c) for c in A), default=0)
    while h > 0 and all((c[h-1] if h-1 < len(c) else 0) == 0 for c in A):
        h -= 1
    return [tuple(c[:h]) for c in A]
def elem(A,p,r):
    if p<0 or p>=len(A): return 0
    if r<0 or r>=len(A[p]): return 0
    return A[p][r]
def height(A): return max((len(c) for c in A), default=0)
def m_parent(A,m,i):
    res=None
    for pp in range(0,i):
        if elem(A,pp,m)>=elem(A,i,m): continue
        if m>0 and not m_anc(A,m-1,i,pp): continue
        res=pp
    return res
def m_anc(A,m,i,j):
    p=m_parent(A,m,i); seen=set()
    while p is not None:
        if p in seen: return False
        seen.add(p)
        if p==j: return True
        if p<j: return False
        p=m_parent(A,m,p)
    return False
def max_parent_level(A):
    last=len(A)-1
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0_start(A):
    t=max_parent_level(A)
    if t is None: return None
    return m_parent(A,t,len(A)-1)
def l1(A):
    s=b0_start(A)
    if s is None: return 0
    return len(A)-1-s
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def check(A):
    H=height(A)
    chainlen_fail=0; mono_fail=0; chainlen_ex=None; mono_ex=None
    # (CL) chain-length invariant at all rows
    for i in range(len(A)):
        for r in range(len(A[i])):
            p=m_parent(A,r,i)
            lhs=elem(A,i,r)
            rhs=0 if p is None else 1+elem(A,p,r)
            if lhs!=rhs:
                chainlen_fail+=1
                if chainlen_ex is None: chainlen_ex=(i,r,lhs,rhs,p)
    # (MONO) elem A (s+j) r nondecreasing in j for r<=t
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is not None and t>0 and s is not None and L1>=2:
        for r in range(t+1):
            for j in range(L1):
                if elem(A,s+j,r) > elem(A,s+j+1,r) if (s+j+1<=s+L1) else False:
                    pass
            # nondecreasing across s..s+L1 (incl C=s+L1)
            vals=[elem(A,s+x,r) for x in range(L1+1)]
            for a in range(len(vals)-1):
                if vals[a]>vals[a+1]:
                    mono_fail+=1
                    if mono_ex is None: mono_ex=(r,a,vals)
                    break
    return chainlen_fail,mono_fail,chainlen_ex,mono_ex

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0; clf=0; mf=0; CAP=2500; clex=None; mex=None
    for seed in seeds:
        if len(visited)>CAP: break
        q=[strip(parse(seed))]; visited.add(fmt(q[0]))
        for d in range(4):
            nq=[]
            for A in q:
                for n in range(1,4):
                    ex=expand(fmt(A),n)
                    if ex is None: continue
                    key=fmt(ex)
                    if key in visited: continue
                    visited.add(key); nq.append(ex)
                    cf,mff,ce,me=check(ex); tested+=1
                    if cf:
                        clf+=1
                        if clex is None: clex=(key,ce)
                    if mff:
                        mf+=1
                        if mex is None: mex=(key,me)
            q=nq
            if len(visited)>CAP: break
    print(f"Tested {tested} stripped BMS.")
    print(f"(CL) elem A i r = Suc(elem A p r) [all rows] fails: {clf}")
    if clex: print(f"   CL-ex {clex[0]}: (i,r,lhs,rhs,p)={clex[1]}")
    print(f"(MONO) elem A (s+x) r nondecreasing in x (r<=t) fails: {mf}")
    if mex: print(f"   MONO-ex {mex[0]}: (r,a,vals)={mex[1]}")
if __name__=='__main__': main()
