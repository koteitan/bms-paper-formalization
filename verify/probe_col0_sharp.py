#!/usr/bin/env python3
"""
Sharp hypothesis for the col0 source parent (c>=1, Suc c<=n, k<height):
  Let pc = m_parent(A[n], k, idx_B(c,0)), ps = m_parent(A[n], k, idx_B(c+1,0)).
  H1: ps == idx_B(c,0)  whenever idx_B(c,0) is a valid candidate of idx_B(c+1,0)
      i.e. elem(idx_B(c,0),k)<elem(idx_B(c+1,0),k) and (k==0 or m_anc(...))
  H2 (fallback): when idx_B(c,0) NOT a valid candidate, ps == (pred from pc).
Also tabulate: does m_parent(idx_B(c+1,0)) == idx_B(c,0) ALWAYS (c>=1)?
"""
import re, subprocess
from collections import Counter
YA="/home/koteitan/bms-paper/tmp/yaBMS/c/bms"
def parse(s): return [tuple(int(x) for x in m.group(1).split(',') if x.strip()) for m in re.finditer(r'\(([^)]*)\)',s)]
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
_MPC={};_MISS=object()
def set_array(A): _MPC.clear()
def m_parent(A,m,i):
    key=(m,i);c=_MPC.get(key,_MISS)
    if c is not _MISS: return c
    res=None
    for pp in range(0,i):
        if elem(A,pp,m)>=elem(A,i,m): continue
        if m>0 and not m_anc(A,m-1,i,pp): continue
        res=pp
    _MPC[key]=res; return res
def m_anc(A,m,i,j):
    p=m_parent(A,m,i);seen=set()
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
    t=mpl(A);return None if t is None else m_parent(A,t,len(A)-1)
def l1(A):
    s=b0(A);return 0 if s is None else len(A)-1-s
def idxB(s,L1,t,j): return s+t*L1+j
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
    if E is None or any(any(x<0 for x in c) for c in E): return False
    E1=expand(fmt(A),1)
    if E1 is None or any(any(x<0 for x in c) for c in E1): return False
    return True
def check(A):
    set_array(A);s=b0(A);L1=l1(A)
    if s is None or L1<1: return Counter()
    l0=s;v=Counter()
    for n in range(1,5):
        E=expand(fmt(A),n)
        if E is None: continue
        HE=height(E)
        for c in range(1,n):
            iC=idxB(l0,L1,c,0); iS=idxB(l0,L1,c+1,0)
            if max(iC,iS)>=len(E): continue
            for k in range(0,HE):
                set_array(E)
                ps=m_parent(E,k,iS)
                v['tot']+=1
                # is iC a valid candidate of iS?
                valid = (elem(E,iC,k)<elem(E,iS,k)) and (k==0 or m_anc(E,k-1,iS,iC))
                if valid:
                    v['valid_tot']+=1
                    if ps==iC: v['ps_eq_iC']+=1
                    else: v['ps_ne_iC']+=1
                else:
                    v['invalid_tot']+=1
                    # when iC invalid, what is ps? does it stay < iC (i.e. in earlier blocks/G)?
                    if ps is None: v['inv_None']+=1
                    elif ps<iC: v['inv_lt_iC']+=1
                    else: v['inv_ge_iC']+=1
                # unconditional: is ps always == iC ?
                if ps==iC: v['ps_is_iC_uncond']+=1
    return v
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
      "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,1)",
      "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,1,1)(2,2,2)",
      "(0,0,0)(1,1,1)(2,1,0)","(0,0,0)(1,2,0)(1,1,1)",
      "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,1,0)",
      "(0,0)(1,1)(2,0)(1,1)","(0,0,0)(1,1,1)(2,2,2)(3,3,1)",
      "(0,0)(1,1)(2,2)(3,1)","(0,0,0)(1,1,1)(2,2,1)(3,3,0)",
      "(0,0,0)(1,2,3)(2,3,1)","(0,0)(1,1)(0,1)(1,1)","(0,0,0)(1,1,1)(1,2,1)(2,2,2)",
      "(0,0,0,0,0)(1,1,1,1,1)(2,2,2,1,0)",]
    seen=set();Q=[];V=Counter();nt=0;CAP=1000
    for sd in seeds:
        A=strip(parse(sd));k=fmt(A)
        if k not in seen: seen.add(k);Q.append(A)
    for d in range(7):
        fr=[]
        for A in Q:
            if len(A)<=22 and is_genuine_bms(A):
                nt+=1;V+=check(A)
            for n in range(1,4):
                if len(A)>18: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key);fr.append(E)
        Q=fr
        print(f"depth {d}: visited={len(seen)} tested={nt}",flush=True)
        if len(seen)>CAP: break
    print("=== sharp (c>=1) ===",dict(V))
if __name__=='__main__': main()
