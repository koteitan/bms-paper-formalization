#!/usr/bin/env python3
"""Diagnostic: for bumped q, t>=1, p=m_parent(E,t,q), print the (t-1)-ancestor
chain of q and, for each x in (p,q), whether anc_lo (m_anc t-1 x p) and
m_anc t-1 q x hold.  Goal: determine if 'Case B' (anc_lo & not m_anc t-1 q x)
ever occurs, by inspecting the chain gaps directly.

Key question: between consecutive (t-1)-chain nodes of q, are there interior
columns?  If gaps>1 exist AND those interiors are anc_lo, Case B is non-empty.
"""
import re, subprocess
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
_MPC={}
def m_parent(A,m,i):
    key=(m,i)
    if key in _MPC: return _MPC[key]
    res=None; ei=elem(A,i,m)
    for pp in range(0,i):
        if elem(A,pp,m)>=ei: continue
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
def chain(A,m,i):
    out=[]; p=m_parent(A,m,i); seen=set()
    while p is not None and p not in seen:
        seen.add(p); out.append(p); p=m_parent(A,m,p)
    return out
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
    s=b0_start(A); return 0 if s is None else len(A)-1-s
def l0(A):
    s=b0_start(A); return s if s is not None else 0
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)"]
    visited=set(); CAP=4000
    caseB=0; printed=0
    interior_anc_lo=0   # x strictly between consec chain nodes, anc_lo true
    interior_total=0
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(6):
            frontier=[]
            for A in Q:
                l0A=l0(A); l1A=l1(A)
                for nn in range(1,4):
                    E=expand(fmt(A),nn)
                    if E is None: continue
                    key=fmt(E)
                    if key in visited: continue
                    visited.add(key); frontier.append(E)
                    if l1A<1 or l0A<0: continue
                    _MPC.clear()
                    LE=len(E); HE=height(E); thr=l0A+l1A
                    for q in range(thr, LE):
                        for t in range(1,HE):
                            p=m_parent(E,t,q)
                            if p is None or p>=q-1: continue
                            tp=t-1
                            ch=[q]+chain(E,tp,q)   # t'-chain from q down
                            chset=set(ch)
                            for x in range(p+1,q):
                                al = m_anc(E,tp,x,p)
                                qx = m_anc(E,tp,q,x)
                                if al and not qx:
                                    caseB+=1
                                    if printed<10:
                                        printed+=1
                                        print(f"CASE-B: A={fmt(A)} n={nn} t={t} q={q} p={p} x={x}")
                                        print(f"   (t-1={tp})-chain of q: {ch}")
                                        print(f"   elem p t={elem(E,p,t)} elem x t={elem(E,x,t)} elem q t={elem(E,q,t)}")
                                # interior between consecutive chain nodes
                                # find chain node just above x
                                if x not in chset:
                                    above=min((cn for cn in ch if cn>x), default=None)
                                    if above is not None:
                                        interior_total+=1
                                        if al: interior_anc_lo+=1
            Q=frontier
            if len(visited)>CAP: break
    print(f"\nCASE-B count: {caseB}")
    print(f"interior-x (not on q's t'-chain) total: {interior_total}, of which anc_lo: {interior_anc_lo}")

if __name__=='__main__': main()
