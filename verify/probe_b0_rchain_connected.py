#!/usr/bin/env python3
"""For BMS A, t=mpl>0, s=b0start, C=last_col=s+l1:
 (CHAIN) for each r<=t, is C an r-ancestor of nothing... rather:
    is the set {s, s+1, ..., C} an r-chain with s at bottom?
    Concretely test: for r<=t, m_ancestor A r C s  (known true, Hunter L2.1 dir)
    AND for 0<j<l1: m_ancestor A r (s+j) s   (the VAC/Qt fact, GOAL).
 KEY new probe (non-circular candidate):
 (CC) for r<=t and 0<j<l1: IS (s+j) an r-ANCESTOR of C?  i.e. m_anc A r C (s+j).
      If yes, then since C's r-chain descends through s+j down to s,
      and the r-chain is linear, s is below s+j on C's chain => need s+j on chain.
 (LIN) Combine: C's r-chain (the descending m_parent sequence from C) -- does it
      pass through EVERY column in [s, C)? Or which ones? Print the r-chain of C."""
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
def rchain(A,r,i):
    """descending m_parent chain from i."""
    out=[]; p=m_parent(A,r,i); seen=set()
    while p is not None and p not in seen:
        seen.add(p); out.append(p); p=m_parent(A,r,p)
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
    s=b0_start(A)
    if s is None: return 0
    return len(A)-1-s
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def check(A,stats):
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or t==0 or s is None or L1<2: return
    C=s+L1
    for r in range(t+1):
        for j in range(1,L1):
            # CC: is s+j an r-ancestor of C?
            if not m_anc(A,r,C,s+j):
                stats['cc_fail']+=1
                if stats['cc_ex'] is None: stats['cc_ex']=(fmt(A),r,j)
    stats['cases']+=1

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); stats={'cases':0,'cc_fail':0,'cc_ex':None}; CAP=2000
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
                    visited.add(key); nq.append(ex); check(ex,stats)
            q=nq
            if len(visited)>CAP: break
    print(stats)
if __name__=='__main__': main()
