#!/usr/bin/env python3
"""UNIFIED is FALSE in general (counterexample E=(0,0)(1,1)(2,0)(1,1)(2,0),
t=1,q=3,p=0,c=2: m_parent(E,1,3)=0 but m_anc(E,1,2,0)=False, max_parent_level=0).
Find the CORRECT hypothesis by testing several restrictions and counting
violations.  Coverage: BFS that DOES reach the counterexample chain.

Restrictions tested (each over the same (t,q,p,c) population that passes its filter):
  R0: none (baseline)
  Rmpl_le:  t <= max_parent_level A
  Rmpl_eq:  t == max_parent_level A
  Rmpl_lt:  t <  max_parent_level A
  Rqlast:   q == len(A)-1            (q is the last column)
  Rqlast_mpl: q==last AND t<=mpl
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
    key=(id(A),m,i)
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
def max_parent_level(A):
    last=len(A)-1
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0,0,0)(1,1,1,1,1)","(0,0,0,0,0,0)(1,1,1,1,1,1)"]
    visited=set(); CAP=6000
    stats={k:[0,0] for k in ["R0","Rmpl_le","Rmpl_eq","Rmpl_lt","Rqlast","Rqlast_mpl"]}
    ex={k:[] for k in stats}
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(7):
            frontier=[]
            for A in Q:
                _MPC.clear()
                H=height(A); L=len(A); mpl=max_parent_level(A); last=L-1
                for q in range(1,L):
                    for t in range(0,H):
                        p=m_parent(A,t,q)
                        if p is None: continue
                        for c in range(p+1,q):
                            good = m_anc(A,t,c,p)
                            filters={
                              "R0": True,
                              "Rmpl_le": (mpl is not None and t<=mpl),
                              "Rmpl_eq": (mpl is not None and t==mpl),
                              "Rmpl_lt": (mpl is not None and t<mpl),
                              "Rqlast": (q==last),
                              "Rqlast_mpl": (q==last and mpl is not None and t<=mpl),
                            }
                            for k,f in filters.items():
                                if not f: continue
                                if good: stats[k][0]+=1
                                else:
                                    stats[k][1]+=1
                                    if len(ex[k])<4: ex[k].append((fmt(A),t,q,p,c,mpl))
                for nn in range(1,4):
                    E=expand(fmt(A),nn)
                    if E is None: continue
                    key=fmt(E)
                    if key in visited: continue
                    visited.add(key); frontier.append(E)
            Q=frontier
            if len(visited)>CAP: break
    print(f"arrays visited ~{len(visited)}")
    for k in stats:
        ok,bad=stats[k]
        print(f"{k:12s}  OK={ok:7d}  BAD={bad:6d}")
        for x in ex[k]: print(f"      ex A=%s t=%d q=%d p=%d c=%d mpl=%s"%x)

if __name__=='__main__': main()
