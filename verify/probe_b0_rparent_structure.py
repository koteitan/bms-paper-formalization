#!/usr/bin/env python3
"""For BMS A, t=mpl>0, s=b0start: examine m_parent A r (s+j) for r<=t, 0<j<l1.
Conjectures to test (each independent of elem_lt):
 (P1) for r<=t and 0<j<l1: m_parent A r (s+j) is NOT None and is >= s.
      (i.e. every B0 col has an r-parent within [s, s+j).)
 (P2) for r<=t: the r-parent of (s+j) lies in [s, s+j)  AND
      iterating r-parent from (s+j) stays >= s until it reaches s.
 (P3) KEY non-circular: is s = m_parent A t (s+j) precisely? or just an ancestor?
 Report distribution of (r, j, parent-s offset)."""
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

def check(A,stats):
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or t==0 or s is None or L1<2: return
    for j in range(1,L1):
        for r in range(t+1):
            p=m_parent(A,r,s+j)
            if p is None:
                stats['p1_none']+=1
            elif p<s:
                stats['p1_below']+=1
            # P3: is parent exactly s at r=t?
            if r==t:
                if p==s: stats['t_par_is_s']+=1
                elif p is not None and p>s: stats['t_par_above_s']+=1
    stats['cases']+=1

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); stats={'cases':0,'p1_none':0,'p1_below':0,'t_par_is_s':0,'t_par_above_s':0}; CAP=2000
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
