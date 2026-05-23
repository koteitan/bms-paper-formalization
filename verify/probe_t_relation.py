#!/usr/bin/env python3
"""STRIP-CORRECT: confirm t(A)=t(A') in BOTH regimes & where the 3 t>t' land."""
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
    s=b0_start(A); return 0 if s is None else len(A)-1-s
def l0(A):
    s=b0_start(A); return s if s is not None else 0
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); CAP=2000
    bs_teq=0; bs_tne=0; o_teq=0; o_tne=0; tne_ex=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for d in range(4):
            frontier=[]
            for Ap in Q:
                sP=b0_start(Ap); tP=max_parent_level(Ap)
                l0P=l0(Ap); l1P=l1(Ap)
                for n in range(1,4):
                    A=expand(fmt(Ap),n)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    if sP is None or l1P==0: continue
                    blockstart=any(s==l0P+c*l1P for c in range(1,n+1))
                    if blockstart:
                        if t==tP: bs_teq+=1
                        else: bs_tne+=1; (tne_ex.append(("BS",fmt(Ap),n,tP,key,t)) if len(tne_ex)<8 else None)
                    else:
                        if t==tP: o_teq+=1
                        else: o_tne+=1; (tne_ex.append(("O",fmt(Ap),n,tP,key,t)) if len(tne_ex)<8 else None)
            Q=frontier
            if len(visited)>CAP: break
    print(f"block-start: t==t' {bs_teq}  t!=t' {bs_tne}")
    print(f"l1'=1 other: t==t' {o_teq}  t!=t' {o_tne}")
    for e in tne_ex: print("  TNE",e)
if __name__=='__main__': main()
