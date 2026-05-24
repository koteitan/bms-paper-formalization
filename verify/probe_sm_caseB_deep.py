#!/usr/bin/env python3
"""STRIP-CORRECT, GENUINE BMS SEEDS ONLY.
Check whether 'Case B' of the sm-kernel ever occurs, and if so whether the
target inequality still holds.

Setup: A in BMS (predecessor), E=A[n], q a column of E with q>=l0(A)+l1(A)
(actually-bumped region), t=Suc t' (so t>=1), p=m_parent(E,t,q), x in (p,q).
 anc_lo: m_anc(E,t-1,x,p)   (p is (t-1)-ancestor of x)
 Case A: m_anc(E,t-1,q,x)   (x is (t-1)-ancestor of q)
 Case B: NOT m_anc(E,t-1,q,x)

We restrict to x with anc_lo true (those are the x the proof must handle).
Report:
 - countA: x with anc_lo and Case A
 - countB: x with anc_lo and Case B   <-- if 0, Case B is vacuous!
 - in Case B, violations of elem(E,p,t) < elem(E,x,t) (must be 0; sm true)
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
    visited=set(); CAP=20000
    countA=countB=0; smviol=0; bex=[]; smbad=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(8):
            frontier=[]
            for A in Q:
                l0A=l0(A); l1A=l1(A)
                for nn in range(1,5):
                    E=expand(fmt(A),nn)
                    if E is None: continue
                    key=fmt(E)
                    if key in visited: continue
                    visited.add(key); frontier.append(E)
                    if l1A<1 or l0A<0: continue
                    _MPC.clear()
                    LE=len(E); HE=height(E); thr=l0A+l1A
                    for q in range(thr, LE):     # actually-bumped region
                        for t in range(1,HE):    # t = Suc t', so t>=1
                            p=m_parent(E,t,q)
                            if p is None: continue
                            tp=t-1
                            for x in range(p+1,q):
                                if not m_anc(E,tp,x,p): continue   # require anc_lo
                                if m_anc(E,tp,q,x):
                                    countA+=1
                                else:
                                    countB+=1
                                    if elem(E,p,t)>=elem(E,x,t):
                                        smviol+=1
                                        if len(smbad)<6: smbad.append((fmt(A),nn,t,q,p,x))
                                    if len(bex)<8: bex.append((fmt(A),nn,t,q,p,x))
            Q=frontier
            if len(visited)>CAP: break
    print(f"anc_lo-x with Case A (m_anc t-1 q x): {countA}")
    print(f"anc_lo-x with Case B (NOT m_anc t-1 q x): {countB}")
    print(f"Case B sm-inequality violations (elem p t >= elem x t): {smviol}")
    for b in bex: print("  CASE-B example",b)
    for b in smbad: print("  SM-BAD",b)

if __name__=='__main__': main()
