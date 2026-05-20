#!/usr/bin/env python3
"""
Intermediate structural fact for bms_m_parent_outside_B0_case_B_pureA:

  CLAIM (chains-to-s): for BMS A with t=max_parent_level>0, s=b0_start,
  for every level r < t and every B_0-internal column s+x (0 <= x < l1),
  if m_parent A r (s+x) = Some q  with  q >= s  (parent inside B_0..),
  then  m_ancestor A r (s+x) s   (the r-chain reaches s).

  Equivalently: every B_0 column whose r-parent is still inside B_0
  eventually r-chains down to s.

  This is what we need: if a (Suc k')-parent candidate of (s+j) lies in
  [s, s+j) (so m_parent (Suc k')(s+j)=Some q1, q1>=s), then
  m_ancestor (Suc k')(s+j) s, contradicting ¬ascends.

  We test the precise contrapositive form actually used:
    (CB) ¬ascends A j (Suc k')  =>  m_parent A (Suc k')(s+j) is None or < s
  is ALREADY verified in verify_m_parent_in_B0_case_B.py.

  Here we test the GENERAL recursion enabler:
    (G) for all r<t, all x in [0,l1): m_parent A r (s+x)=Some q and q>=s
        ==> m_ancestor A r (s+x) s
"""
import re, subprocess
YA = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"

def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)', s)]
def elem(A,p,r):
    if p<0 or p>=len(A): return 0
    if r<0 or r>=len(A[p]): return 0
    return A[p][r]
def height(A): return max((len(c) for c in A), default=0)
def m_parent(A,m,i):
    target=elem(A,i,m)
    for p in range(i-1,-1,-1):
        if elem(A,p,m)>=target: continue
        if m>0 and not m_anc(A,m-1,i,p): continue
        return p
    return None
def m_anc(A,m,i,j):
    p=m_parent(A,m,i)
    while p is not None:
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
        return r.stdout.strip()
    except: return None

def check(A):
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or t==0 or s is None or L1<2: return []
    bad=[]
    for r in range(t):           # levels 0..t-1 (covers Suc k' < t)
        for x in range(0,L1):
            q=m_parent(A,r,s+x)
            if q is not None and q>=s:
                if not m_anc(A,r,s+x,s):
                    bad.append((r,x,q,s))
    return bad

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0,0,0)(1,1,1,1,1)","(0,0,0)(1,2,0)(1,1,1)",
           "(0,0,0,0)(1,1,1,2)","(0,0,0,0)(1,2,3,4)"]
    visited=set(seeds); tested=0; counter=[]
    for seed in seeds:
        q=[seed]
        for d in range(4):
            nq=[]
            for tx in q:
                for n in range(1,4):
                    ex=expand(tx,n)
                    if ex and ex not in visited:
                        visited.add(ex); nq.append(ex)
                        b=check(parse(ex)); tested+=1
                        if b:
                            counter.append((ex,b))
                            if len(counter)<=5:
                                print(f"COUNTER: {ex}  bad(r,x,q,s)={b[:3]}")
            q=nq
    print(f"Tested {tested}, counters={len(counter)}")
    if counter: print("(G) FAILS")
    else: print("(G) HOLDS: every B_0 col whose r-parent is >= s r-chains to s.")

if __name__=='__main__': main()
