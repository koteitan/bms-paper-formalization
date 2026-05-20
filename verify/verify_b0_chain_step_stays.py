#!/usr/bin/env python3
"""
Step-local enabler for the chains-to-s induction:

  (S) for BMS A, t=max_parent_level>0, s=b0_start, level r<t,
      B_0-internal col s+x with x>0 (i.e. s < s+x <= last_col_idx region):
      if m_parent A r (s+x) = Some q  and  q > s   (strictly inside B_0, not yet s),
      then  m_parent A r q  is NOT None  AND  m_parent A r q >= s.

  i.e. the r-chain, once strictly inside (s, s+x], never falls out of [s,..)
  in one step: it either lands on s next, or stays >= s. So by induction it
  reaches s.

Combined with the base (q==s) this gives chains-to-s.
"""
import re, subprocess
YA="/home/koteitan/bms-paper/tmp/yaBMS/c/bms"
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
    for r in range(t):
        for x in range(1,L1):     # s+x strictly above s, inside B_0
            q=m_parent(A,r,s+x)
            if q is not None and q>s:   # strictly between s and s+x
                q2=m_parent(A,r,q)
                if q2 is None or q2<s:
                    bad.append((r,x,q,q2,s))
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
                                print(f"COUNTER: {ex}  (r,x,q,q2,s)={b[:3]}")
            q=nq
    print(f"Tested {tested}, counters={len(counter)}")
    if counter: print("(S) FAILS: chain can jump below s in one step")
    else: print("(S) HOLDS: r-chain inside (s,..] stays >= s next step.")
if __name__=='__main__': main()
