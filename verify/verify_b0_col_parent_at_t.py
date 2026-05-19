#!/usr/bin/env python3
"""
Test: for BMS A with t = max_parent_level > 0, b0_start = s, every interior B_0
column (s+j) for 0 < j < l1 has m_parent A t (s+j) = Some s (direct parent).

This is STRONGER than just m_ancestor at t. If TRUE, the proof is even easier.
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
    try: return subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10).stdout.strip()
    except: return None

def check(A):
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or t==0 or s is None or L1<2: return None
    bad = []
    for j in range(1, L1):
        if m_parent(A, t, s + j) != s:
            bad.append((j, m_parent(A, t, s+j)))
    return bad

def main():
    seeds = [
        "(0,0,0)(1,1,1)",
        "(0,0,0,0)(1,1,1,1)",
        "(0,0,0)(1,1,1)(2,0,0)(1,1,1)",
        "(0,0)(1,1)",
        "(0,0,0,0)(1,1,1,2)",
        "(0,0,0,0)(1,2,3,4)",
        "(0,0,0,0,0)(1,1,1,1,1)",
        "(0,0,0)(1,2,0)(1,1,1)",
    ]
    visited = set(seeds); tested = 0; counter = []
    for seed in seeds:
        q = [seed]
        for d in range(4):
            nq = []
            for tx in q:
                for n in range(1, 4):
                    ex = expand(tx, n)
                    if ex and ex not in visited:
                        visited.add(ex); nq.append(ex)
                        A = parse(ex)
                        b = check(A); tested += 1
                        if b:
                            counter.append((ex, b))
                            if len(counter) <= 5:
                                print(f"COUNTER (parent): {ex}")
                                print(f"  bad j (m_parent t (s+j) ≠ Some s): {b}")
            q = nq
    print(f"Tested {tested}, counter (parent-t=s)={len(counter)}")

if __name__ == '__main__':
    main()
