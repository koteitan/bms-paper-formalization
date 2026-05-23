#!/usr/bin/env python3
"""
STRIP-CORRECT structural probe to find a tractable form of bms_b0_col_elem_lt.

Hypotheses to test (for stripped BMS A, t=max_parent_level>0, s=b0_start):
  (Z)   elem A s r == 0 for all r <= t        (bad root is zero up to level t)
  (P)   elem A (s+j) r > 0 for all r<=t, 0<j<l1   (B0 cols positive up to t)
  (Z')  elem A s r == 0 for all r < height     (bad root all-zero column?)

If (Z) holds, then bms_b0_col_elem_lt (elem A s r < elem A (s+j) r) reduces to
(P): B0 columns have strictly positive row-r elements for r<=t. Much cleaner.

Also report what elem A s r actually IS (the column A!s) to see the pattern.
"""
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

def check(A):
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or t==0 or s is None or L1<2: return None
    Z_fail=[]; P_fail=[]; Zall_fail=False
    for r in range(t+1):
        if elem(A,s,r)!=0:
            Z_fail.append((r,elem(A,s,r)))
    H=height(A)
    for r in range(H):
        if elem(A,s,r)!=0: Zall_fail=True
    for j in range(1,L1):
        for r in range(t+1):
            if not (elem(A,s+j,r)>0):
                P_fail.append((j,r,elem(A,s+j,r)));
    return (Z_fail,P_fail,Zall_fail, tuple(A[s]))

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0; zf=0; pf=0; zallf=0; scols={}; CAP=2000
    first=[]
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
                    visited.add(key); nq.append(ex)
                    r=check(ex)
                    if r is None: continue
                    tested+=1
                    Zf,Pf,Zallf,scol=r
                    if Zf:
                        zf+=1
                        if len(first)<5: first.append(("Z",key,Zf[:3],scol))
                    if Pf: pf+=1
                    if Zallf: zallf+=1
                    scols[scol]=scols.get(scol,0)+1
            q=nq
            if len(visited)>CAP: break
    print(f"Tested {tested} stripped BMS (t>0).")
    print(f"(Z)  elem A s r != 0 for some r<=t : {zf}")
    print(f"(P)  elem A (s+j) r not >0 (r<=t)  : {pf}")
    print(f"(Z') A!s has a nonzero entry        : {zallf}")
    print(f"distinct bad-root columns A!s (top): {sorted(scols.items(), key=lambda x:-x[1])[:8]}")
    for tag,k,ex,sc in first: print(f"  {tag}-FAIL {k}: {ex} A!s={sc}")
    if zf==0:
        print("=> (Z) HOLDS: bad root s is ZERO up to level t. elem_lt reduces to (P).")

if __name__=='__main__': main()
