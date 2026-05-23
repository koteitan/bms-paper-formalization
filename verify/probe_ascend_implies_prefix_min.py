#!/usr/bin/env python3
"""
STRIP-CORRECT verification of Hunter's row-0 equivalence (the => direction)
needed for option (b), case A.

(E1') ascends A j 0  =>  for all c with s < c <= s+j: elem A s 0 < elem A c 0
      (s = b0_start, t = max_parent_level > 0, ascends A j 0 == m_ancestor A 0 (s+j) s for j>0)

(E1)  ascends A j 0  =>  for all x with 0 < x <= j: ascends A x 0  (local prefix all-asc)

If (E1') holds, then for x<=j the interval (s,s+x] is a subset of (s,s+j], so
elem A s 0 < all of it, hence (m_anc_zero_strict_min) m_ancestor A 0 (s+x) s,
i.e. ascends A x 0 -> (E1). This lets case A use a *local* all-asc (x<=j),
which is all the within/outside-block helpers actually need.

Also report whether ALL B_0 columns ascend at row 0 (t>0) -- empirically yes,
so case B (j does not ascend) is empirically vacuous, but we still formalize it.
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
    for p in range(0,i):
        if elem(A,p,m)>=elem(A,i,m): continue
        if m>0 and not m_anc(A,m-1,i,p): continue
        res=p
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
def ascends0(A,j,s):
    # ascends A j 0  (t>0 assumed): non_strict_ancestor A 0 (s+j) s
    return (j==0) or m_anc(A,0,s+j,s)
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def check(A):
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or t==0 or s is None or L1<2: return None
    e1p_fail=[]; e1_fail=[]; notasc=0
    for j in range(1,L1):
        asc=ascends0(A,j,s)
        if not asc: notasc+=1
        if asc:
            # (E1'): elem A s 0 < elem A c 0 for s<c<=s+j
            for c in range(s+1,s+j+1):
                if not (elem(A,s,0) < elem(A,c,0)):
                    e1p_fail.append((j,c)); break
            # (E1): ascends A x 0 for 0<x<=j
            for x in range(1,j+1):
                if not ascends0(A,x,s):
                    e1_fail.append((j,x)); break
    return (e1p_fail,e1_fail,notasc,L1-1)

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0; CAP=2500
    f1=0; f2=0; tot_notasc=0; tot_int=0; first=[]
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
                    e1p,e1,na,ni=r
                    tot_notasc+=na; tot_int+=ni
                    if e1p:
                        f1+=1
                        if len(first)<5: first.append(("E1p",key,e1p[:2]))
                    if e1:
                        f2+=1
                        if len(first)<5: first.append(("E1",key,e1[:2]))
            q=nq
            if len(visited)>CAP: break
    print(f"Tested {tested} stripped BMS, {tot_int} interior B_0 columns.")
    print(f"(E1') ascends j => s row-0 < all (s,s+j]   : {'HOLDS' if f1==0 else f'FAILS ({f1})'}")
    print(f"(E1)  ascends j => ascends x for 0<x<=j    : {'HOLDS' if f2==0 else f'FAILS ({f2})'}")
    print(f"non-ascending interior cols (case B count) : {tot_notasc}")
    for tag,k,ex in first: print(f"  {tag}-FAIL {k}: {ex}")

if __name__=='__main__': main()
