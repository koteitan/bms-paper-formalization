#!/usr/bin/env python3
"""
STRIP-CORRECT discovery probe for the (ii) crux (STRICT).

For BMS A with t=max_parent_level>0, s=b0_start, and each INTERIOR B_0
column s+j (0<j<l1), find at which levels r in [0,t] we have
m_ancestor A r (s+j) s. The last-column proof works because
m_parent A t L = s gives level-(t-1) ancestry then m_ancestor_mono
lowers to 0. We want to know the cleanest UNIVERSAL characterization
of interior columns:

  (Q_t)   m_ancestor A t     (s+j) s   for all interior j ?
  (Q_t1)  m_ancestor A (t-1) (s+j) s   for all interior j ?
  (Q_any) max level r with m_ancestor A r (s+j) s

If (Q_t1) or (Q_t) holds universally, m_ancestor_mono + m_ancestor_elem_lt
give (STRICT) and the crux moves to a level-(t-1)/t ancestry fact tied to
the b0_start definition (which itself uses level t).

CRITICAL: strip every yaBMS expansion before computing s/t/l1.
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
def non_strict_anc(A,m,i,j):
    return i==j or m_anc(A,m,i,j)
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
    # for each interior B_0 column s+j (0<j<l1):
    fail_t=0; fail_t1=0; n_int=0
    minlevel_fail=[]  # j where even level0 anc fails (would break STRICT)
    for j in range(1,L1):
        n_int+=1
        # level-0 ancestry (the actual needed fact)
        if not m_anc(A,0,s+j,s):
            minlevel_fail.append(('L0',j))
        # level t ancestry
        if not non_strict_anc(A,t,s+j,s):
            fail_t+=1
        # level t-1 ancestry
        if not non_strict_anc(A,t-1,s+j,s):
            fail_t1+=1
    return (n_int,fail_t,fail_t1,minlevel_fail)

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0
    tot_int=0; tot_ft=0; tot_ft1=0; l0fails=[]
    CAP=2500
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
                    ni,ft,ft1,l0f=r
                    tot_int+=ni; tot_ft+=ft; tot_ft1+=ft1
                    if l0f and len(l0fails)<5: l0fails.append((key,l0f))
            q=nq
            if len(visited)>CAP: break
    print(f"Tested {tested} stripped BMS, {tot_int} interior B_0 columns.")
    print(f"(Q_t)  level-t   non_strict_anc fails: {tot_ft}")
    print(f"(Q_t1) level-t-1 non_strict_anc fails: {tot_ft1}")
    print(f"(L0)   level-0   m_ancestor fails    : {len(l0fails)} (first 5 shown)")
    for k,f in l0fails: print(f"   L0-FAIL {k}: {f[:3]}")

if __name__=='__main__': main()
