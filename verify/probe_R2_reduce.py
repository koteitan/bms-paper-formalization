#!/usr/bin/env python3
"""STRIP-CORRECT. R2 (l1'=1). We found: s (bad root of A=A'[n]) is, in A', a
t-ancestor of l0'(=s'=b0_start A'). Test the STRONGER reduction that would close R2:

 (R2a) for all c with s < c <= l0' : m_ancestor A' t c s   (s is t-anc of every
       column from s+1 through l0', INSIDE A').  => via mono+elem_lt gives
       elem A' s r < elem A' c r for r<=t, covering G'-tail interior cols.
 (R2b) for bumped-block interior cols c>=l0' (global in A): elem A c r >= elem A' l0' r
       (bumping is non-negative), and elem A s r = elem A' s r < elem A' l0' r.
       => elem A s r < elem A c r.
 Net: if R2a holds, R2 inequality is fully explained by A'-ancestry of s up to l0'
      plus non-negativity of bumping.
Also test (R2a') the weaker: elem A' s r < elem A' c r for s<c<=l0', r<=t (the
      pure inequality, in case ancestry is too strong)."""
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
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,2)(3,3,0)"]
    visited=set(); CAP=3000
    n=0
    r2a_ok=r2a_bad=0    # m_anc A' t c s for s<c<=l0'
    r2ap_ok=r2ap_bad=0  # elem A' s r < elem A' c r for s<c<=l0', r<=t
    r2b_ok=r2b_bad=0    # bumped: elem A c r >= elem A' l0' r for c>=l0' interior
    bad=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(4):
            frontier=[]
            for Ap in Q:
                sP=b0_start(Ap); tP=max_parent_level(Ap)
                l0P=l0(Ap); l1P=l1(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    if sP is None or l1P!=1 or tP is None: continue
                    if not s < l0P: continue   # only the G'-internal R2 cases
                    n+=1
                    # R2a / R2a': columns s<c<=l0' inside A'
                    for c in range(s+1, l0P+1):
                        if m_anc(Ap,t,c,s): r2a_ok+=1
                        else:
                            r2a_bad+=1
                            if len(bad)<10: bad.append(("R2a",fmt(Ap),nn,s,c,t))
                        for r in range(0,t+1):
                            if elem(Ap,s,r) < elem(Ap,c,r): r2ap_ok+=1
                            else:
                                r2ap_bad+=1
                                if len(bad)<10: bad.append(("R2a'",fmt(Ap),nn,s,c,r,elem(Ap,s,r),elem(Ap,c,r)))
                    # R2b: bumped block cols c (global in A) with c>=l0', interior (< last)
                    for c in range(l0P, len(A)-1):
                        for r in range(0,t+1):
                            if elem(A,c,r) >= elem(Ap,l0P,r): r2b_ok+=1
                            else:
                                r2b_bad+=1
                                if len(bad)<10: bad.append(("R2b",fmt(Ap),nn,c,r,elem(A,c,r),elem(Ap,l0P,r)))
            Q=frontier
            if len(visited)>CAP: break
    print(f"R2 G'-internal cases (s<l0'): {n}")
    print(f"R2a   m_anc A' t c s  (s<c<=l0'):       OK={r2a_ok}  BAD={r2a_bad}")
    print(f"R2a'  elem A' s r < elem A' c r:         OK={r2ap_ok} BAD={r2ap_bad}")
    print(f"R2b   elem A c r >= elem A' l0' r:       OK={r2b_ok}  BAD={r2b_bad}")
    for x in bad: print("  ",x)

if __name__=='__main__': main()
