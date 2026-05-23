#!/usr/bin/env python3
"""STRIP-CORRECT. Test UNIFIED conjecture:
  A in BMS, m_parent A t q = Some p  =>  for all c with p<c<q: m_ancestor A t c p.
i.e. the t-parent p of q is a t-ancestor of EVERY column strictly between p and q.
If TRUE, this proves elem_lt directly (q=C=last, p=s=bad root, level t) with NO
BMS.induct and NO location lemma: m_anc A t c s for s<c<C  =>(mono)=> m_anc A r c s
=>(m_ancestor_elem_lt)=> elem A s r < elem A c r for r<=t.
Test over ALL (t,q) pairs in BMS (not just the bad-root one), all strip-correct."""
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
    key=(id(A),m,i)
    if key in _MPC: return _MPC[key]
    res=None
    ei=elem(A,i,m)
    for pp in range(0,i):
        if elem(A,pp,m)>=ei: continue
        if m>0 and not m_anc(A,m-1,i,pp): continue
        res=pp
    _MPC[key]=res
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
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def main():
    # GENUINE BMS seeds only: seed n = (0,...,0)(1,...,1), exactly 2 columns.
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0,0,0)(1,1,1,1,1)","(0,0,0,0,0,0)(1,1,1,1,1,1)"]
    visited=set(); CAP=4000
    npairs=0; ok=0; bad=0; bads=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(6):
            frontier=[]
            for A in Q:
                _MPC.clear()
                # test UNIFIED on THIS array A (assume A in BMS by construction)
                H=height(A); L=len(A)
                for q in range(1,L):
                    for t in range(0,H):
                        p=m_parent(A,t,q)
                        if p is None: continue
                        npairs+=1
                        for c in range(p+1,q):
                            if m_anc(A,t,c,p): ok+=1
                            else:
                                bad+=1
                                if len(bads)<12: bads.append((fmt(A),t,q,p,c))
                # expand
                for nn in range(1,4):
                    E=expand(fmt(A),nn)
                    if E is None: continue
                    key=fmt(E)
                    if key in visited: continue
                    visited.add(key); frontier.append(E)
            Q=frontier
            if len(visited)>CAP: break
    print(f"arrays tested ~{len(visited)}, (t,q)-parent pairs: {npairs}")
    print(f"UNIFIED  m_anc A t c p for p<c<q:   OK={ok}  BAD={bad}")
    for x in bads: print("  BAD A=%s t=%d q=%d p=%d c=%d" % x)

if __name__=='__main__': main()
