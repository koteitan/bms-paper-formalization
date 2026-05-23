#!/usr/bin/env python3
"""STRIP-CORRECT, GENUINE BMS SEEDS ONLY. Characterize UNIFIED's bumped case:
A in BMS (predecessor), E=A[n], q a column of E with q >= l0(A) (bumped region),
m_parent E t q = Some p, p<c<q. The conclusion m_anc E t c p is known true
(UNIFIED). We want the PROOF STRUCTURE. Report, for bumped q:
 - where p lands: G' (p<l0A), same block as q, or earlier block
 - where c lands relative to p,q (G' / bumped)
 - block index c0 and offset x of q  (q = l0A + c0*l1A + x)
 - is the conclusion reducible: does m_anc E t c p hold via 'c,p both reduce
   to A-columns and IH'? Specifically test if there's a uniform pattern."""
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
    visited=set(); CAP=2500
    npairs=0
    p_in_G=0; p_same_block=0; p_earlier_block=0; p_other=0
    c_in_G=0; c_bumped=0
    bad_concl=0; cbad=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(5):
            frontier=[]
            for A in Q:
                l0A=l0(A); l1A=l1(A)
                for nn in range(1,4):
                    E=expand(fmt(A),nn)
                    if E is None: continue
                    key=fmt(E)
                    if key in visited: continue
                    visited.add(key); frontier.append(E)
                    if l1A<1 or l0A<0: continue
                    _MPC.clear()
                    LE=len(E); HE=height(E)
                    for q in range(l0A, LE):     # bumped region
                        if q<l0A: continue
                        for t in range(0,HE):
                            p=m_parent(E,t,q)
                            if p is None: continue
                            for c in range(p+1,q):
                                npairs+=1
                                # classify p
                                if p<l0A: p_in_G+=1
                                else:
                                    cq0=(q-l0A)//l1A if l1A>0 else 0
                                    cp0=(p-l0A)//l1A if l1A>0 else 0
                                    if cp0==cq0: p_same_block+=1
                                    elif cp0<cq0: p_earlier_block+=1
                                    else: p_other+=1
                                if c<l0A: c_in_G+=1
                                else: c_bumped+=1
                                if not m_anc(E,t,c,p):
                                    bad_concl+=1
                                    if len(cbad)<6: cbad.append((fmt(A),nn,t,q,p,c))
            Q=frontier
            if len(visited)>CAP: break
    print(f"bumped-q (t,q,p,c) tuples: {npairs}")
    print(f"p location: G'={p_in_G}  same-block={p_same_block}  earlier-block={p_earlier_block}  other(later)={p_other}")
    print(f"c location: G'={c_in_G}  bumped={c_bumped}")
    print(f"conclusion m_anc E t c p violations: {bad_concl}")
    for x in cbad: print("  CBAD",x)

if __name__=='__main__': main()
