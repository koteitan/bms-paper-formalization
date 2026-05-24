#!/usr/bin/env python3
"""
Is Lemma 2.5 (ii) case-B VACUOUS?

case-B hypothesis: A in BMS, max_parent_level A = Some t, j<l1, Suc k' < t,
                   NOT ascends A j (Suc k').
Vacuity claim V: NO such (A,j,k') exists, i.e. for every BMS A with mpl=t,
    for all j<l1 and all m<t:  ascends A j m  (= nsanc A m (s+j) s).
Equivalently: s=b0_start is a non-strict m-ancestor of every B0 column, for
every level m STRICTLY below t.

CRITICAL (the section-10 trap, memory feedback-verify-with-data): the prior
"case-B vacuous" claim reduced to elem_lt which is machine-checked FALSE.
But that elem_lt counterexample E=(0,0)(1,1)(2,0)(1,1)(1,1) has t=1 and
violates at level r=t=1 (NOT at m<t). So vacuity at m<t may still hold.

We probe hard: deep+wide BFS, AND structurally-targeted candidates (plateau
families like the elem_lt cex but with t>=2). Report any violation explicitly.
"""
import re, subprocess, itertools
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
def nsanc(A,m,i,j): return i==j or m_anc(A,m,i,j)
def ascends(A,d,m):
    s=b0_start(A); t=max_parent_level(A)
    if s is None or t is None: return False
    return m<t and nsanc(A,m,s+d,s)
_ec={}
def expand(text,n):
    k=(text,n)
    if k in _ec: return _ec[k]
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        v=strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: v=None
    _ec[k]=v; return v

def collect(seeds,CAP,depth=6):
    seen=set(); out=[]
    for seed in seeds:
        if len(seen)>CAP: break
        Q=[strip(parse(seed))]; k0=fmt(Q[0])
        if k0 not in seen: seen.add(k0); out.append(Q[0])
        for d in range(depth):
            fr=[]
            for Ap in Q:
                for n in range(1,4):
                    A=expand(fmt(Ap),n)
                    if A is None: continue
                    key=fmt(A)
                    if key in seen: continue
                    seen.add(key); out.append(A); fr.append(A)
            Q=fr
            if len(seen)>CAP: break
    return out

def check(A):
    """return list of violations (j,m) where mpl=t, j<l1, m<t, NOT ascends."""
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or s is None: return []
    v=[]
    for j in range(0,L1):
        for m in range(0,t):
            if not ascends(A,j,m): v.append((j,m))
    return v

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0,0,0)(1,1,1,1,1)","(0,0,0,0,0,0)(1,1,1,1,1,1)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)","(0,0)(1,1)(2,2)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,2)",
           "(0,0,0)(1,1,1)(2,2,1)","(0,0,0)(1,2,0)(1,1,1)",
           "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,2)",
           "(0,0,0,0)(1,1,1,1)(2,2,2,1)","(0,0,0,0)(1,1,1,1)(2,2,1,0)"]
    # targeted candidates FIRST (most important: structural cex hunting)
    print("-- targeted candidates (raw arrays + their expansions) --",flush=True)
    targets=["(0,0)(1,1)(2,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(1,1)(1,1)",
             "(0,0,0)(1,1,1)(2,2,0)(1,1,1)(2,2,0)",
             "(0,0,0)(1,1,1)(2,2,0)(3,3,1)(4,4,0)",
             "(0,0,0)(1,1,1)(2,2,2)(3,3,0)(4,4,1)",
             "(0,0,0)(1,2,1)(2,1,1)(3,3,0)",
             "(0,0,0)(1,1,1)(2,2,1)(3,1,0)"]
    cand=set()
    for tg in targets:
        A=strip(parse(tg)); cand.add(fmt(A))
        for n in range(1,4):
            E=expand(tg,n)
            if E is not None: cand.add(fmt(E))
    tv=0
    for cf in sorted(cand):
        A=strip(parse(cf)); t=max_parent_level(A)
        if t is None or t<2: continue
        vs=check(A)
        flag="VIOL" if vs else "ok"
        if vs: tv+=1
        print(f"  [{flag}] A={cf} t={t} s={b0_start(A)} l1={l1(A)} viol={vs[:6]}",flush=True)
    print(f"targeted t>=2 violations: {tv}\n",flush=True)

    arrays=collect(seeds,CAP=800,depth=4)
    tot=0; viol=0; ex=[]; t_ge2=0
    for A in arrays:
        if len(A)>30: continue
        t=max_parent_level(A)
        if t is None or t<2: continue
        t_ge2+=1
        vs=check(A)
        tot+=1
        if vs:
            viol+=1
            if len(ex)<15: ex.append((fmt(A),max_parent_level(A),b0_start(A),l1(A),vs[:6]))
    print(f"BFS: arrays={len(arrays)} with t>=2: {t_ge2}",flush=True)
    print(f"VACUITY over t>=2 arrays: checked={tot} VIOLATIONS={viol}",flush=True)
    for e in ex: print("  VIOL (A,t,s,l1,[(j,m)..]):",e)

if __name__=='__main__': main()
