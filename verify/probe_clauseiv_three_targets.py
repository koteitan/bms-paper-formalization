#!/usr/bin/env python3
"""
Faithful empirical verification of the THREE clause-(iv) targets, using the
eval-faithful infra from probe_vacuity_refute.py (which DOES `strip`).

CRITICAL difference from the old verify_*.py probes (which gave false
confidence): those parsed yaBMS output WITHOUT strip and computed
b0_start/l1/l0 on the outer array without normalising. Here we strip every
array before computing mpl/b0/l1 (per the project MEMORY rule), and we treat
each BMS member A as a node in the expansion BFS tree (faithful to the
inductive_set BMS = closure of seeds under expansion).

For each BMS member A (stripped), with s=b0(A), t0=mpl(A), L1=l1(A), L0=s:
  idx_B(A,c,j) = L0 + c*L1 + j   (= idx_B_in_expansion A c j; l0/l1 of OUTER A)
We build A[n] via yaBMS (stripped output, matches strip_zero_rows) and test:

T1  m_parent_block_n_stays_until_zero:
      for all m, n>=1, 0<a<L1:
        m_parent(A[n], m, idx_B(A,n,a)) = Some p  ==>  idx_B(A,n,0) <= p

T2  idx_B_n_zero_no_intermediate_B_t_ancestor:
      for all m, n>=1, t<n, j<L1:
        NOT m_anc(A[n], m, idx_B(A,n,0), idx_B(A,t,j))

T3  clause_iv_intermediate_B_t_impossible_at_zero_outside_lands_in_G:
      for n, 0<i<L1, with S = [j'<i : elem(A[n],idx_B(A,0,j'),0) <
                                      elem(A[n],idx_B(A,0,i),0)] == []:
        m_parent(A[n], 0, idx_B(A,n,i)) = Some p  ==>  p < L0

Any failure => REFUTATION (STOP, report counterexample).
"""
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
_MPC={}; _MISS=object()
def set_array(A): _MPC.clear()
def m_parent(A,m,i):
    key=(m,i)
    c=_MPC.get(key,_MISS)
    if c is not _MISS: return c
    res=None
    for pp in range(0,i):
        if elem(A,pp,m)>=elem(A,i,m): continue
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
def mpl(A):
    last=len(A)-1
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0(A):
    t=mpl(A)
    return None if t is None else m_parent(A,t,len(A)-1)
def l1(A):
    s=b0(A); return 0 if s is None else len(A)-1-s
_ec={}
def expand(text,n):
    k=(text,n)
    if k in _ec: return _ec[k]
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        v=strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: v=None
    _ec[k]=v; return v

def idxB(L0,L1,c,j): return L0 + c*L1 + j

def check(Atext, NMAX=4):
    """Return list of (target, detail) violations for one outer BMS member."""
    A=strip(parse(Atext))
    set_array(A)
    s=b0(A); t0=mpl(A); L1=l1(A)
    if s is None or t0 is None or L1<1: return []
    L0=s
    out=[]
    for n in range(1,NMAX+1):
        E=expand(fmt(A),n)
        if E is None: continue
        set_array(E)
        Hn=height(E); LE=len(E)
        # sanity: idx_B(A,n,L1-1) should be the last real column region in E
        if idxB(L0,L1,n,0) >= LE: continue
        # ---- T1 ----
        bn0=idxB(L0,L1,n,0)
        for a in range(1,L1):
            col=idxB(L0,L1,n,a)
            if col>=LE: continue
            for m in range(0,Hn):
                p=m_parent(E,m,col)
                if p is None: continue
                if not (bn0 <= p):
                    out.append(("T1",dict(A=Atext,n=n,a=a,m=m,p=p,bn0=bn0,col=col)))
        # ---- T2 ----
        for t in range(0,n):
            for j in range(0,L1):
                tgt=idxB(L0,L1,t,j)
                if tgt>=bn0: continue  # idx_B(t,j) with t<n always < bn0; guard anyway
                for m in range(0,Hn):
                    if m_anc(E,m,bn0,tgt):
                        out.append(("T2",dict(A=Atext,n=n,t=t,j=j,m=m,bn0=bn0,tgt=tgt)))
        # ---- T3 ----  (only k=0 / m=0, S empty)
        for i in range(1,L1):
            ci=idxB(L0,L1,0,i)
            if ci>=LE: continue
            ei=elem(E,ci,0)
            S=[jp for jp in range(0,i)
               if elem(E,idxB(L0,L1,0,jp),0) < ei]
            if S!=[]: continue   # only the S-empty branch
            col=idxB(L0,L1,n,i)
            if col>=LE: continue
            p=m_parent(E,0,col)
            if p is None: continue
            if not (p < L0):
                out.append(("T3",dict(A=Atext,n=n,i=i,p=p,L0=L0,col=col)))
    return out

def main():
    seeds=[
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0,0,0,0,0)(1,1,1,1,1,1)",
    ]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=3000; depth=8
    tested=0; viol=0; byT={"T1":0,"T2":0,"T3":0}
    shown=0
    for d in range(depth):
        fr=[]
        for A in Q:
            vs=check(fmt(A))
            tested+=1
            for (T,det) in vs:
                viol+=1; byT[T]+=1
                if shown<40:
                    print(f"  VIOL {T}: {det}",flush=True); shown+=1
            set_array(A)
            for n in range(1,4):
                if len(A)>34: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"  depth {d}: visited={len(seen)} tested={tested} viol={viol} {byT}",flush=True)
        if len(seen)>CAP: break
    print(f"FINAL visited={len(seen)} tested={tested} VIOLATIONS={viol} {byT}",flush=True)
    if viol==0:
        print("ALL THREE TARGETS HOLD empirically.")
    else:
        print("REFUTED — see VIOL lines above.")

if __name__=='__main__': main()
