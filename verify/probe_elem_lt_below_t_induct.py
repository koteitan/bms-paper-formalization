#!/usr/bin/env python3
"""
Does the BMS-induction EXPANSION case of elem_lt_below_t reduce to the IH?

Claim to prove: P(A): for m<t, 0<j<l1, elem A s m < elem A (s+j) m  (s=b0_start,
t=max_parent_level).  Seed case is vacuous (l1(seed)<=1).  Expansion case:
given P(A) [IH], prove P(A[n]).

For A[n] we need, for each interior B0' column (s'+j', m'<t'), elem(A[n]) s' m'
< elem(A[n]) (s'+j') m'.  Question: does this follow from IH P(A) plus the
bump structure?  We DIAGNOSE the expansion case structurally:

  - locate s'=b0_start(A[n]), t'=mpl(A[n]), l1'=l1(A[n]).
  - classify s' : in G' (s'<l0') [R2] or at a bumped block start [R1].
  - for the needed (s'+j', m'), express both endpoints via the bump formula
    elem(A[n]) (idx) k = (A!(s+x))!k + (asc(x,k)? c*delta A k : 0)  for B-cols,
    or = A-col verbatim for G'-cols, and check whether the inequality reduces
    to an IH instance (an A-level elem_lt_below_t at some (sA,tA,mA,jA)) or to
    a bump/delta fact.

Goal: find whether there is a CLEAN, uniform reduction (so the expansion case
is provable from IH), or whether it genuinely needs the open location lemma.
"""
import re, subprocess
from collections import Counter
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
def l0(A):
    s=b0(A); return s if s is not None else 0
def nsanc(A,m,i,j): return i==j or m_anc(A,m,i,j)
def ascends(A,d,m):
    s=b0(A); t=mpl(A)
    if s is None or t is None: return False
    return m<t and nsanc(A,m,s+d,s)
def delta(A,m):
    s=b0(A)
    return 0 if s is None else elem(A,len(A)-1,m)-elem(A,s,m)
_ec={}
def expand(text,n):
    k=(text,n)
    if k in _ec: return _ec[k]
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        v=strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: v=None
    _ec[k]=v; return v

def collect(seeds,CAP,depth):
    seen=set(); out=[]
    for sd in seeds:
        if len(seen)>CAP: break
        Q=[strip(parse(sd))]; k0=fmt(Q[0])
        if k0 not in seen: seen.add(k0); out.append(Q[0])
        for d in range(depth):
            fr=[]
            for Ap in Q:
                for n in range(1,4):
                    E=expand(fmt(Ap),n)
                    if E is None: continue
                    key=fmt(E)
                    if key in seen: continue
                    seen.add(key); out.append(E); fr.append(E)
            Q=fr
            if len(seen)>CAP: break
    return out

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0)(1,1)(2,0)","(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)",
           "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)"]
    arrays=[A for A in collect(seeds,350,3) if len(A)<=26]
    # For each A with t>=2, take A[n] and classify s' location; check whether the
    # interior column s'+j' of A[n] is a bumped copy of an A-column or a G'-col,
    # and whether IH suffices.
    loc=Counter()
    reduce_ok=reduce_bad=0; bad_ex=[]
    sprime_in_G=sprime_blockstart=sprime_other=0
    for A in arrays:
        sA=b0(A); tA=mpl(A); l0A=l0(A); l1A=l1(A)
        if sA is None or tA is None or l1A<1: continue
        for n in range(1,4):
            E=expand(fmt(A),n)
            if E is None: continue
            sE=b0(E); tE=mpl(E); l1E=l1(E); l0E=l0(E)
            if sE is None or tE is None or tE<2 or l1E<2: continue
            # classify s'
            if sE<l0A: loc['sprime_in_G']+=1; sprime_in_G+=1
            else:
                off=(sE-l0A)
                if l1A>0 and off% l1A==0: loc['sprime_blockstart']+=1; sprime_blockstart+=1
                else: loc['sprime_other']+=1; sprime_other+=1
            # for each interior col and m'<t', see if it's a bumped copy of an A col
            for j in range(1,l1E):
                col=sE+j
                for mm in range(0,tE):
                    lhs=elem(E,sE,mm); rhs=elem(E,col,mm)
                    # try to express col via A: if col in a B-block c (col>=l0A),
                    # block c=(col-l0A)//l1A, x=(col-l0A)%l1A, value=
                    #   A!(sA+x)[mm] + (asc(x,mm)? c*delta:0)
                    if col>=l0A and l1A>0:
                        c=(col-l0A)//l1A; x=(col-l0A)%l1A
                        if x<l1A and sA+x<len(A):
                            base=elem(A,sA+x,mm); bump=(c*delta(A,mm) if ascends(A,x,mm) else 0)
                            pred=base+bump
                            if pred!=rhs:
                                reduce_bad+=1
                                if len(bad_ex)<5: bad_ex.append(('rhs',fmt(A),n,sE,col,mm,pred,rhs))
                                continue
                    if not (lhs<rhs):
                        reduce_bad+=1
                        if len(bad_ex)<5: bad_ex.append(('ineq',fmt(A),n,sE,col,mm,lhs,rhs))
                    else: reduce_ok+=1
    print("s' location:",dict(loc))
    print(f"interior-col domination checks: ok={reduce_ok} bad={reduce_bad}")
    for e in bad_ex: print("  ",e)

if __name__=='__main__': main()
