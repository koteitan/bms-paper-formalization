#!/usr/bin/env python3
"""
Characterize b0_start(A[n]) / mpl(A[n]) / l1(A[n]) in terms of A's invariants,
to assess whether the LOCATION LEMMA (needed for the BMS-induction expansion
case of elem_lt_below_t at m>0) has a clean closed form.

For A in BMS with sA=b0_start, tA=mpl, lA=l1, l0A=l0, and E=A[n]:
report s'=b0_start(E), t'=mpl(E), l'=l1(E), l0'=l0(E), and try to MATCH
s' against candidate closed forms:
  - R1 (block-start): s' = l0A + c*lA for some c in 0..n  -> record c, and
    whether c==n (last block) etc.
  - R2 (in G'): s' < l0A  -> record s' - sA, and whether s' relates to a
    t-ancestor of sA in A (H4-style).
Also track t' vs tA and l' vs lA.
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
_MPC={}; _MISS=object()
def sa(A): _MPC.clear()
def m_parent(A,m,i):
    key=(m,i); c=_MPC.get(key,_MISS)
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
    t=mpl(A); return None if t is None else m_parent(A,t,len(A)-1)
def l1(A):
    s=b0(A); return 0 if s is None else len(A)-1-s
def l0(A):
    s=b0(A); return s if s is not None else 0
_ec={}
def expand(text,n):
    k=(text,n)
    if k in _ec: return _ec[k]
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        v=strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: v=None
    _ec[k]=v; return v

def main():
    seeds=["(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,1)",
           "(0,0,0,0)(1,1,1,1)(2,2,2,0)","(0,0,0,0)(1,1,1,1)(2,2,2,1)",
           "(0,0,0,0)(1,1,1,1)(2,2,1,0)"]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    rules=Counter(); tprime=Counter(); lprime=Counter(); samples=[]
    CAP=500
    for d in range(4):
        fr=[]
        for A in Q:
            sa(A); sA=b0(A); tA=mpl(A); lA=l1(A); l0A=l0(A)
            if sA is not None and tA is not None and tA>=1 and lA>=1:
                for n in range(1,4):
                    E=expand(fmt(A),n)
                    if E is None: continue
                    sa(E); s2=b0(E); t2=mpl(E); l2=l1(E); l02=l0(E)
                    if s2 is None or t2 is None: continue
                    if s2<l0A:
                        rules['R2_inG']+=1
                        tag=('R2', s2, s2-sA, t2-tA if tA is not None else None)
                    else:
                        off=s2-l0A
                        if lA>0 and off%lA==0:
                            c=off//lA; rules[f'R1_block_c={c}_of_n={n}']+=1
                            tag=('R1', c, n, t2, l2)
                        else:
                            rules['OTHER']+=1; tag=('OTHER',s2,l0A,lA,off)
                    tprime[(tA,t2)]+=1; lprime[(lA,l2)]+=1
                    if len(samples)<25:
                        samples.append((fmt(A),n,f"sA={sA},tA={tA},lA={lA},l0A={l0A}",
                                        f"s'={s2},t'={t2},l'={l2},l0'={l02}",tag))
            sa(A)
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        if len(seen)>CAP: break
    print("location rules:",dict(rules))
    print("t' vs tA (tA,t'):",dict(sorted(tprime.items())))
    print("l' vs lA (lA,l'):",dict(sorted(lprime.items())))
    print("samples:")
    for s in samples: print("  ",s)

if __name__=='__main__': main()
