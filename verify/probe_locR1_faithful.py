#!/usr/bin/env python3
"""FAITHFUL re-implementation of Hunter's expansion (matching BMS_Defs.thy),
NOT the yaBMS C tool. Then BFS from seed n under faithful expansion and test
loc_R1. This avoids the Bashicu-vs-Hunter trap.

Faithful defs (BMS_Defs.thy):
  elem A i m = A[i][m]
  m_parent A 0 i  = last j<i with A[j][0]<A[i][0]   (None if none)
  m_parent A (m+1) i = last j<i with A[j][m+1]<A[i][m+1] AND m_ancestor A m i j
  m_ancestor A m i j = (case m_parent A m i of None->False | Some p-> p==j or m_anc A m p j)
  height A = len(A[0]) (cols equal length)
  max_parent_level A = Max{m in [0..H): m_parent A m (last) != None}  (None if empty/none)
  b0_start A = m_parent A m0 last   where m0=mpl
  G_block A = take s A  (s=b0_start), butlast A if None
  B0_block A = take (last-s) (drop s A)   [columns s..last-1]
  ascends A d m = (m<m0) and non_strict_ancestor A m (s+d) s   [nsa: i=j or m_anc]
  delta A m = A[last][m] - A[s][m]
  bump_col A d i = [ A[s+d][m] + (i*delta A m if ascends A d m else 0) for m in rows ]
  Bi_block A i = [bump_col A d i for d in 0..len(B0)]
  Bs_concat A n = concat Bi_block A i for i in 0..n  (Suc n blocks: 0..n)
  expansion A n = strip_zero_rows( G_block @ Bs_concat A n )   (A!=[])
  strip_zero_rows: remove trailing all-zero rows.
"""
import sys
from functools import lru_cache

def elem(A,i,m):
    if i<0 or i>=len(A): return 0
    c=A[i]
    if m<0 or m>=len(c): return 0
    return c[m]

def height(A):
    return 0 if not A else len(A[0])

def m_parent(A,m,i):
    # build with memo via m_ancestor
    cands=[]
    for j in range(0,i):
        if m==0:
            if elem(A,j,0)<elem(A,i,0): cands.append(j)
        else:
            if elem(A,j,m)<elem(A,i,m) and m_ancestor(A,m-1,i,j): cands.append(j)
    return cands[-1] if cands else None

def m_ancestor(A,m,i,j):
    seen=set()
    cur=i
    while True:
        p=m_parent(A,m,cur)
        if p is None: return False
        if p==j: return True
        if p in seen: return False
        seen.add(p)
        cur=p

def max_parent_level(A):
    if not A: return None
    last=len(A)-1; H=height(A)
    ms=[m for m in range(0,H) if m_parent(A,m,last) is not None]
    return max(ms) if ms else None

def b0_start(A):
    m0=max_parent_level(A)
    if m0 is None: return None
    return m_parent(A,m0,len(A)-1)

def G_block(A):
    s=b0_start(A)
    return A[:-1] if s is None else A[:s]

def B0_block(A):
    s=b0_start(A)
    if s is None: return []
    last=len(A)-1
    return A[s:s+(last-s)]   # take (last-s) (drop s A) = A[s:last]

def non_strict_ancestor(A,m,i,j):
    return i==j or m_ancestor(A,m,i,j)

def ascends(A,d,m):
    s=b0_start(A); m0=max_parent_level(A)
    if s is None or m0 is None: return False
    return m<m0 and non_strict_ancestor(A,m,s+d,s)

def delta(A,m):
    s=b0_start(A)
    if s is None: return 0
    return elem(A,len(A)-1,m)-elem(A,s,m)

def bump_col(A,d,i):
    s=b0_start(A); s=0 if s is None else s
    c=A[s+d]
    return [ c[m]+(i*delta(A,m) if ascends(A,d,m) else 0) for m in range(len(c)) ]

def Bi_block(A,i):
    return [bump_col(A,d,i) for d in range(len(B0_block(A)))]

def Bs_concat(A,n):
    out=[]
    for i in range(0,n+1):
        out.extend(Bi_block(A,i))
    return out

def strip_zero_rows(A):
    if not A: return A
    H=height(A)
    keep=H
    while keep>0 and all(elem(A,i,keep-1)==0 for i in range(len(A))):
        keep-=1
    return [c[:keep] for c in A]

def expansion(A,n):
    if not A: return A
    P=G_block(A)+Bs_concat(A,n)
    return strip_zero_rows(P)

def l0(A):
    s=b0_start(A); return 0 if s is None else s
def l1(A):
    return len(B0_block(A))

def seed(n): return [[0]*n,[1]*n]

def fmt(A): return ''.join('('+','.join(map(str,c))+')' for c in A)

def main():
    # BFS from seed 2..5 under faithful expansion
    seen=set(); Q=[]
    for k in (2,3,4,5):
        s=seed(k); key=fmt(s)
        if key not in seen: seen.add(key); Q.append(s)
    CAP=4000; depth=8
    tot=0; violations=[]
    for d in range(depth):
        fr=[]
        for A in Q:
            sA=b0_start(A); tA=max_parent_level(A); lA=l1(A); l0A=l0(A)
            if sA is not None and lA>=2 and len(A)<=30:
                for n in range(1,4):
                    E=expansion(A,n)
                    sp=b0_start(E)
                    if sp is None: continue
                    tot+=1
                    off=sp-l0A
                    ok=(sp>=l0A) and (lA>0) and (off%lA==0) and (off//lA<=n)
                    if not ok:
                        violations.append((fmt(A),n,lA,l0A,tA,sp,max_parent_level(E),fmt(E)))
            for n in range(1,4):
                if len(A)>25: continue
                E=expansion(A,n)
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        if len(seen)>CAP: break
    print(f"FAITHFUL BFS: tested {tot} (l1 A>=2) expansions; violations of loc_R1: {len(violations)}")
    for v in violations[:15]:
        print(f"  A={v[0]} n={v[1]} l1={v[2]} l0={v[3]} t={v[4]} s'={v[5]} t'={v[6]}")
        print(f"     A[n]={v[7]}")

if __name__=='__main__':
    sys.setrecursionlimit(100000)
    main()
