#!/usr/bin/env python3
"""
Empirical check of the BMS mpl-definedness linchpin (corrected form) + reduction.
Faithful Hunter BMS model, MEMOIZED (frozen tuple-of-tuples keys).

Claims over BMS arrays reachable by BFS from seed(2..N):
  (Z) mpl A = None => elem(A,last,0) == 0                  [proven row0 lemma]
  (L) mpl A = None => mpl_le_zero(A[n]) for n in 0..3       [corrected linchpin]
  (Rf) mpl A = None => forall 1<=m<height A.  m_parent(A,m,len-2)=None  [strong]
  (Rw) mpl A = None => forall 1<=m<height(A[n]). m_parent(A,m,len-2)=None [weak == L]
"""
from functools import lru_cache

def height(A): return 0 if not A else len(A[0])
def elem(A,i,m):
    if i<0 or i>=len(A): return 0
    c=A[i]
    return c[m] if 0<=m<len(c) else 0

@lru_cache(maxsize=None)
def m_parent(A,m,i):
    cands=[]
    for j in range(0,i):
        if m==0:
            if elem(A,j,0)<elem(A,i,0): cands.append(j)
        else:
            if elem(A,j,m)<elem(A,i,m) and m_ancestor(A,m-1,i,j): cands.append(j)
    return cands[-1] if cands else None

@lru_cache(maxsize=None)
def m_ancestor(A,m,i,j):
    seen=set(); cur=i
    while True:
        p=m_parent(A,m,cur)
        if p is None: return False
        if p==j: return True
        if p in seen: return False
        seen.add(p); cur=p

def max_parent_level(A):
    if not A: return None
    last=len(A)-1; H=height(A)
    ms=[m for m in range(0,H) if m_parent(A,m,last) is not None]
    return max(ms) if ms else None
def b0_start(A):
    m0=max_parent_level(A)
    return None if m0 is None else m_parent(A,m0,len(A)-1)
def G_block(A):
    s=b0_start(A); return A[:-1] if s is None else A[:s]
def B0_block(A):
    s=b0_start(A)
    return [] if s is None else list(A[s:len(A)-1])
def non_strict_ancestor(A,m,i,j): return i==j or m_ancestor(A,m,i,j)
def ascends(A,d,m):
    s=b0_start(A); m0=max_parent_level(A)
    if s is None or m0 is None: return False
    return m<m0 and non_strict_ancestor(A,m,s+d,s)
def delta(A,m):
    s=b0_start(A); return 0 if s is None else elem(A,len(A)-1,m)-elem(A,s,m)
def bump_col(A,d,i):
    s=b0_start(A); s=0 if s is None else s
    c=A[s+d]
    return tuple(c[m]+(i*delta(A,m) if ascends(A,d,m) else 0) for m in range(len(c)))
def Bi_block(A,i): return tuple(bump_col(A,d,i) for d in range(len(B0_block(A))))
def Bs_concat(A,n):
    out=()
    for i in range(0,n+1): out=out+Bi_block(A,i)
    return out
def strip_zero_rows(A):
    if not A: return A
    keep=height(A)
    while keep>0 and all(elem(A,i,keep-1)==0 for i in range(len(A))): keep-=1
    return tuple(c[:keep] for c in A)
def expansion(A,n):
    if not A: return A
    return strip_zero_rows(tuple(G_block(A))+Bs_concat(A,n))
def seed(n): return tuple((tuple([0]*n),tuple([1]*n)))
def fmt(A): return ''.join('('+','.join(map(str,c))+')' for c in A)

def mpl_le_zero(A):
    m=max_parent_level(A); return m is None or m==0

def main():
    seen=set(); frontier=[]
    for k in (2,3,4):
        s=seed(k)
        if s not in seen: seen.add(s); frontier.append(s)
    for d in range(3):
        nxt=[]
        for A in frontier:
            for n in range(0,3):
                B=expansion(A,n)
                if B and B not in seen: seen.add(B); nxt.append(B)
        frontier=nxt

    tot=none_ct=h2=0; failZ=[]; failL=[]; failRf=[]; failRw=[]
    for A in seen:
        tot+=1
        if max_parent_level(A) is not None: continue
        none_ct+=1; H=height(A)
        if H>=2 and len(A)>=2: h2+=1
        if len(A)>=1 and elem(A,len(A)-1,0)!=0: failZ.append(A)
        for n in range(0,4):
            B=expansion(A,n)
            if B and not mpl_le_zero(B): failL.append((fmt(A),n,max_parent_level(B)))
        if len(A)>=2:
            c=len(A)-2
            for m in range(1,H):
                if m_parent(A,m,c) is not None: failRf.append((fmt(A),m)); break
            # weak: only below the n=1 expansion height
            B1=expansion(A,1); Hw=height(B1) if B1 else 0
            for m in range(1,Hw):
                if m_parent(A,m,c) is not None: failRw.append((fmt(A),m)); break

    print(f"reached BMS arrays: {tot};  mpl=None: {none_ct};  (none & h>=2,cols>=2): {h2}")
    print(f"(Z) elem(A,last,0)==0          fails={len(failZ)}")
    print(f"(L) mpl_le_zero(A[n])          fails={len(failL)}")
    print(f"(Rf) strong 2nd-last no high   fails={len(failRf)}")
    print(f"(Rw) weak (<height A[1])       fails={len(failRw)}")
    for tag,fl in (("L",failL),("Rf",failRf),("Rw",failRw),("Z",failZ)):
        for x in fl[:6]: print(f"   {tag} FAIL: {x}")

if __name__=="__main__": main()
