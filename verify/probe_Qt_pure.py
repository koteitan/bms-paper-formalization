#!/usr/bin/env python3
"""
Is (Q_t) a PURE m_parent fact (holds for ARBITRARY arrays with a defined
b0_start), or does it need BMS structure?

(Q_t): for A with max_parent_level A = Some t (t>0), s = b0_start A,
       every column c in (s, last_col_idx) has m_ancestor A t c s.

If (Q_t) holds for arbitrary random arrays -> pure lemma, no BMS induction,
no vacuity problem. If it FAILS on some non-BMS array -> needs BMS structure.

We brute-force random small arrays (rectangular, nat entries) and also the
non-rectangular case is irrelevant since BMS arrays are rectangular; we test
rectangular arrays so the comparison is fair.
"""
import random, itertools

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

def check(A):
    t=max_parent_level(A);
    if t is None or t==0: return None
    s=b0_start(A)
    if s is None: return None
    L=len(A)-1
    if L-s < 2: return None   # need interior columns
    bad=[]
    for c in range(s+1,L):
        if not m_anc(A,t,c,s):
            bad.append(c)
    return (s,t,L,bad)

def randcol(h,maxv): return tuple(random.randint(0,maxv) for _ in range(h))

def main():
    random.seed(1)
    tested=0; viol=0; first=[]
    for trial in range(200000):
        ncol=random.randint(4,7)
        h=random.randint(2,4)
        maxv=random.randint(1,4)
        A=[randcol(h,maxv) for _ in range(ncol)]
        r=check(A)
        if r is None: continue
        s,t,L,bad=r
        tested+=1
        if bad:
            viol+=1
            if len(first)<8:
                first.append((A,s,t,L,bad))
        if tested>=8000: break
    print(f"Tested {tested} random rectangular arrays with t>0 & interior B_0.")
    print(f"(Q_t) violations: {viol}")
    for A,s,t,L,bad in first:
        print(f"  VIOL s={s} t={t} L={L} bad_cols={bad}")
        print(f"       A={A}")

if __name__=='__main__': main()
