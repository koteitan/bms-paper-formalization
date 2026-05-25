#!/usr/bin/env python3
"""REFUTATION of loc_R1_guarded under the FAITHFUL Hunter expansion (= the
Isabelle BMS set's recursion in BMS_Defs.thy). The task's premise (R3=0 in
probe_location_3way's key cell) is INVALID because probe_location_3way imports
its `expand` from probe_vacuity_refute, which calls the yaBMS C tool = Bashicu
STANDARD FORM -- a DIFFERENT recursion from Hunter's faithful expansion -- and
uses a tiny hand-picked seed list with depth<=7, so it never reaches the
counterexample below.

COUNTEREXAMPLE (genuine faithful BMS):
  A = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,1)
  faithful provenance: seed (0,0,0)(1,1,1) -[3]-> ... = (0,0)(1,1)(2,2)(3,1)(4,1),
                       then -[1]-> A. So A in BMS.
  l1 A = 3 (>=2, satisfies l1_ge2);  l0 A = 4.
  A[1] = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,0)(8,1)(9,2)
  max_parent_level(A[1]) = Some 1  (>=1, satisfies the GUARD mpl_pos).
  b0_start(A[1]) = Some 8.
  Need 8 = l0 A + c*l1 A = 4 + 3c with c<=1: c=0->4, c=1->7. NO c. MID-BLOCK.

Hence loc_R1_guarded is FALSE for the Isabelle BMS set. This script BFSs the
faithful expansion from genuine seeds and reports all guarded mid-block cases.
"""
import sys
sys.setrecursionlimit(1000000)

def elem(A,i,m):
    if i<0 or i>=len(A): return 0
    c=A[i]
    return c[m] if 0<=m<len(c) else 0
def height(A): return 0 if not A else len(A[0])

class Ctx:
    """Per-array memoized faithful m_parent / m_ancestor (BMS_Defs.thy)."""
    def __init__(self,A): self.A=A; self.mp={}
    def m_parent(self,m,i):
        k=(m,i)
        if k in self.mp: return self.mp[k]
        A=self.A; res=None
        for j in range(0,i):
            if m==0:
                if elem(A,j,0)<elem(A,i,0): res=j
            else:
                if elem(A,j,m)<elem(A,i,m) and self.m_anc(m-1,i,j): res=j
        self.mp[k]=res; return res
    def m_anc(self,m,i,j):
        cur=i; seen=set()
        while True:
            p=self.m_parent(m,cur)
            if p is None: return False
            if p==j: return True
            if p in seen: return False
            seen.add(p); cur=p

def mpl_ctx(A):
    if not A: return None,None
    last=len(A)-1; ctx=Ctx(A)
    ms=[m for m in range(0,height(A)) if ctx.m_parent(m,last) is not None]
    return (max(ms) if ms else None), ctx
def b0_start_ctx(A):
    t,ctx=mpl_ctx(A)
    if t is None: return None,t,ctx
    return ctx.m_parent(t,len(A)-1),t,ctx
def b0_start(A): return b0_start_ctx(A)[0]
def max_parent_level(A): return mpl_ctx(A)[0]
def l0(A):
    s=b0_start(A); return 0 if s is None else s
def l1(A):
    s=b0_start(A); return 0 if s is None else len(A)-1-s
def nsa(ctx,m,i,j): return i==j or ctx.m_anc(m,i,j)
def ascends(d,m,s,m0,ctx):
    if s is None or m0 is None: return False
    return m<m0 and nsa(ctx,m,s+d,s)
def delta(A,m,s):
    return 0 if s is None else elem(A,len(A)-1,m)-elem(A,s,m)
def expansion(A,n):
    if not A: return A
    s,m0,ctx=b0_start_ctx(A)
    ss=0 if s is None else s
    B0len=0 if s is None else (len(A)-1-s)
    G=A[:-1] if s is None else A[:s]
    Bs=[]
    for i in range(0,n+1):
        for d in range(B0len):
            c=A[ss+d]
            Bs.append([c[m]+(i*delta(A,m,s) if ascends(d,m,s,m0,ctx) else 0)
                       for m in range(len(c))])
    P=G+Bs
    H=height(P) if P else 0; keep=H
    while keep>0 and all(elem(P,i,keep-1)==0 for i in range(len(P))): keep-=1
    return [c[:keep] for c in P]
def seed(n): return [[0]*n,[1]*n]
def fmt(A): return ''.join('('+','.join(map(str,c))+')' for c in A)

def main():
    # 1) direct counterexample
    A=[[0,0],[1,1],[2,2],[3,1],[4,0],[5,1],[6,2],[7,1]]
    par=[[0,0],[1,1],[2,2],[3,1],[4,1]]
    assert fmt(expansion(par,1))==fmt(A), "provenance broken"
    E=expansion(A,1)
    print("COUNTEREXAMPLE")
    print("  A      =",fmt(A),"  l0",l0(A),"l1",l1(A),"(l1>=2 ok)")
    print("  A[1]   =",fmt(E))
    print("  mpl(A[1]) =",max_parent_level(E),"(>=1: GUARD satisfied)")
    print("  b0(A[1])  =",b0_start(E),"; need l0+c*l1=4+3c, c<=1 -> {4,7}; 8 NOT in it -> MID-BLOCK")
    # 2) full BFS census
    seen=set(); Q=[]
    for k in (2,3,4,5):
        s=seed(k); Q.append(s); seen.add(fmt(s))
    CAP=8000; depth=10; nc=0; mid=0; d2bad=0
    for d in range(depth):
        fr=[]
        for X in Q:
            sX=b0_start(X); lX=l1(X); l0X=l0(X)
            if sX is not None and lX>=2 and len(X)<=26:
                for n in range(1,4):
                    Y=expansion(X,n)
                    if not Y: continue
                    sp=b0_start(Y); tp=max_parent_level(Y)
                    if sp is None or tp is None or tp<1: continue
                    nc+=1
                    if sp<l0X: d2bad+=1
                    elif lX>0 and (sp-l0X)%lX!=0: mid+=1
            for n in range(1,4):
                if len(X)>22: continue
                Y=expansion(X,n)
                if not Y: continue
                key=fmt(Y)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(Y)
        Q=fr
        if len(seen)>CAP: break
    print(f"\nFAITHFUL BFS census: nodes={len(seen)} guarded(l1>=2,mpl>=1)={nc} "
          f"s'<l0={d2bad} MID-BLOCK={mid}")
    print("=> loc_R1_guarded is FALSE for the Isabelle BMS set." if mid>0
          else "=> no mid-block found (would support the lemma)")

if __name__=='__main__': main()
