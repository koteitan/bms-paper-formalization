#!/usr/bin/env python3
"""
Focused test of T2 = idx_B_n_zero_no_intermediate_B_t_ancestor INCLUDING its
actual hypotheses, to decide whether the bare "violations" found by the first
probe are genuine counterexamples or are excluded by the inductive context.

T2 (exact statement):
  A in BMS, A != [], b0_start A = Some s, l1 A > 0,
  IH:  forall k'<k. lemma_2_5_at A n k'
  ciii: lemma_2_5_iii_clause A n k
  t<n, j<l1,
  anc: m_ancestor (A[n]) m (idx_B(n,0)) (idx_B(t,j))
  ==> False

So: a genuine counterexample is (A,n,k,m,t,j) with t<n, j<l1, anc TRUE, and
IH & ciii TRUE.  We model lemma_2_5_at fully.
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
def nsa(A,m,i,j):  # non-strict ancestor
    return i==j or m_anc(A,m,i,j)
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
def idxB0orig(L0,j): return L0 + j   # idx_B0_in_orig A j = l0 A + j
def idxG(j): return j

# ---- lemma_2_5 clauses, evaluated faithfully ----
def clause_ii(A,En,L0,L1,n,k):
    for i in range(0,L1):
        for j in range(0,L1):
            lhs=m_anc(En,k,idxB(L0,L1,0,j),idxB(L0,L1,0,i))
            rhs=m_anc(En,k,idxB(L0,L1,n,j),idxB(L0,L1,n,i))
            if lhs!=rhs: return False
    return True
def clause_i(A,En,L0,L1,n,k):
    for i in range(0,L0):
        for j in range(0,L1):
            lhs=m_anc(En,k,idxB(L0,L1,0,j),idxG(i))
            rhs=m_anc(En,k,idxB(L0,L1,n,j),idxG(i))
            if lhs!=rhs: return False
    return True
def clause_iii(A,En,L0,L1,n,k):
    m0=mpl(A)
    if not(n>0 and m0 is not None and k<m0): return True  # premise vacuous
    last=len(A)-1
    for i in range(0,L1):
        lhs=m_anc(A,k,last,idxB0orig(L0,i))
        # idx_B_in_expansion A (n-1) i
        set_array(En)
        rhs=m_anc(En,k,idxB(L0,L1,n,0),idxB(L0,L1,n-1,i))
        set_array(A)
        if lhs!=rhs: return False
    return True
def clause_iv(A,En,L0,L1,n,k):
    set_array(En)
    for i in range(1,L1):
        col=idxB(L0,L1,n,i)
        if col>=len(En): continue
        p=m_parent(En,k,col)
        if p is None: continue
        okB=any(p==idxB(L0,L1,n,j) for j in range(0,L1))
        okG=any(p==idxG(j) for j in range(0,L0))
        if not(okB or okG): return False
    return True
def clause_v(A,En,L0,L1,n,k):
    set_array(En)
    for i in range(0,L1):
        for j in range(0,L1):
            for n0 in range(0,n):
                for n1 in range(n0+1,n):
                    lhs=m_anc(En,k,idxB(L0,L1,n1,j),idxB(L0,L1,n0,i))
                    rhs=m_anc(En,k,idxB(L0,L1,n1+1,j),idxB(L0,L1,n0,i))
                    if lhs!=rhs: return False
    return True
def lemma_2_5_at(A,En,L0,L1,n,k):
    return (clause_i(A,En,L0,L1,n,k) and clause_ii(A,En,L0,L1,n,k)
            and clause_iii(A,En,L0,L1,n,k) and clause_iv(A,En,L0,L1,n,k)
            and clause_v(A,En,L0,L1,n,k))

def check(Atext, NMAX=3, KMAX=4):
    A=strip(parse(Atext)); set_array(A)
    s=b0(A); t0=mpl(A); L1=l1(A)
    if s is None or t0 is None or L1<1: return []
    L0=s
    real=[]
    for n in range(1,NMAX+1):
        En=expand(fmt(A),n)
        if En is None: continue
        Hn=height(En); LE=len(En)
        bn0=idxB(L0,L1,n,0)
        if bn0>=LE: continue
        for k in range(0,KMAX+1):
            # IH: forall k'<k lemma_2_5_at A n k'
            set_array(A)
            ih=all(lemma_2_5_at(A,En,L0,L1,n,kp) for kp in range(0,k))
            if not ih: continue
            set_array(A)
            ciii=clause_iii(A,En,L0,L1,n,k)
            if not ciii: continue
            # anc at any level m
            set_array(En)
            for m in range(0,Hn):
                for t in range(0,n):
                    for j in range(0,L1):
                        tgt=idxB(L0,L1,t,j)
                        if tgt>=bn0: continue
                        if m_anc(En,m,bn0,tgt):
                            real.append(dict(A=Atext,n=n,k=k,m=m,t=t,j=j,bn0=bn0,tgt=tgt))
    return real

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)"]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=600; depth=6
    tested=0; real=0; shown=0
    for d in range(depth):
        fr=[]
        for A in Q:
            rs=check(fmt(A))
            tested+=1
            for det in rs:
                real+=1
                if shown<30: print(f"  REAL-CE: {det}",flush=True); shown+=1
            set_array(A)
            for n in range(1,4):
                if len(A)>26: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"  depth {d}: visited={len(seen)} tested={tested} real_CE={real}",flush=True)
        if len(seen)>CAP: break
    print(f"FINAL visited={len(seen)} tested={tested} REAL_COUNTEREXAMPLES={real}",flush=True)
    print("T2 FALSE as stated (with hyps)." if real else
          "T2 holds under its inductive hypotheses (bare violations were excluded).")

if __name__=='__main__': main()
