#!/usr/bin/env python3
"""
STRIP-CORRECT probe: STRATEGY 1 deep dive. For A=A'[n] with bad root
s=b0_start(A) landing at l0'+c0*l1' (start of block B_{c0}), express the
B0-columns of A (s+j, 0<j<l1) and the inequality
   elem A s r < elem A (s+j) r   (r<=t)
in closed form over A' and check whether it reduces to an A'-internal fact
that an induction could supply.

We do NOT assume the closed form; we COMPUTE both sides from the stripped
expansion A and from A' and report congruences.

Key sub-questions:
 (a) Is s ALWAYS = l0' + c0*l1' for SOME c0 in 1..n (when l1'>1)?
 (b) Does the B0-block of A coincide with cols [s, s+l1) inside one A' block
     B_{c0}, i.e. is l1 == l1'? (so A's interior B0 cols map to A' interior
     B0 cols x=1..l1'-1 within block c0)
 (c) Then elem A s r vs elem A (s+j) r maps (via closed form) to
     A'!(s'+0)[r]+c0*delta'(r)*[asc'(0,r)] vs A'!(s'+j)[r]+c0*delta'(r)*[asc'(j,r)]
     -- but col 0 of B0' is s' itself (x=0). ascends'(0,r) is always true
     (s' is its own 0-ancestor). So elem A s r = A'!s'[r]+c0*delta'(r).
     And elem A (s+j) r = A'!(s'+j)[r] + c0*delta'(r)*[asc'(j,r)].
   => inequality becomes, when asc'(j,r):
        A'!s'[r] < A'!(s'+j)[r]    (the SAME inequality for A', smaller!)
      when NOT asc'(j,r):
        A'!s'[r] + c0*delta'(r) < A'!(s'+j)[r].
   We test which case occurs and whether the reductions hold.
"""
import re, subprocess
YA = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"

def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)', s)]
def fmt(A):
    return ''.join('('+','.join(str(x) for x in c)+')' for c in A)
def strip(A):
    if not A: return A
    h = max((len(c) for c in A), default=0)
    while h > 0 and all((c[h-1] if h-1 < len(c) else 0) == 0 for c in A):
        h -= 1
    return [tuple(c[:h]) for c in A]
def elem(A,p,r):
    if p<0 or p>=len(A): return 0
    if r<0 or r>=len(A[p]): return 0
    return A[p][r]
def height(A): return max((len(c) for c in A), default=0)
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
    s=b0_start(A)
    if s is None: return 0
    return len(A)-1-s
def l0(A):
    s=b0_start(A); return s if s is not None else 0
def nsanc(A,m,i,j):  # non_strict_ancestor
    return i==j or m_anc(A,m,i,j)
def ascends(A,d_idx,m):  # ascends A d_idx m
    s=b0_start(A); t=max_parent_level(A)
    if s is None or t is None: return False
    return m<t and nsanc(A,m,s+d_idx,s)
def delta(A,m):
    s=b0_start(A)
    if s is None: return 0
    return elem(A,len(A)-1,m)-elem(A,s,m)
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); CAP=2000
    n_total=0
    n_s_at_block=0      # s = l0'+c0*l1' for some 1<=c0<=n
    n_l1_eq=0           # l1 == l1'
    # for each interior col & level: classify ascends'(j,r)
    asc_reduces_ok=0; asc_reduces_bad=0
    notasc_ok=0; notasc_bad=0
    cf_mismatch=0       # closed-form value mismatch
    examples=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for d in range(4):
            frontier=[]
            for Ap in Q:
                sP=b0_start(Ap); tP=max_parent_level(Ap)
                l0P=l0(Ap); l1P=l1(Ap)
                for n in range(1,4):
                    A=expand(fmt(Ap),n)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A); L0=l0(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    if sP is None or l1P==0: continue
                    n_total+=1
                    # find c0
                    c0=None
                    for c in range(1,n+1):
                        if s==l0P+c*l1P: c0=c; break
                    if c0 is not None:
                        n_s_at_block+=1
                        if L1==l1P: n_l1_eq+=1
                    # closed-form check on the inequality reduction
                    if c0 is not None and L1==l1P:
                        for j in range(1,L1):
                            for r in range(0,t+1):
                                lhs=elem(A,s,r); rhs=elem(A,s+j,r)
                                # closed-form predictions over A':
                                # elem A s r should = A'!s'[r] + c0*delta'(r) (x=0 ascends always since nsanc s' s')
                                cf_lhs = elem(Ap,sP,r) + (c0*delta(Ap,r) if ascends(Ap,0,r) else 0)
                                cf_rhs = elem(Ap,sP+j,r) + (c0*delta(Ap,r) if ascends(Ap,j,r) else 0)
                                if cf_lhs!=lhs or cf_rhs!=rhs:
                                    cf_mismatch+=1
                                    if len(examples)<5:
                                        examples.append(("CFMISS",key,fmt(Ap),n,c0,j,r,lhs,cf_lhs,rhs,cf_rhs))
                                    continue
                                if ascends(Ap,j,r):
                                    # reduces to A'!s'[r] < A'!(s'+j)[r] (note both have +c0 delta only if asc'(0)=asc'(j); asc'(0) always true)
                                    # actual reduced ineq: A'!s'[r]+c0 d < A'!(s'+j)[r]+c0 d  <=> A'!s'[r] < A'!(s'+j)[r]
                                    if elem(Ap,sP,r) < elem(Ap,sP+j,r): asc_reduces_ok+=1
                                    else: asc_reduces_bad+=1
                                else:
                                    # A'!s'[r]+c0 d < A'!(s'+j)[r]
                                    if elem(Ap,sP,r)+c0*delta(Ap,r) < elem(Ap,sP+j,r): notasc_ok+=1
                                    else: notasc_bad+=1
            Q=frontier
            if len(visited)>CAP: break
    print(f"Total A=A'[n] with t>0,l1>=2 : {n_total}")
    print(f"  s = l0'+c0*l1' (block start)   : {n_s_at_block}")
    print(f"  AND l1 == l1'                  : {n_l1_eq}")
    print(f"closed-form value mismatches     : {cf_mismatch}")
    print(f"reduction when ascends'(j,r):")
    print(f"   A'!s'[r] < A'!(s'+j)[r]  OK={asc_reduces_ok}  BAD={asc_reduces_bad}")
    print(f"reduction when NOT ascends'(j,r):")
    print(f"   A'!s'[r]+c0*d' < A'!(s'+j)[r]  OK={notasc_ok}  BAD={notasc_bad}")
    for e in examples: print("  ",e)

if __name__=='__main__': main()
