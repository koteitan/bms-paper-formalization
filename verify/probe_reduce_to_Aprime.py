#!/usr/bin/env python3
"""
STRIP-CORRECT: complete the reduction of  elem A s r < elem A (s+j) r  for
A=A'[n] to facts about A', for the 198 block-start cases (s=l0'+c0*l1').

Closed form (VERIFIED 630/630): for global col = l0'+c*l1'+x (0<=x<l1', 0<=c<=n),
  elem A col r = A'!(s'+x)[r] + (c*delta'(r) if ascends'(x,r) else 0)   [r<=t]
and s itself = l0'+c0*l1' (x=0,c=c0): elem A s r = A'!s'[r] + c0*delta'(r).

For interior j (col=s+j), decompose col=l0'+c*l1'+x. Note c>=c0 and:
  - if x==0: this is a block START (c>c0), col = l0'+c*l1', x=0 => ascends'(0,r) true (r<t')
       elem = A'!s'[r] + c*delta'(r).  ineq: c0*delta'(r) < c*delta'(r) i.e.
       delta'(r)>0  (since c>c0).
  - if x>0: interior col of block c. ineq:
       A'!s'[r]+c0 d' < A'!(s'+x)[r] + (c d' if asc'(x,r) else 0)
  We tally and find the GOVERNING facts about A':
   F1: delta'(r) > 0  for r<=t' ? (needed for x==0,c>c0 subcase, & generally)
   F2: A'!s'[r] < A'!(s'+x)[r]  (the SAME lemma for A', x interior) -- recursion!
   F3: when not asc'(x,r): A'!s'[r]+c0 d' < A'!(s'+x)[r].
  Determine exactly which combination suffices.
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
def l0(A):
    s=b0_start(A); return s if s is not None else 0
def nsanc(A,m,i,j): return i==j or m_anc(A,m,i,j)
def ascends(A,d,m):
    s=b0_start(A); t=max_parent_level(A)
    if s is None or t is None: return False
    return m<t and nsanc(A,m,s+d,s)
def delta(A,m):
    s=b0_start(A)
    return 0 if s is None else elem(A,len(A)-1,m)-elem(A,s,m)
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
    # facts:
    F1_ok=0; F1_bad=0   # delta'(r)>0 for r<=t'
    F1_eq0=0            # delta'(r)==0 occurrences (interesting; only when r row not changing)
    x0_subcase=0        # interior col with x==0 (block start beyond c0)
    xpos_asc=0; xpos_notasc=0
    # F2 same-lemma recursion check (x>0 interior, asc):
    F2_ok=0; F2_bad=0
    # F3 (x>0, not asc): A'!s'[r]+c0 d' < A'!(s'+x)[r]
    F3_ok=0; F3_bad=0
    # overall ineq actual
    ineq_ok=0; ineq_bad=0
    other=0
    f1bad_ex=[]; f3bad_ex=[]; f2bad_ex=[]
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
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    if sP is None or l1P==0: continue
                    c0=None
                    for c in range(1,n+1):
                        if s==l0P+c*l1P: c0=c; break
                    if c0 is None:
                        other+=1; continue
                    # F1 over A': for r<=t (note t==t' usually). use tP.
                    for r in range(0,(tP if tP is not None else 0)+1):
                        dv=delta(Ap,r)
                        if dv>0: F1_ok+=1
                        elif dv==0: F1_eq0+=1
                        else: F1_bad+=1; (f1bad_ex.append((fmt(Ap),r,dv)) if len(f1bad_ex)<5 else None)
                    for j in range(1,L1):
                        col=s+j
                        cc=(col-l0P)//l1P; xx=(col-l0P)%l1P
                        for r in range(0,t+1):
                            lhs=elem(A,s,r); rhs=elem(A,col,r)
                            if lhs<rhs: ineq_ok+=1
                            else: ineq_bad+=1
                            asc=ascends(Ap,xx,r); dv=delta(Ap,r)
                            if xx==0:
                                x0_subcase+=1
                                # ineq: c0*dv < cc*dv  (cc>c0). holds iff dv>0
                            else:
                                if asc:
                                    xpos_asc+=1
                                    # reduces to A'!s'[r] < A'!(s'+x)[r] when cc==c0; if cc>c0 extra +(cc-c0)dv>=0 helps
                                    if elem(Ap,sP,r) < elem(Ap,sP+xx,r): F2_ok+=1
                                    else: F2_bad+=1; (f2bad_ex.append((fmt(Ap),sP,xx,r,elem(Ap,sP,r),elem(Ap,sP+xx,r),cc,c0,asc)) if len(f2bad_ex)<8 else None)
                                else:
                                    xpos_notasc+=1
                                    if elem(Ap,sP,r)+c0*dv < elem(Ap,sP+xx,r): F3_ok+=1
                                    else: F3_bad+=1; (f3bad_ex.append((fmt(Ap),sP,xx,r,c0,dv,elem(Ap,sP,r),elem(Ap,sP+xx,r))) if len(f3bad_ex)<8 else None)
            Q=frontier
            if len(visited)>CAP: break
    print(f"other (non-block-start) skipped: {other}")
    print(f"F1 delta'(r)>0 for r<=t'  OK={F1_ok} ==0:{F1_eq0} BAD(neg,impossible)={F1_bad}")
    print(f"interior cols: x==0 subcase={x0_subcase}  x>0 asc={xpos_asc}  x>0 notasc={xpos_notasc}")
    print(f"F2 (x>0,asc): A'!s'[r] < A'!(s'+x)[r]   OK={F2_ok} BAD={F2_bad}")
    print(f"F3 (x>0,notasc): A'!s'[r]+c0 d' < A'!(s'+x)[r]  OK={F3_ok} BAD={F3_bad}")
    print(f"overall ineq (cross-check): OK={ineq_ok} BAD={ineq_bad}")
    print("F1bad:",f1bad_ex)
    print("F2bad:",f2bad_ex)
    print("F3bad:",f3bad_ex)

if __name__=='__main__': main()
