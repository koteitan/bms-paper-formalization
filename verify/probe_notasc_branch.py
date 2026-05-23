#!/usr/bin/env python3
"""
STRIP-CORRECT: investigate the not-ascends interior columns. The proposed
reduction A'!s'[r]+c0 d' < A'!(s'+x)[r] FAILED, yet overall ineq holds.
Resolve the discrepancy by printing, for each interior col of A with x>0 and
NOT ascends'(x,r), the ACTUAL elem A s r and elem A col r and the closed-form
breakdown. Maybe ascends(A col-local, r) for A differs, or maybe these cols
are never actually interior B0 of A (filtered by L1), or strip changes things.
We recompute elem directly from A (no closed-form assumption) to be safe.
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
    # focus on the reported bad seed line
    Ap=strip(parse("(0,0)(1,1)(2,2)"))  # produces (0,0)(1,1)(2,1)... let's just sweep
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); CAP=2000
    printed=0
    notasc_total=0; notasc_overall_ok=0
    # NEW hypothesis: when not asc'(x,r) at level r, then asc'(x,r') is true for
    # some lower-? Actually the GOVERNING fact may be: not asc'(x,r) =>
    # A'!s'[r] < A'!(s'+x)[r] STILL holds with strict, OR delta'(r)=... Let's
    # tally a cleaner reduction: maybe the correct claim when not-asc is just
    # A'!s'[r] < A'!(s'+x)[r] (same as F2) regardless of asc.
    G_ok=0; G_bad=0; gbad=[]
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
                    if c0 is None: continue
                    for j in range(1,L1):
                        col=s+j
                        cc=(col-l0P)//l1P; xx=(col-l0P)%l1P
                        for r in range(0,t+1):
                            asc=ascends(Ap,xx,r)
                            if xx==0 or asc:
                                # general fact G: A'!s'[r] < A'!(s'+x)[r]  (x interior of A')
                                pass
                            if xx>0:
                                gv_l=elem(Ap,sP,r); gv_r=elem(Ap,sP+xx,r)
                                if gv_l<gv_r: G_ok+=1
                                else:
                                    G_bad+=1
                                    if len(gbad)<10: gbad.append((fmt(Ap),sP,xx,r,gv_l,gv_r,asc,tP,l1P))
                            if xx>0 and not asc:
                                notasc_total+=1
                                if elem(A,s,r)<elem(A,col,r): notasc_overall_ok+=1
                                if printed<12:
                                    printed+=1
                                    print(f"NOTASC A={key} A'={fmt(Ap)} n={n} c0={c0} col={col}(c={cc},x={xx}) r={r}: "
                                          f"elemAs={elem(A,s,r)} elemAcol={elem(A,col,r)} | "
                                          f"A'!s'={elem(Ap,sP,r)} A'!(s'+x)={elem(Ap,sP+xx,r)} d'={delta(Ap,r)}")
            Q=frontier
            if len(visited)>CAP: break
    print(f"\nnotasc interior cols total={notasc_total} overall-ineq-ok={notasc_overall_ok}")
    print(f"General fact G: x interior of A' => A'!s'[r] < A'!(s'+x)[r] :  OK={G_ok}  BAD={G_bad}")
    print("G bad (A',s',x,r,A's',A'(s'+x),asc,t',l1'):")
    for e in gbad: print("  ",e)

if __name__=='__main__': main()
