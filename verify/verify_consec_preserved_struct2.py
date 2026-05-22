#!/usr/bin/env python3
"""
Refined structural probe. Earlier: only C2 (s'>=l0) fails, C3/C4/C5 hold.
So the goal C5 holds even when s' < l0. Investigate WHY: when s' < l0,
is row-0 of E consecutive on the LARGER range [s', last]?

New checks (only on A consec, t>0):
  (D1) row-0 of E consecutive on [s', last]:  elem E (s'+j) 0 = elem E s' 0 + j
       for all j in [0, last - s'].   (subsumes C5; this is the real claim)
  (D2) when s' < l0(A): characterize. report (s', l0, the row-0 at s'.. l0).
  (D3) does m_parent E 0 (l0) = Some(l0-1)? i.e. is the consecutive run
       glued continuously across the G|B boundary at column l0?
Report violations of D1. Also tally how often s' < l0 and by how much.
"""
import re, subprocess
YA="/home/koteitan/bms-paper/tmp/yaBMS/c/bms"
def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)',s)]
def height(A): return max((len(c) for c in A),default=0)
def elem(A,p,r): return A[p][r] if p<len(A) and r<len(A[p]) else 0
def m_parent(A,m,i):
    tgt=elem(A,i,m)
    for p in range(i-1,-1,-1):
        if elem(A,p,m)>=tgt: continue
        if m>0 and not m_anc(A,m-1,i,p): continue
        return p
    return None
def m_anc(A,m,i,j):
    p=m_parent(A,m,i)
    while p is not None:
        if p==j: return True
        if p<j: return False
        p=m_parent(A,m,p)
    return False
def last_idx(A): return len(A)-1
def mpl(A):
    last=last_idx(A)
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0(A):
    m0=mpl(A); return m_parent(A,m0,last_idx(A)) if m0 is not None else None
def l1(A):
    s=b0(A); return last_idx(A)-s if s is not None else 0
def l0(A):
    s=b0(A); return s if s is not None else last_idx(A)
def expand(t,n):
    try: return subprocess.run([YA,f"{t}[{n}]"],capture_output=True,text=True,timeout=10).stdout.strip()
    except: return None
def consec_A(A,s,L1):
    return all(elem(A,s+j,0)==elem(A,s,0)+j for j in range(L1+1))

def check(A_text,n):
    A=parse(A_text); s=b0(A); t=mpl(A)
    if s is None or t is None or t==0: return None
    L1=l1(A)
    if L1==0 or not consec_A(A,s,L1): return None
    L0=l0(A)
    E_text=expand(A_text,n);
    if not E_text: return None
    E=parse(E_text)
    if len(E)==0: return None
    sp=b0(E); tp=mpl(E)
    if sp is None or tp is None: return ('badE',A_text,n)
    last=last_idx(E)
    # D1: row-0 of E consecutive on [sp, last]
    d1ok=all(elem(E,sp+j,0)==elem(E,sp,0)+j for j in range(0,last-sp+1))
    below = sp < L0
    # D3 continuity at boundary l0 (if l0 in (sp,last])
    d3=None
    if sp < L0 <= last and L0>0:
        d3 = (elem(E,L0-1,0) < elem(E,L0,0))
    return ('ok' if d1ok else 'D1FAIL', A_text, n, s,t,L0,L1, sp,tp,last, below, d3,
            [elem(E,i,0) for i in range(max(0,sp), min(len(E),last+1))])

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)"]
    visited=set(seeds); tested=0; d1fail=0; below_cnt=0; d3false=0; ex=[]
    for seed in seeds:
        queue=[seed]
        for depth in range(4):
            nxt=[]
            for bt in queue:
                for n in range(1,4):
                    e=expand(bt,n)
                    if e and e not in visited:
                        visited.add(e); nxt.append(e)
                        for nn in range(1,4):
                            r=check(e,nn)
                            if r is None: continue
                            tested+=1
                            if r[0]!='ok':
                                d1fail+=1; ex.append(r)
                            if len(r)>10 and r[10]: below_cnt+=1
                            if len(r)>11 and r[11] is False: d3false+=1
            queue=nxt
    print(f"=== tested {tested}; D1 fails {d1fail}; s'<l0 count {below_cnt}; D3(boundary continuity) false {d3false} ===")
    for r in ex[:15]: print(" ",r)
    if d1fail==0:
        print("D1 HOLDS: row-0 of A[n] is consecutive on the WHOLE [s', last] -- subsumes C5.")

if __name__=='__main__': main()
