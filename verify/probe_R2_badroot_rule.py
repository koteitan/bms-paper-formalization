#!/usr/bin/env python3
"""STRIP-CORRECT. R2 regime (l1'(A')=1): the bad root s of A=A'[n] lands inside G'
(s < l0'). GOAL: pin down the RULE for d = l0' - s, and what s IS in terms of A'.

Hypotheses to test:
 (H1) s = m_parent A' t' C'  ? i.e. the t'-parent of C' (last col of A')?
 (H2) s = m_parent A' t (C') where t = max_parent_level(A) (level may shift)?
 (H3) t (=max_parent_level A) relates to t' how?  t == t' ? t < t' ?
 (H4) s = the (t)-ancestor chain of C(=last of A) re-entering G' -- i.e. s is the
      t-parent in A of the first bumped block b0(=col l0'), or of C.
Also: is s an m-ancestor (in A') of s'(=l0') for relevant m? That would tie the
G'-region fact to ordinary A'-ancestry (usable as a sub-induction)."""
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
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,2,2)(3,3,0)"]
    visited=set(); CAP=3000
    n=0
    h1_ok=h1_bad=0      # s == m_parent A' t' C'
    t_eq_tp=0; t_lt_tp=0; t_gt_tp=0
    sanc_ok=0; sanc_bad=0   # is s an m_anc(A') of s'(=l0') for m=t ?
    samples=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for d in range(4):
            frontier=[]
            for Ap in Q:
                sP=b0_start(Ap); tP=max_parent_level(Ap)
                l0P=l0(Ap); l1P=l1(Ap)
                for nn in range(1,4):
                    A=expand(fmt(Ap),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    if sP is None or l1P!=1 or tP is None: continue
                    n+=1
                    Cp=len(Ap)-1   # last col of A'
                    # H1: s == t'-parent of C' in A'
                    h1 = m_parent(Ap,tP,Cp)
                    if h1==s: h1_ok+=1
                    else:
                        h1_bad+=1
                        if len(samples)<10: samples.append(("H1bad",fmt(Ap),nn,s,h1,t,tP,l0P))
                    # H3: t vs t'
                    if t==tP: t_eq_tp+=1
                    elif t<tP: t_lt_tp+=1
                    else: t_gt_tp+=1
                    # H4: is s an t-ancestor in A' of s'(=l0P, start of B0')?
                    if s < l0P:
                        if m_anc(Ap,t,l0P,s) or s==l0P: sanc_ok+=1
                        else:
                            sanc_bad+=1
            Q=frontier
            if len(visited)>CAP: break
    print(f"R2 (l1'=1) cases: {n}")
    print(f"H1  s == m_parent A' t' C' :  OK={h1_ok}  BAD={h1_bad}")
    print(f"H3  t vs t':  t==t':{t_eq_tp}  t<t':{t_lt_tp}  t>t':{t_gt_tp}")
    print(f"H4  s is t-anc(A') of s'(=l0'):  OK={sanc_ok}  BAD={sanc_bad}")
    for x in samples: print("  ",x)

if __name__=='__main__': main()
