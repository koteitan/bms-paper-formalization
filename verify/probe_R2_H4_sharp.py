#!/usr/bin/env python3
"""STRIP-CORRECT. R2 (l1 B=1, A=B[n], s=b0_start A < l0 B). Sharp hypothesis:
 (SH) s == m_parent B t s'   where s'=b0_start B, t=max_parent_level A.
 i.e. the bad root of B[n] is exactly the t-parent (IN B) of B's bad root s'.
 Rationale: at level t (=max), bumped copies b0..bn tie (no bump since ascend
 needs level<t'), so C=bn's t-parent skips them into G' and lands at s' t-parent.
Also report the t==t' vs t>t' split and whether SH holds in each."""
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
    sh_ok=sh_bad=0
    teq=tgt=0
    sh_ok_teq=sh_ok_tgt=0
    bad=[]; tgt_samples=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]; visited.add(fmt(Q[0]))
        for dd in range(4):
            frontier=[]
            for B in Q:
                sB=b0_start(B); tB=max_parent_level(B)
                l0B=l0(B); l1B=l1(B)
                for nn in range(1,4):
                    A=expand(fmt(B),nn)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    if sB is None or l1B!=1 or tB is None: continue
                    if not s < l0B: continue
                    n+=1
                    # SH: s == m_parent B t s'  (s'=sB=b0_start B, but its index in B is l0B)
                    sprime_idx = l0B   # b0_start(B) index == l0B since l1B=1
                    mp = m_parent(B, t, sprime_idx)
                    if mp == s: sh_ok+=1; (sh_ok_teq:=sh_ok_teq)
                    if t==tB: teq+=1
                    else: tgt+=1
                    if mp==s:
                        if t==tB: sh_ok_teq+=1
                        else: sh_ok_tgt+=1
                    else:
                        sh_bad+=1
                        if len(bad)<10: bad.append(("SHbad",fmt(B),nn,"s=",s,"mp=",mp,"t=",t,"tB=",tB,"sprime_idx=",sprime_idx))
                    if t>tB and len(tgt_samples)<8:
                        tgt_samples.append((fmt(B),nn,"s=",s,"mp=",mp,"t=",t,"tB=",tB))
            Q=frontier
            if len(visited)>CAP: break
    print(f"R2 G'-internal cases: {n}")
    print(f"SH  s == m_parent B t s':  OK={sh_ok}  BAD={sh_bad}")
    print(f"   split: t==t':{teq} (SH ok {sh_ok_teq}),  t>t':{tgt} (SH ok {sh_ok_tgt})")
    for x in bad: print("  SHBAD",x)
    print("t>t' samples:")
    for x in tgt_samples: print("  ",x)

if __name__=='__main__': main()
