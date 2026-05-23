#!/usr/bin/env python3
"""STRIP-CORRECT. R2 (l1'=1, B=A' predecessor, A=B[n], s=b0_start A < l0(B)).
Goal: find the PROOF MECHANISM for H4/R2a (m_ancestor B t c s for s<c<=l0(B)).

Test the candidate mechanism:
 (M1) G'-preservation of t-parent: for columns p in G' region (p < l0(B)),
      m_parent A t p == m_parent B t p  (the t-parent in the expansion equals
      the t-parent in B, since G' is copied unchanged and earlier cols too).
      If M1 holds, the t-parent chain of any G' column is identical in A and B.
 (M2) s is on the t-parent chain of l0(B)-as-seen... actually test directly:
      in B, is m_ancestor B t l0(B) s ? (=H4) and is the chain B-internal?
 (M3) KEY: s = m_parent A t C (C=last of A). Walk the t-parent chain of C in A.
      Does it reach l0(B)-region then continue into G' to s, with the G' part
      matching B's chain? Report: first chain element < l0(B) (entry into G'),
      and whether from there the A-chain == B-chain down to s.
 (M4) Simpler: in B, what is m_parent B t (l0 B)? Is the chain l0(B)->...->s
      entirely within B and equal to A's chain restricted to G'?"""
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
def chain(A,m,i):  # t-parent chain from i downward
    out=[]; p=m_parent(A,m,i); seen=set()
    while p is not None and p not in seen:
        seen.add(p); out.append(p); p=m_parent(A,m,p)
    return out
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
    m1_ok=m1_bad=0     # m_parent A t p == m_parent B t p for p<l0(B)
    h4_inB_ok=h4_inB_bad=0   # m_anc B t l0(B) s
    m3_chain_match=0; m3_chain_mismatch=0  # A-chain G'-part == B-chain to s
    bad=[]
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
                    if sB is None or l1B!=1: continue
                    if not s < l0B: continue
                    n+=1
                    # M1: t-parent preservation in G' region (p in [0,l0B))
                    for p in range(0, l0B):
                        if m_parent(A,t,p)==m_parent(B,t,p): m1_ok+=1
                        else:
                            m1_bad+=1
                            if len(bad)<8: bad.append(("M1",fmt(B),nn,p,t,m_parent(A,t,p),m_parent(B,t,p)))
                    # H4 inside B: m_anc B t l0B s
                    if m_anc(B,t,l0B,s): h4_inB_ok+=1
                    else:
                        h4_inB_bad+=1
                        if len(bad)<8: bad.append(("H4inB",fmt(B),nn,s,l0B,t,"chainB=",chain(B,t,l0B)))
                    # M3: A-chain of C, its part with index < l0B, vs B-chain of l0B to s
                    cA=chain(A,t,len(A)-1)
                    cA_Gp=[x for x in cA if x < l0B]
                    cB=chain(B,t,l0B)  # from l0B down
                    # does cB end at s and is prefix-compatible with cA_Gp?
                    if s in cB and cA_Gp and cA_Gp[-1]==s and cB[-1]==s:
                        m3_chain_match+=1
                    else:
                        m3_chain_mismatch+=1
                        if len(bad)<12: bad.append(("M3",fmt(B),nn,"cA_Gp=",cA_Gp,"cB=",cB,"s=",s))
            Q=frontier
            if len(visited)>CAP: break
    print(f"R2 G'-internal cases: {n}")
    print(f"M1  m_parent A t p == m_parent B t p (p<l0B):  OK={m1_ok}  BAD={m1_bad}")
    print(f"H4  m_anc B t l0B s (H4 inside B):              OK={h4_inB_ok}  BAD={h4_inB_bad}")
    print(f"M3  A-chain(C)|G' ends at s & B-chain(l0B) ends at s: match={m3_chain_match} mismatch={m3_chain_mismatch}")
    for x in bad: print("  ",x)

if __name__=='__main__': main()
