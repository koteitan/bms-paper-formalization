#!/usr/bin/env python3
"""
Case-B mechanism probe for Lemma 2.5 (ii), the single remaining sorry in
lemma_2_5_ii_clause_step.

Case-B inputs: A=Ap[n], Suc k' < t=max_parent_level(Ap), i<j<l1(Ap),
               NOT ascends Ap j (Suc k').   (kk := Suc k', so k' = kk-1)

We verify, eval-faithfully (m_parent/m_anc match the Isabelle defs):
  (1) iff: LHS = m_anc(A,kk,idx0j,idx0i) == RHS = m_anc(A,kk,idxnj,idxni)
      (MUST always hold: (ii) is a Hunter theorem)
  (2) nasc_chain0: for all x<j that are k'-ancestors of j in block 0,
      NOT ascends Ap x (Suc k').  (memory claims this is FALSE sometimes)
  (3) parent transfer: is m_parent(A,kk,idx_c_j) a block-copy across c=0,n?
      classify: both None / both within-own-block at same offset / both
      outside-own-block / MISMATCH.
idx_B(c,j) in A = l0(Ap) + c*l1(Ap) + j.
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
_ecache={}
def expand(text,n):
    key=(text,n)
    if key in _ecache: return _ecache[key]
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        v=strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: v=None
    _ecache[key]=v; return v

def collect(seeds,CAP):
    visited=set(); out=[]
    for seed in seeds:
        if len(visited)>CAP: break
        Q=[strip(parse(seed))]
        k0=fmt(Q[0])
        if k0 not in visited: visited.add(k0); out.append(Q[0])
        for d in range(5):
            frontier=[]
            for Ap in Q:
                for n in range(1,4):
                    A=expand(fmt(Ap),n)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); out.append(A); frontier.append(A)
            Q=frontier
            if len(visited)>CAP: break
    return out

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)",
           "(0,0,0)(1,1,1)(2,2,0)","(0,0,0)(1,1,1)(2,0,0)",
           "(0,0,0,0,0)(1,1,1,1,1)","(0,0,0)(1,1,1)(2,2,2)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,1,1,1)(2,2,2,0)"]
    CAP=900
    arrays=[A for A in collect(seeds,CAP) if len(A)<=22]
    # histogram of max_parent_level
    from collections import Counter
    hist=Counter()
    for A in arrays:
        t=max_parent_level(A); hist[t]+=1
    print("max_parent_level histogram:",dict(sorted(hist.items(),key=lambda kv:(kv[0] is None,kv[0]))))
    iff_ok=iff_bad=0; iff_bad_ex=[]
    nasc_chain_ok=nasc_chain_bad=0; ncb_ex=[]
    pt_both_none=pt_within=pt_outside=pt_mismatch=0; mism_ex=[]
    ncfail_iff_ok=ncfail_iff_bad=0
    caseB_inputs=0
    for Ap in arrays:
        sP=b0_start(Ap); tP=max_parent_level(Ap)
        l0P=l0(Ap); l1P=l1(Ap)
        if sP is None or tP is None or tP<2 or l1P<2: continue
        for n in range(1,4):
            A=expand(fmt(Ap),n)
            if A is None: continue
            for kk in range(1,tP):           # Suc k' = kk, k' = kk-1, kk<t
                kp=kk-1
                for j in range(1,l1P):
                    if ascends(Ap,j,kk): continue   # case-B: NOT ascends
                    caseB_inputs+=1
                    idx0j=l0P+j; idxnj=l0P+n*l1P+j
                    chain_fail=False
                    for x in range(0,j):
                        idx0x=l0P+x
                        if m_anc(A,kp,idx0j,idx0x) and ascends(Ap,x,kk):
                            chain_fail=True
                            if len(ncb_ex)<8: ncb_ex.append((fmt(Ap),n,kk,j,x))
                            break
                    if chain_fail: nasc_chain_bad+=1
                    else: nasc_chain_ok+=1
                    pp0=m_parent(A,kk,idx0j); ppn=m_parent(A,kk,idxnj)
                    def cls(pp,c):
                        if pp is None: return ('none',None)
                        bs=l0P+c*l1P
                        if bs<=pp<bs+l1P: return ('within',pp-bs)
                        return ('outside',None)
                    c0=cls(pp0,0); cn=cls(ppn,n)
                    if c0[0]=='none' and cn[0]=='none': pt_both_none+=1
                    elif c0[0]=='within' and cn[0]=='within' and c0[1]==cn[1]: pt_within+=1
                    elif c0[0]=='outside' and cn[0]=='outside': pt_outside+=1
                    else:
                        pt_mismatch+=1
                        if len(mism_ex)<8: mism_ex.append((fmt(Ap),n,kk,j,pp0,ppn,c0,cn))
                    for i in range(0,j):
                        idx0i=l0P+i; idxni=l0P+n*l1P+i
                        L=m_anc(A,kk,idx0j,idx0i)
                        R=m_anc(A,kk,idxnj,idxni)
                        if L==R: iff_ok+=1
                        else:
                            iff_bad+=1
                            if len(iff_bad_ex)<8: iff_bad_ex.append((fmt(Ap),n,kk,i,j,L,R))
                        if chain_fail:
                            if L==R: ncfail_iff_ok+=1
                            else: ncfail_iff_bad+=1
    print(f"arrays = {len(arrays)}   case-B inputs = {caseB_inputs}")
    print(f"(1) iff (must always hold): OK={iff_ok} BAD={iff_bad}")
    for e in iff_bad_ex: print("    iff BAD:",e)
    print(f"(2) nasc_chain0: OK={nasc_chain_ok} BAD(fails)={nasc_chain_bad}")
    for e in ncb_ex: print("    nasc_chain FAIL (Ap,n,kk,j,x):",e)
    print(f"    when nasc_chain FAILS, iff: OK={ncfail_iff_ok} BAD={ncfail_iff_bad}")
    print(f"(3) parent transfer: both_none={pt_both_none} within(same off)={pt_within} "
          f"outside={pt_outside} MISMATCH={pt_mismatch}")
    for e in mism_ex: print("    PT MISMATCH (Ap,n,kk,j,pp0,ppn,c0,cn):",e)

if __name__=='__main__': main()
