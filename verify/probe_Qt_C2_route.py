#!/usr/bin/env python3
"""
Try to find a PROVABLE route to C2 (s<=mp_t(s+j)<s+j) / Q_t.
Sub-probes for 0<j<l1, t=mpl>0, s=b0:
  (E)   mp_t(s+j) exists (not None)
  (A1)  m_ancestor A t (s+j) s  holds  AND  is there ALSO a route:
        s is a t-ancestor of s+j because: both s and s+j are <... hmm
  (D)   Is s+j a t-ancestor of C? -> known False (C1).
  Key idea route via chain_linear on source (s+j):
    s+j has t-parent p. We want p>=s. Suppose NOT (p<s). Then ...
  (F)   For the t-parent p of (s+j): does C have p as a t-ancestor?
        m_ancestor A t C p ?
  (G)   does m_ancestor A (t-1) (s+j) s hold? (the level below)
  (H)   elem A s t < elem A (s+j) t ? (row-t strict, needed for s to be
        a t-candidate of s+j)
  (I)   m_ancestor A (t-1) (s+j) s  AND elem A s t<elem A (s+j) t
        => s is a t-PARENT-CANDIDATE of s+j. Is s the LAST such? (=mp_t)
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
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def check(A):
    t=max_parent_level(A); s=b0_start(A); L1=l1(A)
    if t is None or t==0 or s is None or L1<2: return None
    C=len(A)-1
    f={'E':[],'G':[],'H':[],'F':[],'I_anc_t1':[],'I_elem':[]}
    for j in range(1,L1):
        p=m_parent(A,t,s+j)
        if p is None: f['E'].append(j)
        # G: m_anc t-1 (s+j) s
        if not m_anc(A,t-1,s+j,s): f['G'].append(j)
        # H: elem s t < elem (s+j) t
        if not (elem(A,s,t)<elem(A,s+j,t)): f['H'].append(j)
        # F: m_anc t C p (parent of s+j is t-ancestor of C)
        if p is not None and not m_anc(A,t,C,p): f['F'].append((j,p))
    return f

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0; agg={'E':0,'G':0,'H':0,'F':0}; first=[]; CAP=3000
    for seed in seeds:
        if len(visited)>CAP: break
        q=[strip(parse(seed))]; visited.add(fmt(q[0]))
        for d in range(4):
            nq=[]
            for A in q:
                for n in range(1,4):
                    ex=expand(fmt(A),n)
                    if ex is None: continue
                    key=fmt(ex)
                    if key in visited: continue
                    visited.add(key); nq.append(ex)
                    r=check(ex)
                    if r is None: continue
                    tested+=1
                    for kk in agg:
                        if r[kk]:
                            agg[kk]+=1
                            if len(first)<10: first.append((kk,key,r[kk][:3]))
            q=nq
            if len(visited)>CAP: break
    print(f"Tested {tested} stripped BMS (t>0, l1>=2).")
    print(f"(E) mp_t(s+j) exists fails        : {agg['E']}")
    print(f"(G) m_anc(t-1)(s+j) s   fails     : {agg['G']}")
    print(f"(H) elem s t < elem (s+j) t fails : {agg['H']}")
    print(f"(F) m_anc t C (parent) fails      : {agg['F']}")
    for tag,k,ex in first: print(f"  {tag}-FAIL {k}: {ex}")

if __name__=='__main__': main()
