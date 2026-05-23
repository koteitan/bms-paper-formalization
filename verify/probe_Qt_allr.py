#!/usr/bin/env python3
"""
Generalize C2 to all levels r<=t and check the candidate-membership route.
For 0<j<l1, t=mpl>0, s=b0, for each r in 0..t:
  (P_r)  s <= m_parent(A,r,s+j) < s+j      (parent in [s,s+j))
  (CAND_r) s is an r-parent-candidate of s+j:
           elem A s r < elem A (s+j) r  AND  (r==0 or m_anc(A,r-1,s+j,s))
  (ANC_r) m_anc(A,r,s+j,s)
Goal: confirm ANC_r holds for ALL r<=t (not just r=t), so we can prove the
whole family by induction on r (base r=0 is pure level-0, step uses CAND).
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
    f={'P':[],'CAND':[],'ANC':[]}
    for j in range(1,L1):
        for r in range(0,t+1):
            p=m_parent(A,r,s+j)
            if p is None or not (s<=p<s+j): f['P'].append((r,j,p))
            candok = (elem(A,s,r)<elem(A,s+j,r)) and (r==0 or m_anc(A,r-1,s+j,s))
            if not candok: f['CAND'].append((r,j))
            if not m_anc(A,r,s+j,s): f['ANC'].append((r,j))
    return f
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0; agg={'P':0,'CAND':0,'ANC':0}; first=[]; CAP=3000
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
    print(f"(P)    s<=mp_r(s+j)<s+j  all r<=t fails : {agg['P']}")
    print(f"(CAND) s is r-cand of s+j  all r<=t fails: {agg['CAND']}")
    print(f"(ANC)  m_anc r (s+j) s     all r<=t fails: {agg['ANC']}")
    for tag,k,ex in first: print(f"  {tag}-FAIL {k}: {ex}")
if __name__=='__main__': main()
