#!/usr/bin/env python3
"""
Probe sub-conjectures that could discharge bms_b0_col_t_ancestor:
  Q_t : m_ancestor A t (s+j) s   for 0<j<l1   (the target, re-verify)
Sub-conjectures (try to find a route):
  (C1) every interior B0 col s+j is a level-t ancestor of C=last:
       m_ancestor A t C (s+j)
  (C2) the level-t m-parent of s+j lands in [s, s+j):   s <= mp_t(s+j) < s+j
  (C3) (C2)'s parent is itself an interior or =s
Report violations.
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
    qt_fail=[];c1_fail=[];c2_fail=[]
    for j in range(1,L1):
        if not m_anc(A,t,s+j,s): qt_fail.append(j)
        if not m_anc(A,t,C,s+j): c1_fail.append(j)
        pt=m_parent(A,t,s+j)
        if pt is None or not (s<=pt<s+j): c2_fail.append((j,pt))
    return (qt_fail,c1_fail,c2_fail)

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0; qf=c1f=c2f=0; first=[]; CAP=3000
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
                    qtf,c1,c2=r
                    if qtf: qf+=1
                    if c1:
                        c1f+=1
                        if len(first)<8: first.append(("C1",key,c1[:3]))
                    if c2:
                        c2f+=1
                        if len(first)<8: first.append(("C2",key,c2[:3]))
            q=nq
            if len(visited)>CAP: break
    print(f"Tested {tested} stripped BMS (t>0, l1>=2).")
    print(f"(Q_t)  m_ancestor A t (s+j) s   fails : {qf}")
    print(f"(C1)   m_ancestor A t C (s+j)   fails : {c1f}")
    print(f"(C2)   s<=mp_t(s+j)<s+j         fails : {c2f}")
    for tag,k,ex in first: print(f"  {tag}-FAIL {k}: {ex}")

if __name__=='__main__': main()
