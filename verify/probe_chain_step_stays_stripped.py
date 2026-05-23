#!/usr/bin/env python3
"""
STRIP-CORRECT re-verification of bms_b0_chain_step_stays (the lone remaining
(ii) crux):

  For A in BMS (stripped), t = max_parent_level A, s = b0_start A,
  for every level r < t and every column p with
     m_parent A r p = Some q  and  q > s,
  we require:  m_parent A r q = Some q2  (NOT None)  AND  q2 >= s.

i.e. once a level-r m-parent chain is at a column q strictly above s but
inside the bad part, the next step stays >= s (does not skip below s, and
does not terminate).

CRITICAL: yaBMS does NOT strip; Hunter BMS does. strip changes
b0_start/max_parent_level. So we strip every expansion before computing
s/t (see feedback_strip_before_bms_verify).
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
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def check(A):
    t=max_parent_level(A); s=b0_start(A)
    if t is None or t==0 or s is None: return None
    bad=[]
    for r in range(t):                 # r < t
        for p in range(len(A)):
            q=m_parent(A,r,p)
            if q is None or not (q>s): continue
            q2=m_parent(A,r,q)
            if q2 is None or not (q2>=s):
                bad.append((r,p,q,q2))
    return bad

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0; viol=0; first=[]; CAP=2500
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
                    b=check(ex)
                    if b is None: continue
                    tested+=1
                    if b:
                        viol+=1
                        if len(first)<6: first.append((key,b[:3]))
            q=nq
            if len(visited)>CAP: break
    print(f"Tested {tested} stripped BMS (t>0).")
    print(f"chain_step_stays violations: {viol}")
    if viol==0:
        print("HOLDS: level-r m-parent chain stays >= s (and not None) once above s.")
    else:
        for k,b in first: print(f"  VIOL {k}: (r,p,q,q2)={b}")

if __name__=='__main__': main()
