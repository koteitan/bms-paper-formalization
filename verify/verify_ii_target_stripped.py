#!/usr/bin/env python3
"""
STRIP-CORRECT verification of the genuine Lemma 2.5 (ii) target.

Two claims, for BMS A with t=max_parent_level>0 and s=b0_start, over all
B_0-internal columns j in [1, l1):
  (STRICT) elem A (s+j) 0 > elem A s 0          -- s is strict row-0 min of B_0
  (ANC)    m_ancestor A 0 (s+j) s                -- s is level-0 common ancestor

CRITICAL: yaBMS does NOT strip trailing all-zero rows; Hunter BMS does.
strip changes height -> changes max_parent_level/b0_start/l1. So we MUST
strip every expansion before computing structural quantities, else false
negatives (see feedback_strip_before_bms_verify). All earlier verify_b0_*
scripts omitted strip and are UNRELIABLE for s/l1-dependent claims.
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
    target=elem(A,i,m)
    res=None
    for p in range(0,i):          # pick LAST p<i with elem<target & ancestry
        if elem(A,p,m)>=target: continue
        if m>0 and not m_anc(A,m-1,i,p): continue
        res=p
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
    base=elem(A,s,0)
    bad_strict=[]; bad_anc=[]
    for j in range(1,L1):             # B_0 columns: indices s+1..s+l1-1 (j<l1)
        if s+j >= len(A): break
        if not (elem(A,s+j,0) > base):
            bad_strict.append((j,elem(A,s+j,0),base))
        if not m_anc(A,0,s+j,s):
            bad_anc.append((j,))
    return (bad_strict,bad_anc)

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0; cs=0; ca=0; first=[]
    CAP=2500
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
                    bs,ba=r
                    if bs:
                        cs+=1
                        if len(first)<5: first.append(("STRICT",key,bs)); print(f"STRICT-FAIL: {key} {bs[:3]}")
                    if ba:
                        ca+=1
                        if len(first)<5: first.append(("ANC",key,ba)); print(f"ANC-FAIL: {key} {ba[:3]}")
            q=nq
            if len(visited)>CAP: break
    print(f"\nTested {tested} stripped BMS.")
    print(f"(STRICT) elem(s+j,0)>elem(s,0): {'HOLDS' if cs==0 else f'FAILS ({cs})'}")
    print(f"(ANC)   m_ancestor 0 (s+j) s : {'HOLDS' if ca==0 else f'FAILS ({ca})'}")

if __name__=='__main__': main()
