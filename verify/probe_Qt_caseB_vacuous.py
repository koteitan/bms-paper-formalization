#!/usr/bin/env python3
"""
STRIP-CORRECT rigorous verification before restructuring case_B_pureA to
be vacuous. Two claims that MUST both hold (else the restructure is unsound):

  (Q_t)    for BMS A (stripped), t=max_parent_level>0, s=b0_start,
           every interior B_0 column s+j (0<j<l1):  m_ancestor A t (s+j) s
  (VAC)    for every level r < t and every interior B_0 column s+j:
           ascends A j r  (== m_ancestor A r (s+j) s, since 0<j<t=m0).
           i.e. NO non-ascending B_0 column exists at any level r<t,
           so Hunter case B (Suc k' < t, not ascends) is VACUOUS.

If (Q_t)/(VAC) hold with 0 violations, then case_B_pureA (which assumes
Suc k'<t AND not ascends A j (Suc k')) has contradictory hypotheses and is
vacuously true -- safe to prove via Q_t ex-falso and delete chain_step.

If ANY violation -> DO NOT restructure (Q_t false, would be the consec trap).
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
    qt_fail=[]; vac_fail=[]
    for j in range(1,L1):
        if not m_anc(A,t,s+j,s):
            qt_fail.append((j,))
        for r in range(t):
            if not m_anc(A,r,s+j,s):
                vac_fail.append((r,j)); break
    return (qt_fail,vac_fail)

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); tested=0; qf=0; vf=0; first=[]; CAP=2500
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
                    qtf,vacf=r
                    if qtf:
                        qf+=1
                        if len(first)<6: first.append(("Qt",key,qtf[:2]))
                    if vacf:
                        vf+=1
                        if len(first)<6: first.append(("VAC",key,vacf[:2]))
            q=nq
            if len(visited)>CAP: break
    print(f"Tested {tested} stripped BMS (t>0).")
    print(f"(Q_t) m_ancestor A t (s+j) s fails : {qf}")
    print(f"(VAC) some B_0 col not-ascend r<t  : {vf}")
    for tag,k,ex in first: print(f"  {tag}-FAIL {k}: {ex}")
    if qf==0 and vf==0:
        print("BOTH HOLD: Q_t true, case B (Suc k'<t, not ascends) is VACUOUS. Safe to restructure.")

if __name__=='__main__': main()
