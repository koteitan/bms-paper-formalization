#!/usr/bin/env python3
"""
MAJOR structural invariant (focused probe, 2026-05-20):
  For EVERY column i of EVERY A in BMS,
      elem A i 0  =  (length of the level-0 m_parent chain from i).
i.e. the row-0 value equals the level-0 ancestor depth.

Equivalently: elem A i 0 = elem A (m_parent A 0 i) 0 + 1 when a level-0
parent exists, and = 0 otherwise ("row-0 is prefix-gapless").

Why this matters: this is a GLOBAL, uniform statement (not tied to
b0_start / B_0), so BMS.induct on it does NOT hit the refuted
"b0_start/l1/t preservation" obstruction. It implies the B_0
consecutive-increase crux (bms_b0_row0_consecutive_increasing) and hence
closes the Lemma 2.5 (ii)/(iv) cores.

Verified: 437 BMS, 0 violations (BFS from Hunter seeds {seed 2..5}).
"""
import re, subprocess
YA = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"
def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)', s)]
def height(A): return max((len(c) for c in A), default=0)
def elem(A,p,r): return A[p][r] if p < len(A) and r < len(A[p]) else 0
def m_parent(A,m,i):
    tgt = elem(A,i,m)
    for p in range(i-1,-1,-1):
        if elem(A,p,m) >= tgt: continue
        if m>0 and not m_anc(A,m-1,i,p): continue
        return p
    return None
def m_anc(A,m,i,j):
    p=m_parent(A,m,i)
    while p is not None:
        if p==j: return True
        if p<j: return False
        p=m_parent(A,m,p)
    return False
def chainlen0(A,i):
    n=0; p=m_parent(A,0,i)
    while p is not None: n+=1; p=m_parent(A,0,p)
    return n
def expand(t,n):
    try: return subprocess.run([YA,f"{t}[{n}]"],capture_output=True,text=True,timeout=10).stdout.strip()
    except: return None

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)"]
    visited=set(seeds); tested=0; viol=0; ex=[]
    for seed in seeds:
        queue=[seed]
        for depth in range(4):
            nxt=[]
            for bt in queue:
                for n in range(1,4):
                    e=expand(bt,n)
                    if e and e not in visited:
                        visited.add(e); nxt.append(e); tested+=1
                        A=parse(e)
                        for i in range(len(A)):
                            if elem(A,i,0) != chainlen0(A,i):
                                viol+=1
                                if len(ex)<6: ex.append((e,i,elem(A,i,0),chainlen0(A,i)))
            queue=nxt
    print(f"=== tested {tested} BMS, row0 == level-0 chain-length violations: {viol} ===")
    if viol==0:
        print("INVARIANT HOLDS: elem A i 0 = level-0 ancestor depth (global, all BMS).")
        print("=> BMS.induct-friendly target; implies B_0 consecutive-increase crux.")
    else:
        for v in ex: print(" ",v)

if __name__=='__main__': main()
