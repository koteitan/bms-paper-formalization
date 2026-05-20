#!/usr/bin/env python3
"""
Probe: understand WHY b0_start s is row-0 minimal in B_0, to design the
right induction hypothesis for proving (*) on interior B_0 columns.

For each BMS A (BFS from Hunter seeds) with max_parent_level t>0:
  - print s = b0_start, t, l1
  - for each B_0 column index c = s+j (j in [0, l1]):
      row-0 value elem A c 0, level-0 m_parent, and whether m_anc A 0 c s
  - flag the level-0 m_parent chain from the LAST column
Goal: find an invariant preserved under expansion.
"""
import re, subprocess
YA = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"

def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)', s)]
def height(A): return max((len(c) for c in A), default=0)
def elem(A,p,r):
    return A[p][r] if p < len(A) and r < len(A[p]) else 0
def m_parent(A,m,i):
    tgt = elem(A,i,m)
    for p in range(i-1,-1,-1):
        if elem(A,p,m) >= tgt: continue
        if m>0 and not m_anc(A,m-1,i,p): continue
        return p
    return None
def m_anc(A,m,i,j):
    p = m_parent(A,m,i)
    while p is not None:
        if p==j: return True
        if p<j: return False
        p = m_parent(A,m,p)
    return False
def last_idx(A): return len(A)-1
def max_parent_level(A):
    last=last_idx(A)
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0_start(A):
    m0=max_parent_level(A)
    return m_parent(A,m0,last_idx(A)) if m0 is not None else None
def l1(A):
    s=b0_start(A)
    return last_idx(A)-s if s is not None else 0
def chain0(A, start):
    """level-0 m_parent chain from start."""
    ch=[]; p=m_parent(A,0,start)
    while p is not None:
        ch.append(p); p=m_parent(A,0,p)
    return ch
def expand(t,n):
    try: return subprocess.run([YA,f"{t}[{n}]"],capture_output=True,text=True,timeout=10).stdout.strip()
    except: return None

def show(A_text):
    A=parse(A_text); s=b0_start(A); t=max_parent_level(A)
    if s is None or t is None or t==0: return
    L1=l1(A)
    if L1<2: return
    row0=[elem(A,s+j,0) for j in range(L1+1)]
    # level-0 m_parent of each B_0 col (relative offset, or 'G'/'None')
    mp0=[]
    for j in range(L1+1):
        p=m_parent(A,0,s+j)
        if p is None: mp0.append('N')
        elif p>=s: mp0.append(f"+{p-s}")
        else: mp0.append(f"G{p}")  # below s
    anc=[m_anc(A,0,s+j,s) for j in range(1,L1+1)]
    print(f"{A_text}")
    print(f"  s={s} t={t} l1={L1}  last=s+{L1}")
    print(f"  row0(s+j) j=0..l1: {row0}   (s-min? {all(row0[0]<row0[j] for j in range(1,L1+1))})")
    print(f"  mp0(s+j)  j=0..l1: {mp0}")
    print(f"  anc0(s+j)->s j=1..l1: {anc}   chain(last)={[(c-s if c>=s else f'G{c}') for c in chain0(A,s+L1)]}")
    print()

def main():
    seeds=["(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)"]
    visited=set(seeds); shown=0
    for seed in seeds:
        queue=[seed]
        for depth in range(3):
            nxt=[]
            for bt in queue:
                for n in range(1,4):
                    ex=expand(bt,n)
                    if ex and ex not in visited:
                        visited.add(ex); nxt.append(ex)
                        A=parse(ex); s=b0_start(A); t=max_parent_level(A)
                        if s is not None and t and t>0 and l1(A)>=2 and shown<25:
                            show(ex); shown+=1
            queue=nxt
    print(f"shown {shown} non-trivial B_0 cases")

if __name__=='__main__': main()
