#!/usr/bin/env python3
"""
Probe to design the BMS.induct expand-case for the invariant
    elem A i 0 = level-0 m_parent chain length (depth).
For several A and n, print:
  - row0(A)        : [elem A i 0 for all cols]
  - chainlen0(A)   : [level-0 chain length per col]   (== row0 if invariant holds)
  - row0(A[n])     : row-0 of the expansion
  - chainlen0(A[n])
  - structural markers: |G|, |B0|, s=b0_start, t=max_parent_level
so we can SEE how row-0 transforms G ++ (B0,B1,...,Bn) and how the chain extends.
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
def last_idx(A): return len(A)-1
def mpl(A):
    last=last_idx(A)
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0(A):
    m0=mpl(A); return m_parent(A,m0,last_idx(A)) if m0 is not None else None
def expand(t,n):
    try: return subprocess.run([YA,f"{t}[{n}]"],capture_output=True,text=True,timeout=10).stdout.strip()
    except: return None

def row0(A): return [elem(A,i,0) for i in range(len(A))]
def cl0(A):  return [chainlen0(A,i) for i in range(len(A))]

def show(txt,n):
    A=parse(txt); s=b0(A); t=mpl(A)
    e=expand(txt,n)
    if not e: return
    E=parse(e)
    print(f"A = {txt}   n={n}   s={s} t={t} |A|={len(A)}")
    print(f"  row0(A)     = {row0(A)}")
    print(f"  chain0(A)   = {cl0(A)}   match={row0(A)==cl0(A)}")
    print(f"  A[{n}] = {e}")
    print(f"  row0(A[n])  = {row0(E)}")
    print(f"  chain0(A[n])= {cl0(E)}   match={row0(E)==cl0(E)}")
    print()

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)"]
    visited=set(seeds); samples=[]
    for seed in seeds:
        queue=[seed]
        for depth in range(3):
            nxt=[]
            for bt in queue:
                for n in range(1,3):
                    e=expand(bt,n)
                    if e and e not in visited:
                        visited.add(e); nxt.append(e); samples.append(e)
            queue=nxt
    for txt in samples[:14]:
        for n in (1,2):
            show(txt,n)

if __name__=='__main__': main()
