#!/usr/bin/env python3
"""
Conjecture (from probe): for A in BMS with max_parent_level t>0, b0_start=s,
the level-0 m_parent of every interior/edge B_0 column s+j (1<=j<=l1) is
EXACTLY the immediately preceding column s+(j-1).
Equivalently: row-0 is strictly increasing across consecutive B_0 columns:
    elem A (s+j-1) 0 < elem A (s+j) 0   for j in [1, l1].
If TRUE universally, m_ancestor A 0 (s+j) s follows by a trivial consecutive
chain, closing the (*) core.

Test exhaustively via BFS; report ANY violation.
"""
import re, subprocess
YA="/home/koteitan/bms-paper/tmp/yaBMS/c/bms"
def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)',s)]
def height(A): return max((len(c) for c in A),default=0)
def elem(A,p,r): return A[p][r] if p<len(A) and r<len(A[p]) else 0
def m_parent(A,m,i):
    tgt=elem(A,i,m)
    for p in range(i-1,-1,-1):
        if elem(A,p,m)>=tgt: continue
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
def last_idx(A): return len(A)-1
def mpl(A):
    last=last_idx(A)
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0(A):
    m0=mpl(A); return m_parent(A,m0,last_idx(A)) if m0 is not None else None
def l1(A):
    s=b0(A); return last_idx(A)-s if s is not None else 0
def expand(t,n):
    try: return subprocess.run([YA,f"{t}[{n}]"],capture_output=True,text=True,timeout=10).stdout.strip()
    except: return None

def check(A_text):
    A=parse(A_text); s=b0(A); t=mpl(A)
    if s is None or t is None or t==0: return []
    L1=l1(A); v=[]
    for j in range(1,L1+1):
        # conjecture: m_parent A 0 (s+j) = s+(j-1)
        mp=m_parent(A,0,s+j)
        consec = elem(A,s+j-1,0) < elem(A,s+j,0)
        if mp != s+j-1:
            v.append(('mp',j,mp,s+j-1,A_text))
        if not consec:
            v.append(('row0',j,elem(A,s+j-1,0),elem(A,s+j,0),A_text))
    return v

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
                        visited.add(e); nxt.append(e)
                        vs=check(e); tested+=1
                        if vs:
                            viol+=len(vs); ex.extend(vs[:2])
            queue=nxt
    print(f"=== tested {tested} BMS (t>0), violations {viol} ===")
    if viol==0:
        print("CONJECTURE HOLDS: m_parent A 0 (s+j) = s+(j-1) for all B_0 cols (t>0).")
        print("=> row-0 strictly increasing on B_0 => consecutive level-0 chain => (*) core closed.")
    else:
        for v in ex[:10]: print(" ",v)

if __name__=='__main__': main()
