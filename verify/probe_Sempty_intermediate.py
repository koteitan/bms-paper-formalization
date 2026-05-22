#!/usr/bin/env python3
"""
In the ?S-empty, t0 case for k=idx_B(c,j) (1<=c<=n), is there ANY index p in
[0,k) lying in an intermediate block (l0<=p, p<Cstart) with value < v?
And: is there any offset m (any), with elem(idx_B 0 m) < v ?  (global-min test)
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
def last_col(A): return len(A)-1
def max_parent_level(A):
    last=last_col(A)
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0_start(A):
    m0=max_parent_level(A)
    return None if m0 is None else m_parent(A,m0,last_col(A))
def l0(A):
    s=b0_start(A); return s if s is not None else len(A)
def l1(A):
    s=b0_start(A); return 0 if s is None else last_col(A)-s
def idx_B(A,t,j): return l0(A)+t*l1(A)+j
def expand(t,n):
    try: return subprocess.run([YA,f"{t}[{n}]"],capture_output=True,text=True,timeout=10).stdout.strip()
    except: return None
def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
           "(0,0)(1,2)","(0,0,0)(1,1,2)","(0,0,0)(1,2,2)","(0,0,0)(1,2,3)"]
    visited=set(seeds)
    inter_below_v=0; global_min_fail=0; cases=0
    ex=[]
    for seed in seeds:
        queue=[seed]
        for depth in range(4):
            nxt=[]
            for bt in queue:
                A=parse(bt)
                for n in range(1,4):
                    e=expand(bt,n)
                    if e and e not in visited: visited.add(e); nxt.append(e)
                if max_parent_level(A)!=0: continue
                L0=l0(A); L1=l1(A)
                if L1<1: continue
                for n in range(1,4):
                    e=expand(bt,n)
                    if not e: continue
                    An=parse(e)
                    for c in range(1,n+1):
                        for j in range(0,L1):
                            k=idx_B(A,c,j)
                            if k>=len(An): continue
                            k0=idx_B(A,0,j); v=elem(An,k0,0)
                            S=[jp for jp in range(j) if elem(An,idx_B(A,0,jp),0)<v]
                            if S: continue
                            cases+=1
                            Cstart=idx_B(A,c,0)
                            # intermediate-block indices below k with value < v
                            inter=[p for p in range(L0,k) if elem(An,p,0)<v]
                            if inter:
                                inter_below_v+=1
                                if len(ex)<6: ex.append(("INTER",e,c,j,v,inter[:5]))
                            # global-min over offsets: any m with b0-value < v
                            gm=[m for m in range(L1) if elem(An,idx_B(A,0,m),0)<v]
                            if gm:
                                global_min_fail+=1
            queue=nxt
    print(f"?S-empty t0 cases: {cases}")
    print(f"  has intermediate-block index <v in [l0,k): {inter_below_v}")
    print(f"  v NOT a global-min over offsets (exists m with b0[m]<v): {global_min_fail}")
    for e in ex: print("  ",e)
if __name__=='__main__': main()
