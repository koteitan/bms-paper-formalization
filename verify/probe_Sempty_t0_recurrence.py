#!/usr/bin/env python3
"""
Target the ?S-empty, t_A=0 (max_parent_level A = Some 0), inter-block escape
sub-case of bms_row0_eq_chainlen0 (BMS_Ancestry.thy ~line 1752).

For BMS A with max_parent_level A = Some 0, expansion A[n], and bumped column
k = idx_B(A,c,j) with 1<=c<=n, 0<j<l1, in the ?S-empty case, check:
  (R) recurrence: elem(A[n]) k 0 == (0 if mp None else 1 + elem(A[n]) p 0)
  (G) where parent p lands (G / which block) and whether p < l0
  (P) parent-of-k value vs parent-of-k0 value
  (V) value at k == value at k0  (block-shift invariance)
BFS over Hunter seeds.
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
    if m0 is None: return None
    return m_parent(A,m0,last_col(A))
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
    tested=0
    cases=0; rec_viol=0; val_viol=0
    p_in_G=0; p_in_block=0; p_none=0
    parent_val_mismatch=0
    examples=[]
    for seed in seeds:
        queue=[seed]
        for depth in range(4):
            nxt=[]
            for bt in queue:
                A=parse(bt)
                if max_parent_level(A)!=0:  # only t_A=0
                    # still expand to keep BFS reaching t=0 nodes
                    pass
                for n in range(1,4):
                    e=expand(bt,n)
                    if not e or e in visited: continue
                    visited.add(e); nxt.append(e); tested+=1
                # now analyze bt itself if t_A=0
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
                            k0=idx_B(A,0,j)
                            vk=elem(An,k,0); vk0=elem(An,k0,0)
                            # S
                            S=[jp for jp in range(j) if elem(An,idx_B(A,0,jp),0)<vk0]
                            if S: continue  # only ?S-empty
                            cases+=1
                            if vk!=vk0: val_viol+=1
                            # recurrence at k
                            p=m_parent(An,0,k)
                            rhs = 0 if p is None else 1+elem(An,p,0)
                            if vk!=rhs:
                                rec_viol+=1
                                if len(examples)<8:
                                    examples.append((e,c,j,k,vk,p,rhs,"REC"))
                            # parent landing
                            Cstart=idx_B(A,c,0)
                            if p is None: p_none+=1
                            elif p<L0: p_in_G+=1
                            else:
                                p_in_block+=1
                                if len(examples)<8:
                                    bt_idx=(p-L0)//L1; off=(p-L0)%L1
                                    examples.append((e,c,j,k,vk,p,f"B({bt_idx},{off})","PINBLK"))
                            # parent value vs parent-of-k0
                            p0=m_parent(An,0,k0)
                            pv = None if p is None else elem(An,p,0)
                            p0v= None if p0 is None else elem(An,p0,0)
                            if pv!=p0v:
                                parent_val_mismatch+=1
                                if len(examples)<8:
                                    examples.append((e,c,j,k,vk,pv,p0v,"PVAL"))
            queue=nxt
    print(f"tested {tested} BMS; ?S-empty t0 bumped cases: {cases}")
    print(f"  recurrence violations: {rec_viol}")
    print(f"  value(k)!=value(k0)  : {val_viol}")
    print(f"  parent landing: G={p_in_G}  in-block={p_in_block}  None={p_none}")
    print(f"  parent-val != parent(k0)-val : {parent_val_mismatch}")
    if examples:
        print("examples:")
        for ex in examples: print("  ",ex)

if __name__=='__main__': main()
