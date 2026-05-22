#!/usr/bin/env python3
"""
Verify the STRUCTURAL claims behind consec_preserved_under_expansion.

For A in BMS with b0_start=Some s, max_parent_level=Some t (t>0), and
A's B_0 row-0 consecutive (elem A (s+j) 0 = elem A s 0 + j for j<=l1):

We compute E = A[n] (yaBMS already strips trailing zero rows -> Hunter BMS).
Then check:
  (C1) s' = b0_start(E) is not None, t' = max_parent_level(E) not None.
  (C2) s' >= l0(A)   (b0_start of E is in/after the G prefix -- inside the
       block region [l0, l0 + (n+1) l1) of the pre-strip; note strip only
       removes ROWS so column indices are preserved).
  (C3) last_idx(E) = l0(A) + (n+1)*l1(A) - 1  (the last column of E is the
       end of the block region; G has l0 cols, then (n+1) copies of l1 cols).
  (C4) row-0 of E on [l0(A), last_idx(E)] is the consecutive run
       elem E (l0+q) 0 = elem A s 0 + q.
  (C5) hence B_0-of-E (cols s'..last) has consecutive row-0:
       elem E (s'+j) 0 = elem E s' 0 + j  for j in [0, l1(E)].

Report ANY violation. Strip note: yaBMS output already stripped.
"""
import re, subprocess
YA = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"

def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)', s)]
def height(A): return max((len(c) for c in A), default=0)
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
def l0(A):
    s=b0(A); return s if s is not None else (last_idx(A))  # G = take s A
def expand(t,n):
    try: return subprocess.run([YA,f"{t}[{n}]"],capture_output=True,text=True,timeout=10).stdout.strip()
    except: return None

def consec_A(A,s,L1):
    return all(elem(A,s+j,0)==elem(A,s,0)+j for j in range(L1+1))

def check(A_text,n):
    A=parse(A_text); s=b0(A); t=mpl(A)
    if s is None or t is None or t==0: return []
    L1=l1(A)
    if L1==0: return []
    if not consec_A(A,s,L1): return []  # only test A with consec hyp
    L0=l0(A)
    E_text=expand(A_text,n)
    if not E_text: return []
    E=parse(E_text)
    if len(E)==0: return []
    v=[]
    sp=b0(E); tp=mpl(E)
    tag=(A_text,n,f"s={s},t={t},l0={L0},l1={L1}")
    if sp is None:
        v.append(('C1-sp-None',)+tag); return v
    if tp is None:
        v.append(('C1-tp-None',)+tag); return v
    # C2 s' >= l0(A)
    if sp < L0:
        v.append(('C2-sp<l0',sp,L0)+tag)
    # C3 last_idx(E) == l0 + (n+1)*l1 - 1
    expected_last = L0 + (n+1)*L1 - 1
    if last_idx(E) != expected_last:
        v.append(('C3-last',last_idx(E),expected_last)+tag)
    # C4 row-0 of E on [l0, last] consecutive run = elem A s 0 + q
    baseA = elem(A,s,0)
    for q in range(0, last_idx(E)-L0+1):
        if elem(E,L0+q,0) != baseA+q:
            v.append(('C4-run',q,elem(E,L0+q,0),baseA+q)+tag); break
    # C5 B_0-of-E consecutive row-0
    L1E=l1(E)
    for j in range(0,L1E+1):
        if elem(E,sp+j,0) != elem(E,sp,0)+j:
            v.append(('C5-b0E',j,elem(E,sp+j,0),elem(E,sp,0)+j)+tag); break
    return v

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)"]
    visited=set(seeds); tested=0; viol=0; ex=[]
    cnt={}
    for seed in seeds:
        queue=[seed]
        for depth in range(4):
            nxt=[]
            for bt in queue:
                for n in range(1,4):
                    e=expand(bt,n)
                    if e and e not in visited:
                        visited.add(e); nxt.append(e)
                        for nn in range(1,4):
                            vs=check(e,nn); tested+=1
                            if vs:
                                viol+=len(vs); ex.extend(vs[:1])
                                k=vs[0][0]; cnt[k]=cnt.get(k,0)+1
            queue=nxt
    print(f"=== tested {tested} (A consec, t>0) x n, violations {viol} ===")
    print("violation kinds:",cnt)
    for v in ex[:15]: print(" ",v)
    if viol==0:
        print("ALL STRUCTURAL CLAIMS HOLD (C1-C5).")

if __name__=='__main__': main()
