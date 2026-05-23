#!/usr/bin/env python3
"""
STRIP-CORRECT structural characterization to UNDERSTAND why Q_t holds
(s = b0_start is a level-t ancestor of every B0 column). This is read-only
analysis to find the proof mechanism; it edits nothing.

For each stripped BMS A (t=max_parent_level>0, s=b0_start, C=last_col_idx):
  For each B0 column q = s+j (0<j<l1):
    - pt(q)  = m_parent A t q          : where does the level-t parent land?
    - in_B0  = (s <= pt(q) < q)        : does it stay in [s, q)?
    - q_anc_C = m_ancestor A t q C ... no; ancestor goes downward. Check if
      q is a t-ancestor of C is meaningless (q<C). Instead check whether C's
      t-parent chain passes through q, and whether q's t-parent chain hits s.
Tally:
  A) pt(q) is None
  B) pt(q) < s        (jumps below s) -- if any, level-t chain_step FALSE
  C) pt(q) in [s,q)   (good)
  D) fraction of B0 cols q that lie ON C's level-t ancestor chain
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
def t_chain(A,t,i):  # set of columns on i's level-t parent chain
    s=set(); p=m_parent(A,t,i)
    while p is not None and p not in s:
        s.add(p); p=m_parent(A,t,p)
    return s
def expand(text,n):
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        return strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: return None

def main():
    seeds=["(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)",
           "(0,0,0)(1,2,0)(1,1,1)","(0,0,0,0)(1,2,3,4)",
           "(0,0)(1,1)(2,0)","(0,0)(1,1)(2,0)(3,1)"]
    visited=set(); CAP=1500
    nA=0; nq=0; A_none=0; B_below=0; C_in=0; on_Cchain=0
    examples=[]
    for seed in seeds:
        if len(visited)>CAP: break
        q=[strip(parse(seed))]; visited.add(fmt(q[0]))
        for d in range(4):
            frontier=[]
            for A in q:
                for n in range(1,4):
                    ex=expand(fmt(A),n)
                    if ex is None: continue
                    key=fmt(ex)
                    if key in visited: continue
                    visited.add(key); frontier.append(ex)
                    t=max_parent_level(ex); s=b0_start(ex); L1=l1(ex)
                    if t is None or t==0 or s is None or L1<2: continue
                    C=len(ex)-1
                    Cchain=t_chain(ex,t,C)
                    nA+=1
                    for j in range(1,L1):
                        col=s+j; nq+=1
                        pt=m_parent(ex,t,col)
                        if pt is None: A_none+=1
                        elif pt<s: B_below+=1
                        elif s<=pt<col:
                            C_in+=1
                            if col in Cchain: on_Cchain+=1
                        if pt is not None and not pt<s and len(examples)<3 and j==1:
                            examples.append((key,s,t,col,pt,col in Cchain))
            q=frontier
            if len(visited)>CAP: break
    print(f"Analyzed {nA} BMS, {nq} B0 columns (q=s+j).")
    print(f"  pt(q)=None        : {A_none}")
    print(f"  pt(q) < s (BAD)   : {B_below}")
    print(f"  pt(q) in [s,q)    : {C_in}")
    print(f"  of those, q on C's t-chain: {on_Cchain} / {C_in}")
    print("examples (key,s,t,q,pt(q),q_on_Cchain):")
    for e in examples: print("  ",e)

if __name__=='__main__': main()
