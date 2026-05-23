#!/usr/bin/env python3
"""
STRIP-CORRECT probe for STRATEGY 1: where does the bad root of A=A'[n] land
relative to A'? We want to understand the derivation structure to attack
  bms_b0_col_elem_lt:  elem A s r < elem A (s+j) r  (r<=t, 0<j<l1).

Every non-seed BMS A is A'[n] for some BMS A', n>=1.  Compute for A':
  s'=b0_start, t'=max_parent_level, l0', l1', C'=last_col_idx, delta'(r)
and for A=strip(A'[n]):
  s=b0_start, t=max_parent_level, l0, l1, C=last_col_idx.

Closed form (from BMS_Defs): for x in B0 of A' (0<=x<l1'), block c in 0..n,
  column at idx_B(c,x) = l0' + c*l1' + x in (unstripped) A'[n] equals
     A'!(s'+x) [r]  + (c*delta'(r) if ascends'(x,r) else 0).
G part (first l0' cols) is just A' unchanged prefix.

QUESTIONS:
 Q1. Express s (bad root of A) in terms of l0',l1',n,s'. Is it s = l0'+ k*l1'
     for some predictable k (start of some Bk block)?  Or = s' (in G)?
 Q2. Express t (max_parent_level of A) vs t'.
 Q3. For r<=t, is elem A s r expressible via A' closed form, and does the
     elem_lt inequality reduce to a fact about A' (induction step)?
We tally s's location and print examples.
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
def l0(A):
    s=b0_start(A)
    return s if s is not None else 0
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
    # categories for s = b0_start(A) location
    cat = {}   # description -> count
    examples=[]
    t_rel = {}
    for seed in seeds:
        if len(visited)>CAP: break
        q=[strip(parse(seed))]; visited.add(fmt(q[0]))
        for d in range(4):
            frontier=[]
            for Ap in q:
                tP=max_parent_level(Ap); sP=b0_start(Ap)
                l0P=l0(Ap); l1P=l1(Ap)
                for n in range(1,4):
                    A=expand(fmt(Ap),n)
                    if A is None: continue
                    key=fmt(A)
                    if key in visited: continue
                    visited.add(key); frontier.append(A)
                    s=b0_start(A); t=max_parent_level(A); L1=l1(A); L0=l0(A)
                    if s is None or t is None or t==0 or L1<2: continue
                    # classify s relative to A' decomposition
                    # candidate block boundaries in unstripped A'[n]: l0P + c*l1P
                    desc="other"
                    if sP is not None:
                        for c in range(0,n+1):
                            if s == l0P + c*l1P:
                                desc=f"l0'+{c}*l1'"
                                break
                        if desc=="other" and s==sP:
                            desc="s'"
                        if desc=="other":
                            # is it l0'+c*l1'+x?
                            if l1P>0:
                                c=(s-l0P)//l1P; x=(s-l0P)%l1P
                                if 0<=c<=n and 0<=x<l1P:
                                    desc=f"l0'+c*l1'+x (c={c},x={x})"
                    cat[desc]=cat.get(desc,0)+1
                    # t relation
                    tr = f"t={t},t'={tP}"
                    key_tr = "t==t'" if t==tP else ("t<t'" if (tP is not None and t<tP) else "t>t' or t'None")
                    t_rel[key_tr]=t_rel.get(key_tr,0)+1
                    if len(examples)<8 and desc=="other":
                        examples.append((fmt(Ap),n,sP,tP,l0P,l1P,"->",key,s,t,L0,L1))
            q=frontier
            if len(visited)>CAP: break
    print("=== s=b0_start(A) location relative to A' decomposition ===")
    for k,v in sorted(cat.items(),key=lambda kv:-kv[1]): print(f"  {k:30s}: {v}")
    print("=== t=max_parent_level(A) vs t'=max_parent_level(A') ===")
    for k,v in sorted(t_rel.items(),key=lambda kv:-kv[1]): print(f"  {k:20s}: {v}")
    print("=== 'other' examples (A',n,s',t',l0',l1' -> A,s,t,l0,l1) ===")
    for e in examples: print("  ",e)

if __name__=='__main__': main()
