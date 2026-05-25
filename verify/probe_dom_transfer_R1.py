#!/usr/bin/env python3
"""
Probe for dom_transfer_R1.

Claim (R1 block-start interior domination via DOM(A)+bump):
  Let A be genuine BMS, t=mpl(A)>=2, s=b0_start(A), L1=l1(A)>=2.
  Suppose DOM(A): for all 0<j<L1, m<t:  elem A s m < elem A (s+j) m.
  Then for any block c0<=n, any later interior column (c'',off'') with
  c0<=c''<=n, 0<=off''<L1, and (c''>c0 OR off''>0), and any m<t:
      V_blockstart(c0) := elem(A[n], idx_B c0 0) m
                        < elem(A[n], idx_B c'' off'') m =: V(c'',off'')
  where, by the bump formula,
      elem(A[n], idx_B c off) m = elem(A, s+off, m) + (asc(off,m) ? c*delta(m) : 0)
      asc(off,m) = (m<t and non_strict_ancestor A m (s+off) s)
      delta(m)  = elem(A,last,m) - elem(A,s,m)   (a nat, >=0)
  Note off=0 always ascends (m<t): non_strict_ancestor with d_idx=0 means s..s.

We screen on genuine BMS seeds (2-col), deep BFS, MECE: count EVERY (c0,c'',off'',m)
combination, report violations. We ALSO verify against the real expanded array A[n]
(yaBMS=Hunter eval-confirmed) that idx_B values match the bump formula, and that the
true b0_start(A[n]) (when a block-start) is indeed dominated by its interior columns.
"""
import re, subprocess
YA = "/home/koteitan/bms-paper/tmp/yaBMS/c/bms"
def parse(s):
    return [tuple(int(x) for x in m.group(1).split(',') if x.strip())
            for m in re.finditer(r'\(([^)]*)\)', s)]
def fmt(A): return ''.join('('+','.join(str(x) for x in c)+')' for c in A)
def strip(A):
    if not A: return A
    h=max((len(c) for c in A),default=0)
    while h>0 and all((c[h-1] if h-1<len(c) else 0)==0 for c in A): h-=1
    return [tuple(c[:h]) for c in A]
def elem(A,p,r):
    if p<0 or p>=len(A): return 0
    if r<0 or r>=len(A[p]): return 0
    return A[p][r]
def height(A): return max((len(c) for c in A),default=0)
_MPC={}
def set_array(A): _MPC.clear()
def m_parent(A,m,i):
    key=(m,i); c=_MPC.get(key,'?')
    if c!='?': return c
    res=None
    for pp in range(0,i):
        if elem(A,pp,m)>=elem(A,i,m): continue
        if m>0 and not m_anc(A,m-1,i,pp): continue
        res=pp
    _MPC[key]=res; return res
def m_anc(A,m,i,j):
    p=m_parent(A,m,i); seen=set()
    while p is not None:
        if p in seen: return False
        seen.add(p)
        if p==j: return True
        if p<j: return False
        p=m_parent(A,m,p)
    return False
def non_strict_anc(A,m,i,j):
    # ascends uses non_strict_ancestor A m (s+d) s : i==j OR m_ancestor
    return i==j or m_anc(A,m,i,j)
def mpl(A):
    last=len(A)-1
    if last<0: return None
    for m in range(height(A)-1,-1,-1):
        if m_parent(A,m,last) is not None: return m
    return None
def b0(A):
    t=mpl(A)
    return None if t is None else m_parent(A,t,len(A)-1)
def l1(A):
    s=b0(A); return 0 if s is None else len(A)-1-s
_ec={}
def expand(text,n):
    k=(text,n)
    if k in _ec: return _ec[k]
    try:
        r=subprocess.run([YA,f"{text}[{n}]"],capture_output=True,text=True,timeout=10)
        v=strip(parse(r.stdout.strip())) if r.stdout.strip() else None
    except: v=None
    _ec[k]=v; return v

def dom_holds(A,s,L1,t):
    for j in range(1,L1):
        for m in range(0,t):
            if not (elem(A,s,m) < elem(A,s+j,m)): return False
    return True

def asc(A,s,t,off,m):
    return m<t and non_strict_anc(A,m,s+off,s)
def delta(A,s,m):
    last=len(A)-1
    return elem(A,last,m)-elem(A,s,m)
def bumpval(A,s,t,c,off,m):
    base=elem(A,s+off,m)
    return base + (c*delta(A,s,m) if asc(A,s,t,off,m) else 0)

def check_formula(A,nmax=3):
    """For DOM(A)-satisfying A, verify the R1 domination claim across MECE buckets."""
    set_array(A)
    t=mpl(A); s=b0(A); L1=l1(A)
    if t is None or s is None or t<2 or L1<2: return None  # not in design regime
    if not dom_holds(A,s,L1,t): return None  # DOM(A) hypothesis false -> skip
    viol=[]; total=0
    for n in range(1,nmax+1):
        for c0 in range(0,n+1):
            for cpp in range(c0,n+1):
                for off in range(0,L1):
                    if cpp==c0 and off==0: continue  # the block-start itself
                    for m in range(0,t):
                        total+=1
                        bs=bumpval(A,s,t,c0,0,m)
                        iv=bumpval(A,s,t,cpp,off,m)
                        if not (bs<iv):
                            viol.append((n,c0,cpp,off,m,bs,iv))
    return (total,viol)

def main():
    seeds=[
      "(0,0)(1,1)","(0,0,0)(1,1,1)","(0,0,0,0)(1,1,1,1)","(0,0,0,0,0)(1,1,1,1,1)",
      "(0,0,0,0,0,0)(1,1,1,1,1,1)",
    ]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=3000; depth=11
    indesign=0; domsat=0; totalchecks=0; viol=0
    samples=[]
    for d in range(depth):
        fr=[]
        for A in Q:
            set_array(A)
            t=mpl(A); s=b0(A); L1=l1(A)
            if len(A)<=44 and t is not None and t>=2 and L1>=2:
                indesign+=1
                r=check_formula(A)
                if r is not None:
                    domsat+=1
                    tot,vs=r; totalchecks+=tot
                    if vs:
                        viol+=len(vs)
                        if len(samples)<25:
                            samples.append((fmt(A),t,s,L1,vs[:4]))
            for n in range(1,4):
                if len(A)>34: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"  depth {d}: visited={len(seen)} indesign={indesign} domsat={domsat} checks={totalchecks} viol={viol}",flush=True)
        if len(seen)>CAP: break
    print(f"FINAL visited={len(seen)} in-design(t>=2,l1>=2)={indesign} DOM-sat={domsat} formula-checks={totalchecks} VIOLATIONS={viol}",flush=True)
    for sm in samples: print("  VIOL",sm,flush=True)

if __name__=='__main__': main()
