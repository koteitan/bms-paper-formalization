"""Trace the actual m_parent chain from idx_B(c,j) down to idx_B(c-1,j)
for ASCENDING column j at level k, l1>1.  Goal: discover the chain shape
so the onestep engine can be designed.

For each genuine 2-row seed expansion, ascending j (k<t, strictly bumped),
0<c<=n, l1>=2: walk m_parent from idx_B(c,j) and record the sequence of
columns until we hit idx_B(c-1,j) (or stop).  Classify each chain hop as
within-block-c (offset decreases, same block c) / cross to block c-1 / other.
Tally whether idx_B(c-1,j) is ALWAYS on the chain, and the typical hop shape.
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,mpl,b0,l1,set_array,expand)
def idxB(c,j,l0A,l1A): return l0A + c*l1A + j

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=6000;depth=10

reached=0; not_reached=0
first_hop=collections.Counter()   # classify first m_parent hop
chain_lens=collections.Counter()
ex_notreached=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA
        if sA is not None and lA>=2 and len(A)<=40:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);tp=mpl(E)
                if tp is None: set_array(A); continue
                lenE=len(E)
                for j in range(1,lA):          # j>0 (col0 is the proven l1=1-style case)
                    for c in range(1,n+1):
                        ic=idxB(c,j,l0A,lA); tgt=idxB(c-1,j,l0A,lA)
                        if ic>=lenE: continue
                        for k in range(0,tp):  # ascending levels k<t
                            if k>=len(E[ic]): continue
                            # ascending check: strictly bumped vs block c-1 same col
                            if elem(E,ic,k)<=elem(E,tgt,k): continue
                            # walk the parent chain
                            cur=ic; steps=0; hit=False; firsthop=None
                            seenp=set()
                            while True:
                                p=m_parent(E,k,cur)
                                if p is None: break
                                if steps==0:
                                    # classify first hop
                                    off=p-l0A
                                    pc=off//lA if off>=0 else -1; pj=off%lA if off>=0 else -1
                                    if p<l0A: firsthop=('G',)
                                    elif pc==c: firsthop=('inblock_c','dj',j-pj)
                                    elif pc==c-1: firsthop=('block_cm1','j',pj)
                                    else: firsthop=('other_block','pc',pc)
                                steps+=1
                                if p==tgt: hit=True; break
                                if p in seenp or steps>200: break
                                seenp.add(p); cur=p
                            if hit:
                                reached+=1; chain_lens[steps]+=1
                                if firsthop is not None: first_hop[firsthop]+=1
                            else:
                                not_reached+=1
                                if len(ex_notreached)<8:
                                    ex_notreached.append((fmt(A),'n',n,'j',j,'c',c,'k',k,'lA',lA))
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} reached={reached} not_reached={not_reached}",flush=True)
    if len(seen)>CAP: break

print(f"\n=== onestep chain idx_B(c,j)->idx_B(c-1,j), j>0, ascending, l1>=2 ===")
print(f"reached idx_B(c-1,j) on chain: {reached}; NOT reached: {not_reached}")
print(f"chain length distribution (hops to reach): {dict(chain_lens.most_common(12))}")
print(f"first-hop classification: {dict(first_hop.most_common(12))}")
if ex_notreached:
    print("NOT-reached examples (POTENTIAL onestep failure / different route):")
    for e in ex_notreached: print("  ",e)
