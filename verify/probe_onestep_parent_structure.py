#!/usr/bin/env python3
"""
probe_onestep_parent_structure.py

For ascending column j of expansion E = expand(A,n) at level k < t = mpl(E),
report what m_parent(E, k, idx_B(c,j)) actually is, partitioned into:
  - None
  - G        (parent < l0 of E)
  - inblock  (idx_B(c,0) <= parent < idx_B(c,j))   same block, smaller col
  - prev     (parent == idx_B(c-1,j))               immediate predecessor block, same col j
  - other    (anything else)

Also separately tally whether m_anc(E, k, idx_B(c,j), idx_B(c-1,j)) holds
(the property onestep_anc_when_ascends actually claims).

Asc proxy (ascending column j at level k):
  k < t AND elem(E, idx_B(c,j), k) > elem(E, idx_B(c-1,j), k)
(strictly bumped between consecutive blocks at row k; this is the easy
empirical proxy for `ascends`).

Seeds: genuine 2-column [[0]*k,[1]*k] for k in 2..7.  BFS depth<=11, CAP=7000.
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,
                                         mpl,b0,l1,set_array,expand)

def idxB(c,j,l0A,l1A): return l0A + c*l1A + j

# bucket counters by lA category
CATS = ['l1=1','l1=2','l1>=3']
def catkey(lA):
    if lA<=1: return 'l1=1'
    if lA==2: return 'l1=2'
    return 'l1>=3'

# parent-bucket -> count, per cat
buckets = {c:{'None':0,'G':0,'inblock':0,'prev':0,'other':0} for c in CATS}
totals = {c:0 for c in CATS}
anc_true = {c:0 for c in CATS}      # m_anc(E,k,ic,icm) holds
anc_true_parent_other = {c:0 for c in CATS}  # parent != icm but ancestor still true
examples_other = []   # parent != icm, parent not None, parent != G, not inblock
examples_none = []
examples_inblock = []

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)

CAP=7000;depth=11

for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A);sA=b0(A);lA=l1(A);l0A=sA
        if sA is not None and lA>=1 and len(A)<=40:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E);tp=mpl(E)
                if tp is None: set_array(A); continue
                lenE=len(E)
                sE=b0(E); lE=l1(E)
                if sE is None: set_array(A); continue
                cat = catkey(lE)
                for j in range(0,lE):
                    for c in range(1,n+1):
                        ic=idxB(c,j,sE,lE); icm=idxB(c-1,j,sE,lE)
                        if ic>=lenE or icm>=lenE: continue
                        # bounds for c-th block column 0
                        ic0=idxB(c,0,sE,lE)
                        for k in range(0,tp+1):
                            if k>=len(E[ic]) or k>=len(E[icm]): continue
                            if elem(E,ic,k) <= elem(E,icm,k): continue  # not bumped at k
                            # ascending proxy holds at (c,j,k)
                            pp = m_parent(E,k,ic)
                            totals[cat]+=1
                            if pp is None:
                                buckets[cat]['None']+=1
                                if len(examples_none)<3:
                                    examples_none.append(('None',cat,fmt(A),'n',n,'j',j,'c',c,'k',k,'ic',ic,'sE',sE,'lE',lE))
                                bucket_label='None'
                            elif pp < sE:
                                buckets[cat]['G']+=1
                                bucket_label='G'
                            elif ic0 <= pp < ic:
                                buckets[cat]['inblock']+=1
                                if len(examples_inblock)<4:
                                    examples_inblock.append(('inblock',cat,fmt(A),'n',n,'j',j,'c',c,'k',k,'ic',ic,'pp',pp,'icm',icm))
                                bucket_label='inblock'
                            elif pp == icm:
                                buckets[cat]['prev']+=1
                                bucket_label='prev'
                            else:
                                buckets[cat]['other']+=1
                                if len(examples_other)<6:
                                    examples_other.append(('other',cat,fmt(A),'n',n,'j',j,'c',c,'k',k,'ic',ic,'pp',pp,'icm',icm,'sE',sE,'lE',lE))
                                bucket_label='other'
                            # ancestor relation (what the lemma actually claims)
                            anc_ok = m_anc(E,k,ic,icm)
                            if anc_ok:
                                anc_true[cat]+=1
                                if bucket_label!='prev':
                                    anc_true_parent_other[cat]+=1
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    if d%2==0 or d==depth-1:
        tot=sum(totals.values())
        print(f"depth {d}: vis={len(seen)} samples={tot}",flush=True)
    if len(seen)>CAP: break

print("")
print("="*78)
print("Parent breakdown for ascending (c,j,k), partitioned by l1 (=lE) category")
print("="*78)
for cat in CATS:
    T=totals[cat]
    if T==0:
        print(f"\n[{cat}] total=0 (no samples)")
        continue
    b=buckets[cat]
    print(f"\n[{cat}] total={T}")
    for k in ['None','G','inblock','prev','other']:
        v=b[k]
        pct = 100.0*v/T if T else 0.0
        print(f"   parent={k:8s}: {v:6d}  ({pct:5.1f}%)")
    print(f"   m_anc(E,k,ic,icm) holds: {anc_true[cat]}/{T}  "
          f"({100.0*anc_true[cat]/T:5.1f}%)")
    print(f"   ... of which parent != icm: {anc_true_parent_other[cat]}  "
          f"(parent differs but ancestor relation still true)")

print("\n--- examples: parent == None ---")
for e in examples_none: print(" ",e)
print("\n--- examples: parent in same block (inblock) ---")
for e in examples_inblock: print(" ",e)
print("\n--- examples: parent = 'other' (neither G/inblock/prev/None) ---")
for e in examples_other: print(" ",e)
