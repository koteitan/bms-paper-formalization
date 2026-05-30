"""Probe the off-chain case of elem_lt_below_t to find a proof handle.

Setup (base array A in BMS, b0_start=Some s, mpl=Some t, 0<m<t, 0<j<l1):
  C = last_col_idx A. s is the t-parent of C, hence a (Suc m')-ancestor
  (m=Suc m').  ON-chain (s+j is m'-ancestor of C): already proven.
  OFF-chain (s+j NOT an m'-ancestor of C): the open gap. We need
  elem A s m < elem A (s+j) m.

For each off-chain instance, record:
  - mp_j = m_parent A m (s+j): where does the off-chain column's m-parent go?
    classify: == s / < s (G) / in (s, s+j) interior B0 / None.
  - is s an m-ancestor of (s+j)?  (m_anc A m (s+j) s)
  - is s+j an m-ancestor of C at level m (not m')?  (m_anc A m C (s+j))
  - does elem A s m < elem A (s+j) m hold? (should: 0 viol)
Goal: find which handle (s ancestor of s+j? parent location?) is uniform.
"""
import sys, collections
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,mpl,b0,l1,set_array,height)

# enumerate base BMS arrays directly (no expansion needed: elem_lt_below_t is about A)
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,9)]
# Build a corpus of base arrays via a few manual expansions using yabms, but
# elem_lt_below_t is a BASE fact, so we just need many genuine BMS base arrays.
# Reuse the BFS over expansions to harvest diverse base arrays.
from verify.probe_vacuity_refute import expand
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=7000;depth=11

tot=0; lt_viol=0
mpj_cls=collections.Counter()
s_anc_sj=collections.Counter()   # is s an m-ancestor of s+j?
sj_anc_C_m=collections.Counter()  # is s+j an m-ancestor of C at level m?
ex=[]
for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); s=b0(A); t=mpl(A); lA=l1(A)
        if s is not None and t is not None and t>=2 and lA>=2:
            C=len(A)-1
            for m in range(1,t):           # 0<m<t (row 0 proven separately)
                mp_ = m-1
                for j in range(1,lA):
                    sj=s+j
                    if m>=len(A[sj]) or m>=len(A[s]): continue
                    # on-chain?  s+j is m'-ancestor of C
                    onchain = m_anc(A,mp_,C,sj)
                    if onchain: continue   # only off-chain
                    tot+=1
                    # the target fact
                    if not (elem(A,s,m)<elem(A,sj,m)): lt_viol+=1
                    # mp_j classification
                    pj=m_parent(A,m,sj)
                    if pj is None: mpj_cls['None']+=1
                    elif pj==s: mpj_cls['==s']+=1
                    elif pj<s: mpj_cls['<s(G)']+=1
                    elif pj<sj: mpj_cls['interior(s,sj)']+=1
                    else: mpj_cls['other']+=1
                    s_anc_sj[m_anc(A,m,sj,s)]+=1
                    sj_anc_C_m[m_anc(A,m,C,sj)]+=1
                    if (not (elem(A,s,m)<elem(A,sj,m))) and len(ex)<10:
                        ex.append((fmt(A),'s',s,'t',t,'m',m,'j',j))
        for n in range(1,3):
            if len(A)>34: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} offchain_tot={tot} lt_viol={lt_viol}",flush=True)
    if len(seen)>CAP: break

print(f"\n=== elem_lt_below_t OFF-CHAIN structure (0<m<t, 0<j<l1) ===")
print(f"off-chain instances: {tot}, target elem A s m < elem A (s+j) m violations: {lt_viol}")
print(f"m_parent A m (s+j) classification: {dict(mpj_cls.most_common())}")
print(f"is s an m-ancestor of (s+j) [m_anc A m (s+j) s]: {dict(s_anc_sj)}")
print(f"is (s+j) an m-ancestor of C at level m [m_anc A m C (s+j)]: {dict(sj_anc_C_m)}")
for e in ex: print("  LT-VIOL:",e)
