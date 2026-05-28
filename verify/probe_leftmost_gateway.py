import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,elem,m_anc,m_parent,mpl,b0,l1,set_array,expand,height)
def idxB(c,j,l0A,l1A): return l0A + c*l1A + j

# Genuine 2-row seeds only (per reference_genuine_bms_seeds_only).
seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=7000;depth=11

# At non-ascending level for column 0 (k >= t), check the leftmost gateway:
#   m_anc(E,k, idx_B(0,0), i)  ==  m_anc(E,k, idx_B(n,0), i)   for all i < l0
# Also tabulate m_parent behaviour of the two leftmost columns.
nB=0; vB=0; ex=[]
p_both_none=0; p_coincide=0; p_differ=0; p_total=0
n0_parent_in_G=0; n0_parent_in_bump=0; n0_parent_none=0
s_has_parent_above_t=0; s_total_above_t=0
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
                i0=idxB(0,0,l0A,lA); inn=idxB(n,0,l0A,lA)
                if inn>=lenE: set_array(A); continue
                # levels k >= t (column 0 non-ascending)
                hmax=min(len(E[i0]),len(E[inn]))
                for k in range(tp,hmax):
                    # gateway biconditional over G-targets i<l0
                    for i in range(0,l0A):
                        a0=m_anc(E,k,i0,i); an=m_anc(E,k,inn,i)
                        nB+=1
                        if a0!=an:
                            vB+=1
                            if len(ex)<8: ex.append(('B',fmt(A),'n',n,'k',k,'t',tp,'i',i,'lA',lA))
                    # parent comparison
                    p0=m_parent(E,k,i0); pn=m_parent(E,k,inn); p_total+=1
                    if p0 is None and pn is None: p_both_none+=1
                    elif p0==pn: p_coincide+=1
                    else: p_differ+=1
                    if pn is None: n0_parent_none+=1
                    elif pn<l0A: n0_parent_in_G+=1
                    else: n0_parent_in_bump+=1
                    if k>tp:
                        s_total_above_t+=1
                        if p0 is not None: s_has_parent_above_t+=1
                set_array(A)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key);fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} gw={nB}/v{vB} parent[none={p_both_none} coin={p_coincide} diff={p_differ}]",flush=True)
    if len(seen)>CAP: break
print(f"\ngateway biconditional viol = {vB}/{nB}")
print(f"parent: both-None={p_both_none} coincide={p_coincide} differ={p_differ} (total {p_total})")
print(f"idxB(n,0) parent: None={n0_parent_none} inG={n0_parent_in_G} inBump={n0_parent_in_bump}")
print(f"s has parent at k>t: {s_has_parent_above_t}/{s_total_above_t}")
for e in ex: print("  ",e)
