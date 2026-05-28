"""Empirical check: clause-(iv) "intermediate B_t impossible".

For each genuine 2-row seed A and n>=1, expansion E=expand(A,n) (with valid b0),
and each 0 < i < l1 and 0 <= k < min(len(E[idxB(n,i)]), height(E)):
   pn = m_parent(E, k, idx_B(n,i))
classify pn into:
   - None
   - G       : pn < l0
   - B_n     : l0 + n*l1 <= pn < l0 + (n+1)*l1
   - intermediate : l0 <= pn < l0 + n*l1   (i.e. some B_t, 0 <= t < n)
   - other        : (should not happen for parent within ancestry table)

Also split by regime: ascending (k < t) vs non-ascending (k >= t), where t=mpl(E).

If "intermediate" never fires, the clause-(iv) intermediate-impossible
sub-claim holds empirically on genuine 2-row seeds.
"""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse,fmt,strip,m_parent,mpl,b0,l1,set_array,expand,height)

def idxB(c,j,l0A,l1A): return l0A + c*l1A + j

seeds=[fmt([[0]*k,[1]*k]) for k in range(2,8)]
seen=set();Q=[]
for sd in seeds:
    A=strip(parse(sd));kk=fmt(A)
    if kk not in seen: seen.add(kk);Q.append(A)
CAP=7000;depth=11

# Counters
cnt_total=0
cnt_none=0; cnt_G=0; cnt_Bn=0; cnt_inter=0; cnt_other=0
# Split by regime
asc_total=0; asc_inter=0
nasc_total=0; nasc_inter=0
# Dump
inter_examples=[]

for d in range(depth):
    fr=[]
    for A in Q:
        set_array(A); sA=b0(A); lA=l1(A); l0A=sA
        if sA is not None and lA>=1 and len(A)<=40:
            for n in range(1,4):
                E=expand(fmt(A),n)
                if E is None: continue
                set_array(E); tp=mpl(E)
                if tp is None: set_array(A); continue
                lenE=len(E)
                # i ranges over 0 < i < l1 inside block B_n
                for i in range(1,lA):
                    inn=idxB(n,i,l0A,lA)
                    if inn>=lenE: continue
                    hi=len(E[inn])
                    for k in range(0,hi):
                        pn=m_parent(E,k,inn)
                        cnt_total+=1
                        if pn is None:
                            cnt_none+=1; cat='none'
                        elif pn<l0A:
                            cnt_G+=1; cat='G'
                        elif l0A+n*lA<=pn<l0A+(n+1)*lA:
                            cnt_Bn+=1; cat='Bn'
                        elif l0A<=pn<l0A+n*lA:
                            cnt_inter+=1; cat='inter'
                        else:
                            cnt_other+=1; cat='other'
                        # regime split
                        if k<tp:
                            asc_total+=1
                            if cat=='inter': asc_inter+=1
                        else:
                            nasc_total+=1
                            if cat=='inter': nasc_inter+=1
                        if cat=='inter' and len(inter_examples)<10:
                            inter_examples.append(dict(A=fmt(A),n=n,i=i,k=k,t=tp,pn=pn,l0=l0A,l1=lA))
            set_array(A)
        # BFS expansion (n=1..3, like the gateway probe)
        for n in range(1,4):
            if len(A)>35: continue
            E=expand(fmt(A),n)
            if E is None: continue
            key=fmt(E)
            if key in seen or len(seen)>CAP: continue
            seen.add(key); fr.append(E)
    Q=fr
    print(f"depth {d}: vis={len(seen)} total={cnt_total} "
          f"[none={cnt_none} G={cnt_G} Bn={cnt_Bn} inter={cnt_inter} other={cnt_other}] "
          f"asc_inter={asc_inter}/{asc_total} nasc_inter={nasc_inter}/{nasc_total}",flush=True)
    if len(seen)>CAP: break

print("\n=== clause-(iv) intermediate-impossible probe summary ===")
print(f"checks total          : {cnt_total}")
print(f"  None                : {cnt_none}")
print(f"  G (pn<l0)           : {cnt_G}")
print(f"  B_n (current block) : {cnt_Bn}")
print(f"  intermediate B_t    : {cnt_inter}")
print(f"  other               : {cnt_other}")
print(f"ascending (k<t)       : inter={asc_inter}/{asc_total}")
print(f"non-asc   (k>=t)      : inter={nasc_inter}/{nasc_total}")
verdict = "YES (no intermediate violations)" if cnt_inter==0 else "NO (intermediate violations found)"
print(f"intermediate impossible empirically holds? {verdict}")
if inter_examples:
    print("\nintermediate violation examples (max 10):")
    for e in inter_examples:
        print("  ",e)
