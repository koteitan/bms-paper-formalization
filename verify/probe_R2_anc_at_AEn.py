#!/usr/bin/env python3
"""
CORE-B / R2 precise reconstruction question (verify-first, all pitfalls obeyed:
genuine 2-col seeds only; strip via expand; deep BFS; MECE).

dom_transfer_R2 target = elem_lt_below_t INSTANTIATED AT E=A[n] (E in BMS by
expand_in_BMS). I.e. for E=A[n] with b0(E)=s', mpl(E)=t', the claim is
   elem E s' m < elem E (s'+j) m   for 0<j<l1(E), m<t'.
This is EXACTLY elem_lt_below_t at E, whose ON-CHAIN case is proven and whose
OFF-CHAIN case (s'+j NOT an m'-ancestor of last_col(E)) is the lone sorry.

QUESTION A (does R2 ADD a gap beyond elem_lt_below_t?): no, it's an instance.
QUESTION B (is the gap VACUOUS for E in R2 regime?): for every interior B0'-col
s'+j of E, and every m<t'(=mpl E), is s'+j an m'-ancestor of last_col(E) where
m=Suc m' (the on-chain predicate of elem_lt_below_t)? Equivalently: does the
OFF-CHAIN branch ever fire for E in the R2 design regime?
Also QUESTION C: is s' an m-ancestor of (s'+j) in E for all m<t' (the
b0_col_ancestor_below_t conclusion at E)? That's what m_ancestor_elem_lt needs.
Report MECE counts + any violation.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand)

def last_col_idx(A):
    return len(A) - 1

def main():
    seeds = [f"({','.join(['0']*n)})({','.join(['1']*n)})" for n in range(2,7)]
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=8000; depth=13
    r2=0
    # QB: offchain predicate of elem_lt_below_t at E fires (m=Suc m', s'+j not m'-anc of C)
    offchain_fires=0; offchain_dom_fails=0
    # QC: s' is m-anc of s'+j in E for all m<t' ; count fails
    qc_checks=0; qc_fail=0
    # raw domination at E (the literal target) fails?
    dom_checks=0; dom_fail=0
    exoff=[]; exdom=[]; exqc=[]
    for d in range(depth):
        fr=[]
        for A in Q:
            set_array(A); sA=b0(A); lA=l1(A); l0A=sA
            if sA is not None and lA>=1 and len(A)<=45:
                for n in range(1,4):
                    E=expand(fmt(A),n)
                    if E is None: continue
                    set_array(E); sp=b0(E); tp=mpl(E); lp=l1(E)
                    if sp is None or tp is None:
                        set_array(A); continue
                    if not (lp>=2 and tp>=1 and sp<l0A):
                        set_array(A); continue
                    r2+=1
                    C=last_col_idx(E)   # = sp + lp
                    # iterate interior B0'-columns of E: sp < sp+j < C, i.e. 0<j<lp
                    for j in range(1, lp):
                        col=sp+j
                        for m in range(0, tp):  # m<t'
                            if m>=len(E[sp]) or m>=len(E[col]): continue
                            # raw domination (literal target)
                            dom_checks+=1
                            if not (elem(E,sp,m) < elem(E,col,m)):
                                dom_fail+=1
                                if len(exdom)<6: exdom.append((fmt(A),n,fmt(E),sp,col,m))
                            # QC: s' m-anc of col in E
                            qc_checks+=1
                            if not m_anc(E,m,col,sp):
                                qc_fail+=1
                                if len(exqc)<6: exqc.append((fmt(A),n,fmt(E),sp,col,m))
                            # QB: elem_lt_below_t on-chain predicate is for m=Suc m'>0:
                            #     s'+j is m'-anc of C. (m=0 handled separately/proven.)
                            if m>0:
                                mp_=m-1
                                onchain = m_anc(E, mp_, C, col)
                                if not onchain:
                                    offchain_fires+=1
                                    if not (elem(E,sp,m) < elem(E,col,m)):
                                        offchain_dom_fails+=1
                                    if len(exoff)<8: exoff.append((fmt(A),n,fmt(E),sp,col,m,'domOK' if elem(E,sp,m)<elem(E,col,m) else 'DOMFAIL'))
                    set_array(A)
            for n in range(1,4):
                if len(A)>40: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"  d{d}: seen={len(seen)} r2={r2} domchk={dom_checks} domfail={dom_fail} qcfail={qc_fail} offchain={offchain_fires}(domfail {offchain_dom_fails})",flush=True)
        if len(seen)>CAP: break
    print(f"\n=== R2 design-regime cases at E=A[n]: {r2} ===")
    print(f"[LITERAL TARGET] raw domination elem E s' m < elem E (s'+j) m, 0<j<l1(E), m<mpl(E):")
    print(f"   checks={dom_checks}  FAILURES={dom_fail}   (0 => literal dom_transfer_R2 TRUE on genuine BMS)")
    print(f"[QC ancestry] s' m-anc of (s'+j) in E for m<mpl(E):")
    print(f"   checks={qc_checks}  FAILURES={qc_fail}   (0 => m_ancestor_elem_lt route closes target)")
    print(f"[QB off-chain] elem_lt_below_t off-chain branch fires at E: {offchain_fires}  (of which dom actually fails: {offchain_dom_fails})")
    for e in exdom: print("   DOMFAIL:",e)
    for e in exqc:  print("   QCFAIL :",e)
    for e in exoff[:8]: print("   OFFCHAIN:",e)

if __name__=='__main__': main()
