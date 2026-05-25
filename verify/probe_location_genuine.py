#!/usr/bin/env python3
"""
RE-VERIFY the location finding with GENUINE seeds ONLY (pitfall #5: earlier
location probes seeded the BFS with 3+-column arrays like (0,0,0)(1,1,1)(2,2,2),
which are NOT true seeds and may be non-BMS, contaminating results).

True BMS seeds = 2-column [replicate n 0, replicate n 1] only. BFS from those.
For E = A[n] in the design regime (l1(E)>=2 AND mpl(E)>=1), MECE 3-way buckets
R1(block-start)/R2(in-G')/R3(mid-block), strip-correct (expand strips), deep BFS.
Question: do R2 and R3 still occur for GENUINE BMS? If R2=R3=0, location is always
a block-start (R1) and the reconstruction reduces to the already-proven R1 branch.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, elem, m_parent,
    m_anc, mpl, b0, l1, set_array, expand, height)

def main():
    # GENUINE seeds ONLY: 2-column [0^n, 1^n]
    seeds = [f"({','.join(['0']*n)})({','.join(['1']*n)})" for n in range(2,7)]
    print("genuine seeds:", seeds)
    seen=set(); Q=[]
    for sd in seeds:
        A=strip(parse(sd)); k=fmt(A)
        if k not in seen: seen.add(k); Q.append(A)
    CAP=8000; depth=13
    R1=R2=R3=0; r2ex=[]; r3ex=[]; checkedE=0
    for d in range(depth):
        fr=[]
        for A in Q:
            set_array(A); sA=b0(A); lA=l1(A); l0A=sA
            if sA is not None and lA>=1 and len(A)<=45:
                for n in range(1,4):
                    E=expand(fmt(A),n)
                    if E is None: continue
                    set_array(E); sp=b0(E); tp=mpl(E); lp=l1(E)
                    set_array(A)
                    if sp is None or tp is None: continue
                    checkedE+=1
                    if not (lp>=2 and tp>=1): continue
                    if sp<l0A:
                        R2+=1
                        if len(r2ex)<8: r2ex.append((fmt(A),n,fmt(E),sp,l0A,lA))
                    elif (sp-l0A)%lA==0: R1+=1
                    else:
                        R3+=1
                        if len(r3ex)<8: r3ex.append((fmt(A),n,fmt(E),sp,l0A,lA))
            for n in range(1,4):
                if len(A)>40: continue
                E=expand(fmt(A),n)
                if E is None: continue
                key=fmt(E)
                if key in seen or len(seen)>CAP: continue
                seen.add(key); fr.append(E)
        Q=fr
        print(f"  depth {d}: visited={len(seen)} checkedE={checkedE} | R1={R1} R2={R2} R3={R3}",flush=True)
        if len(seen)>CAP: break
    print(f"\nGENUINE-BMS design regime (l1(E)>=2 & mpl(E)>=1): R1={R1} R2(in-G')={R2} R3(mid-block)={R3}")
    if R2==0 and R3==0:
        print("  => location is ALWAYS block-start (R1) for genuine BMS! reconstruction = R1 branch (PROVEN dom_transfer_R1).")
    else:
        print("  => R2/R3 genuinely occur; design must handle them.")
    for e in r2ex: print("   R2:",e)
    for e in r3ex: print("   R3:",e)

if __name__=='__main__': main()
