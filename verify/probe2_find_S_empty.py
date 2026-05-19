#!/usr/bin/env python3
"""Probe: find S_empty cases for (iv) at k=0."""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper/verify')
from probe_iv_at_zero_S_empty import (parse_bms, b0_start, max_parent_level,
                                        idx_B, l0, l1, m_parent, elem, expand)

def find_S_empty(A_text, max_n=3):
    A = parse_bms(A_text)
    s = b0_start(A)
    if s is None: return []
    L0 = l0(A); L1 = l1(A)
    if L1 < 2: return []
    out = []
    for n in range(1, max_n + 1):
        An_text = expand(A_text, n)
        if not An_text: continue
        An = parse_bms(An_text)
        for i in range(1, L1):
            target = idx_B(A, n, i)
            if target >= len(An): continue
            v_target = elem(An, target, 0)
            S = [j for j in range(i) if elem(An, idx_B(A,0,j), 0) < v_target]
            if not S:
                p = m_parent(An, 0, target)
                out.append((n, i, p, L0, L1, v_target))
    return out

seeds=['(0,0)(1,1)','(0,0,0)(1,1,1)','(0,0,0,0)(1,1,1,1)','(0)(1)',
        '(0,0)(1,0)','(0,0)(1,2)','(0,0)(1,1)(2,1)','(0,0)(1,1)(2,2)',
        '(0,0,0)(1,1,0)','(0,0,0)(1,0,0)']
visited=set(seeds)
for seed in seeds:
    queue=[seed]
    for d in range(4):
        nq=[]
        for b in queue:
            for n in range(1,4):
                e=expand(b,n)
                if e and e not in visited:
                    visited.add(e); nq.append(e)
                    r=find_S_empty(e, max_n=3)
                    if r:
                        for v in r[:2]:
                            n_,i_,p_,L0_,L1_,vt = v
                            print(f"{e}: n={n_}, i={i_}, p={p_}, L0={L0_}, L1={L1_}, row0_target={vt}")
        queue=nq
