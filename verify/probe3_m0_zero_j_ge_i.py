#!/usr/bin/env python3
"""Probe: under m0=0, are there cases where m_parent (A[n]) 0 (idx_B(n,i)) = Some p
with p = idx_B(t,j) and j >= i? If not, then j < i always, and then S is automatically non-empty."""
import sys
sys.path.insert(0,'/home/koteitan/bms-paper/verify')
from probe_iv_at_zero_S_empty import (parse_bms, b0_start, max_parent_level,
                                        idx_B, l0, l1, m_parent, elem, expand)

def check(A_text, max_n=3):
    A = parse_bms(A_text)
    s = b0_start(A)
    if s is None: return []
    m0 = max_parent_level(A)
    if m0 is None: return []
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
            p = m_parent(An, 0, target)
            if p is None: continue
            # any candidate (p known)
            row0_target = elem(An, target, 0)
            row0_p = elem(An, p, 0)
            if p >= L0:
                blk_off = p - L0; t = blk_off // L1; j = blk_off % L1
                # Note: for t = n, j < i always (same block, p < target)
                # Interesting: t < n and j >= i
                if t < n:
                    out.append((A_text, n, i, p, t, j, m0))
    return out

seeds=['(0,0)(1,1)','(0,0,0)(1,1,1)','(0)(1)','(0,0)(1,0)','(0,0)(1,0)(1,0)',
        '(0,0)(2,0)','(0,0)(1,2)','(0,0)(2,1)','(0,0)(1,1)(2,1)',
        '(0,0,0)(1,1,0)','(0,0,0)(1,0,0)','(0,0)(1,0)(2,0)','(0,0)(2,0)(2,0)']
visited=set(seeds); tested=0; bad=[]
for seed in seeds:
    queue=[seed]
    for d in range(4):
        nq=[]
        for b in queue:
            for n in range(1,4):
                e=expand(b,n)
                if e and e not in visited:
                    visited.add(e); nq.append(e); tested += 1
                    bad += check(e)
        queue=nq
for b in bad[:5]:
    print(b)
print(f"tested={tested}, bad={len(bad)}")
