"""Reachability of the residual sub-cases of m_parent_block_n_stays_until_zero.

Lemma (BMS_Ancestry @13474):
  A in BMS, A!=[], b0_start A=Some s, 0<l1 A, 0<a<l1 A,
  m_parent (A[n]) m (idx_B(n,a)) = Some p  ==>  idx_B(n,0) <= p.

The proven branch is  m=0 AND t>0 AND n>0  (t = mpl A).  The single sorry
covers the residual  NOT(m=0 & t>0 & n>0), i.e.
   (R-m)  m = Suc m'              (positive level)
   (R-t)  m = 0 & t = 0
   (R-n)  m = 0 & n = 0   (and t>0)

This probe enumerates genuine BMS predecessors A (BFS from 2-column seeds),
forms expansions E=A[n], and for every column idx_B(n,a) (0<a<l1 A) whose
level-m m_parent is Some p, classifies which residual it falls in and checks
the conclusion idx_B(n,0)<=p.  Goal: find which residuals are REACHABLE
(non-vacuous) so the sorry can be split and the vacuous ones closed by
deriving False from the premises.

idx_B(c,x) = s + c*l1 A + x   (column index into E; strip removes rows only,
so column indices are preserved).
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (
    parse, fmt, strip, elem, height, set_array, m_parent, mpl, b0, l1, expand)

SEEDS = [fmt([[0]*k, [1]*k]) for k in range(2, 7)]
CAP = 1500
DEPTH = 7


def main():
    seen = set(); Q = []
    for sd in SEEDS:
        kk = fmt(strip(parse(sd)))
        if kk not in seen:
            seen.add(kk); Q.append(kk)
    # counters: per residual class -> [firings, conclusion-violations]
    cls = {'Rm': [0, 0], 'Rt': [0, 0], 'Rn': [0, 0], 'proven(m0,t>0,n>0)': [0, 0]}
    examples = {'Rm': None, 'Rt': None, 'Rn': None}
    i = 0
    while i < len(Q):
        txt = Q[i]; i += 1
        A = strip(parse(txt)); set_array(A)
        s = b0(A); t = mpl(A); L1 = l1(A)
        # enqueue children regardless
        for n in range(0, DEPTH):
            E = expand(txt, n)
            if not E:
                continue
            ek = fmt(E)
            if ek not in seen and len(Q) < CAP:
                seen.add(ek); Q.append(ek)
        if s is None or t is None or L1 < 2:
            continue
        for n in range(0, DEPTH):
            E = expand(txt, n)
            if not E:
                continue
            set_array(E)
            HE = height(E); LE = len(E)
            b0n = s + n*L1            # idx_B(n,0)
            for a in range(1, L1):
                col = s + n*L1 + a    # idx_B(n,a)
                if col >= LE:
                    continue
                for m in range(0, HE):
                    p = m_parent(E, m, col)
                    if p is None:
                        continue
                    if m == 0 and t > 0 and n > 0:
                        k = 'proven(m0,t>0,n>0)'
                    elif m > 0:
                        k = 'Rm'
                    elif t == 0:
                        k = 'Rt'
                    else:                # m==0, t>0, n==0
                        k = 'Rn'
                    cls[k][0] += 1
                    if not (b0n <= p):
                        cls[k][1] += 1
                        if k in examples and examples[k] is None:
                            examples[k] = (txt, n, a, m, p, b0n, t)
            set_array(A)   # restore predecessor cache context
    print(f"enumerated {i} BMS arrays")
    print("class                  firings  concl-violations")
    for k, (f, v) in cls.items():
        print(f"  {k:22s} {f:7d}  {v}")
    print("first examples (txt, n, a, m, p, idxB(n,0), t):")
    for k, ex in examples.items():
        print(f"  {k}: {ex}")


if __name__ == "__main__":
    main()
