"""Empirical test of the candidate foundational lemma
'within-A[n] block-translation invariance of m-ancestry':

  (BT)  for B-region columns, shifting BOTH source p and target q up by one
        block (+l1 A) preserves the k-ancestry verdict:
          m_anc (A[n]) k p q  <->  m_anc (A[n]) k (p+l1) (q+l1)

This is the missing piece the iii_single_step / v_clause workflow agents both
identified.  We test it over genuine BMS expansions A[n], for p = idx_B(cp,xp),
q = idx_B(cq,xq) with cp,cq < n (so the +l1 shift lands cp+1,cq+1 <= n, still a
full bumped block), at every level k < height.

We ALSO test the v-specific SOURCE-ONLY shift with fixed target:
  (SV)  m_anc (A[n]) k (idx_B(n1,j)) (idx_B(n0,i))
        <-> m_anc (A[n]) k (idx_B(n1+1,j)) (idx_B(n0,i))   for n0<n1<n
(= the v_clause statement; sanity check it is empirically true).

idx_B(c,x) = l0 + c*l1 + x   (column index into A[n]).
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (
    parse, fmt, strip, elem, height, set_array, m_anc, mpl, b0, l1, expand)

SEEDS = [fmt([[0]*k, [1]*k]) for k in range(2, 7)]
CAP = 1200
DEPTH = 8


def main():
    seen = set(); Q = []
    for sd in SEEDS:
        kk = fmt(strip(parse(sd)))
        if kk not in seen:
            seen.add(kk); Q.append(kk)
    bt_chk = bt_viol = sv_chk = sv_viol = 0
    bt_ex = sv_ex = None
    i = 0
    while i < len(Q):
        txt = Q[i]; i += 1
        A = strip(parse(txt)); set_array(A)
        s = b0(A); t = mpl(A); L1 = l1(A)
        for nn in range(0, DEPTH):
            E = expand(txt, nn)
            if not E:
                continue
            ek = fmt(E)
            if ek not in seen and len(Q) < CAP:
                seen.add(ek); Q.append(ek)
        if s is None or t is None or L1 < 1:
            continue
        L0 = s  # l0 A = b0_start
        for n in range(1, DEPTH):
            E = expand(txt, n)
            if not E:
                continue
            set_array(E)
            HE = height(E); LE = len(E)

            def idxB(c, x):
                return L0 + c * L1 + x

            # (BT) both-shift block translation
            for cp in range(0, n):           # cp+1 <= n
                for cq in range(0, n):
                    for xp in range(0, L1):
                        for xq in range(0, L1):
                            p = idxB(cp, xp); q = idxB(cq, xq)
                            p2 = p + L1; q2 = q + L1
                            if max(p, q, p2, q2) >= LE:
                                continue
                            for k in range(0, HE):
                                a = m_anc(E, k, p, q)
                                b = m_anc(E, k, p2, q2)
                                bt_chk += 1
                                if a != b:
                                    bt_viol += 1
                                    if bt_ex is None:
                                        bt_ex = (txt, n, k, (cp, xp), (cq, xq), a, b)

            # (SV) source-only shift, fixed target  (n0<n1<n)
            for n0 in range(0, n):
                for n1 in range(n0 + 1, n):
                    for ii in range(0, L1):
                        for jj in range(0, L1):
                            tgt = idxB(n0, ii)
                            src1 = idxB(n1, jj); src2 = idxB(n1 + 1, jj)
                            if max(tgt, src1, src2) >= LE:
                                continue
                            for k in range(0, HE):
                                a = m_anc(E, k, src1, tgt)
                                b = m_anc(E, k, src2, tgt)
                                sv_chk += 1
                                if a != b:
                                    sv_viol += 1
                                    if sv_ex is None:
                                        sv_ex = (txt, n, k, n0, n1, ii, jj, a, b)
            set_array(A)
    print(f"enumerated {i} BMS arrays")
    print(f"(BT) both-shift block-translation  checks {bt_chk:8d}  violations {bt_viol}")
    print(f"(SV) source-only shift fixed tgt   checks {sv_chk:8d}  violations {sv_viol}")
    print(f"(BT) first violation: {bt_ex}")
    print(f"(SV) first violation: {sv_ex}")


if __name__ == "__main__":
    main()
