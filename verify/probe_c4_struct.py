"""Structural facts for completing the c4' STRUCT crux (b0_start_expansion_some).

c4':  A in BMS, b0_start A /= None, 2 <= height(A[n])  ==>  b0_start(A[n]) /= None.

The main branch (t = mpl A > 0, n > 0) is PROVEN sorry-free in BMS_Ancestry.thy
(b0_start_expansion_some_when_n_pos, v0.1.116): the last column idx_B(n,l1-1) has
row-0 value base + n*delta_0 >= 1.  The residual is t = 0 and n = 0.

This probe records the verified enabling facts (genuine BMS seeds, strip-correct
BFS) that pin down the residual:

  (E)  mpl A = Some 0  ==>  height A = 1                       (729/729)
       => the t=0 branch of c4' is VACUOUS (height(A[n]) <= height A = 1 < 2).

  last-column facts (height A > 0), all 0 violations / 2990 BMS arrays:
    - last col is the row-0 MAXIMUM:  elem A i 0 <= elem A C 0  for all i
    - last col is NONZERO at the top row:  elem A C (height A - 1) /= 0
    - last col is DENSE:  elem A C m /= 0  for every m < height A

  With c1 (col_row0_zero_imp_col_zero), ANY of the last-column facts gives
  height(A[n]) >= 1 ==> elem(A[n]) C_n 0 >= 1 ==> b0_start(A[n]) /= None,
  closing c4' uniformly.  BUT: an expansion's last column idx_B(n,l1-1) is built
  from A's PENULTIMATE B0 column (s+l1-1 = C-1), not A's last column C, so a naive
  BMS.induct on a "last column is special" statement does not transfer through the
  expand step -- the base column changes.  Hence the n=0 / butlast route:

  n=0 path:  A[0] = strip(butlast A); last col of A[0] = C-1 = s+l1-1 (offset l1-1).
    - l1 >= 2: offset l1-1 > 0 ascends at row 0 (all_ascend_row0, t>0), so s+l1-1 has
      a 0-parent in A; butlast (removing C, which is to the right) and strip preserve
      it -> b0_start(A[0]) /= None.   [CLEAN, next to formalize]
    - l1 = 1: C-1 = s (the bad root); if elem A s 0 >= 1, s has a 0-parent (done);
      if elem A s 0 = 0 then column s is all-zero (c1) and the config must force a
      short G (height(A[0]) <= 1), the remaining delicate corner.
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import parse, fmt, strip, mpl, height, set_array, expand, elem

SEEDS = [fmt([[0] * k, [1] * k]) for k in range(2, 8)]
CAP = 3000
DEPTH = 12


def main():
    seen = set()
    Q = []
    for sd in SEEDS:
        kk = fmt(strip(parse(sd)))
        if kk not in seen:
            seen.add(kk)
            Q.append(kk)
    e_viol = maxv = topv = densev = chk = mpl0 = 0
    i = 0
    while i < len(Q):
        txt = Q[i]
        i += 1
        A = strip(parse(txt))
        set_array(A)
        H = height(A)
        nc = len(A)
        tA = mpl(A)
        if tA == 0:
            mpl0 += 1
            if H != 1:
                e_viol += 1
        if nc > 0 and H > 0:
            chk += 1
            last = nc - 1
            lv = elem(A, last, 0)
            if any(elem(A, c, 0) > lv for c in range(nc)):
                maxv += 1
            if elem(A, last, H - 1) == 0:
                topv += 1
            if any(elem(A, last, m) == 0 for m in range(H)):
                densev += 1
        for n in range(0, DEPTH):
            E = expand(txt, n)
            if not E:
                continue
            ek = fmt(E)
            if ek not in seen and len(Q) < CAP:
                seen.add(ek)
                Q.append(ek)
    print(f"checked {chk} arrays ({mpl0} with mpl=0)")
    print(f"(E) mpl A=0 but height/=1            violations: {e_viol}")
    print(f"last col NOT row-0 max               violations: {maxv}")
    print(f"last col zero at top row             violations: {topv}")
    print(f"last col not dense (internal zero)   violations: {densev}")


if __name__ == "__main__":
    main()
