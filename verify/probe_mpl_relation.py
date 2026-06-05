"""Empirical confirmation of the two mpl-relation bounds needed to discharge the
`Hmpl_gt1` / `Hmpl_le1` premises of `ancestor_monotone_expand` (BMS_Ancestry.thy).

Let tA = mpl A, tE = mpl (A[n]).  The expand case of `ancestor_monotone` needs:

  Hmpl_le1:  tE <= tA + 1                 (always)
  Hmpl_gt1:  l1 A > 1  ==>  tE <= tA       (the tall-B0 regime)

Both are UPPER bounds on the expanded max-parent-level (the existing
`mpl_bound_from_R2` only supplies the LOWER bound tA <= tE in the R2/l1=1 regime).

Result (genuine BMS seeds, strip-correct, BFS): 0 / 29748 violations for BOTH.
So discharging these two premises is sound; the proof route is the
"levels-with-a-parent are downward closed" characterization of mpl on the last
column, i.e. show m_parent (A[n]) (tA+2) (last_col (A[n])) = None  (resp. tA+1
when l1 A > 1), using that at levels >= tA no B0 offset ascends (the bump
vanishes, so A[n]'s high levels are A's columns with B0 repeated n+1 times).
"""
import sys
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import parse, fmt, strip, mpl, l1, set_array, expand

SEEDS = [fmt([[0] * k, [1] * k]) for k in range(2, 8)]
CAP = 2500
DEPTH = 12


def main():
    seen = set()
    Q = []
    for sd in SEEDS:
        kk = fmt(strip(parse(sd)))
        if kk not in seen:
            seen.add(kk)
            Q.append(kk)
    le1_viol = gt1_viol = chk = 0
    ex_le1 = ex_gt1 = None
    i = 0
    while i < len(Q):
        txt = Q[i]
        i += 1
        A = strip(parse(txt))
        set_array(A)
        tA = mpl(A)
        l1A = l1(A)
        if tA is None:
            continue
        for n in range(0, DEPTH):
            E = expand(txt, n)
            if not E:
                continue
            ek = fmt(E)
            if ek not in seen and len(Q) < CAP:
                seen.add(ek)
                Q.append(ek)
            set_array(E)
            tE = mpl(E)
            if tE is None:
                continue
            chk += 1
            if not (tE <= tA + 1):
                le1_viol += 1
                if ex_le1 is None:
                    ex_le1 = (txt, 'n', n, 'tA', tA, 'tE', tE, 'l1A', l1A)
            if l1A > 1 and not (tE <= tA):
                gt1_viol += 1
                if ex_gt1 is None:
                    ex_gt1 = (txt, 'n', n, 'tA', tA, 'tE', tE, 'l1A', l1A)
    print(f"checked {chk}  arrays {len(Q)}")
    print(f"Hmpl_le1 (tE <= tA+1)         violations: {le1_viol}  {ex_le1}")
    print(f"Hmpl_gt1 (l1A>1 => tE <= tA)  violations: {gt1_viol}  {ex_gt1}")


if __name__ == "__main__":
    main()
