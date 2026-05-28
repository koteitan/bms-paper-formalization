"""Hypothesis: l1A > 1 ==> leftmost gateway @ k>=t has EMPTY bump-tail.

I.e. at idx = idx_B(n,0) = l0A + n*l1A, for any k in [tp, hmax),
m_parent(E,k,idx) does NOT land in (l0A .. idx) when l1A >= 2.

Bigger coverage than probe_bump_parent_l0_pos.py:
  - genuine 2-row seeds [[0]*k,[1]*k] for k in 2..10
  - depth <= 14, CAP=12000
Bucket counts and bump counts by l1A in {1,2,3,>=4}.
Also (secondary) for l1A=1, frequency of bump events vs n.
"""
import sys, collections, time
sys.path.insert(0, '/home/koteitan/bms-paper')
from verify.probe_vacuity_refute import (parse, fmt, strip, m_parent, mpl, b0, l1, set_array, expand)

def idxB(c, j, l0A, l1A): return l0A + c*l1A + j

# Seeds: genuine 2-row only, k in 2..10
seeds = [fmt([[0]*k, [1]*k]) for k in range(2, 11)]
seen = set(); Q = []
for sd in seeds:
    A = strip(parse(sd)); kk = fmt(A)
    if kk not in seen:
        seen.add(kk); Q.append(A)

CAP = 12000
depth = 14
NMAX = 4  # n in 1..NMAX-1 (= 1,2,3) — same as base probe

# Counters
# inspections[l1_bucket] = total (A,n,k,idx_B) tested
# bumps[l1_bucket]       = how many showed bump-parent (l0A<=pn<idx_B(n,0))
def bucket_of(L1):
    if L1 == 1: return 'l1=1'
    if L1 == 2: return 'l1=2'
    if L1 == 3: return 'l1=3'
    return 'l1>=4'

inspections = collections.Counter()
bumps       = collections.Counter()

# For secondary: l1=1, frequency of bumps per n
l1_one_inspect_by_n = collections.Counter()
l1_one_bumps_by_n   = collections.Counter()

# Counterexample dumps for l1>=2 (target hypothesis): up to 20
ce_dump = []

t0 = time.time()
for d in range(depth):
    fr = []
    for A in Q:
        set_array(A); sA = b0(A); lA = l1(A); l0A = sA
        if sA is not None and lA >= 1 and len(A) <= 40:
            for n in range(1, NMAX):
                E = expand(fmt(A), n)
                if E is None: continue
                set_array(E); tp = mpl(E)
                if tp is None: set_array(A); continue
                lenE = len(E)
                inn = idxB(n, 0, l0A, lA)
                if inn >= lenE: set_array(A); continue
                hmax = len(E[inn])
                bkt = bucket_of(lA)
                for k in range(tp, hmax):
                    inspections[bkt] += 1
                    if lA == 1: l1_one_inspect_by_n[n] += 1
                    pn = m_parent(E, k, inn)
                    if pn is not None and l0A <= pn < inn:
                        bumps[bkt] += 1
                        if lA == 1: l1_one_bumps_by_n[n] += 1
                        if lA >= 2 and len(ce_dump) < 20:
                            cp = (pn - l0A)//lA; xp = (pn - l0A) % lA
                            ce_dump.append({
                                'l0A': l0A, 'l1A': lA, 'n': n, 'k': k, 't': tp,
                                'inn': inn, 'pn': pn, 'cp': cp, 'xp': xp,
                                'A': fmt(A),
                            })
                set_array(A)
        # BFS expansion (with cap)
        for n in range(1, NMAX):
            if len(A) > 35: continue
            E = expand(fmt(A), n)
            if E is None: continue
            key = fmt(E)
            if key in seen or len(seen) > CAP: continue
            seen.add(key); fr.append(E)
    Q = fr
    elapsed = time.time() - t0
    total_insp = sum(inspections.values())
    total_bump = sum(bumps.values())
    print(f"depth {d}: vis={len(seen)} insp={total_insp} bumps={total_bump} ce_l1ge2={len(ce_dump)} t={elapsed:.1f}s",
          flush=True)
    if len(seen) > CAP: break
    if elapsed > 240:
        print("time budget hit; stopping BFS", flush=True)
        break

print("\n=== inspections / bump-parent counts by l1A bucket ===")
order = ['l1=1', 'l1=2', 'l1=3', 'l1>=4']
for k in order:
    insp = inspections[k]; bp = bumps[k]
    rate = (bp/insp) if insp else 0.0
    print(f"  {k:7s}  insp={insp:8d}  bump={bp:6d}  rate={rate:.4f}")

ge2_bumps = bumps['l1=2'] + bumps['l1=3'] + bumps['l1>=4']
ge2_insp  = inspections['l1=2'] + inspections['l1=3'] + inspections['l1>=4']
print(f"\nl1>=2 totals: insp={ge2_insp} bump={ge2_bumps}")

print("\n=== HYPOTHESIS: l1A>=2 ==> bump-tail empty at leftmost gateway ===")
if ge2_bumps == 0:
    print("  VERDICT: YES (no counterexample observed)")
else:
    print(f"  VERDICT: NO ({ge2_bumps} counterexamples found in l1>=2)")
    print("  example counterexamples (up to 20):")
    for e in ce_dump:
        print(f"    l0A={e['l0A']} l1A={e['l1A']} n={e['n']} k={e['k']} t={e['t']} "
              f"idx={e['inn']} pn={e['pn']} (cp={e['cp']},xp={e['xp']})  A={e['A']}")

print("\n=== SECONDARY: l1A=1 bump-rate by n ===")
for n in sorted(l1_one_inspect_by_n):
    ins = l1_one_inspect_by_n[n]; bp = l1_one_bumps_by_n[n]
    rate = (bp/ins) if ins else 0.0
    print(f"  n={n}: insp={ins} bump={bp} rate={rate:.4f}")
