# Reducing the `elem_lt_below_t` crux to a non-circular value fact

This documents how the central domination crux of the BMS formalization was
reduced from a circular ancestry⟺domination problem to a single non-circular
*pure value* statement, and the proof strategy for the remaining gap.

## The crux

`elem_lt_below_t` (BMS_Ancestry.thy): for `A ∈ BMS`, `b0_start A = Some s`,
`max_parent_level A = Some t`, `m < t`, interior `B₀` column `s+j`
(`0 < j < l1 A`): `elem A s m < elem A (s+j) m`.

It feeds `b0_col_ancestor_below_t` (clause (ii) case B vacuity) and the whole
DOM machinery. Its old proof split on whether `s+j` is an `(m-1)`-ancestor of
the last column `C`: the **on-chain** case is discharged by
`m_anc_Suc_imp_strict_min_on_anc`; the **off-chain** case was the long-standing
`sorry`.

## Why every ancestry route was circular

Establishing the off-chain domination at level `m` needs `s` to be an
`(m-1)`-ancestor/candidate of `s+j` at level `m`, whose candidacy needs the
*same* domination. `m_anc_build_Suc` (build `Suc m'`-ancestry from `m'`-ancestry
+ level-`Suc m'` domination) also needs the level-`Suc m'` domination first.
The PSS 2-row proof (`../pss-proof`, `le1_build`) does **not** break this
standalone either — it threads the stratified domination `H5` in from the
simultaneous induction. Confirmed dead ends: `INTERVAL-ANC` (`s'` ancestor of
all of `(s',sA)`, off-chain fails 7164/42624), the `floor` fact, chain-linear
through `sA`, prefix sub-array (loses BMS).

## The non-circular reformulation (the key move)

The off-chain case is **vacuous**: empirically every interior `B₀` column `s+j`
*is* an `m'`-ancestor of `C` for `m' < t-1` (`probe_interiorB0_anc_of_C.py`:
0/46085; the `elem_lt_below_t` `Suc m' < t` range is exactly `m' < t-1`). And
that ancestry comes from a **consecutive parent chain**: for `c ∈ (s,C]`,
`m' < t-1`, the `m'`-parent of `c` is its predecessor `c-1`
(`probe_C_chain_over_B0.py`: 53470/0). Which in turn comes from a **pure value**
fact — adjacent columns strictly increase:

    adjacent_value_monotone:  A ∈ BMS, s < c ≤ C, m < t-1  ⟹  elem A (c-1) m < elem A c m

`probe_adjacent_value_monotone.py`: 0/53470 for `m < t-1` (plateaus appear only
at the *top* level `m = t-1`, which is outside the statement; the global row-0
version is false, so the `(s,C]` / `m<t-1` restriction is essential).

This statement mentions **no ancestry and no `m_parent`** — it sidesteps the
circularity entirely.

## The cascade (all build-green, BMS_Ancestry.thy)

1. `elem_lt_from_adjacent` — telescoping: adjacent monotonicity ⟹ `elem A s m < elem A (s+j) m`.
2. `consecutive_parent_from_mono` — adjacent monotonicity ⟹ `m_parent A m c = Some (c-1)`
   (strong induction on the level via `m_parent_ge_candidate_{zero,Suc}` + `m_parent_lt`).
3. `m_anc_of_consecutive_chain` — consecutive parents ⟹ every `d ∈ [s,e)` is an `m`-ancestor of `e`.
4. `adjacent_value_monotone` (**the only remaining `sorry`**).
5. `elem_lt_below_t` off-chain rewired: `m' < t-1` ⟹ `s+j` is an `m'`-ancestor of `C`
   (via 2+3) ⟹ contradicts the off-chain assumption ⟹ vacuous. **`elem_lt_below_t` is now `sorry`-free.**

So the entire central crux now rests on `adjacent_value_monotone`.

## Proof strategy for `adjacent_value_monotone` (the remaining gap)

By `BMS.induct` on `A` (the statement is a *pure value* fact, so the induction
carries no ancestry circularity):

- **seed `A = seed n`**: `s = 0`, `t = n-1`, `C = 1`, forces `c = 1`; goal is
  `elem (seed n) 0 m < elem (seed n) 1 m = 0 < 1` for `m < n` (from `m < t-1 = n-2`).
  Use `b0_start_seed`, `max_parent_level_seed`, `elem_seed_0/1`.

- **expand `A = A'[n']`**: split on where `A`'s bad root `s_A = b0_start(A'[n'])`
  lands in the expansion `G_block(A') @ B₀'..B_{n'}'` (the same R1/R2 dichotomy
  as the DOM transfer):
  - **R1** (`s_A` is a block-start `idx_B(A',c0,0)`): `(s_A, C_A]` lies within the
    bumped blocks. **Provable.**
    - *within-block* adjacent pair: `elem_expansion_B_lt_same_block` lifts the IH
      (`A'`'s adjacent monotonicity over its own `B₀`).
    - *cross-block boundary* (last col of block `c`, offset `l1'-1`, vs first col
      of block `c+1`, offset `0`): bumped values give
      `bigBase + c·δ < smallBase + (c+1)·δ ⟺ bigBase - smallBase < δ`, where
      `bigBase = elem A' (s'+l1'-1) m`, `smallBase = elem A' s' m`,
      `δ = delta A' m = elem A' C' m - elem A' s' m`. Since `s'+l1'-1 < C'`, the
      IH (telescoped) gives `elem A' (s'+l1'-1) m < elem A' C' m`, i.e.
      `bigBase - smallBase < δ`. ✓
  - **R2** (`s_A < l0_{A'}`, inside `A'`'s `G`-block; forces `l1 A' = 1`): `(s_A, C_A]`
    includes verbatim `A'` `G`-columns, so it needs adjacent monotonicity over
    `A'`'s `G`-block — **not** covered by the IH (`A'`'s `B₀` region). This is the
    residual; it connects to the R2 location lemma `b0_start_expansion_R2_eq`
    (`s_A = m_parent A' (mpl (A'[n'])) (b0_start A')`).

The R2/`G`-block case is the genuine remaining work — a recursion into `A'`'s
`G`-block structure (or a strengthened invariant covering it).

## Update (2026-05-31, autonomous): strengthened invariant chosen = `ancestor_monotone`

A 5-agent workflow (`wepq9a5l7`) designed + probe-verified four candidate
strengthened invariants; synthesis (with independent re-runs) selected:

    ancestor_monotone(A) :=  for s = b0_start A, t = mpl A, C = last_col_idx A:
      ∀m < t-1. ∀q. (q = s ∨ m_ancestor A m s q) → ∀c ∈ (q, C]. elem A (c-1) m < elem A c m

i.e. adjacent columns strictly increase over `(q, C]` for **every m-ancestor `q`
of the bad root `s`** (and `q = s` itself). Why this beats the alternatives:

- **(a) implies target**: instantiate `q = s` → exactly `adjacent_value_monotone`
  (no ancestry needed for this instance).
- **(b) covers R2 — decisive**: in R2, `s' = b0_start(A[n]) < s` *always*
  (probe 1304/1304), so the needed region `(s', l0 A)` reaches **left of `s`** —
  this is exactly why the bare target (and any `(boundary, C]` invariant with
  boundary ≥ a prefix's own bad root) cannot self-cover R2. But `s'` **is** an
  m-ancestor of `s` (probe 2722/2722, matching `b0_start_expansion_R2_eq`), so
  the `q = s'` clause of `ancestor_monotone(A)` gives monotone over `(s', C'] ⊇
  (s', l0 A)`. Genuine implication, not a probe artifact.
- **(c) self-transfers**: empirically 4460/4460 (properly conditioned on INV(A)).

Eliminated: candidate "bare target" (R2 region `⊄ (s,C]` since `s'<s`);
candidates "prefix_adjacent_monotone" and "mparent_chain_boundary" both **over-claimed**
R2 coverage — their probes silently clamped past the left-gap (`2048/3002` R2 cases
reach left of the prefix bad root). `ancestor_monotone` has no such gap.

### Independent verification of the one formal residual (the ancestry-restriction lemma)

`ancestor_monotone`'s self-transfer reduces to one genuinely-new lemma for the
G-block sub-case:

    ancestry_restriction:  m_ancestor (A[n]) m s' q'  ∧  q' < l0 A  ⟹  m_ancestor A m s q'

(a G-block m-ancestor of the new bad root is an m-ancestor of the *old* bad root,
so the IH `ancestor_monotone A` supplies monotone over `(q', C_A]` verbatim).
The workflow only probed the `q' = s'` base instance. **Independently verified in
FULL (all chain depths)**: `verify/probe_ar_lean.py` — basic `ancestor_monotone`
113015/0, **ancestry-restriction full-chain 8748/0**. So the residual lemma holds.

### Isabelle building blocks already in BMS_Ancestry.thy
- `m_anc_eq_of_m_parent_eq` (parent-equality → ancestor-equality)
- `m_anc_below_ancestor_transfer`, `m_ancestor_trans`, `m_ancestor_chain_linear`
- `block_start_anc_zero`, `block_copy_anc_from_onestep` (block ancestry chaining)
- `b0_start_expansion_R2_eq` (s' = m_parent A (mpl A[n]) s)
- R1 machinery: `elem_expansion_B_lt_same_block`, `delta_pos_of_lt_m0`

### Plan: prove `ancestor_monotone` by BMS.induct, derive `adjacent_value_monotone`
- SEED: q-ancestors of s=0 collapse, interval (q,1]={1}, 0<1 via elem_seed.
- EXPAND, split q' vs l0 A: B-sub-case (q'≥l0 A) via R1 machinery; G-sub-case
  (q'<l0 A) via ancestry_restriction + IH (ancestor_monotone A), lifted across the
  l0 A boundary by the same cross-block delta step.

## Probes (verify/)

`probe_interiorB0_anc_of_C.py`, `probe_C_chain_over_B0.py`,
`probe_adjacent_value_monotone.py`, `probe_row0_global_monotone.py`,
`probe_R2_*` (location/floor/interval-anc). All genuine 2-row-seed BFS.

## Update (2026-05-31, autonomous): expand-case structure fully clarified

The expand case of `adjacent_value_monotone` (`A[n]` expands predecessor `A`,
IH = `adjacent_value_monotone A`) splits on `b0_start(A[n])` vs `l0 A` **only**
(no location dichotomy / R3 exclusion needed):

- **R1** (`b0_start(A[n]) ≥ l0 A`): the region `(s', C']` lies entirely in the
  B-region. Verified facts that make it provable:
  - `mpl(A[n]) - mpl(A) ∈ {0,1}` (`probe_expand_mpl_vs_pred.py`: 0/10464), so
    `m < mpl(A[n]) - 1 ⟹ m < mpl(A)`.
  - `diff=1 ⟹ l1 A = 1` and `l1 A > 1 ⟹ diff=0` (`probe_diff1_implies_l1A1.py`: 0 viol).
  - **`l1 A = 1`**: every B-region column is a block-start `idx_B(A,blk,0)`; adjacent
    pairs are consecutive block-starts. Same base `(A!s)!m`, bump `blk·δ` vs
    `(blk-1)·δ`, `ascends A 0 m` is reflexive (`m < mpl A`), `δ = delta A m > 0`
    (`delta_pos_of_lt_m0`, `m < mpl A`) ⟹ strict. Covers all `m < mpl(A[n])-1`
    including the `m = mpl(A)-1` top level (which only occurs when `l1 A=1`).
    The earlier "within-block plateau at top level" worry is void: `l1 A=1` has
    **no** within-block pairs (`probe_within_block_top_level.py`: 0).
  - **`l1 A > 1`** (⟹ diff=0, so `m < mpl(A)-1`): base adjacency holds (IH) and
    the cascade gives `s` an `m`-ancestor of B0 columns, so ascends holds and the
    bump is uniform within a block. *within-block*: `elem_expansion_B_lt_same_block`
    + IH base adjacency. *cross-block* (`idx_B(A,c,l1-1) → idx_B(A,c+1,0)`):
    `bigBase + c·δ < smallBase + (c+1)·δ ⟺ bigBase - smallBase < δ`, and
    `bigBase = elem A (s+l1-1) m < elem A C m` (IH adjacency at the last step) gives
    `bigBase - smallBase < δ`.

  So **R1 is fully provable from the IH** (substantial but routine Isar).

- **R2** (`b0_start(A[n]) < l0 A`): `(s', C']` includes verbatim `A` `G`-block
  columns `[s'+1, l0 A)`, needing adjacent monotonicity over (part of) `A`'s
  `G`-block — **not** covered by the single-step IH (`A`'s B0 region). This is the
  **genuine remaining crux**: it needs either a strengthened induction invariant
  covering the relevant `G`-prefix, or a recursion into `A`'s `G`-block structure.
  (`s' = m_parent A (mpl (A[n])) (b0_start A)` by `b0_start_expansion_R2_eq` when
  `l1 A=1`.)

## Update (2026-06-03, autonomous): the m<t-1 R2/G crux is CLOSED; the frontier moved to the m=t-1 boundary

v0.1.88 closed the m<t-1 R2/G-block crux above via the strengthened invariant
`ancestor_monotone` + `ancestry_restriction` + an IH-discharged `mono_A` (the
apparent onestep⟺ancestor_monotone circularity is a false alarm: well-founded
descent `A[n]→A`). What remains of `ancestor_monotone`'s expand case is exactly
the **boundary** obligation, isolated by `ancestor_monotone_expand` (BMS_Ancestry
~13099) into residuals:
- `keep` (easy, from `BMS_keep_of_eq_height`),
- `Hmpl_le1: tE≤tA+1` and `Hmpl_gt1: 1<l1 A ⟹ tE≤tA` (**gate 2**),
- `Rb_cond: sE<sA ⟹ m_ancestor A m sA sE`,
- `Htop: l1 A=1 ⟹ m=tA-1 ⟹ elem(A[n])(c-1)m < elem(A[n]) c m` (**the boundary, gate 3**).

**gate 2 is empirically settled** (`probe_gate2_mpl`, 0 fail over 42k): `tE≤tA+1`
always; `1<l1 A ⟹ tE=tA` exactly; for `l1 A=1`, `tE-tA ∈ {-1,0,+1}` and Htop fires
only in the `+1` (leaf) case. So both mpl bounds are true invariants, provable.

**Htop splits** (two independent workflows + 8 agents agree): B-region (`sA<c`) is
**fully discharged sorry-free** by `b_region_adj_increase_l1_eq_1` (covers the top
level `k=tA-1`); the G-region (`c≤sA`) reduces, via the G-prefix value coincidence
`elem(A[n]) c (tA-1) = elem A c (tA-1)` (`elem_AEn_eq_le_l0`/`elem_AEn_eq_on_G_prefix`)
and `m_parent_elem_lt`, to a SINGLE residual:

    mp_c:  in the leaf regime (l1 A=1, tE=tA+1, R2 with sE<sA),
           m_parent A (tA-1) c = Some (c-1)  for c on the reachable G-prefix
           (equivalently  elem A (c-1)(tA-1) < elem A c (tA-1)  for q<c≤sA).

`mp_c` is `adjacent_value_monotone` **extended to the top level m=t-1**, ancestor-
restricted, leaf-conditioned. It is the SAME foundational value-induction gap as the
original `elem_lt_below_t`. It is **NOT a context-free A-fact**: the A-only and
chain-only forms are FALSE (counterexample `(0,0)(1,1)(1,0)(2,1)`: `m_parent A 0 2 = 0`,
not 1; 648/54 counterexamples, all `tA=1`). Those arrays do not arise as genuine
Htop consumers, so `A∈BMS` + the leaf hypotheses (`Rb`, `qor`, `tE=tA+1`) are load-
bearing. The generic `m'-parent ⟹ elem(Suc m') strict` bridge is also FALSE.

### The Hunter-faithful proof plan for `mp_c` (from paper proof-ii, tmp/prop/chapter2.md)

Hunter does NOT prove "parent = c-1" directly (which is what every reduction attempt
got stuck on). His clause (ii) is part of a **simultaneous induction on the level k**,
and the mechanism is: let `I = {columns that are k'-ancestors (for ALL k'<k) of the
target}`; since `k'<k`-ancestry is a **total order on I**, the `k`-parent of each
column in `I` is **the last column before it in `I` with a smaller `k`-th element**
(not necessarily the immediate predecessor). Ascension of the target's `k`-th element
then forces either "all of `I` ascends" or "the target doesn't ascend".

Mapped onto our boundary `k = tA-1`: the membership condition for `I` is `k'-ancestry
for all k'<tA-1`, which is **exactly the range `m<tA-1` covered by the `ancestor_monotone`
IH**. So `mp_c` should be provable in the current architecture WITHOUT a new axiom:
use the IH to fix `I` (the sub-boundary ancestor chain), then Hunter's last-smaller-
value argument to pin the `(tA-1)`-parent, with the leaf condition `tE=tA+1` forcing
`I` to be the consecutive run with strictly increasing `(tA-1)`-th values ⟹ parent
`= c-1`. This is the untried angle (reduction workflows all tried to prove `parent=c-1`
directly and hit the same wall).

**Potential architectural fork (watch):** if the Hunter-mechanism attack on `mp_c`
also stalls, the boundary gap is likely an artifact of the array-induction (`BMS.induct`)
+ pure-value-reduction architecture — in Hunter's level-induction, `k=m₀-1` is just one
ordinary value of `k`. The principled alternative is to build out `BMS_Hunter.thy`'s
faithful simultaneous k-induction (see `reference_simultaneous_induction_playbook`).
That is a high-backtrack-cost pivot (v0.1.70–0.1.89 invested in the array path), so it
is a decision to weigh only after the in-architecture Hunter-mechanism attempt is
exhausted.

## Update (2026-06-03 #2): reduction EXHAUSTED — the verified target and the fork

A third workflow (Hunter-mechanism) joined the two reduction workflows; all three
(5+ agents) confirm the boundary residual **cannot be closed by reduction inside the
single-clause array induction**. Both Hunter-mechanism agents honestly reported "not
proven" and refused to introduce dangling/circular sorries. The precise, **coverage-
safe-verified** target is the trigger-conditioned intrinsic fact (NOT the unconditional
or pure-leaf forms — both were probe artifacts; the unconditional `tA≥2` form has 504
real counterexamples):

    g_prefix_boundary_increase:
      A∈BMS, l1 A = 1, b0_start A = Some sA, max_parent_level A = Some tA, 2 ≤ tA,
      T1: (∃ q < sA. m_ancestor A tA sA q)         -- sA has a level-tA ancestor below it
      ⟹  elem A (c-1)(tA-1) < elem A c (tA-1)        for 0 < c ≤ sA
      (equivalently m_parent A (tA-1) c = Some (c-1) on (0, sA])

Verified `T1 ⟹ adjacent increase` 37800/0; every adjacency counterexample (342) has
`T1 = False` (excluded). `T1` is supplied in-context for free by the leaf regime:
`b0_start_expansion_R2_eq` gives `sE = m_parent A (tA+1) sA`, hence `m_ancestor A tA sA sE`
with `sE < sA`.

**Why reduction is exhausted (the precise blocker):** for genuine `A = A₀[k]` with
`l1 A = 1, tA ≥ 2`, the case `tA = mpl A₀` is frequent (1149 vs 759). There the boundary
level `tA-1` coincides with the predecessor's own top boundary — it does **not** descend
to a strictly-lower IH-clean level, so `BMS.induct` on this lemma alone doesn't reduce.
The non-circular input lives at level `tA`, but `sA`'s level-`tA` ancestor chain is
**sparse** (e.g. `[2,1,0]`, skipping columns) whereas level-`(tA-1)` is the **consecutive**
run `[sA-1,…,0]`; bridging sparse-`tA` → consecutive-`(tA-1)` is the foundational value
recursion that resisted v0.1.70–0.1.89. Strengthening the invariant from `m<t-1` to `m<t`
is **unsound** (real counterexample on a genuine stripped array).

**The fork (now actionable):**
- **(A) lightweight joint induction** — add `g_prefix_boundary_increase` as a SECOND
  clause to the existing `ancestor_monotone` `BMS.induct`, carried jointly with the
  `m<t-1` clause (a 2-clause simultaneous array induction), reusing all v0.1.70–0.1.89
  machinery. Risk: the `tA = mpl A₀` non-descent subcase may still require importing
  Hunter's I-set / last-smaller argument for that one subcase.
- **(B) full Hunter pivot** — build `BMS_Hunter.thy`'s faithful simultaneous induction
  on the level `k` over all of Lemma 2.5 (i)–(v) (task #56). Most faithful; largest rebuild.

Recommendation: attempt (A) first (asset reuse, only two clauses); fall back to (B) if
the `tA = mpl A₀` subcase cannot be discharged without the full level-induction.
