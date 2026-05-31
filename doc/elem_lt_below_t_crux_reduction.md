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
