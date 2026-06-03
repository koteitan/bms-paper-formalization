# (B) Hunter simultaneous k-induction — execution plan

Decision (2026-06-04, user): pivot from the array-induction boundary-reduction path
(exhausted across 3 workflows — see `elem_lt_below_t_crux_reduction.md`) to making
Hunter's faithful **simultaneous induction on the level k** over Lemma 2.5 (i)–(v)
fully sorry-free. The scaffold already exists.

## What exists

`BMS_Hunter.thy : lemma_2_5_at_main` — the outer `induct k rule: nat_less_induct`
(IH: all clauses for every `k'<k` via `lemma_2_5_at A n k'`), nested `induct n`,
assembling the five clauses per step in the order **ii → iii → iv → i → v** through
`lemma_2_5_{ii_main_v2, iii_clause_step, iv_clause_step, i_clause_step, v_clause_step}`
(definitions in `BMS_Ancestry.thy`). Build is GREEN under `quick_and_dirty`.

`lemma_2_5_ii_clause_step` (BMS_Ancestry ~9394–9572) is **sorry-free and boundary-
independent** (defined before `ancestor_monotone`/`elem_lt_below_t`, so cannot use them).
So clause (ii)'s step in the Hunter path does not depend on the array-induction boundary.

## The 6 genuine sorries to close (the entire (B) work list)

| # | line | enclosing lemma | clause | note |
|---|------|-----------------|--------|------|
| 1 | 10130 | `iii_single_step_t_to_Suc_t` | (iii) | next-copy-of-first-column step |
| 2 | 10823 | `m_parent_block_n_stays_until_zero` | (iv) | k-parent of Bₙ column stays in Bₙ |
| 3 | 12130 | `onestep_anc_when_ascends` | one-step (l1>1) | relocated in v0.1.88; boundary k=t-1 |
| 4 | 13220 | `ancestor_monotone` (expand case) | boundary | THE mp_c crux; feeds `elem_lt_below_t` |
| 5 | 14259 | `clause_i_iff_when_not_ascends` | (i) | non-ascending branch |
| 6 | 14593 | `lemma_2_5_v_clause_step_iff` | (v) | source-shift iff |

Dependency note: `elem_lt_below_t` (13232) currently routes through `ancestor_monotone`
(13230 `using ancestor_monotone…`), so sorry #4 transitively feeds the clause-(i)/(v)
machinery (13314/13352/13393, 14910–14961 via `b0_col_ancestor_below_t`).

## The key faithful move (decouples #4 from the array boundary)

Re-prove `elem_lt_below_t` (bad-root domination `elem A s m < elem A (s+j) m`, `m<t`)
**inside the simultaneous induction using the k'<k IH**, via Hunter's mechanism (paper
proof-ii, `tmp/prop/chapter2.md`): let `I = {columns that are k'-ancestors of the target
for all k'<k}`; `k'<k`-ancestry is a total order on `I`, so the k-parent is the last
column of `I` before it with a smaller k-th element; ascension of the target's k-th
element forces "all of I ascends or the target doesn't ascend". At the boundary `k=t-1`
the membership condition `k'<t-1` is supplied by the IH — no array-induction
`ancestor_monotone` needed. This removes sorry #4's role in the (ii)/(i)/(v) chain.

(`m_anc_Suc_imp_strict_min_on_anc` at BMS_Ancestry ~9021 already formalizes Hunter's
same-level domination over m'-ancestors — the reusable kernel of this mechanism.)

## Execution order (foundational first)

1. **#3 `onestep_anc_when_ascends`** and **#4 `elem_lt_below_t`/`ancestor_monotone`** —
   the boundary one-step / domination, via the Hunter I-set mechanism with the simultaneous
   IH. Closing these unblocks the (ii)/(i)/(v) value chain. Reuse `m_anc_Suc_imp_strict_min_on_anc`,
   `onestep_icm_interval_dom` (v0.1.87, sorry-free), `m_parent_elem_lt`.
2. **#1 (iii)** `iii_single_step_t_to_Suc_t` and **#2 (iv)** `m_parent_block_n_stays_until_zero`
   — the k-parent-stays-in-Bₙ / next-copy steps (Hunter proof-iii/iv), using IH (ii)@k and (iii)@k'.
3. **#5 (i)** `clause_i_iff_when_not_ascends` and **#6 (v)** `lemma_2_5_v_clause_step_iff`
   — the not-ascending / source-shift branches (Hunter proof-i/v), once the value chain is closed.

Empirically every clause statement was verified earlier (genuine-BMS BFS); the gap is
purely the faithful proof. Keep build GREEN after each; commit per closed sorry; no
net-new sorry. Probes: `tmp/verify-scratch/` (gitignored).

## The precise dependency (located 2026-06-04)

`elem_lt_below_t` (13232) is structured as: **case 0** (sorry-free, `m_anc_zero_imp_strict_min`);
**case Suc m'** splits on whether `s+j` is an `m'`-ancestor of `C`:
- **on-chain (True)**: sorry-free via the Hunter kernel `m_anc_Suc_imp_strict_min_on_anc`
  (9021) — Hunter's last-filter/total-order mechanism for one level transition, fully proven.
- **off-chain (False)**: proven *vacuous* by showing `s+j` IS an `m'`-ancestor of `C` — but
  via `adjacent_value_monotone` (13314, `m'<t-1`) → `consecutive_parent_from_mono` →
  `m_anc_of_consecutive_chain`. `adjacent_value_monotone` is the `q=s` instance of
  `ancestor_monotone`, whose expand case is the bare sorry #4 (13220).

So **the entire clause-(ii)/(i)/(v) chain depends on sorry #4 only through the off-chain
vacuity's use of `adjacent_value_monotone`**. The boundary is intrinsic to the array
induction: even though `ancestor_monotone` only claims `m<t-1`, its expand case proves
`A[n]` at `m<tE-1` and with `tE=tA+1` that range reaches `m=tA-1` (the predecessor's
boundary) — there is no array-induction way around it. This is exactly why (B) is needed.

**The core (B) restructuring:** re-prove the off-chain vacuity (`m'<t-1` ⟹ every interior
`B₀` column `s+j` is an `m'`-ancestor of `C`) using the **simultaneous k-induction IH**
(clauses for `k'<k`) instead of `adjacent_value_monotone`. This requires `elem_lt_below_t`
(or the off-chain vacuity lemma it uses) to be proven WITH IH access — i.e. threaded through
`lemma_2_5_at_main` rather than standalone — which severs the dependency on sorry #4 and the
array-induction boundary entirely. The Hunter kernel `m_anc_Suc_imp_strict_min_on_anc`
already supplies the on-chain domination; the off-chain "all interior columns are on the
`m'`-chain" must come from the IH's clause-(ii)-at-`m'` content, not a value-monotone lemma.

## The faithful route, concretely (located 2026-06-04, from the paper proof-ii)

Reading Hunter's actual proof of (ii) (PDF p.4–5) settles the architecture: **Hunter's
clause (ii) is an ancestry EQUIVALENCE** ("i'-th column in B₀ is a k-ancestor of the j-th
column in B₀ iff the same holds in Bₙ"), proven from the I-set total order + the dichotomy
"either all columns of I ascend or the j-th column doesn't ascend" — **there is no
value-domination lemma in it**. Our `elem_lt_below_t` / `adjacent_value_monotone` /
`ancestor_monotone` are an *artifact value-route* we introduced; the boundary sorry is a
consequence of that route, not of Hunter's argument. (The level-induction workflow confirmed
the value primitive `ev: elem A (c-1) m < elem A c m` is irreducible bump-arithmetic content —
it cannot be derived from the ancestry kernels, which only give min-domination `elem A s m <
elem A c m`.)

**The faithful fix is already half-scaffolded.** There are two variants of the (ii) case-B
leaf used by the clause-(i)/(v) steps:
- `b0_col_ancestor_below_t` (used at 14961, standalone) → routes to `elem_lt_below_t` →
  `adjacent_value_monotone` → `ancestor_monotone` boundary sorry.
- `b0_col_ancestor_below_t_from_DOM` (used at 15790) → takes the domination `DOM` as an
  **explicit hypothesis**, no value sorry.

So the (B) plan is: **carry `DOM` (the per-level domination invariant) through
`lemma_2_5_at_main` as part of the simultaneous invariant, prove `DOM`@k inside the step from
clause-(ii)@k's ascend/non-ascend dichotomy (Hunter's mechanism, the kernel
`m_anc_Suc_imp_strict_min_on_anc`), and switch every clause step from
`b0_col_ancestor_below_t` to `b0_col_ancestor_below_t_from_DOM`.** That severs the entire
value-route (and the boundary sorry #4) from the clause-(i)/(v) machinery — `elem_lt_below_t`,
`adjacent_value_monotone`, `ancestor_monotone` become dead code, droppable.

Concrete first targets (in dependency order): (1) state `DOM` as a simultaneous-invariant
clause and prove `DOM`@k from clause-(ii)@k + IH (Hunter's dichotomy); (2) repoint
`b0_col_ancestor_below_t`'s consumers (14961 etc.) to the `_from_DOM` variant fed by the new
`DOM` clause; (3) then close the remaining ancestry sorries #1/#2/#5/#6 (iii/iv/i/v steps)
following Hunter proof-iii/iv/i/v, which are pure ancestry arguments over the simultaneous IH.

## The convergent target: carry interval-ANCESTRY (not value) — located 2026-06-04

The DOM-carried BMS.induct (workflow) is **provably insufficient**: R1 (l1≥2) is sorry-free
(`dom_transfer_R1_from_DOM` 15830, DOM(A[n]) from IH DOM(A) via `ASC_of_DOM`+`delta_pos_of_lt_m0`),
but R2 (l1=1) reduces (`dom_transfer_R2_modulo_intervaldom` 15677) to one open hypothesis
`dom_intv` (15690): `m'<t' ⟹ s'<x≤sA ⟹ elem A s' m' < elem A x m'` — domination from the *deep*
ancestor `s' = t'-parent of sA` (s'<sA) over the predecessor's G-prefix interval. In R2, l1 A=1
so the carried `DOM A` is **vacuous** and its level range m<t is below dom_intv's m'<t' — the IH
supplies nothing. So plain DOM does not self-transfer through R2.

**The right carried invariant is interval-ANCESTRY**, in the form already consumed by
`R2_gprefix_dom_from_interval_anc` (13544):

    interval_anc:  ⋀q m'. s' < q ⟹ q < sA ⟹ 0 < m' ⟹ m' ≤ t'' ⟹ m_ancestor A m' q s'

i.e. the deep ancestor `s'` is an `m'`-ancestor of *every* column `q` in `(s', sA)` at every
level `0<m'≤t''`. Given `interval_anc`, `dom_intv` follows immediately by `m_ancestor_elem_lt`,
closing R2. This is the **ancestry** form (not the adjacency-value form `ancestor_monotone`):
ancestry is exactly what the Hunter kernel `m_anc_Suc_imp_strict_min_on_anc` and the I-set/total-
order mechanism handle, and — unlike raw adjacent values — it does **not** plateau at the boundary
m=t-1, so it sidesteps the irreducible bump-arithmetic primitive that defeated three workflows.

So the genuine (B) step is: **define the interval-ancestry invariant (every ancestor q of sA is an
m'-ancestor of every column in (q, sA] for the relevant m'), carry it through `BMS.induct`,
self-transfer it via the kernel / Hunter's mechanism (NOT via adjacent values), and derive
`elem_lt_below_t` (q=sA instance) and `dom_intv` (q=s' deep instance).** R1 reuses
`dom_transfer_R1_from_DOM`; R2 chains `interval_anc → R2_gprefix_dom_from_interval_anc →
dom_transfer_R2_modulo_intervaldom`. (Still needed: an R1/R2 location-dichotomy lemma and, for
R1 l1≥2, the interior-column ↔ `idx_B_in_expansion` coordinate bridge — the file's own
15748–15751 header flags this as the multi-session geometry work.)

## Out of scope here

`BMS_Lex.thy` (lex order, sorries 1369/1814) and `BMS_WellOrdered.thy` (final theorem,
685/725) are separate downstream concerns, not part of the Lemma 2.5 simultaneous induction.
