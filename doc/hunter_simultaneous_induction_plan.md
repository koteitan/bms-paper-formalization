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

## Out of scope here

`BMS_Lex.thy` (lex order, sorries 1369/1814) and `BMS_WellOrdered.thy` (final theorem,
685/725) are separate downstream concerns, not part of the Lemma 2.5 simultaneous induction.
