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

## Status (2026-06-04): INTV chain landed (v0.1.91); the crux + a verification caveat

The interval-ancestry chain is now on `main` (v0.1.91): `INTV` (definition) + `INTV_imp_interval_anc`
+ `R2_gprefix_dom_from_INTV` + `dom_intv_from_INTV` + `dom_transfer_R2_from_INTV` + `INTV_from_floor`
+ `dom_transfer_R2_from_floor`. These are body-`sorry`-free and build GREEN, and reduce the **R2 branch**
of `DOM A ⟹ DOM (A[n])` to a single strictly-local **m-parent floor** obligation. `elem_lt_below_t` is
NOT yet closed — the remaining residuals are (a) the BMS.induct self-transfer / floor supply for INTV in
R2, and (b) the R1 location-dichotomy + interior↔`idx_B` coordinate bridge (l1≥2).

**Verification caveat (important).** `Thm_Deps.has_skip_proof` is UNRELIABLE in this `quick_and_dirty`
batch build: it correctly flags `refl`=clean / `ancestor_monotone`=tainted, but ALSO flags definitely-clean
basic lemmas (`m_parent_lt`, `m_ancestor_trans`, defined before every `sorry`) as TAINTED — i.e. false
positives. So transitive-`sorry` taint cannot be judged by `has_skip_proof` here. The project's working
standard is **body-`sorry`-free + build-GREEN + no direct reference to the 6 known-`sorry` lemmas**
(`iii_single_step_t_to_Suc_t`, `m_parent_block_n_stays_until_zero`, `onestep_anc_when_ascends`,
`ancestor_monotone`, `clause_i_iff_when_not_ascends`, `lemma_2_5_v_clause_step_iff`); the INTV chain meets
it. For a genuine transitive check, use a proofterm-enabled build (`Proofterm.proofs := 2`) or a full
name-based dependency trace, not `has_skip_proof`.

## Out of scope here

`BMS_Lex.thy` (lex order, sorries 1369/1814) and `BMS_WellOrdered.thy` (final theorem,
685/725) are separate downstream concerns, not part of the Lemma 2.5 simultaneous induction.

## The complete @13220 obligation map (2026-06-05) — the faithful (b) reconstruction's precise shape

The keystone is `ancestor_monotone`'s expand-case sorry (@13220). Its closure via the already-proven
`ancestor_monotone_expand` (@13099) was confirmed to **typecheck and build GREEN** (the plumbing is correct);
it reduces to exactly **7 interlocking obligations**, NOT the single "Htop" previously believed:

| group | obligation | status / what it needs |
|-------|-----------|------------------------|
| STRUCT | `b0_start A = Some sA`, `max_parent_level A = Some tA`, `0 < l1 A` | the **BMS linchpin** `A∈BMS ⟹ mpl(A[n]) defined ⟹ mpl A defined` (described @923-931, **unproven**; false for `is_array`, true for BMS) |
| ENTANGLED | `Hmpl_le1: tE ≤ tA+1` | needs a height/mpl upper bound (no lemma; `height A ≤ mpl A + 2` is **refuted**, so a different proof) |
| ENTANGLED | `Hmpl_gt1: 1<l1 A ⟹ tE ≤ tA` | same family, harder (l1>1 in-bounds) |
| ENTANGLED | `Rb_cond: sE<sA ⟹ m_ancestor A m sA sE` | via `R2_new_root_anc_of_old` (@12446) which **requires `lemma_2_5_i_clause`** — the simultaneous-induction entanglement |
| TOPLEVEL | `Htop: l1 A=1 ⟹ m=tA-1 ⟹ adjacent increase` | needs the carried invariant **strengthened to INV1** (T1-conditional top-level m=t-1 clause) so the IH supplies the `mono` hypothesis of `dom_transfer_R2_from_mono` at m'=tA-1 |

**Conclusion:** closing @13220 is genuinely the **full Hunter simultaneous (i)–(v) k-induction** — `Rb_cond` ties it
to clause (i), `Htop` needs the strengthened invariant, plus the structural linchpin and mpl upper bounds. This is a
multi-session interlocking build (confirmed across ~15 workflow attempts; reduction/bump/ancestry/IH/vacuity all
exhausted). The sorry-free INTV→MONO→floor→R2 chain (v0.1.92, @15939–16330) and `ancestor_monotone_expand` are the
assembled scaffolding; the remaining work is the joint induction carrying the value/top-level clause.

Most self-contained next sub-target: the **BMS structural linchpin** (mpl-definedness monotone under expansion).

## The STRUCT linchpin, fully reduced (2026-06-05) — row0_invariant landed, one crux left

`row0_invariant` (elem A i 0 = case m_parent A 0 i of None=>0 | Some p=>Suc(elem A p 0))
is now **landed on main, sorry-free, clause-iv-free** (v0.1.105, @11381). Built on it:

- `mpl_none_imp_last_col_row0_zero` (v0.1.106, @~11716): mpl A=None => elem A (last) 0 = 0.
- `expansion_no_b0_eq_strip_butlast` (v0.1.107, BMS_Defs): b0_start A=None => A[n]=strip(butlast A).
- `height_expansion_le` (v0.1.108, @~17946): A∈BMS => height(A[n]) <= height A.

**The linchpin `A∈BMS ⟹ mpl A=None ⟹ mpl_le_zero(A[n])` reduces to the single keystone**

  **(c2)  A∈BMS ⟹ height A ≥ 2 ⟹ b0_start A ≠ None**   (equiv. mpl A=None ⟹ height A≤1)

because: mpl A=None ⟹ height A≤1 ⟹ height(A[n])≤height A≤1 ⟹ no level≥1 on A[n]'s last
col (m_parent_None_at_ge_height) ⟹ mpl_le_zero(A[n]) vacuously.

**c2 is provable by BMS.induct** (all pieces empirically 0-fail over 1784 faithful BMS arrays,
verify/probe_mpl_none_linchpin.py):
- seed m: height m≥2 ⟹ last col [1..1] has col-0 [0..0] as parent. **TODO (easy)**.
- expand A[n], height(A[n])≥2:
  - if b0_start A=None: IH contrapositive gives height A≤1, and height(A[n])≤height A≤1
    (height_expansion_le) contradicts height(A[n])≥2 — **vacuous. DONE (mechanical)**.
  - if b0_start A=Some s: height(A[n])≤height A (height_expansion_le) ⟹ height A≥2, then need
    **(c4')  b0_start A=Some s ∧ height(A[n])≥2 ⟹ b0_start(A[n]) ≠ None**.

**STATUS (v0.1.110): the whole reduction above is now LANDED sorry-free on main**, with c4'
carried as an explicit premise: `height_ge2_imp_b0_some_cond` (keystone), 
`mpl_le_zero_expansion_of_height_le1` (vacuity, unconditional), and
`mpl_none_imp_mpl_le_zero_expansion_cond` (the full STRUCT linchpin modulo c4'). Discharging
c4' unconditionally instantly turns all three unconditional.

**c4' is the SOLE remaining crux** (= the open STRUCT linchpin @187). Empirically 0-fail.
NOTE: the naive "b0(A)≠None ⟹ b0(A[n])≠None" is **FALSE** (128/1784 fails, e.g. (0)(1)(0)(1)(0)(1));
the height(A[n])≥2 guard is essential. Reduction of c4' (via cascade+col0+row0_invariant on A[n]):
b0(A[n])=None ⟺ elem(A[n])(last_col A[n]) 0 = 0; last col of A[n] = bump of A-col (last_col_idx A −1)
at block n, so this is a fact about the bumped row-0 tiling closed form (chainlen0_bumped_tiling @556).
Supporting facts available: (c1) elem A i 0=0 ⟹ col i all-zero [0-fail, unproven];
(c3) b0≠None ⟹ elem(last,0)≥1 [provable via upward m_parent cascade, no consec needed].

---

## v0.1.113 premise-map: how to discharge `ancestor_monotone` expand (@15879)

Definitive analysis (2026-06-06). The entire formalization's open frontier = the single
`sorry` at `ancestor_monotone`'s `expand_in_BMS` case (@15879). Its ready-made vehicle
`ancestor_monotone_expand` (@15758, sorry-free, with R1/R2 step lemmas assembled) needs the
premises below. Discharge status from a *bare* `BMS.induct` (predecessor `A`, IH = the
`ancestor_monotone` statement for `A`):

| premise | discharge |
|---|---|
| `A_BMS`, `A_ne` | `A∈BMS` from `expand_in_BMS`; handle `A=[]` vacuously (`A[]=[]`, b0=None ⟹ goal vacuous) |
| `b0A`, `mpA` (`b0_start A=Some sA`, `mpl A=Some tA`) | case-split; **`b0_start A=None` branch is vacuous** via the height≤1 cascade (`height_expansion_le` + `mpl_le_zero_expansion_of_height_le1`): then `mpl(A[n])≤Some 0`, so the goal's `m<t'-1` is unsatisfiable |
| `IH` | the `BMS.induct` IH for `A` — verbatim ✓ |
| `b0E`, `mpE`, `m_lt`, `qor`, `q_lt`, `c_le` | from the unpacked goal for `A[n]` ✓ |
| `keep` (`m<keep_of(G@Bs)`) | from `m<tE-1` + `keep_of_pre_strip_ge_max_parent_level` ✓ |
| `Hmpl_gt1` (`1<l1 A ⟹ tE≤tA`) | mpl relation — **needs an `mpl(A[n])` vs `mpl A` bound lemma** (likely provable; `mpl_bound_from_R2` exists for R2; R1 side TBD) |
| `Hmpl_le1` (`tE≤tA+1`) | mpl relation — same family, TBD-provable |
| **`Rb_cond`** (`sE<sA ⟹ m_ancestor A m sA sE`) | **= `R2_new_root_anc_of_old` (@15105), which needs `lemma_2_5_i_clause A n t''`** → the clause-(i) entanglement. AVAILABLE in the joint bundle (IH carries ∀n k. clause_i). **CRUX #1** |
| **`Htop`** (`l1 A=1 ⟹ m=tA-1 ⟹ elem(A[n])(c-1)m < elem(A[n]) c m`) | top-level adjacent-monotone over `(sE,sA]` at level `tA-1=tE-2`. NOT a boundary (tE-2 < tE-1) so TRUE, but = `ancestor_monotone (A[n])` at level tE-2 = **same-level self-reference**. **CRUX #2** — the irreducible same-level circularity Hunter resolves by the intra-level clause order (ii→iii→iv→i→DOM). |

**Conclusion.** A *bare* `BMS.induct` cannot close @15879: `Rb_cond` needs clause-(i)
(only the joint bundle supplies it) and `Htop` is the same-level circularity. The faithful
restructure: prove `J A ≡ ancestor_monotone(A) ∧ (∀n k. clause_i..v A n k)` by `BMS.induct`;
the expand case discharges `ancestor_monotone(A[n])` via `ancestor_monotone_expand` (Rb_cond ←
clause_i from IH) and the 5 clauses via their `_clause_step` lemmas (DOM-leaves ← ancestor_monotone
from IH). The single residual that survives even the bundle is **Htop / MONO** (design gap §2
"l1=1 R2 G'-tail"), i.e. the staircase at level `tE-2` over `(sE,sA]`, which must come from the
intra-level clause structure at the SAME k — not from lower k or the IH-for-A.

**Empirical guard-rails (probes, 2026-06-06):** `ancestor_monotone` at boundary `m=t-1` is
genuinely violated (`probe_anc_monotone_boundary`: 1660, all G-prefix) ⟹ range `m<t-1` is TIGHT,
no extension route. Broad G-prefix monotone is false (`probe_gprefix_monotone`: 28k+). So Htop
is ONLY the narrow chain-staircase, never a broad value statement.

**First incremental step (DONE, v0.1.114):** the two mpl-relation premises `Hmpl_gt1`/`Hmpl_le1`
are discharged sorry-free by `mpl_expansion_le_from_height_bound` / `..._sharp`, reducing them to
a single *predecessor-only* BMS fact:

> **HBND:** `A ∈ BMS ⟹ A ≠ [] ⟹ mpl A = Some t ⟹ height A ≤ t + 2`
> (sharper `height A ≤ t + 1` when `l1 A > 1`).

Empirically exact (`verify/probe_mpl_relation.py`: `0/2990`). With the known lower bound
`max_parent_level_lt` (`t < height A`), HBND pins `height A ∈ {t+1, t+2}` exactly.

**HBND proof path (next target):** `BMS.induct`, proving HBND *and* the SHARP variant jointly.
Seed: `height(seed n)=n`, `mpl=n-1`, so `n ≤ (n-1)+2` ✓ (and `l1=1`, no sharp obligation). Expand
(`mpl(A[n]) = Some t'`): `height(A[n]) ≤ height A` (`height_expansion_le`); split on `t'` vs `tA`:
- `t' ≥ tA` (mpl stays/rises): `height(A[n]) ≤ height A ≤ tA+2 ≤ t'+2` from IH HBND for `A`. ✓
- `t' < tA` (mpl DROPS): empirically (`probe`, **0/384**) the predecessor is then already **sharp**,
  `height A ≤ tA+1`, so `height(A[n]) ≤ tA+1 = (tA-1)+2`; with `t' = tA-1` (the drop is by exactly
  one) this is `t'+2`. ✓

So the single residual behind HBND is the lever **`mpl(A[n]) < mpl A ⟹ height A ≤ mpl A + 1`**
(equivalently, contrapositive: when `A` has maximal height slack `height A = mpl A + 2`, the
expansion's mpl does NOT drop) plus **the drop is by exactly one** (`t' = tA-1`, not less). Both
are clean BMS structural facts about how `mpl` moves under expansion — the genuine next sub-target.

So @15879's full premise residual is now exactly `{HBND, Rb_cond, Htop}`: `Rb_cond` is handled by
the joint bundle (clause-i from IH), and `HBND`/`Htop` are the two structural facts left. The
grand crux remains **Htop** (the same-level circularity).

---

## 2026-06-06 (workflow 5-agent 収束): 全 sorry ⟹ 単一 crux `mono_A`

2 つの workflow (計 5 worktree-agent) が独立に同一の根本原因へ収束。全 attempt
GREEN baseline 維持・patch 空 (= sorry-free な前進は mono_A 抜きでは存在しない、と
機械的に再確認)。

### 単一 crux
全 6 bare sorry が以下の一点に帰着する:

```
mono_A :  A∈BMS, A≠[], b0_start A=Some s, max_parent_level A=Some m0,
          s < c ≤ last_col_idx A, m < m0  ⟹  elem A (c-1) m < elem A c m
```
= 連続 B0 列の行単調性 = `adjacent_value_monotone` = `ancestor_monotone`(q=s)。
経験的に真 (`verify/probe_block_translation.py` 系, 0/19689; `probe_*`)。
`m < m0` 版 (m=m0-1 含む) も真。`ancestor_monotone` は `m < m0-1` のみ主張する
ので、境界 `m = m0-1` は Htop 領域。

### 6 sorry ≡ mono_A の地図
- `ancestor_monotone` @16047 … mono_A 本体 (q=s 一般化 = ∀q 版)。
- `onestep_anc_when_ascends` @14957 … 残差 mono_res = mono_A (m≤k, k<m0)。
- `m_parent_block_n_stays_until_zero` @13648 (Suc m' 残差) … gateway。block-start
  候補性 = elem strict bound = mono_A。
- `iii_single_step_t_to_Suc_t` @12789 ≡ `lemma_2_5_v_clause_step_iff` ¬asc @17457
  … **同一の block-translation 不変性 crux**。両端点/source-only どちらも mono_A 依存。
- `clause_i_iff_when_not_ascends` @17086 … leftmost gateway、同 crux 系。

### block-translation 不変性 (BT) の分解 (iii/v の正体)
`m_anc(A[n]) k p q ⟷ m_anc(A[n]) k (p+l1)(q+l1)` (B-region, 両端点 +1 block)。
probe: 真 (0/8.085M)。**target-only +l1 は偽** (474411 viol) ⟹ (BT) は
source-shift + target-shift に分離不可。分解:
1. **value 層 = 解決可能**: `k<m0 ⟹ ascends A x k (∀x<l1)` (probe 0/27762) ⟹ +l1 は
   一様 +delta 平行移動 ⟹ value 比較合同は既存 `elem_AEn_lt_block_invariant_when_both_ascend`
   (BMS_Ancestry.thy:3703) に帰着。**ただし「∀x ascend」自体が mono_A 経由**
   (`ascends_offset_from_IH`/`consecutive_parent_from_mono` 経由で mono_A に底打ち)。
2. **構造層 = gateway 必須**: `m_parent` は +l1 と**非可換** (probe 239935 viol;
   G/block-0 境界で候補域 [0..<p] vs [0..<p+l1] が食い違う)。差は m_ancestor の
   推移閉包でのみ washout = gateway 性質 (`m_parent_block_n_stays_until_zero`) で、
   その Suc 残差が再び mono_A 依存。
3. `m_anc_below_ancestor_transfer` (14205, BMS_Defs 依存のみ, 12691 より上流へ relocate 可)
   は source-shift(target 固定)のみ閉じる。target-shift が偽不変性 (上記) のため
   transfer-pair では iii を閉じられない。

### 次手 (推奨)
**mono_A を先に証明する**。すると:
- (BT) ⟸ `elem_AEn_lt_block_invariant_when_both_ascend` + gateway transfer。
- iii/v/gateway/onestep が一斉に解ける。
mono_A は単独では閉じず、Hunter (i)-(v) 同時帰納に bundle 要 (Rb_cond ⟸ clause_i;
Htop = 同 level 循環)。`joint_induction_design.md` の `bms_2_5_joint` (DOM+5clause を
BMS.induct) が唯一の道。
