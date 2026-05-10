# タスクリスト

## 残タスク (推奨順)

| 順 | タスク | 状態 | 見込み |
|:--:|--------|------|:--:|
| 1 | `lex_implies_le_B` (Cor 2.4 backward 相当): A,A'∈BMS, A<_lex A' ⟹ A ≤_B A' | sorry | cross-branch 補題要 |
| 2 | `lemma_2_5_at_main` の `b0_start = Some s` ケース (Lemma 2.5 同時帰納) | sorry (no_b0 ケース完全本証明済) | 数時間〜 |
| 3 | Theorem 2.7 のサブステップ (`o_on_seed`, `stable_rep_extend`, `o_defined`, `o_preserves`) | sorry | 1〜2h + Ord_t 公理化判断 |
| 4 | Phase 3: Isabelle/ZF で Lemma 2.6 を解消 | 未着手 | 数週間 (Paulson Constructible 学習要) |

## 残 `sorry` (合計 5)

| ファイル | 数 | 内訳 |
|----------|:--:|------|
| `BMS_Defs.thy` | 0 | (termination 解消済) |
| `BMS_Lex.thy` | 1 | `lex_implies_le_B` (Cor 2.4 backward; lemma_2_3 と corollary_2_4 は本証明済) |
| `BMS_Ancestry.thy` | 1 | Lemma 2.5 (`lemma_2_5_at_main` の `b0_start = Some s` ケース) |
| `BMS_WellOrdered.thy` | 3 | 2.7 sub-steps (o_on_seed, stable_rep_extend, o_preserves; o_defined は証明済) |
| `BMS_Stability.thy` | 0 | (Lemma 2.6 は axiomatized) |

## 完了履歴

- **v0.1.10** Step 3 (`bump_col_lt_C`) 完成
- **v0.1.11** Step 4 (`expansion_some_lt_orig`) + Step 5 (`lemma_2_1`) + `BMS_is_array` 完成。
  Lemma 2.1 の sorry を完全解消 (BMS_is_array bridge も本証明済)。
  sorry 9 → 8 に減少。Lemma 2.1 → Cor 2.2, Lemma 2.3, Cor 2.4 への依存連鎖が完全解放。
- **v0.1.12** `bump_col_value_lt_m0` に `m_0 < length (A!s)` 仮定を追加し縁ケース sorry 解消。
  caller `bump_col_lt_C` も既に同条件を持つので呼び出し変更のみ。sorry 8 → 7。
- **v0.1.13** seed chain の基礎: `seed_Suc_expand_one : (seed (Suc n))[1] = seed n` を証明。
  さらに `seed_le_B_succ` (seed n ≤_B seed (Suc n)) と `seed_chain_le_B` (n ≤ m ⟹ seed n ≤_B seed m) を追加。Lemma 2.3 の seed 部分の基盤。
- **v0.1.14** `bms_below_seed : A ∈ BMS ⟹ ∃N. A ≤_B seed N` 追加。
  `bms_pair_below_seed`: 2要素が共通の seed M 以下に収まることを示す。Lemma 2.3 への中間補題。
- **v0.1.15** `seed_pair_le_B_total` 追加: 任意の2 seeds は ≤_B 比較可能。
  Lemma 2.3 の seed-vs-seed ケースを完全カバー。
- **v0.1.16** `m_parent` / `m_ancestor` の termination を解消。
  3段 lex measure (m, i, tag) を `inv_image` で wrap し、case 4 の `p < i`
  を `m_parent.psimps` (under dom) + `m_parent_lt_aux` で discharge。sorry 7 → 6。
- **v0.1.17** Lemma 2.3 を `lex_implies_le_B` 経由に再構築。
  `lemma_2_3` 自体は `arr_lex_total` + `lex_implies_le_B` から自動で証明され、
  `corollary_2_4_backward` も `lex_implies_le_B` を直接参照する 3 行の証明に簡素化。
  sorry の総数は 6 で同じだが、未証明の核 (Cor 2.4 backward) が単一の lemma に
  集約され、構造が明確化された。
- **v0.1.18** `o_defined` を `o_on_seed` + `stable_rep_extend` から BMS.induct で導出。
  sorry 6 → 5。
- **v0.1.19** `o_le_via_bms_le : A ∈ BMS, A' ≤_B A ⟹ o_of A' = o_of A ∨ o_of A' <_o o_of A` を bms_le.induct で証明。
  `o_preserves` の strict 化には未だ axiom 強化が必要だが、≤_o レベルのチェイン補題が利用可能に。
