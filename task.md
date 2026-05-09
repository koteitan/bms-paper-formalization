# タスクリスト

## 残タスク (推奨順)

| 順 | タスク | 状態 | 見込み |
|:--:|--------|------|:--:|
| 1 | Lemma 2.3 の証明 (BMS 全順序) | sorry | 不明 (構造帰納要) |
| 2 | `lemma_2_5_at_main` の `b0_start = Some s` ケース (Lemma 2.5 同時帰納) | sorry (no_b0 ケース完全本証明済) | 数時間〜 |
| 3 | Theorem 2.7 のサブステップ (`o_on_seed`, `stable_rep_extend`, `o_defined`, `o_preserves`) | sorry | 1〜2h + Ord_t 公理化判断 |
| 4 | `m_parent` / `m_ancestor` の termination 証明 | sorry (補助 m_parent_lt は本証明済) | 1〜2h (`partial_function` 化等) |
| 5 | Phase 3: Isabelle/ZF で Lemma 2.6 を解消 | 未着手 | 数週間 (Paulson Constructible 学習要) |

## 残 `sorry` (合計 7)

| ファイル | 数 | 内訳 |
|----------|:--:|------|
| `BMS_Defs.thy` | 1 | termination |
| `BMS_Lex.thy` | 1 | lemma_2_3 |
| `BMS_Ancestry.thy` | 1 | Lemma 2.5 (`lemma_2_5_at_main` の `b0_start = Some s` ケース) |
| `BMS_WellOrdered.thy` | 4 | 2.7 sub-steps (o_on_seed, stable_rep_extend, o_defined, o_preserves) |
| `BMS_Stability.thy` | 0 | (Lemma 2.6 は axiomatized) |

## 完了履歴

- **v0.1.10** Step 3 (`bump_col_lt_C`) 完成
- **v0.1.11** Step 4 (`expansion_some_lt_orig`) + Step 5 (`lemma_2_1`) + `BMS_is_array` 完成。
  Lemma 2.1 の sorry を完全解消 (BMS_is_array bridge も本証明済)。
  sorry 9 → 8 に減少。Lemma 2.1 → Cor 2.2, Lemma 2.3, Cor 2.4 への依存連鎖が完全解放。
- **v0.1.12** `bump_col_value_lt_m0` に `m_0 < length (A!s)` 仮定を追加し縁ケース sorry 解消。
  caller `bump_col_lt_C` も既に同条件を持つので呼び出し変更のみ。sorry 8 → 7。
