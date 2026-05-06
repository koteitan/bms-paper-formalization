# タスクリスト

## 残タスク

| ID | タスク | 状態 |
|----|--------|------|
| 3 | Lemma 2.1 (一般 n) の証明 | sorry (n=0, m_0 未定義 ケースは本証明済) |
| 4 | Lemma 2.3 / Cor 2.4 backward の証明 | sorry |
| 5 | Lemma 2.5 (i)〜(v) の証明 | sorry (4 sorry → 1 sorry: 同時帰納の `b0_start = None` 自明ケースを切り出し、実質ケースは単一の `sorry` に統合) |
| 7 | Theorem 2.7 のサブステップ (o_on_seed, stable_rep_extend, o_defined, o_preserves) | sorry |
| 8 | Phase 3: Isabelle/ZF で Lemma 2.6 を解消 | 未着手 |
| 10 | `m_parent` / `m_ancestor` の termination 証明 | sorry (補助 m_parent_lt は本証明済) |
| 12 | `strip_zero_rows_le_lex` の本証明 | sorry (strict 部分は map_take_arr_lex_lt で本証明済) |
| 13 | `bump_col_seed_one` の本証明 | sorry (構成要素は全て本証明済) |

## 本証明済 (実 sorry なし)

### Sanity / 帰納定義
- `seed_in_BMS_check`, `expand_in_BMS_check`, `bms_le_refl_check`
- `bms_le_in_BMS` (≤_B が BMS を保つ)

### 順序の構造
- `col_lt_irrefl`, `arr_lex_irrefl`
- `trans_nat_lt`, `col_lt_trans`, `trans_col_lt_set`, `arr_lex_trans`
- `col_lt_total`, `arr_lex_total` (任意の配列で全順序)
- `arr_lex_Nil_lt`, `butlast_arr_lex`
- `take_strict_prefix_col_lt` (k < length c ⇒ take k c <_clex c)
- `map_take_arr_lex_lt` (head 列が縮むと <_lex)
- `bms_le_trans`, `bms_le_expand`
- `bms_lt_irrefl`, `bms_lt_implies_lex`, `bms_lt_trans`

### 展開の組合せ論
- `m_parent_lt_aux`, `m_parent_lt`
- `last_filter_satisfies`, `m_parent_elem_lt` (m-親の m-要素 < 自身の m-要素)
- `b0_start_lt`, `b0_start_le_length`
- `bump_col_zero` (i=0 で identity)
- `map_nth_offset` (リスト補助)
- `Bi_block_zero`, `Bs_concat_zero` (i=0 で B_0)
- `G_block_B0_block` (G + B_0 = butlast A)
- `expansion_empty`, `expansion_zero_eq` (A[0] = strip_zero_rows (butlast A))
- `Bi_block_no_b0`, `Bs_concat_no_b0`, `expansion_no_b0_eq_zero`

### iter_zero
- `iter_zero` (定義), `iter_zero_le`
- `iter_zero_Suc_lex` (A ≠ [] ⇒ iter_zero A (Suc k) <_lex A)

### 補助補題
- `bms_le_empty`, `bms_le_implies_lex`

### seed の構造
- `length_seed`, `height_seed`, `seed_nonempty`
- `seed_nth0`, `seed_nth1`, `elem_seed_0`, `elem_seed_1`
- `m_parent_seed_zero`, `m_parent_seed_succ`, `m_ancestor_seed_zero`
- `max_parent_level_seed`, `b0_start_seed`
- `ascends_seed_succ`, `not_ascends_seed_succ_top`
- `delta_seed_succ`
- `replicate_strict_prefix_col_lt`, `seed_lex_succ`, **`seed_lex_lt`**
- `seed_inj`, `X0_lex_total`

### 主要結果
- `corollary_2_2` (Lemma 2.1 sorry を仮定)
- `corollary_2_4_forward` (← 方向, Cor 2.2 経由)
- `lemma_2_1_zero` (Lemma 2.1 の n=0 ケース、本証明)
- `lemma_2_1_no_b0` (Lemma 2.1 の m_0 未定義ケース、本証明)
- **`theorem_2_7_BMS_well_ordered`** (Theorem 2.7、`o_preserves` を sorry 仮定として、`ord_wf` から条件付本証明)

## 残 `sorry` (合計 11)

| ファイル | 数 | 内訳 |
|----------|:--:|------|
| `BMS_Defs.thy` | 2 | termination, bump_col_seed_one |
| `BMS_Lex.thy` | 4 | lemma_2_1, lemma_2_3, corollary_2_4, strip_zero_rows_le_lex |
| `BMS_Ancestry.thy` | 1 | Lemma 2.5 (`lemma_2_5_at_main` の `b0_start = Some s` ケース) |
| `BMS_WellOrdered.thy` | 4 | 2.7 sub-steps (o_on_seed, stable_rep_extend, o_defined, o_preserves) |
| `BMS_Stability.thy` | 0 | (Lemma 2.6 は axiomatized) |

## メモ

- **proof script の罠**: `consider...cases` 構造や帰納の `induct ... arbitrary:` で
  `lexord` まわりの自動化がループする場合あり。`metis` 単発が安定。
- 環境: Isabelle2025-2 (`/opt/Isabelle2025-2`), Ubuntu 22.04 WSL2。
- ビルド時間: `0:00:02`〜`0:00:03` 程度 (heap キャッシュ後)。
- 進捗: 種集合 `X_0` が辞書式順序で線形に並んでいる事実は `seed_lex_succ`,
  `seed_lex_lt`, `seed_inj`, `X0_lex_total` で完全確立。
- Theorem 2.7 (主定理) は `o_preserves` のみ仮定すれば本証明されている。
