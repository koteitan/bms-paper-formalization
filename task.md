# タスクリスト

## 残タスク

| ID | タスク | 状態 |
|----|--------|------|
| 3 | Lemma 2.1 (一般 n) の証明 | sorry (n=0, m_0 未定義 ケースは本証明済; m_0 定義済ケースの core 補題群進行中) |
| 4 | Lemma 2.3 の証明 | sorry |
| 5 | Lemma 2.5 (i)〜(v) の証明 | sorry (no_b0 ケース完全本証明、Some s ケースは単一 sorry) |
| 7 | Theorem 2.7 のサブステップ (o_on_seed, stable_rep_extend, o_defined, o_preserves) | sorry |
| 8 | Phase 3: Isabelle/ZF で Lemma 2.6 を解消 | 未着手 |
| 10 | `m_parent` / `m_ancestor` の termination 証明 | sorry (補助 m_parent_lt は本証明済) |
| 14 | `bump_col_value_lt_m0` の縁ケース (m_0 ≥ length (A!s)) | sorry |

## 本証明済 (実 sorry なし)

### Sanity / 帰納定義
- `seed_in_BMS_check`, `expand_in_BMS_check`, `bms_le_refl_check`
- `bms_le_in_BMS` (≤_B が BMS を保つ)

### 順序の構造
- `col_lt_irrefl`, `arr_lex_irrefl`
- `trans_nat_lt`, `col_lt_trans`, `trans_col_lt_set`, `arr_lex_trans`
- `col_lt_total`, `arr_lex_total` (任意の配列で全順序)
- `arr_lex_Nil_lt`, `butlast_arr_lex`
- `take_strict_prefix_col_lt`, `map_take_arr_lex_lt`, **`map_take_arr_lex_le`**, **`strip_zero_rows_le_lex`**
- `bms_le_trans`, `bms_le_expand`
- `bms_lt_irrefl`, `bms_lt_implies_lex`, `bms_lt_trans`

### m-parent / m-ancestor 構造
- `m_parent_lt_aux`, `m_parent_lt`
- `last_filter_satisfies`, `m_parent_elem_lt`
- **`m_ancestor_elem_lt`**, **`m_ancestor_trans`**, **`m_ancestor_trans_aux`**
- **`m_parent_Suc_implies_m_ancestor`**
- **`m_ancestor_Suc_implies_m_ancestor`**, **`m_ancestor_Suc_implies_m_ancestor_aux`**
- **`m_ancestor_mono`** (m ≤ m' での祖先関係単調性)
- `b0_start_lt`, `b0_start_le_length`

### 展開の組合せ論
- `bump_col_zero` (i=0 で identity)
- **`bump_col_value_lt_m0`** (bump_col[m_0] < C[m_0]; 縁ケース sorry)
- **`bump_col_value_eq_below`** (m < m_0 で bump_col[m] = C[m])
- **`bump_col_seed_one`** (seed の bump_col 計算)
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
- `replicate_strict_prefix_col_lt`, `seed_lex_succ`, `seed_lex_lt`
- `seed_inj`, `X0_lex_total`

### Lemma 2.5 サポート
- `l1_zero_of_no_b0`
- `max_parent_level_None_imp_b0_start_None`
- `b0_start_None_imp_max_parent_level_None`
- 5 節のクローズドスタイル predicate (`lemma_2_5_*_clause`)
- **`lemma_2_5_at_no_b0`** (Lemma 2.5 の `b0_start = None` ケース完全本証明)
- `lemma_2_5_i`〜`v`, `lemma_2_5_iv_and_v` (joint statement の projection)

### 主要結果
- `corollary_2_2` (Lemma 2.1 sorry を仮定)
- **`corollary_2_4_forward`**, **`corollary_2_4_backward`**, **`corollary_2_4`** (lemma_2_3 を仮定として両方向完成)
- `lemma_2_1_zero` (Lemma 2.1 の n=0 ケース、本証明)
- `lemma_2_1_no_b0` (Lemma 2.1 の m_0 未定義ケース、本証明)
- **`theorem_2_7_BMS_well_ordered`** (Theorem 2.7、`o_preserves` を sorry 仮定として、`ord_wf` から条件付本証明)

## 残 `sorry` (合計 9)

| ファイル | 数 | 内訳 |
|----------|:--:|------|
| `BMS_Defs.thy` | 2 | termination, bump_col_value_lt_m0 縁ケース |
| `BMS_Lex.thy` | 2 | lemma_2_1 (一般 n), lemma_2_3 |
| `BMS_Ancestry.thy` | 1 | Lemma 2.5 (`lemma_2_5_at_main` の `b0_start = Some s` ケース) |
| `BMS_WellOrdered.thy` | 4 | 2.7 sub-steps (o_on_seed, stable_rep_extend, o_defined, o_preserves) |
| `BMS_Stability.thy` | 0 | (Lemma 2.6 は axiomatized) |

## メモ

- **proof script の罠**: `consider...cases` 構造や帰納の `induct ... arbitrary:` で
  `lexord`/`m_ancestor` まわりの自動化がループする場合あり。`metis` 単発か `proof (induct ... rule: nat_less_induct)` の `∀x. P x` 統一形が安定。
- 環境: Isabelle2025-2 (`/opt/Isabelle2025-2`), Ubuntu 22.04 WSL2。
- ビルド時間: `0:00:02`〜`0:00:03` 程度 (heap キャッシュ後)。
- Lemma 2.1 完成への道: bump_col_value_lt_m0 + bump_col_value_eq_below 揃い → bump_col_lt_C → expansion_some_lt_orig → lemma_2_1。
