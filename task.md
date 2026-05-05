# タスクリスト

## 残タスク

| ID | タスク | 状態 |
|----|--------|------|
| 3 | Lemma 2.1 (一般 n) の証明 | sorry (n=0 ケースは本証明済) |
| 4 | Lemma 2.3 / Cor 2.4 backward の証明 | sorry |
| 5 | Lemma 2.5 (i)〜(v) の証明 | sorry |
| 7 | Theorem 2.7 のサブステップ | sorry |
| 8 | Phase 3: Isabelle/ZF で Lemma 2.6 を解消 | 未着手 |
| 10 | `m_parent` / `m_ancestor` の termination 証明 | sorry (補助 m_parent_lt は本証明済) |
| 12 | `strip_zero_rows_le_lex` の本証明 | sorry |

## 本証明済 (実 sorry なし)

### Sanity / 帰納定義
- `seed_in_BMS_check`, `expand_in_BMS_check`, `bms_le_refl_check`
- `bms_le_in_BMS` (≤_B が BMS を保つ)

### 順序の構造
- `col_lt_irrefl`, `arr_lex_irrefl`
- `trans_nat_lt`, `col_lt_trans`, `trans_col_lt_set`, `arr_lex_trans`
- `col_lt_total`, `arr_lex_total` (任意の配列で全順序)
- `arr_lex_Nil_lt`, `butlast_arr_lex`
- `bms_le_trans`, `bms_le_expand`
- `bms_lt_irrefl`, `bms_lt_implies_lex`, `bms_lt_trans`

### 展開の組合せ論
- `m_parent_lt_aux`, `m_parent_lt`
- `b0_start_lt`, `b0_start_le_length`
- `bump_col_zero` (i=0 で identity)
- `map_nth_offset` (リスト補助)
- `Bi_block_zero`, `Bs_concat_zero` (i=0 で B_0)
- `G_block_B0_block` (G + B_0 = butlast A)
- `expansion_empty`, `expansion_zero_eq` (A[0] = strip_zero_rows (butlast A))

### iter_zero
- `iter_zero` (定義)
- `iter_zero_le` (iter_zero A k ≤_B A)
- `iter_zero_Suc_lex` (A ≠ [] ⇒ iter_zero A (Suc k) <_lex A)

### 補助補題
- `bms_le_empty`, `bms_le_implies_lex`

### 主要結果
- `corollary_2_2` (Lemma 2.1 sorry を仮定)
- `corollary_2_4_forward` (← 方向, Cor 2.2 経由)
- **`lemma_2_1_zero`** (Lemma 2.1 の n=0 ケース、本証明)

## 残 `sorry` (合計 15)

| ファイル | 数 | 内訳 |
|----------|:--:|------|
| `BMS_Defs.thy` | 1 | termination of m_parent/m_ancestor |
| `BMS_Lex.thy` | 4 | lemma_2_1 (一般), lemma_2_3, corollary_2_4 (backward), strip_zero_rows_le_lex |
| `BMS_Ancestry.thy` | 5 | Lemma 2.5 (i)-(v) |
| `BMS_WellOrdered.thy` | 5 | 2.7 sub-steps (o_on_seed, stable_rep_extend, o_defined, o_preserves, theorem_2_7) |
| `BMS_Stability.thy` | 0 | (Lemma 2.6 は axiomatized) |

## メモ

- **proof script の罠**: `consider...cases` 構造は `lexord` まわりの `auto`/`blast` でビルドが無限ループする場合あり。代替として `metis` を使うと安定。
- 環境: Isabelle2025-2 (`/opt/Isabelle2025-2`), Ubuntu 22.04 WSL2。
- ビルド時間: `0:00:02` 程度 (heap キャッシュ後)。
