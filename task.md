# タスクリスト

| ID | タスク | 状態 |
|----|--------|------|
| 1 | Phase 1.1: BMS_Defs.thy 作成 | 完了 |
| 2 | Phase 1.2: BMS の帰納的定義 | 完了 |
| 3 | Phase 1.3: Lemma 2.1 / Cor 2.2 の証明 | Cor 2.2 本証明 / Lemma 2.1 sorry |
| 4 | Phase 1.4: Lemma 2.3 / Cor 2.4 の証明 | Cor 2.4 forward 本証明 / Lemma 2.3, Cor 2.4 backward sorry |
| 5 | Phase 1.5: Lemma 2.5 (i)〜(v) の証明 | sorry |
| 6 | Phase 2.1: Lemma 2.6 を axiomatization | 完了 |
| 7 | Phase 2.2: Theorem 2.7 の証明 | sorry |
| 8 | Phase 3: Isabelle/ZF で Lemma 2.6 を解消 | 未着手 |
| 9 | Isabelle 環境構築 | 完了 (Isabelle2025-2, build OK) |
| 10 | `m_parent` / `m_ancestor` の termination 証明 | sorry |
| 11 | Cor 2.4 backward 方向 | Lemma 2.3 待ち |

## 本証明済 (実 sorry なし)

### Sanity / 帰納定義
- `seed_in_BMS_check`, `expand_in_BMS_check`, `bms_le_refl_check`
- `bms_le_in_BMS` (≤_B が BMS を保つ)

### 順序の構造
- `col_lt_irrefl`, `arr_lex_irrefl`
- `trans_nat_lt`, `col_lt_trans`, `trans_col_lt_set`, `arr_lex_trans`
- `bms_le_trans`, `bms_le_expand`
- `bms_lt_irrefl`, `bms_lt_implies_lex`, `bms_lt_trans`

### 補助補題
- `m_parent_lt_aux`
- `expansion_empty`, `bms_le_empty`
- `iter_zero` (定義), `iter_zero_le`
- `bms_le_implies_lex`

### 主要結果 (条件付き)
- `corollary_2_2` (Lemma 2.1 sorry を仮定)
- `corollary_2_4_forward` (← 方向, Cor 2.2 経由)
