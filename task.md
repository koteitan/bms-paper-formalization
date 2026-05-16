# タスクリスト

> **メモ**: 完了は ✅、 未完は 🚨。
> 各 commit が一次履歴であり、 本ファイルは概観用。

## 現在のステータス

**コード上の sorry: 8 件** (`grep -rn "^[[:space:]]*sorry\|sorry$" isabelle/*.thy`):
- `seed_descendants_total_strong` N≥2 case (BMS_Lex.thy:1369)
- `BMS_all_B0_ascending_below_t` inductive case (BMS_Lex.thy:1660)
- `lemma_2_5_at_main` Some s case (BMS_Ancestry.thy:1452)
- `lemma_2_5_ii_clause_step` k=0 0<t (BMS_Ancestry.thy:1308)
- `lemma_2_5_ii_clause_step` Suc k' k<t (BMS_Ancestry.thy:1355)
- `lemma_2_5_ii_clause_step` Suc k' k≥t (BMS_Ancestry.thy:1362)
- `lemma_2_5_iii_clause_step` k<m_0 (BMS_Ancestry.thy:1421)
- `stable_rep_extend_strict` Suc n' Some s (BMS_WellOrdered.thy:410)

**コード上の axiom: 6 件** — `ord_lt_irrefl`, `ord_lt_trans`, `ord_wf`, `sigma_pair_exists`, `lemma_2_6`, `o_of_def`。 `lemma_2_6` は ZF 側で discharge 予定、 他は ordinal/σ-pair の前提として保持。

## Hunter Lemma 2.5 (i)-(v) 同時 k-induction

- 🚨 `lemma_2_5_at_main` Some s case (BMS_Ancestry.thy)
  - ✅ scaffold restructure: `nat_less_induct` on k 化 [ID 45, 62]
  - ✅ `lemma_2_5_at_n_zero`: n=0 base [ID 44]
  - ✅ `lemma_2_5_at_no_b0`: b0_start=None case
  - ✅ `lemma_2_5_v_clause_n_le_one`: n≤1 で (v) vacuous [ID 63]
  - ✅ `lemma_2_5_iii_clause_when_k_ge_m0`: k≥m_0 で (iii) vacuous [ID 64]
  - 🚨 (i) step lemma (未着手、 inline in main)
  - 🚨 (ii) step lemma (`lemma_2_5_ii_clause_step`)
    - ✅ scaffold: 8-way case split (n=0/None/i≥j proven) [ID 70]
    - 🚨 k=0 0<t: uniform bumping (BMS_all_B0 経由)
    - ✅ k=0 t=0: helper 完全 close [ID 74]
      - ✅ `AEn_nth_idx_B_eq_when_m0_zero`: column equality across blocks [ID 75]
      - ✅ `elem_AEn_idx_B_eq_when_m0_zero`: 上記 corollary [ID 76]
      - ✅ `elem_AEn_idx_B_eq_block_zero_at_row_zero_when_m0_zero`: 上記 row-0 特化
      - ✅ `m_anc_zero_idx_B_in_block_shift_when_t_zero` chain induction 本体
      - ✅ `m_parent_AEn_zero_idx_B_within_block_when_t_zero` sub-helper
      - ✅ `m_parent_AEn_zero_idx_B_outside_block_when_t_zero` sub-helper
    - 🚨 Suc k' k<t: σ-equivariance
    - 🚨 Suc k' k≥t: no bumping at row k
  - 🚨 (iii) step lemma (`lemma_2_5_iii_clause_step`)
    - ✅ scaffold: 5-way case split (n=0/None/k≥m_0 proven) [ID 71]
    - 🚨 k<m_0: (ii) at same k 経由
  - 🚨 (iv) step lemma (未着手、 inline; ID 66-69 で構造解析済)
  - 🚨 (v) step lemma (未着手、 inline)
  - 🚨 (古い) [ID 5] 補助補題群整備 → 現 helpers で代替
  - 🚨 (古い) [ID 6] `lemma_2_5_at_inductive_step`: 5 clause 独立化 → (ii)(iii) で進行中
  - 🚨 (古い) [ID 7] `lemma_2_5_at_main_some` 本体
  - 🚨 (古い) [ID 8] projection sanity check (ID 7 完了後)

### Lemma 2.5 helpers (proven infra)
- ✅ 9 件 chain/value helpers [ID 73]:
  - `m_ancestor_target_lt`, `m_ancestor_chain_linear`, `ascends_invariant_along_chain`
  - `bump_col_uniform_k_lt_t`, `bump_col_no_bump`
  - `elem_expansion_B_lt_invariant_in_block`, `elem_expansion_B_eq_orig_k_ge_t`
  - `BMS_all_B0_ascending_below_t` base case
- ✅ pre-strip / Bs_concat / bump helpers [IDs 46, 49-58, 65]:
  - `b0_start_lt_last`, `l1_pos_of_some` [46]
  - `arr_len_expansion_l01`, `pre_strip_nth_G` [49]
  - `Bs_concat_nth_block`, `pre_strip_nth_B` [50]
  - `elem_expansion_G_lt_keep`, `elem_expansion_B_lt_keep` [51]
  - `bump_col_nth_general` [52]
  - `elem_Bi_block_via_bump_col`, `elem_expansion_B_via_bump` [53]
  - `delta_pos_of_lt_m0`, `bump_col_lt_step` [54]
  - `clause_iv_G_case`, `clause_iv_B_n_case` [55]
  - `elem_expansion_B_lt_step_same_j` [56]
  - `elem_expansion_B_lt_same_block` [57]
  - `bump_col_zero_eq_orig`, `elem_expansion_B0_via_orig` [58]
  - `clause_iv_p_decomposition` [65]
- ✅ m_0=0 helpers [ID 59]:
  - `Bi_block_eq_B0_when_m0_zero`
  - `Bs_concat_when_m0_zero`
  - `pre_strip_expansion_when_m0_zero`
- 🚨 `BMS_all_B0_ascending_below_t` inductive case [ID 72]
  - 経験的に 1193 Hunter BMS で 4824 件 OK、 base case (seed n) proven
  - inductive case (A'[k_exp]) は expand 後の b0_start/max_parent_level/B0_block の structural lemmas が必要

### m_ancestor unfold helpers (proven infra)
- ✅ `m_anc_via_parent_some`: `m_parent A m i = Some p ⟹ m_anc A m i j ⟷ p = j ∨ m_anc A m p j` (本日追加)
- ✅ `m_anc_via_parent_none`: `m_parent A m i = None ⟹ ¬ m_anc A m i j` (本日追加)

## Hunter Cor 2.4 / Lemma 2.3

- 🚨 `seed_descendants_total_strong` N≥2 case [ID 3] (BMS_Lex.thy:1369)
  - Hunter の論証は (α)(β)(γ) を使うが (α) は strip と矛盾 (bug.md B-1)
  - strip-faithful な再構成が必要
- ✅ N=0 dispatch (`seed_0_descendants_total`)
- ✅ N=1 dispatch (`seed_1_descendants_total`) [v0.1.37]
- ✅ `seed_expansion_succ_zero` [ID 1]
- ✅ `seed_chain_le_B_expansion` [ID 2]
- ✅ `seed_lex_implies_le_B`, `lex_implies_le_B` [ID 4]
- ✅ `bms_lt_imp_le_expansion` [ID 47]
- ✅ N=0/1 case 分離で N≥2 narrow [ID 48]
- ✅ `bms_descendants_lex_total` [ID 60]

### clause (iv) 攻撃失敗 history (削除せず保存)
- ✅ [ID 66] (b) conjecture 構造解析 (`(seed 5)[3][2]` で l1≥2 確認)
- ✅ [ID 67] (b) 反証: yaBMS + strip で 3740 件 BFS、 反例 `(0,0)(1,1)(1,1)(1,1)`
- ✅ [ID 68] 計画 (取消)
- ✅ [ID 69] (b') 反証: user 提示反例 `(0,0,0)(1,1,1)(2,0,0)(1,1,1)`
- **結論**: (iv) の sufficient condition は単純な structural property に分解不可、 Hunter 同時 induction の interlock が本質

## Hunter Theorem 2.7 / stable_rep_extend_strict

- 🚨 `stable_rep_extend_strict` Suc n' Some s case (BMS_WellOrdered.thy:410)
  - 🚨 [ID 12] g 構成: G_block には f、 B_i (i≥1) には Lemma 2.6 の Y' 反射値
  - 🚨 [ID 13] g が stable_rep を満たす証明 (Lemma 2.5 本質的使用)
  - 🚨 [ID 14] β 構成 (Hunter handwave、 f の最大値を β に取る具体 indexing が論文未明示)
  - 🚨 [ID 43] 反射構築本体: Lemma 2.6 適用での X, Y 具体化 / sigma_bound 所属検証 / g_{Suc n'} 定義 / stable_rep 検証 / β 選定
- ✅ `stable_rep_extend_strict_zero`: n=0 base [ID 31]
- ✅ induct n refactor [ID 41]
- ✅ b0_start=None case 分離 [ID 42]
- ✅ `stable_rep_imp_strict_mono` / `stable_rep_imp_ancestor_stable` [ID 61]
- ✅ `stable_rep_restrict` [ID 27]
- ✅ `m_ancestor (A[0]) m i j ⟹ m_ancestor A m i j` [ID 28]
- ✅ `m_parent_m_ancestor_butlast` [ID 29]
- ✅ `nth_same_length_oob` [ID 30]
- ✅ `m_ancestor_A0_subsume_A` [ID 32]
- ✅ `is_array_butlast` [ID 33]
- ✅ `keep_of` 分離 (`keep_of_le_height`, `keep_of_row_zero`) [ID 34]
- ✅ `length_col_arr` / `length_col_strip` / `strip_zero_rows_eq_map_take` [ID 35]
- ✅ `elem_strip_lt_keep` / `elem_strip_lt_iff` [ID 36]
- ✅ `m_parent_m_ancestor_strip` (full iff) [ID 37]
- ✅ `Bs_concat_Suc` [ID 38]
- ✅ `arr_len_expansion` [ID 39]
- ✅ `arr_len_expansion_Suc` [ID 40]
- ✅ o_on_seed 一式 [IDs 9, 10, 11]:
  - `sigma_pair_exists` axiom 拡張
  - seed n 2 列に対する stable_rep 構築
  - `m_ancestor (seed n) m 1 0` の m≥n 補強

## Hunter Lemma 2.6 / Phase 3 ZF discharge

- 🚨 [ID 24] HOL 側の `axiomatize lemma_2_6` を ZF 側からの transfer に置換
- 🚨 [ID 16] Paulson `Constructible` ライブラリ import
- 🚨 [ID 17] 2.6.A: `φ_0(η,ξ) := η ∈ ξ` が Σ_0
- 🚨 [ID 18] 2.6.B: `φ_1(η,ξ,k) := η <_k ξ` が Σ_{n+1}
- 🚨 [ID 19] 2.6.C: `φ_2(η,k) := L_η ≺_{Σ_{k+1}} L` が Π_{k+1} (Kranakis 1982 Theorem 1.8 依存)
- 🚨 [ID 20] 2.6.D: 有限 Σ_{n+1} 連言の Σ_{n+1} 性
- 🚨 [ID 21] 2.6.E: Σ_{n+1} 存在閉包
- 🚨 [ID 22] 2.6.F: ψ ∧ φ の `L_β` から `L_α` への反射
- 🚨 [ID 23] 2.6.G: `L_α` 内の証拠から `Y'` と全単射 `f` を構成
- ✅ [ID 15] `isabelle_zf/` ディレクトリ + ROOT 雛形

## Soundness audit

- ✅ [ID 25] `sigma_pair_exists` を Hunter の σ-pair 条件に強化 [v0.1.27]
- ✅ [ID 26] `o_of_def` 公理を `A ∈ BMS` に制限 [v0.1.28]
