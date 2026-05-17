# タスクリスト

> **メモ**: 完了は ✅、 未完は 🚨。
> 各 commit が一次履歴であり、 本ファイルは概観用。

## 現在のステータス

**重大発見 (2026-05-17)**: yaBMS で `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` が standard BMS かつ `ascends A 2 1 = False` を確認。 これにより `BMS_all_B0_ascending_below_t` は FALSE statement であることが判明。 dependent な `bump_col_uniform_k_lt_t` と (ii)/(iii) helpers が unsound。 paper 精読の結果、 Hunter は universal ascending を主張しておらず、 各 clause 内で「ascending か否か」 の case-split を行う論法を採用していた。 我々の Isabelle 定式化が over-strong 仮定を導入していた。

**コード上の sorry: 7 件** (うち 2 件は確認済 FALSE statement、 既存 proven body は false 前提から derive されており unsound):
- `seed_descendants_total_strong` N≥2 case (BMS_Lex.thy:1369)
- 🚨 `BMS_all_B0_ascending_below_t` inductive case (BMS_Lex.thy:1660) — **FALSE statement** (反例確認済)、 sorry は永久に discharge 不可
- 🚨 `elem_B0_lt_last_col_when_k_lt_m0` (BMS_Ancestry.thy:3048) — **FALSE conjecture** (同反例で elem cond も破綻)、 削除予定
- `lemma_2_5_iv_clause_step` n>0 case (BMS_Ancestry.thy:3935)
- `lemma_2_5_i_clause_step` 全体 (BMS_Ancestry.thy:3946)
- `lemma_2_5_v_clause_step` 全体 (BMS_Ancestry.thy:3957)
- `stable_rep_extend_strict` Suc n' Some s (BMS_WellOrdered.thy:410)

**Unsound (proven body だが false 前提)**:
- `bump_col_uniform_k_lt_t` (BMS_Lex.thy:1669) — `BMS_all_B0_ascending_below_t` 経由
- (ii) Suc k' k<t helpers (`m_parent_AEn_idx_B_within/outside_block_at_Suc_k_when_k_lt_t`, `m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t`) — `bump_col_uniform_k_lt_t` 経由
- `lemma_2_5_ii_clause_step` Suc k' k<t case — 上記経由
- (iii) first-step helpers (`m_parent_orig_last_col_when_k_lt_m0`, `m_parent_AEn_idx_B_n_zero_when_k_lt_m0`) — `elem_B0_lt_last_col_when_k_lt_m0` 経由

**コード上の axiom: 6 件** — `ord_lt_irrefl`, `ord_lt_trans`, `ord_wf`, `sigma_pair_exists`, `lemma_2_6`, `o_of_def`。

## Hunter Lemma 2.5 (i)-(v) 改訂依存マトリックス (paper 精読 2026-05-17)

paper のproof を再精読した結果、 各 clause が真に要する IH は以下:

| at k で証明 \ 依存 → | (i)k | (ii)k | (iii)k | (iv)k | (v)k | IH(i) | IH(ii) | IH(iii) | IH(iv) | IH(v) |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| **(i) at k**   | -   | ✓ | ✓ | ✓ | - | ✓ | - | - | - | - |
| **(ii) at k**  | -   | - | - | - | - | - | ✓ | - | - | - |
| **(iii) at k** | -   | ✓ | - | - | - | - | - | - | - | - |
| **(iv) at k**  | -   | ✓ | - | - | - | - | - | - | ✓ | - |
| **(v) at k**   | -   | ✓ | ✓ | ✓ | - | - | - | - | - | - |

### IH 依存グラフ (DAG)

```
IH(ii) → (ii)@k → (iii)@k ↘
                            (i)@k ← IH(i)
       IH(iv) → (iv)@k ↗ ↘
                            (v)@k
```

矢印は **prerequisite → consequence** (a → b は b が a に依存)。

### 帰結

- **k-induction が真に必要なのは (ii), (iv), (i) のみ** (各々自前 IH 要)
- **(iii), (v) は同 k の他 clause の直接 corollary** (induction 不要)
- **simultaneous induction 不要** — 各 clause を独立に layered で証明可能

### Layered な構築方式 (新方針)

```
ステージ 1: ∀k. (ii) at k   ← k-induction、 IH(ii) only
ステージ 2: ∀k. (iv) at k   ← k-induction、 IH(iv) + (ii) at all k
ステージ 3: ∀k. (iii) at k  ← 直接 corollary、 (ii) at k
ステージ 4: ∀k. (i) at k    ← k-induction、 IH(i) + (ii)(iii)(iv) at all k
ステージ 5: ∀k. (v) at k    ← 直接 corollary、 (ii)(iii)(iv) at all k
```

### 現実装 (simultaneous) vs 改訂 (layered) の比較

| 項目 | 現状 (unsound) | 改訂 (layered, 新方針) |
|---|---|---|
| 帰納構造 | 5 clause 同時 nat_less_induct | (ii)/(iv)/(i) は独立 nat_less_induct、 (iii)/(v) は直接 |
| step lemma 数 | 5 個 (各 IH = 5-AND) | (ii)(iv)(i) は step + IH 自前、 (iii)(v) は直接 lemma |
| sound/unsound 局所化 | (ii) sorry が全 clause に伝播 | clause 単位で隔離 |
| 不要依存 | (iv) → (iii)、 (v) → (i) | 削除 |

## 旧 step lemma 群 (deprecated/unsound 化予定)

注: 旧 `lemma_2_5_at_main` は nested (k, n) induction で 5 step lemma を call、 (iii) k<m_0 assembly は 4 sub-helper で組み上げ、 などの構造的 work は残るが、 unsound 前提に立つため再実装が必要。

**コード上の axiom: 6 件** — `ord_lt_irrefl`, `ord_lt_trans`, `ord_wf`, `sigma_pair_exists`, `lemma_2_6`, `o_of_def`。 `lemma_2_6` は ZF 側で discharge 予定、 他は ordinal/σ-pair の前提として保持。

## Hunter Lemma 2.5 (i)-(v) 同時 k-induction

- 🚨 `lemma_2_5_at_main` (5 step lemma assembly は本体 sorry 解除済、 ただし step lemma 群が sorry)
  - ✅ assembly 本体: `nat_less_induct` on k + Hunter 順 ((ii)→(iii)→(iv)→(i)→(v)) で step lemma を呼ぶ
  - ✅ scaffold restructure: `nat_less_induct` on k 化 [ID 45, 62]
  - ✅ `lemma_2_5_at_n_zero`: n=0 base [ID 44]
  - ✅ `lemma_2_5_at_no_b0`: b0_start=None case
  - ✅ `lemma_2_5_v_clause_n_le_one`: n≤1 で (v) vacuous [ID 63]
  - ✅ `lemma_2_5_iii_clause_when_k_ge_m0`: k≥m_0 で (iii) vacuous [ID 64]
  - 🚨 (i) step lemma (`lemma_2_5_i_clause_step` stub、 sorry)
  - ✅ (ii) step lemma (`lemma_2_5_ii_clause_step`) — 全 sub-case proven
    - ✅ scaffold: 8-way case split (n=0/None/i≥j proven) [ID 70]
    - ✅ k=0 0<t: helper 完全 close (2026-05-17、 uniform bumping + block-shift invariance)
      - ✅ `keep_of_pre_strip_pos_of_t_pos_and_n_pos`: B_1 row 0 > 0 で keep_of > 0 を establish
      - ✅ `m_parent_AEn_idx_B_within_block_at_row_zero_when_0_lt_t`: m_parent within-block 特化
      - ✅ `m_parent_AEn_idx_B_outside_block_at_row_zero_when_0_lt_t`: m_parent outside-block 特化
      - ✅ `m_anc_idx_B_in_block_shift_at_row_zero_when_0_lt_t`: chain induction 本体
    - ✅ k=0 t=0: helper 完全 close [ID 74]
      - ✅ `AEn_nth_idx_B_eq_when_m0_zero`: column equality across blocks [ID 75]
      - ✅ `elem_AEn_idx_B_eq_when_m0_zero`: 上記 corollary [ID 76]
      - ✅ `elem_AEn_idx_B_eq_block_zero_at_row_zero_when_m0_zero`: 上記 row-0 特化
      - ✅ `m_anc_zero_idx_B_in_block_shift_when_t_zero` chain induction 本体
      - ✅ `m_parent_AEn_zero_idx_B_within_block_when_t_zero` sub-helper
      - ✅ `m_parent_AEn_zero_idx_B_outside_block_when_t_zero` sub-helper
    - ✅ Suc k' k<t: helper 完全 close (2026-05-17、 parameterized manc_inv で IH (ii) at k' を経由)
      - ✅ `keep_of_pre_strip_ge_max_parent_level`: t ≤ keep_of を establish (rows 0..t-1 all positive in pre-strip)
      - ✅ `m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t`: m_parent within-block 特化、 manc_inv parameter で c⟷0 invariance
      - ✅ `m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t`: m_parent outside-block 特化、 manc_inv parameter
      - ✅ `m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t`: chain induction (c=0 trivial / c=n via IH (ii) at k')
    - ✅ Suc k' k≥t: helper 完全 close (2026-05-17、 elem 等式 in-bounds + OOB の uniform 処理)
      - ✅ `elem_AEn_eq_at_row_k_ge_t_across_blocks`: elem 値の block 不変性 (in-bounds via elem_expansion_B_eq_orig_k_ge_t、 OOB via nth_same_length_oob)
      - ✅ `m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_ge_t`
      - ✅ `m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_ge_t`
      - ✅ `m_anc_idx_B_in_block_shift_at_Suc_k_when_k_ge_t`: chain induction
  - 🚨 (iii) step lemma (`lemma_2_5_iii_clause_step`)
    - ✅ scaffold: 5-way case split (n=0/None/k≥m_0 proven) [ID 71]
    - ✅ k<m_0 assembly: 4 sub-helper を経由した chain translation 組み立て (2026-05-17)
      - ✅ `lemma_2_5_at_main` nested (k, n) induction 化 (IH_n = lemma_2_5_at A (n-1) k を提供)
      - ✅ `lemma_2_5_iii_clause_step` signature に IH_n_minus_1 追加
      - ✅ assembly: first-step in A + first-step in A[n] + Lemma A + Lemma A' + (ii) for A[n-1] at k で chain translation
      - ✅ sub-helper: `m_parent_orig_last_col_when_k_lt_m0` (first step in A) [2026-05-17 close]
        - ✅ induct k less_induct + cases k=0/Suc k': cand X-2 (= ?p) は largest cand、 elem cond + m_anc cond (Suc 経由 IH at k')
        - 依存: `elem_B0_lt_last_col_when_k_lt_m0` (Hunter 構造 conjecture、 sorry)
      - ✅ sub-helper: `m_parent_AEn_idx_B_n_zero_when_k_lt_m0` (first step in A[n]) [2026-05-17 close]
        - ✅ 同構造 (less_induct on k) + bumping arithmetic で elem cond を導出
        - 依存: `elem_B0_lt_last_col_when_k_lt_m0` + `bump_col_uniform_k_lt_t` + `BMS_all_B0_ascending_below_t`
      - ✅ sub-helper Lemma A: `m_anc_orig_eq_AEn_shared_B0` (orig vs A[n] for shared cols ≤ idx_B(0, l_1)-1) [2026-05-17 close]
        - ✅ `elem_orig_eq_AEn_shared_below_l1` (G/B_0 case split via elem_expansion_G_lt_keep + elem_expansion_B0_via_orig)
        - ✅ chain induction: outer less_induct on k + inner less_induct on p、 m_parent match via filter cong + IH at k'
      - ✅ sub-helper Lemma A': `m_anc_AEn_minus_1_eq_AEn_shared` (A[n-1] vs A[n] for shared cols ≤ idx_B(n-1, l_1)-1) [2026-05-17 close]
        - ✅ `elem_AEn_minus_1_eq_AEn_shared`: pre-strip cols match (G/B-block case split) + strip preserves elem for k < t ≤ keep_of (both)
        - ✅ chain induction (same structure as Lemma A)、 precondition `n_minus_1_pos: 0 < n - 1` (n ≥ 2) で両 keep_of bound を保証
        - ✅ (iii) substantive case を `n - 1 = 0` (n=1) と `0 < n - 1` (n≥2) で case-split: n=1 では chain が step1 (Lemma A) に collapse、 n≥2 では step1+Lemma A'+(ii) at A[n-1]+Lemma A'
  - 🚨 (iv) step lemma (`lemma_2_5_iv_clause_step`)
    - ✅ n=0 case proven inline (block 0 = only B-block, positions trivially split G + block 0)
    - 🚨 n>0 case: BMS structural property要 (block n partial cand 存在保証)
  - 🚨 (v) step lemma (`lemma_2_5_v_clause_step` stub、 sorry)
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
