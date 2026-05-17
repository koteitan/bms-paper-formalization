# タスクリスト

> **メモ**: 完了は ✅、 未完は 🚨。
> 各 commit が一次履歴であり、 本ファイルは概観用。

## 現在のステータス

**重大発見 (2026-05-17)**: yaBMS で `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` が standard BMS かつ `ascends A 2 1 = False` を確認。 これにより `BMS_all_B0_ascending_below_t` は FALSE statement であることが判明。 dependent な `bump_col_uniform_k_lt_t` と (ii)/(iii) helpers が unsound。 paper 精読の結果、 Hunter は universal ascending を主張しておらず、 各 clause 内で「ascending か否か」 の case-split を行う論法を採用していた。 我々の Isabelle 定式化が over-strong 仮定を導入していた。

**コード上の sorry: 8 件** (全 honest sorry、 false statement 0):
- `seed_descendants_total_strong` N≥2 case (BMS_Lex.thy:1369)
- `lemma_2_5_ii_clause_step` (BMS_Ancestry.thy:1956) — 旧 signature 残存、 body sorry 化 (削除前は unsound)
- `lemma_2_5_ii_clause_step_v2` (BMS_Ancestry.thy:1985) — 新 sound scaffold (Hunter case-split)
- `lemma_2_5_iii_clause_step` (BMS_Ancestry.thy:2447) — 旧 signature 残存、 body sorry 化
- `lemma_2_5_iv_clause_step` n>0 case (BMS_Ancestry.thy:2511)
- `lemma_2_5_i_clause_step` 全体 (BMS_Ancestry.thy:2522)
- `lemma_2_5_v_clause_step` 全体 (BMS_Ancestry.thy:2533)
- `stable_rep_extend_strict` Suc n' Some s (BMS_WellOrdered.thy:410)

**削除済の unsound infrastructure (2026-05-17 commit)**:
- 🗑️ `BMS_all_B0_ascending_below_t` (FALSE statement、 反例 `(0,0,0)(1,1,1)(2,0,0)(1,1,1)`)
- 🗑️ `bump_col_uniform_k_lt_t` (上記経由、 statement も false)
- 🗑️ `elem_expansion_B_lt_invariant_in_block` (上記経由)
- 🗑️ (ii) k=0 0<t helpers (within / outside / shift)
- 🗑️ (ii) Suc k' k<t helpers (within / outside / shift)
- 🗑️ `elem_B0_lt_last_col_when_k_lt_m0` (FALSE conjecture)
- 🗑️ `m_parent_orig_last_col_when_k_lt_m0` (first-step in A)
- 🗑️ `m_parent_AEn_idx_B_n_zero_when_k_lt_m0` (first-step in A[n])

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

## Hunter Lemma 2.5 (i)-(v) layered 帰納 (2026-05-17 改訂)

旧 simultaneous induction は unsound infrastructure 経由で全 clause が unsound 化したため削除。 改訂版は paper 精読に基づく per-clause layered approach (詳細は `important-lemma.md`)。

- 🚨 `lemma_2_5_at_main` (旧 5-AND assembly が unsound 削除済、 layered 構造で再構築待ち)
  - ✅ `lemma_2_5_at_n_zero`: n=0 base
  - ✅ `lemma_2_5_at_no_b0`: b0_start=None case
  - ✅ `lemma_2_5_v_clause_n_le_one`: n≤1 で (v) vacuous
  - ✅ `lemma_2_5_iii_clause_when_k_ge_m0`: k≥m_0 で (iii) vacuous
  - 🚨 layered 構築待ち: (ii)→(iv)→(iii)→(i)→(v)

- 🚨 (ii) step `lemma_2_5_ii_clause_step` (旧 signature、 body sorry、 削除前は unsound)
- 🚨 (ii) step v2 `lemma_2_5_ii_clause_step_v2` (Hunter case-split、 IH(ii) only)
  - ✅ scaffold: 4-way dispatch [2026-05-17 cherry-pick 66bb06d]
  - ✅ vacuous (n=0 / b0=None / i≥j): direct discharge
  - ✅ k=0 t=0: `m_anc_zero_idx_B_in_block_shift_when_t_zero` で dispatch
  - ✅ Suc k' k≥t: `m_anc_idx_B_in_block_shift_at_Suc_k_when_k_ge_t` で dispatch
  - 🚨 k=0 0<t (line 2094): sound per-col case-split helpers 要 (~150 行)
  - 🚨 Suc k' k<t (line 2119): 同上 + IH (ii) at k'

- 🚨 (iv) step `lemma_2_5_iv_clause_step`
  - ✅ n=0 case proven inline (block 0 only B-block)
  - ✅ Suc n' 部分: `b0_start=None` vacuous + G case (`clause_iv_G_case`) + B_n case (`clause_iv_B_n_case`) discharge [2026-05-17 cherry-pick f4bc700]
  - 🚨 Suc n' 残: intermediate B_t case (0 ≤ t < n、 line 2588) — (ii) k<t sound helpers 経由

- 🚨 (iii) step `lemma_2_5_iii_clause_step` (旧 signature、 body sorry、 削除前は unsound)
  - 古い 4 sub-helpers 構造 (Lemma A, Lemma A', first-step in A, first-step in A[n]) は削除済 (first-step 2 つは false conjecture 依存だった)
  - 残: Lemma A と Lemma A' は sound に保持済 (現コードに残っている)
  - 🚨 再実装待ち: (ii) at k を oracle として layered で証明 (paper page 5「trivial extension」)

- 🚨 (i) step `lemma_2_5_i_clause_step` (全体 sorry)
  - 🚨 再実装待ち: layered で (ii)(iii)(iv) at k + IH(i) を使用

- 🚨 (v) step `lemma_2_5_v_clause_step` (全体 sorry)
  - 🚨 再実装待ち: layered で (ii)(iii)(iv) at k を直接 corollary

## (ii) k<t cases 用 sound infrastructure (両 agent 共通指摘の foundational work)

🚨 **次の round の中核 task** (~300 行):
- `elem_AEn_cross_block_not_ascends`: ¬ ascends A x k で elem A[n] @ idx_B(c, x) = (A!(s+x))!k (block 不変)
- `m_parent_AEn_idx_B_within_block_at_k_when_k_lt_t_ascending`: ascending case 用
- `m_parent_AEn_idx_B_within_block_at_k_when_k_lt_t_not_ascending`: non-ascending case 用
- chain shift for k=0 / Suc k' in k < t regime、 ascending case-split で構築
- `ascends_invariant_along_chain` を活用 (= 既存 sound helper)

## 🤖 Sub-agent 並列実行プラン (2026-05-17)

### Round 1 (foundational、 1 agent)
- 🤖 **Agent E**: (ii) k<t sound infrastructure (~300 行)
  - 📥 input: 既存 sound helpers + Hunter paper p.5 case-split
  - 📤 output: elem cross-block helpers + per-col case-split chain shift

### Round 2 (1 agent、 Round 1 依存)
- 🤖 **Agent F**: (ii) v2 substantive proof 完成
  - 📥 input: Agent E の helpers
  - 📤 output: `lemma_2_5_ii_clause_step_v2` 残 2 sorry (line 2094, 2119) close
  - 結果: Stage 1 完了 (∀k. (ii))

### Round 3 (2 agents 並列、 Round 2 依存)
- 🤖 **Agent G**: (iv) Suc n' intermediate B_t case 完成
  - 📥 input: (ii) main + Agent E の k<t helpers
  - 📤 output: `lemma_2_5_iv_clause_step` line 2588 sorry close → Stage 2 完了
- 🤖 **Agent H**: (iii) layered 再実装
  - 📥 input: (ii) main、 残存 Lemma A、 Lemma A'
  - 📤 output: `lemma_2_5_iii_clause_step` を Hunter「trivial extension」 で書き直し → Stage 3 完了

### Round 4 (2 agents 並列、 Round 3 依存)
- 🤖 **Agent I**: (i) substantive proof (paper p.7)
  - 📥 input: (ii)(iii)(iv) main + IH(i)
  - 📤 output: `lemma_2_5_i_clause_step` 全体 + `lemma_2_5_i_main` → Stage 4 完了
- 🤖 **Agent J**: (v) layered 実装 (paper p.7、 直接 corollary)
  - 📥 input: (ii)(iii)(iv) main (oracle)
  - 📤 output: `lemma_2_5_v_clause_step` 全体 → Stage 5 完了

### Final (1 agent、 全 Stage 完了後)
- 🤖 **Agent K**: `lemma_2_5_at_main` を layered 5-Stage で組み立て
  - 📥 input: 5 main lemmas
  - 📤 output: `lemma_2_5_at_main` + projection lemmas update

### 並列タイムライン

```
Round 1: [Agent E]
Round 2:         [Agent F]
Round 3:                 [Agent G][Agent H]    ← 並列 2
Round 4:                                  [Agent I][Agent J]  ← 並列 2
Final:                                                       [Agent K]
```

並列性 max 2 agents (Round 3, 4)。 Stage 1 (foundational) と Stage 5 (final assembly) は serial。
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
