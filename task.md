# タスクリスト

> **メモ**: 完了は ✅、 未完は 🚨。
> 各 commit が一次履歴であり、 本ファイルは概観用。

## 現在のステータス

**重大発見 (2026-05-17)**: yaBMS で `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` が standard BMS かつ `ascends A 2 1 = False` を確認。 これにより `BMS_all_B0_ascending_below_t` は FALSE statement であることが判明。 dependent な `bump_col_uniform_k_lt_t` と (ii)/(iii) helpers が unsound。 paper 精読の結果、 Hunter は universal ascending を主張しておらず、 各 clause 内で「ascending か否か」 の case-split を行う論法を採用していた。 我々の Isabelle 定式化が over-strong 仮定を導入していた。

**コード上の sorry: 14 件** (全 honest sorry、 false statement 0):

外部 (Lemma 2.5 以外):
- `seed_descendants_total_strong` N≥2 case (BMS_Lex.thy:1369)
- `stable_rep_extend_strict` Suc n' Some s (BMS_WellOrdered.thy:410)

(ii) v2 step (`lemma_2_5_ii_clause_step_v2`):
- BMS_Ancestry.thy:3229 — k=0 0<t outer case
- BMS_Ancestry.thy:3306 — Suc k' k<t、 asc_chain 内 sub-sorry 1
- BMS_Ancestry.thy:3320 — Suc k' k<t、 not_asc_chain 内 sub-sorry 2

旧 (ii) step (signature 残、 body sorry):
- BMS_Ancestry.thy:3091 — `lemma_2_5_ii_clause_step` (旧 5-AND IH 形式、 v2 が新 form)

(iii) step (`lemma_2_5_iii_clause_step`):
- BMS_Ancestry.thy:4078 — n≥2 「shift by (n-1) blocks」 bridge (H delivery)

(iv) step (auxiliary `clause_iv_intermediate_B_t_impossible`):
- BMS_Ancestry.thy:4155 — k=0 row-0 monotonicity
- BMS_Ancestry.thy:4168 — ancestor-of-G-is-G lemma
- BMS_Ancestry.thy:4186 — chain transfer via (ii)/(iii)
- BMS_Ancestry.thy:4193 — IH (iv) at offending k' on witness

(i) step (`lemma_2_5_i_clause_step`):
- BMS_Ancestry.thy:4411 — forward direction sub-sorry (I delivery)
- BMS_Ancestry.thy:4419 — backward direction sub-sorry

(v) step (`lemma_2_5_v_clause_step`):
- BMS_Ancestry.thy:4476 — paper p.7 「last k-ancestor in B_{n_2}」 substantive (J delivery)

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

- 🚨 `lemma_2_5_at_main` (旧 5-AND assembly 削除済、 layered 5-stage 組み立て待ち)
  - ✅ `lemma_2_5_at_n_zero`: n=0 base
  - ✅ `lemma_2_5_at_no_b0`: b0_start=None case
  - ✅ `lemma_2_5_v_clause_n_le_one`: n≤1 で (v) vacuous
  - ✅ `lemma_2_5_iii_clause_when_k_ge_m0`: k≥m_0 で (iii) vacuous
  - 🚨 5 main lemmas (∀k. (i)(ii)(iii)(iv)(v)) の AND 構築

- 🚨 (ii) step v2 `lemma_2_5_ii_clause_step_v2` (Hunter case-split、 IH(ii) only)
  - ✅ scaffold: 4-way dispatch
  - ✅ vacuous (n=0 / b0=None / i≥j) + k=0 t=0 + Suc k' k≥t: dispatch 済
  - ✅ Round 1 (Agent E): 11 sound k<t helpers 構築 (~1027 行)
  - ✅ Round 1.5 (Agent E2): helpers' `asc_all` を `asc_chain` (per-cand chain conditional) に weaken
  - 🟡 Round 2 (Agent F2): Suc k' k<t case scaffold + 2 sub-sorries (lines 3306, 3320)
  - 🚨 残: k=0 0<t (line 3229) — Round 1 に k=0 helpers なし、 追加要

- 🚨 (iv) step `lemma_2_5_iv_clause_step`
  - ✅ n=0 case proven inline
  - ✅ Suc n' 部分: b0_start=None + G case + B_n case discharge
  - ✅ Round 3a (Agent G): auxiliary `clause_iv_intermediate_B_t_impossible` で intermediate B_t case を Hunter page 6 case-split に scaffold、 step lemma を dispatch 化
  - 🚨 残: 4 sub-sorries in auxiliary (lines 4155, 4168, 4186, 4193)

- 🚨 (iii) step `lemma_2_5_iii_clause_step`
  - ✅ 既存 sound infra: Lemma A、 Lemma A' (m_anc 同等性 for shared cols)
  - ✅ Round 3b (Agent H): 2 new helpers + (iii) re-implement、 STEP 1 + n=1 case rigorous
  - 🚨 残: n≥2 「(n-1)-block bridge」 sorry (line 4078)

- 🚨 (i) step `lemma_2_5_i_clause_step`
  - ✅ Round 4a (Agent I): scaffold + trivial cases (n=0, b0=None) + iff 構造
  - 🚨 残: forward/backward 2 sub-sorries (lines 4411, 4419) — Hunter p.7 ascending case-split

- 🚨 (v) step `lemma_2_5_v_clause_step`
  - ✅ Round 4b (Agent J): scaffold + trivial cases (n≤1, b0=None)
  - 🚨 残: substantive case (line 4476) — Hunter p.7 「last k-ancestor in B_{n_2}」 argument

- 🚨 旧 (ii) step `lemma_2_5_ii_clause_step` (BMS_Ancestry.thy:3091)
  - 旧 5-AND IH 形式、 body sorry (削除前は unsound、 v2 が新 form として並列)。 layered 完了後に削除予定

## 🤖 Sub-agent 並列実行履歴 (2026-05-17)

### Round 1 (Agent E、 worktree isolation、 1027 行追加)
- ✅ Output: 11 sound k<t helpers (elem_AEn_cross_block_when_(not_)ascends, m_parent_AEn_within/outside_block_at_Suc_k_when_k_lt_t_asc/_not_asc, m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t_asc/_not_asc, etc.)

### Round 1.5 (Agent E2、 helper redesign)
- ✅ Output: helpers' hypothesis を `asc_all: ∀x≤j. x<l1A → ascends` から `asc_chain: ∀x<j. m_ancestor (A[n]) k' (idx_B 0 j) (idx_B 0 x) → ascends` (per-cand chain conditional) に書き直し
- 経緯: F2 (Round 2) が遭遇した design flaw。 `asc_all` は yaBMS 反例 `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` で偽の universal claim と同型で derive 不可

### Round 2 (Agent F → F2、 cherry-pick + main 編集)
- ✅ Output: v2 step scaffold (4-way dispatch) + Suc k' k<t case の case-split + side condition discharge
- 🟡 残: 内部 2 sub-sorry (asc_chain/not_asc_chain lift) + k=0 0<t outer sorry

### Round 3 (Agent G + H、 並列、 worktree+diff)
- ✅ Agent G: (iv) auxiliary `clause_iv_intermediate_B_t_impossible` + step dispatch、 1 bare → 4 sub-sorries
- ✅ Agent H: (iii) extended Lemma A 2 件 + step re-implement、 STEP 1 + n=1 rigorous、 n≥2 1 sub-sorry

### Round 4 (Agent I + J、 並列、 worktree+diff)
- ✅ Agent I: (i) scaffold + trivial cases + iff 構造、 forward/backward 2 sub-sorries
- ✅ Agent J: (v) scaffold + trivial cases、 substantive 1 sub-sorry

### Round 5+ (未着手、 sub-sorries close + Final assembly)
- 🚨 Round 2.5: v2 step の 3 sub-sorries (line 3229, 3306, 3320)
- 🚨 Round 3a.5: (iv) intermediate 4 sub-sorries
- 🚨 Round 3b.5: (iii) n≥2 bridge
- 🚨 Round 4a.5: (i) 2 sub-sorries
- 🚨 Round 4b.5: (v) substantive case
- 🚨 Final: `lemma_2_5_at_main` 5-stage assembly

### Lemma 2.5 helpers (proven infra)
- ✅ `elem_AEn_idx_B_value` (block-shift elem identity、 2026-05-18 追加):
  - `elem (A[n]) (idx_B t j) k = (A!(s+j))!k + (if ascends A j k then t·δ_k else 0)`
  - 用途: (iii) bridge、 (iv) k=0 row-0 monotonicity、 block-shift 推論
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
