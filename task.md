# タスクリスト

> **メモ**: 完了したタスクは行を残し、状態欄に ✅ を入れる。
> 各 commit が一次履歴であり、本ファイルは概観用。
> **メモ**: 番号 (ID) は一度付けたら変更しない。新規追加は末尾に追加し、
> 完了・削除しても他の ID は再採番しない。
> **メモ**: 表は **怪しさ (truth が破れるリスク) の高い順** に並べる。
> 行内容を変更しても並べ替え順序は維持する。

## 現在のステータス

**コード上の `sorry`: 3 件** (`grep -rn "^  *sorry\| sorry$" isabelle/*.thy`):
- `seed_descendants_total` の (N ≥ 2 ∧ A, A' 両者 strict descendants) sub-case (BMS_Lex.thy 内) — Hunter Lemma 2.3 closure (N=0/1 case は `seed_{0,1}_descendants_total` で dispatch、 A または A' = seed N の trivial case も dispatch)
- `lemma_2_5_at_main` の (n ≥ 1 ∧ b0_start = Some s) sub-case (BMS_Ancestry.thy 内) — Hunter Lemma 2.5 (i)–(v) 同時 k-induction (n=0 case は `lemma_2_5_at_n_zero` で proven, b0_start = None case は既存 `lemma_2_5_at_no_b0`)
- `stable_rep_extend_strict` Suc n の **Some s** sub-case (BMS_WellOrdered.thy:385) — Hunter 2.7.c–d Lemma 2.6 reflection (None case は v0.1.39 中で proven)

**未完タスク (状態 ≠ ✅): 17 件** — 上の 3 sorry は内部で複数のサブタスクに分解されている (例: `stable_rep_extend_strict` Suc n に対し ID 12,13,14):

- ID 3 (`seed_descendants_total` N≥2)
- IDs 12,13,14 (`stable_rep_extend_strict` の `g` 定義 / `stable_rep` 満たし / β 構成)
- IDs 5,6,7,8 (`lemma_2_5_at_main` 補題群 / inductive step / 本体 / projection sanity)
- IDs 16,17,18,19,20,21,22,23,24 (Lemma 2.6 ZF discharge: ROOT 雛形 → 2.6.A→B→C→D→E→F→G → axiomatize 置換)

**コード上の axiom (sorry とは別カウント):** `ord_lt_irrefl`, `ord_lt_trans`, `ord_wf`, `sigma_pair_exists`, `lemma_2_6`, `o_of_def` の 6 件。 `lemma_2_6` は ZF 側 (ID 16–24) で discharge 予定、 他は ordinal/σ-pair の前提として保持。

**完了済 (v0.1.39 で追加):** `is_array_butlast`, `m_ancestor_strip_subsume` (`m_parent_m_ancestor_strip` full-iff 経由), n=0 case の `stable_rep_extend_strict_zero`。

公理一覧 (BMS_Stability.thy / BMS_WellOrdered.thy):
- `ord_lt_irrefl`, `ord_lt_trans`, `ord_wf`: `<_o` の基本性質
- `sigma_pair_exists`: `∃α β ∈ sigma_bound. ω_o <_o α <_o β ∧ ∀m. stable_lt m α β` — Hunter の σ-pair 存在条件
- `lemma_2_6`: Hunter Lemma 2.6 そのまま (ZF 側で discharge 予定)
- `o_of_def`: `A ∈ BMS ⟹ ∃f. stable_rep A f ∧ (∀i. f i <_o o_of A) ∧ (β-minimality)` — BMS に制限済み (v0.1.28)

`stable_rep_extend_strict` は `A ≠ []` を仮定として持つ (`o_of [] = bottom` で `β <_o o_of []` が偽になるため、v0.1.25)。

## タスク (怪しさ高 → 低)

| ID | Lemma | タスク | 怪しさ要因 | 状態 | 見込み |
|---:|---|---|---|---|:---:|
|  3 | Cor 2.4 backward | `seed_descendants_total` 一般 N: `A ≤_B seed N ∧ A' ≤_B seed N ⟹ A ≤_B A' ∨ A' ≤_B A` (Hunter Lemma 2.3 closure 議論). N=0 ✅, N=1 ✅ (degenerate, chain enumerate) | Hunter の論証は (α)(β)(γ) を使うが (α) は strip と矛盾 (bug.md B-1)。strip-faithful な再構成が必要で、Hunter の loose な議論をそのまま写せない。N≥2 で genuine cross-branch | N≥2 残 | 数h–数日 |
| 14 | Theorem 2.7 / `stable_rep_extend_strict` | `β` の構成と `g i <_o β` の検証 | `β` の存在は Hunter handwave。`f` の最大値 (= `f(last col)`) を `β` に取れるか具体 indexing が論文未明示 | 13 待ち | 半日 |
| 13 | Theorem 2.7 / `stable_rep_extend_strict` | `g` が `stable_rep` を満たす証明 (Lemma 2.5 を本質的に使用) | Lemma 2.5 (i)-(v) の convention が Hunter の使い方と完全一致するか要検証。我々の `m_ancestor A m i j` の (j 早い側, i 後) と Hunter の (i 早い, j 後) で reverse が必要 | 12 待ち | 1日 |
| 12 | Theorem 2.7 / `stable_rep_extend_strict` | `g` の構成定義: G_block には `f` の対応値、B_i (i ≥ 1) には Lemma 2.6 の Y' 反射値 | indexing (B_n と B_{n+1} の対応) と Lemma 2.6 への X, Y の渡し方が Hunter で省略気味 | 5-8 待ち | 数h |
| 27 | Theorem 2.7 helper | `stable_rep_restrict`: stable_rep が m_ancestor 保存な subset に restrict できる | — | ✅ | — |
| 28 | Theorem 2.7 helper | `m_ancestor (A[0]) m i j \<Longrightarrow> m_ancestor A m i j` (i,j < arr_len A - 1): A[0] = strip(butlast A) を経由した m_ancestor 保存。strip の row 削減と butlast の col 削減双方を m に関する nested induction で処理 | strip 後の elem out-of-bound 挙動 (`undefined < undefined = False`) と m_ancestor 終結条件の相互作用が厄介。Hunter は "trivially" で済ましているが Isabelle では明示的処理が必要 | ✅ | — |
| 29 | Theorem 2.7 helper | `m_parent_m_ancestor_butlast`: butlast 経由の m_parent/m_ancestor 同時保存 (`m` × `i` の nested 帰納) | — | ✅ | — |
| 30 | Theorem 2.7 helper | `nth_same_length_oob`: 同長リスト同士は OOB index でも一致 (`list_induct2`) | — | ✅ | — |
| 31 | Theorem 2.7 helper | `stable_rep_extend_strict_zero`: n=0 base case (Hunter "$f_0 = f$ restricted to $l_0$") | — | ✅ | — |
| 32 | Theorem 2.7 helper | `m_ancestor_A0_subsume_A`: butlast preservation ⊕ strip preservation。 `m_parent_m_ancestor_strip` (full iff) を `elem_strip_lt_iff` 経由で証明し、 そこから subsume を導出。 `keep_of`, `keep_of_row_zero`, `length_col_strip`, `elem_strip_lt_keep` の helper を整備 | — | ✅ | — |
| 33 | Theorem 2.7 helper | `is_array_butlast`: butlast が is_array を保つ。 `?H = height A` (abbreviation) と `by blast` ベースで初期 simp loop を回避。 `in_set_butlastD` で set 包含、 `hd_append2 + append_butlast_last_id` で hd 一致 | — | ✅ | — |
| 34 | Theorem 2.7 helper | `keep_of`: `strip_zero_rows` の trailing-zero cutoff を `definition` として分離 (`LEAST h. h ≤ height A ∧ ...`)。 `keep_of_le_height`, `keep_of_row_zero` で `Least_le` / `LeastI` 経由の性質を抽出 | — | ✅ | — |
| 35 | Theorem 2.7 helper | `length_col_arr` (`is_array` 列の長さ = `height A`), `length_col_strip` (strip 列の長さ = `keep_of A`), `strip_zero_rows_eq_map_take` (A ≠ [] のとき strip = map take keep) | — | ✅ | — |
| 36 | Theorem 2.7 helper | `elem_strip_lt_keep` (m < keep で elem 一致), `elem_strip_lt_iff` (`<` の同値: m < keep は elem 一致 / keep ≤ m < height は 0 = 0 / m ≥ height は OOB 同値) | — | ✅ | — |
| 37 | Theorem 2.7 helper | `m_parent_m_ancestor_strip` (full iff、 m × i nested induction、 butlast 版と並行構造) | — | ✅ | — |
| 38 | Theorem 2.7 helper | `Bs_concat_Suc`: `Bs_concat A (Suc n) = Bs_concat A n @ Bi_block A (Suc n)` を名前付き lemma 化 (元は inline have が 3 箇所) | — | ✅ | — |
| 39 | Theorem 2.7 helper | `arr_len_expansion`: `A ≠ [] ⟹ arr_len (A[n]) = length (G_block A) + Suc n * length (B0_block A)` (`length_strip_zero_rows` + `length_Bs_concat`) | — | ✅ | — |
| 40 | Theorem 2.7 helper | `arr_len_expansion_Suc`: `arr_len (A[Suc n]) = arr_len (A[n]) + length (B0_block A)` (39 から導出) | — | ✅ | — |
| 41 | Theorem 2.7 / `stable_rep_extend_strict` | `cases n` → `induct n` に refactor して Suc n' で IH (g_n, β_n) を `Suc.hyps` から explicit obtain | — | ✅ | — |
| 42 | Theorem 2.7 / `stable_rep_extend_strict` Suc n' | b0_start A = None case を分離: `expansion_no_b0_eq_zero` で `A[Suc n'] = A[n']` を導出し、 IH をそのまま流用。 残 sorry は `b0_start A = Some s` 内部のみ | — | ✅ | — |
| 43 | Theorem 2.7 / `stable_rep_extend_strict` Suc n' Some s | Hunter 反射構築本体: Lemma 2.6 適用での X, Y 具体化 / sigma_bound 所属検証 / g_{Suc n'} 定義 / stable_rep 検証 (Lemma 2.5 経由) / β 選定 | sorry の所在が None case 除去で集約。 sigma_bound 所属の axiom 拡張が必要かもしれない | sorry | 数 session |
| 44 | Lemma 2.5 helper | `lemma_2_5_at_n_zero`: n=0 case (b0_start に依らず)。 (i)(ii) は両辺同一、 (iii)(v) は vacuous、 (iv) は m_parent 値を G_block / B_0 に分類 | — | ✅ | — |
| 45 | Lemma 2.5 main restructure | `lemma_2_5_at_main` を 3 case: n=0 / Suc n' & None / Suc n' & Some s に分解。 sorry は最後の 1 case のみ | — | ✅ | — |
| 46 | Theorem 2.7 helper | `b0_start_lt_last`: `b0_start A = Some s ⟹ s < last_col_idx A` (m_parent_lt 経由)、 `l1_pos_of_some`: `A ≠ [] ∧ b0_start A = Some s ⟹ 0 < l1 A` | — | ✅ | — |
| 47 | Cor 2.4 helper | `bms_lt_imp_le_expansion`: `A <_B B ⟹ ∃n. A ≤_B expansion B n` (bms_le.cases で bms_le_refl 枝を排除)。 strict descendant をひと expansion step に decompose する基礎 | — | ✅ | — |
| 48 | Cor 2.4 / `seed_descendants_total` 残 case | (N ≥ 2) sub-case を分離: N=0/1 case を `seed_{0,1}_descendants_total` で dispatch、 sorry を N ≥ 2 のみに更に narrow | — | ✅ | — |
| 49 | Lemma 2.5 helper | `arr_len_expansion_l01`: `A ≠ [] ⟹ arr_len (A[n]) = l0 A + Suc n * l1 A` (`arr_len_expansion` の l0/l1 projection)、 `pre_strip_nth_G`: `i < l0 ⟹ pre-strip A[n] ! i = G_block A ! i` | — | ✅ | — |
| 50 | Lemma 2.5 helper | `Bs_concat_nth_block`: `t ≤ n ∧ j < l1 ⟹ Bs_concat A n ! (t * l1 + j) = Bi_block A t ! j` (induction on n + `Bs_concat_Suc` + `length_Bs_concat`)、 `pre_strip_nth_B`: `t ≤ n ∧ j < l1 ⟹ pre-strip A[n] ! (idx_B_in_expansion A t j) = Bi_block A t ! j` | — | ✅ | — |
| 51 | Lemma 2.5 helper | `elem_expansion_G_lt_keep`: `i < l0 ∧ m < keep_of pre-strip ⟹ elem (A[n]) i m = elem (G_block A) i m`、 `elem_expansion_B_lt_keep`: `t ≤ n ∧ j < l1 ∧ m < keep ⟹ elem (A[n]) (idx_B_in_expansion A t j) m = elem (Bi_block A t) j m`。 `elem_strip_lt_keep` + `pre_strip_nth_G/B` の組合せ | — | ✅ | — |
| 52 | Lemma 2.5 helper | `bump_col_nth_general`: `b0_start A = Some s ∧ m < length (A!(s+d)) ⟹ (bump_col A d i) ! m = (A!(s+d))!m + (if ascends A d m then i * delta A m else 0)`。 既存 `bump_col_value_*` の汎化版 | — | ✅ | — |
| 53 | Lemma 2.5 helper | `elem_Bi_block_via_bump_col`: `j < l1 ⟹ elem (Bi_block A t) j m = (bump_col A j t) ! m`、 `elem_expansion_B_via_bump`: 上記 + `elem_expansion_B_lt_keep` の合成で `elem (A[n]) (idx_B t j) m = (bump_col A j t) ! m` | — | ✅ | — |
| 54 | Lemma 2.5 helper | `delta_pos_of_lt_m0`: `b0_start = Some s ∧ max_parent_level = Some m_0 ∧ m < m_0 ⟹ 0 < delta A m` (`m_ancestor_mono` + `m_ancestor_elem_lt`)、 `bump_col_lt_step`: `ascends ∧ 0 < delta ∧ i < i' ⟹ (bump_col A d i) ! k < (bump_col A d i') ! k` | — | ✅ | — |
| 55 | Lemma 2.5 clause (iv) helper | `clause_iv_G_case`: `p < l0 ⟹ ∃j<l0. p = idx_G A j` (trivial via `idx_G_def`)、 `clause_iv_B_n_case`: `l0 + n*l1 ≤ p < l0 + (n+1)*l1 ⟹ ∃j<l1. p = idx_B_in_expansion A n j` (algebraic) | — | ✅ | — |
| 56 | Lemma 2.5 elem comparison | `elem_expansion_B_lt_step_same_j`: same column index j, different block t < t' (≤ n) で ascending 行 k に対し `elem (A[n]) (idx_B t j) k < elem (A[n]) (idx_B t' j) k`。 `elem_expansion_B_via_bump` + `bump_col_lt_step` + `delta_pos_of_lt_m0` の合成 | — | ✅ | — |
| 57 | Lemma 2.5 elem comparison | `elem_expansion_B_lt_same_block`: same block t, different column indices j, i in B_t (両 ascending at k)。 base 不等式 `(A!(s+j))!k < (A!(s+i))!k` を `elem (A[n]) (idx_B t j) k < elem (A[n]) (idx_B t i) k` に propagate (両 bump = +t*delta) | — | ✅ | — |
| 58 | Lemma 2.5 helper | `bump_col_zero_eq_orig`: `b0_start = Some s ∧ k < length (A!(s+d)) ⟹ (bump_col A d 0) ! k = (A!(s+d)) ! k` (i=0 で bump 量 0)、 `elem_expansion_B0_via_orig`: `elem (A[n]) (idx_B 0 j) k = elem A (s+j) k` (B_0 列は元の A 列に直結) | — | ✅ | — |
| 19 | Lemma 2.6 / Phase 3 ZF | 2.6.C: `φ_2(η,k) := L_η ≺_{Σ_{k+1}} L` が Π_{k+1} (Kranakis 1982 Theorem 1.8) | 外部依存 (Kranakis 論文の前提と命題が Paulson の `Constructible` 内で言明可能か未確認) | 18 待ち | 数日 |
|  5 | Lemma 2.5 | 補助補題群整備 (m_parent / m_ancestor が strip / bumping / k-祖先と相互作用する性質) | Hunter は "tedious but straightforward" と書くが、補題リストを論文に書かない。手作業で発見・列挙する必要 | 未着手 | 不明 |
|  6 | Lemma 2.5 | `lemma_2_5_at_inductive_step`: IH at `k' < k` から 5 clause を順に独立化 | (iv) と (v) が同一 k で相互依存 (BMS_Ancestry.thy のコメント参照)。Hunter の順序 (ii)→(iii)→(iv)→(i)→(v) を我々は (iv,v 同時)→(i,ii,iii) に変更したが、それで証明が通るかは未確認 | 5 待ち | 数h+ |
|  7 | Lemma 2.5 | `lemma_2_5_at_main_some` 本体: `nat_less_induct` で 6 を組み立て | 6 が完成すれば直接的だが、誘導の cong 関係に subtle なミスマッチが出やすい | 6 待ち | 1h |
| 22 | Lemma 2.6 / Phase 3 ZF | 2.6.F: ψ ∧ φ の `L_β` から `L_α` への反射 | Paulson の reflection theorem を ψ∧φ の具体形に当てはめる必要。論文では暗黙 | 21 待ち | 1日 |
| 23 | Lemma 2.6 / Phase 3 ZF | 2.6.G: `L_α` 内の証拠から `Y'` と全単射 `f` を構成 | 反射した formula の witness 抽出を全単射として整理する箇所、bijection を Isabelle で具体化する手間あり | 22 待ち | 1日 |
| 20 | Lemma 2.6 / Phase 3 ZF | 2.6.D: 有限 Σ_{n+1} 連言の Σ_{n+1} 性 | Σ_n hierarchy の closure は Paulson 内で確立済みだが、Σ_{n+1} 形式の boilerplate が要る | 19 待ち | 1日 |
| 21 | Lemma 2.6 / Phase 3 ZF | 2.6.E: Σ_{n+1} 存在閉包 | 同上 (20 と同質) | 20 待ち | 1日 |
| 18 | Lemma 2.6 / Phase 3 ZF | 2.6.B: `φ_1(η,ξ,k) := η <_k ξ` が Σ_{n+1} | 17 上の組合せ。Hunter は構造的に書くが Isabelle/ZF での Σ_n 階層内符号化に手間 | 17 待ち | 1日 |
|  8 | Lemma 2.5 | 既存 `lemma_2_5_i` 〜 `lemma_2_5_v` projection が新証明と互換に動作することを確認 | 7 完成後の sanity check。怪しさ低 | 7 待ち | 30m |
| 17 | Lemma 2.6 / Phase 3 ZF | 2.6.A: `φ_0(η,ξ) := η ∈ ξ` が Σ_0 | 標準事実、Paulson 内に既存の可能性 | 16 待ち | 1日 |
| 16 | Lemma 2.6 / Phase 3 ZF | Paulson `Constructible` ライブラリ import | 怪しさ低 (作業量のみ) | 15 待ち | 1日 |
| 24 | Lemma 2.6 / Phase 3 ZF | HOL 側の `axiomatize lemma_2_6` を ZF 側からの transfer に置換 | 23 完成後の機械的 transfer | 23 待ち | 半日 |
|  1 | Cor 2.4 backward | `seed_expansion_succ_zero`: `(seed (Suc n)[Suc k])[0] = seed (Suc n)[k]` (Hunter p.4 "A[0] = butlast A" の strip-faithful 版; bug.md B-1) | — | ✅ | — |
|  2 | Cor 2.4 backward | `seed_chain_le_B_expansion`: `k ≤ k' ⟹ seed (Suc n)[k] ≤_B seed (Suc n)[k']` (1 から導出) | — | ✅ | — |
|  4 | Cor 2.4 backward | `seed_lex_implies_le_B` (3 + Cor 2.2 + arr_lex_irrefl/trans で導出); `lex_implies_le_B` (`bms_pair_below_seed` + 3 経由で導出済み) | — | ✅ | — |
|  9 | Theorem 2.7 / `o_on_seed` | `Ord_t` の axiom 拡張: `sigma_pair_exists` (Hunter σ-pair 存在) | — | ✅ | — |
| 10 | Theorem 2.7 / `o_on_seed` | seed n の 2 列に対し `f 0 = α, f 1 = β` で `stable_rep` を構築 | — | ✅ | — |
| 11 | Theorem 2.7 / `o_on_seed` | `m_ancestor (seed n) m 1 0` の `m ≥ n` ケース補強 | — | ✅ | — |
| 15 | Lemma 2.6 / Phase 3 ZF | `isabelle_zf/` ディレクトリ・`ROOT` 雛形 | — | ✅ | — |
| 25 | Soundness audit | `sigma_pair_exists` を Hunter の σ-pair 条件に強化 (v0.1.27) | — | ✅ | — |
| 26 | Soundness audit | `o_of_def` 公理を `A ∈ BMS` に制限 (v0.1.28) | — | ✅ | — |
