# タスクリスト

> **進捗 (✅ 完了 / 🚨 未完) 以外の情報をこのファイルに書くな。**
> 解説・理由・反例・証明方針・helper 詳細・履歴・削除ログ・比較表・commit ハッシュ・検証件数・[[link]] などは
> task.md に書かず、 commit / コード / memory に残す。 各行は「アイコン + 補題/タスク名」のみ。

## Lemma 2.3 / Cor 2.4: BMS 全順序

- 🚨 seed_descendants_total_strong N≥2 case [ID 3]
  - ✅ seed_0_descendants_total
  - ✅ seed_1_descendants_total
  - ✅ seed_expansion_succ_zero [ID 1]
  - ✅ seed_chain_le_B_expansion [ID 2]
  - ✅ seed_lex_implies_le_B / lex_implies_le_B [ID 4]
  - ✅ bms_lt_imp_le_expansion [ID 47]
  - ✅ bms_descendants_lex_total [ID 60]
  - 🚨 k'≥2 chain-depth sub-case (BMS_Lex:1369 sorry)

## Lemma 2.5: 5 clauses ancestry

- 🚨 lemma_2_5_at_main (layered 5-stage assembly)
  - ✅ lemma_2_5_at_n_zero
  - ✅ lemma_2_5_at_no_b0
  - ✅ lemma_2_5_v_clause_n_le_one
  - ✅ lemma_2_5_iii_clause_when_k_ge_m0
  - 🚨 5 main lemmas の AND 構築

- ✅ Stage 1: ∀k.(ii)@k — lemma_2_5_ii_main_v2 (clause ii 忠実化完了, elem_lt 非依存)
  - ✅ lemma_2_5_ii_clause_step (6-way dispatch; case-B を not_asc engine で直接処理)
  - ✅ 忠実化: case-B(Suc k', ¬ascends)を elem_lt vacuity でなく not_asc engine で直接処理 (Hunter [2.5.proof-ii] 第2ケース; elem_lt 依存除去)
    - ✅ m_parent_AEn_idx_B_within_block_at_block0_Suc_k (block-0 within-block parent @Suc k', 無条件)
    - ✅ last_S_not_asc_when_j_not_asc (Suc k' 伝播補題; nasc_j のみ→within-block parent ¬ascend)
    - ✅ last_filter_eq_of_implies_subset (bump-monotone containment list 核)
    - ✅ m_parent_AEn_idx_B_{within,outside}_block_at_Suc_k_when_j_not_asc (nasc_j のみ parent characterization, bump除外)
    - ✅ m_anc_idx_B_in_block_shift_at_Suc_k_when_j_not_asc (not_asc engine, nasc_j のみ; Hunter case-B 本体)
    - ✅ dispatcher case-B 配線 → elem_lt 依存消滅
  - ✅ elem_lt_below_t m=0 / m>0 on-chain (clause ii では不要に; off-chain sorry は旧 DOM 迂回路のみ残存)
    - ✅ DOM / ANC / DOM_of_ANC / l1_seed_le_1
    - ✅ DOM_all_if_transfer (off-chain → 単一 TRANSFER obligation に簡約)
    - ✅ b0_col_ancestor_below_t_from_DOM
    - ✅ ANC_of_DOM / DOM_iff_ANC
    - ✅ DOM_all_if_DOM_transfer
    - ✅ dom_transfer_R1
    - ✅ dom_transfer_R2 / dom_transfer_R2_via_BMS
    - 🚨 DOM_transfer: DOM A ⟹ DOM (A[n])
      - ✅ R1 (block-start): dom_transfer_R1
      - 🚨 R2 (in-G', l1 A=1): closable, off-chain vacuous
        - ✅ P1: b0_start(A[n]) = m_parent A t' (b0_start A) (P1_keystone_R2 で組立完成)
          - ✅ last_col_idx_expansion
          - ✅ b0_start_expansion_as_mparent (P1 LHS を idx_B 形に)
          - ✅ elem_AEn_last_block_start (idx_B A n 0 の値)
          - ✅ P1_from_struct (asc_false + P1b ⟹ P1, filter 一致で組立)
          - ✅ height_pre_strip_eq / height_expansion_eq_keep (t'=mpl(A[n]) の keep/height 境界)
          - ✅ cross-block の残 hypothesis 2本:
            - ✅ asc_false ⟸ mpl(A[n]) ≥ mpl A (mpl_bound_from_R2: R2+consecutive-parent で直接, s-t-parent 不要)
              - ✅ mpl_ge_of_parent_exists / mpl_ge_of_badroot_tparent (補助)
            - ✅ P1a_bumped_region_value (bumped 列の値=elem A s t', 候補除外)
            - ✅ P1b_from_clause_i (P1b ⟸ clause(i) j=0 + m_anc_orig_eq)
            - ✅ clause_i_j0 (clause(i) j=0 slice 完成, P1b 用)
        - ✅ R2_endpoint_ancestor (P1 → s' は s_A の m-祖先, m<t')
        - ✅ ganc_from_interval_dom (GANC ⟸ dom_intv, offset 帰納で sorry-free 帰着)
        - ✅ r2b_R2 (R2B 完全証明: endpoint + bump 非負, elem_AEn_idx_B_value)
        - ✅ dom_transfer_R2_from_struct (GANC+R2B → R2 dom, 組立)
        - ✅ dom_transfer_R2_modulo_intervaldom (R2 全体を dom_intv 単一仮説に帰着, capstone)
        - 🚨 interval-density (dom_intv = CLAIM D): s' が (s',s_A] を全レベル m<t' で支配
            (deep-ancestor 区間支配; off-chain は elem_lt と同難度の foundational core; R2 残はこれ1本)
      - 🚨 DOM_holds 配線 (elem_lt_below_t@7084 sorry を閉じる, placement 再編)
  - ✅ b0_col_ancestor_below_t
  - ✅ m_anc_Suc_imp_strict_min_on_anc
  - ✅ m_anc_zero_imp_strict_min / m_anc_zero_strict_min
  - ✅ ascends_row0_prefix
  - ✅ bms_ascend_propagates_to_chain_ancestor
  - ✅ m_anc_zero_idx_B_in_block_shift_when_{t_zero,t_pos_all_asc,t_pos_prefix_asc,j_not_asc}
  - ✅ m_anc_idx_B_in_block_shift_at_Suc_k_when_{k_ge_t,k_lt_t_asc,k_lt_t_not_asc}

- 🚨 Stage 2: ∀k.(iv)@k — lemma_2_5_iv_main
  - ✅ lemma_2_5_iv_clause_step
  - ✅ clause_iv_intermediate_B_t_impossible_when_G_parent_exists
  - ✅ idx_B_earlier_block_lt_block_n
  - ✅ clause_iv_intermediate_B_t_impossible_at_zero
  - ✅ clause_iv_intermediate_B_t_impossible_chain_through_Bn_first
  - ✅ clause_iv_intermediate_B_t_impossible_chain_breaks
  - ✅ idx_B_n_zero_gateway_for_earlier_block_ancestor
  - ✅ idx_B_n_zero_gateway_aux
  - 🚨 m_parent_block_n_stays_until_zero
    - ✅ gateway_from_candidate_Suc (gateway ⟸ G1 bumped-DOM + G2 bumped-ANC)
    - ✅ row-0 枝 (m=0 ∧ t>0 ∧ n>0)
    - 🚨 残差 (Suc m' / t=0 / n=0) = elem_lt_below_t crux
    - 🚨 G1/G2 = simultaneous induction invariant (block-n DOM/ANC)
  - ✅ clause_iv_intermediate_B_t_impossible_at_zero_outside_lands_in_G

- 🚨 Stage 3: ∀k.(iii)@k — lemma_2_5_iii_main
  - ✅ lemma_2_5_iii_clause_step
  - ✅ iii_block_shift_bridge_n_ge_2
  - 🚨 iii_single_step_t_to_Suc_t

- 🚨 Stage 4: ∀k.(i)@k — lemma_2_5_i_main
  - ✅ lemma_2_5_i_clause_step
  - ✅ lemma_2_5_i_clause_step_forward / _backward
  - 🚨 ascending case (forward+backward 同時): onestep_anc に帰着
    - ✅ clause_i_ascends_iff_from_blockcopy (asc 両方向 ⟸ block_copy_anc)
    - ✅ block_copy_anc_from_onestep (block_copy_anc ⟸ onestep_anc, c 帰納 + m_ancestor_trans)
    - 🚨 onestep_anc (bumped: idx_B A (c-1) j が idx_B A c j の k-祖先; chain maximality=clause(iv)要, SI内)
  - 🚨 lemma_2_5_i_clause_step_forward_case_not_ascends
  - 🚨 lemma_2_5_i_clause_step_backward_case_not_ascends
  - 🚨 clause_i_iff_when_not_ascends (T=[] above-t vacuity に帰着, leftmost_gateway_iff_when_T_empty 呼ぶだけ)
  - ✅ clause (i) @ j=0 slice (P1b に十分, level 帰納):
    - ✅ m_anc_eq_of_m_parent_eq (m_parent 一致 ⟹ m_anc 一致)
    - ✅ clause_i_j0_step_not_asc (not-asc level: P1_from_struct で m_parent 一致)
    - ✅ m_anc_below_ancestor_transfer (X が Z の祖先 ∧ i<X ⟹ m_anc Z i⟺m_anc X i)
    - ✅ clause_i_j0 asc level: fact2 + transfer 補題
      - ✅ consecutive_block_start_parent (l1=1,asc, level 帰納)
      - ✅ block_start_anc_zero (fact2, c 帰納)
      - ✅ clause_i_j0_step_asc
    - ✅ clause_i_j0 (level 帰納 assembly, asc/not-asc dispatch) ← P1b の源, R2 crux 完成

- 🚨 Stage 5: ∀k.(v)@k — lemma_2_5_v_main
  - ✅ lemma_2_5_v_clause_step
  - ✅ lemma_2_5_v_clause_step_substantive / _forward / _backward
  - 🚨 lemma_2_5_v_clause_step_iff
    - ✅ clause_v_asc_iff_from_onestep (asc case ⟸ onestep_anc, clause(i) asc と共通 crux)
    - 🚨 onestep_anc (clause(i) asc と共有) + not-asc case (値一致, 別 argument)

- 🚨 row0-linchpin route → STRUCT mpl-definedness linchpin (単一 crux c4' に帰着)
  - ✅ row0_invariant
  - ✅ mpl_none_imp_last_col_row0_zero
  - ✅ mpl_some_imp_last_col_row0_pos
  - ✅ m_parent_level_down_ne
  - ✅ expansion_no_b0_eq_strip_butlast
  - ✅ height_expansion_le
  - ✅ height_ge2_imp_b0_some_cond (c4' modulo)
  - ✅ mpl_le_zero_expansion_of_height_le1
  - ✅ mpl_none_imp_mpl_le_zero_expansion_cond (STRUCT linchpin, c4' modulo)
  - ✅ ascends_antitone_level
  - ✅ drop_dom_ancestor_from_onestep (V ⟸ V1)
  - 🚨 c4' (STRUCT crux: tall expansion keeps bad root) — 2 height 事実に還元済
    - ✅ col_row0_zero_imp_col_zero (c1: row0=0 列は全ゼロ)
    - ✅ b0_start_expansion_some_when_n_pos (c4' 主ケース t>0 ∧ n>0)
    - ✅ b0_start_expansion_some_when_l1_ge2 (t>0 ∧ l1≥2, 全 n)
    - ✅ b0_start_expansion_zero_some_of_penult_parent (n=0, penult が 0-parent)
    - ✅ b0_start_expansion_some_modulo_height (assembly: c4' ⟸ Hres)
    - ✅ height_zero_of_row0_all_zero (row0 全ゼロ ⟹ height 0)
    - ✅ b0_start_expansion_some_modulo_lastmax (c4' ⟸ 単一 residual (A))
    - 🚨 (A): last col が row-0 max ⟸ B0-row0-consecutive = value crux (隣接単調)
  - 🚨 V1 (value crux = ancestor_monotone = drop-domination; clause-i 必須)

- ✅ Lemma 2.5 helpers
  - ✅ m_anc_build_Suc (PSS le1_build 移植: stratified 支配→高レベル祖先 build, endpoint 帰納; SI ancestry step 用)
  - ✅ m_ancestor_tree_Suc (PSS ancestor_tree_2 移植: 高レベル stratified 区間密度; 生区間でなく m'-祖先鎖上)
  - ✅ elem_AEn_idx_B_value
  - ✅ elem_AEn_idx_B_block_shift_diff
  - ✅ chain/value helpers [ID 73]
  - ✅ pre-strip / Bs_concat / bump helpers [ID 46,49-58,65]
  - ✅ m_0=0 helpers [ID 59]
  - ✅ m_anc_via_parent_some / m_anc_via_parent_none

## Lemma 2.6: stability reflection (ZF discharge)

- 🚨 axiomatize lemma_2_6 を ZF transfer に置換 [ID 24]
  - ✅ Paulson ZF-Constructible import [ID 16]
  - ✅ isabelle_zf/ + ROOT [ID 15]
  - ✅ 2.6.A phi_0_is_Sigma_0 [ID 17]
  - ✅ 2.6.B φ_1 が Σ_{n+1} [ID 18]
  - ✅ 2.6.C φ_2 が Π_{k+1} [ID 19]
  - ✅ 2.6.D 連言閉包 [ID 20]
  - ✅ 2.6.E 存在閉包 [ID 21]
  - ✅ stab_fm_is_Sigma_succ_k
  - 🚨 2.6.F 反射 [ID 22]
  - 🚨 2.6.G witness 抽出 [ID 23]

## Theorem 2.7: BMS は整礎

- 🚨 stable_rep_extend_strict (Suc n' Some s case)
  - ✅ β 構成 [ID 14]
  - ✅ lemma_2_6_reflect_package
  - ✅ refl_exists_from_sigma_align
  - 🚨 refl_exists [ID 43]
  - 🚨 g_stable_rep [ID 12,13]
  - ✅ g_lt_β
  - ✅ stable_rep_extend_strict_zero [ID 31]
  - ✅ induct n refactor [ID 41]
  - ✅ b0_start=None case 分離 [ID 42]
  - ✅ stable_rep_imp_strict_mono / stable_rep_imp_ancestor_stable [ID 61]
  - ✅ stable_rep_restrict [ID 27]
  - ✅ m_ancestor_A0_imp_A [ID 28]
  - ✅ m_parent_m_ancestor_butlast [ID 29]
  - ✅ nth_same_length_oob [ID 30]
  - ✅ m_ancestor_A0_subsume_A [ID 32]
  - ✅ is_array_butlast [ID 33]
  - ✅ keep_of_le_height / keep_of_row_zero [ID 34]
  - ✅ length_col_arr / length_col_strip / strip_zero_rows_eq_map_take [ID 35]
  - ✅ elem_strip_lt_keep / elem_strip_lt_iff [ID 36]
  - ✅ m_parent_m_ancestor_strip [ID 37]
  - ✅ Bs_concat_Suc [ID 38]
  - ✅ arr_len_expansion / arr_len_expansion_Suc [ID 39,40]
  - ✅ o_on_seed [ID 9,10,11]

## Soundness audit

- ✅ sigma_pair_exists を Hunter σ-pair 条件に強化 [ID 25]
- ✅ o_of_def 公理を A ∈ BMS に制限 [ID 26]
