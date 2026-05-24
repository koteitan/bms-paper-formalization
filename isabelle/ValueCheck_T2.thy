theory ValueCheck_T2
  imports BMS_Ancestry
begin

text \<open>
  Confirm the empirical T2 counterexample against the formalization itself.
  A = (0,0)(1,1).  A[1] computed by yaBMS = (0,0)(1,0) = [[0,0],[1,0]].
  On the OUTER A: l0 A = 0, l1 A = 1, so idx_B_in_expansion A 0 0 = 0 and
  idx_B_in_expansion A 1 0 = 1.  Then on A[1] = [[0,0],[1,0]] the column
  idx_B(1,0)=1 has level-0 m-parent = column 0 = idx_B(0,0), i.e.
     m_ancestor (A[1]) 0 (idx_B(1,0)) (idx_B(0,0))   is TRUE,
  with t=0 < n=1 and j=0 < l1.  This is exactly what
  idx_B_n_zero_no_intermediate_B_t_ancestor (T2) asserts to be impossible,
  so T2 is FALSE as stated.
\<close>

definition Aex  :: array where "Aex  = [[0,0],[1,1]]"
definition A1ex :: array where "A1ex = [[0,0],[1,0]]"

text \<open>Outer-array index data (small, direct unfolding).\<close>
lemma vc_l0:  "l0 Aex = 0"
  by (simp add: Aex_def l0_def G_block_def b0_start_def max_parent_level_def
                m_parent.simps elem_def)
lemma vc_idx00: "idx_B_in_expansion Aex 0 0 = 0"
  using vc_l0 by (simp add: idx_B_in_expansion_def)
lemma vc_idx10: "idx_B_in_expansion Aex 1 0 = l1 Aex"
  using vc_l0 by (simp add: idx_B_in_expansion_def)

text \<open>l1 Aex = 1: B0 has one column. b0_start Aex = Some 0, last_col_idx = 1.\<close>
lemma vc_l1: "l1 Aex = 1"
proof -
  have "b0_start Aex = Some 0"
    by (simp add: Aex_def b0_start_def max_parent_level_def m_parent.simps elem_def)
  thus ?thesis by (simp add: l1_def B0_block_def Aex_def)
qed

text \<open>The two load-bearing facts, evaluated on the concrete expansion A1ex.\<close>
lemma vc_par: "m_parent A1ex 0 1 = Some 0"
  by (simp add: A1ex_def m_parent.simps elem_def)

lemma vc_T2_counterexample_concrete:
  "m_ancestor A1ex 0 1 0"
  by (simp add: A1ex_def m_ancestor.simps m_parent.simps elem_def)

text \<open>Tie the concrete fact to the lemma's exact index expressions.\<close>
lemma vc_T2_counterexample:
  "m_ancestor A1ex 0 (idx_B_in_expansion Aex 1 0) (idx_B_in_expansion Aex 0 0)"
  using vc_T2_counterexample_concrete vc_idx00 vc_idx10 vc_l1 by simp

end
