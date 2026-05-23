(*
  BMS_Hunter.thy

  Faithful formalization of the statements and proofs that appear
  EXPLICITLY in Rachel Hunter, "Well-Orderedness of the Bashicu Matrix
  System" (arXiv:2307.04606v3).

  This file is the "Hunter layer": it holds the paper-level lemmas
  (here, Lemma 2.5 (i)-(v) and the simultaneous k-induction that proves
  them) stated as close to the paper as the formalization allows.
  Auxiliary lemmas that do NOT appear in the paper live in the other
  theories (BMS_Defs, BMS_Lex, BMS_Ancestry, ...).  Keeping the paper's
  statements isolated here is a guard against drifting away from
  Hunter's actual proof structure.

  Lemma 2.1 (lexicographic decrease) is in BMS_Lex.
*)

theory BMS_Hunter
  imports BMS_Ancestry
begin

section \<open>Lemma 2.5: the simultaneous k-induction (Hunter, page 4-6)\<close>

text \<open>
  Hunter proves the five clauses (i)--(v) of Lemma 2.5 simultaneously by
  induction on \<open>k\<close>.  The per-clause step lemmas
  (\<open>lemma_2_5_*_clause_step\<close>) and the clause predicates
  (\<open>lemma_2_5_*_clause\<close>, \<open>lemma_2_5_at\<close>) are in BMS_Ancestry; here we
  assemble them into the paper-level statement.
\<close>

lemma lemma_2_5_at_main:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
  shows "lemma_2_5_at A n k"
proof -
  \<comment> \<open>Outer induction on \<open>k\<close>; for each \<open>k\<close>, nested induction on
      \<open>n\<close> to provide @{thm lemma_2_5_iii_clause_step} access to
      \<open>lemma_2_5_at A (n-1) k\<close> (same level, smaller expansion).\<close>
  have "\<forall>n. lemma_2_5_at A n k"
  proof (induct k rule: nat_less_induct)
    case (1 k)
    have IH_k: "\<forall>k'<k. \<forall>n. lemma_2_5_at A n k'" using "1.hyps" by blast
    show ?case
    proof (intro allI)
      fix n
      show "lemma_2_5_at A n k"
      proof (induct n)
        case 0
        show ?case using lemma_2_5_at_n_zero[OF A_ne] by simp
      next
        case (Suc n')
        have IH_at_n: "\<forall>k'<k. lemma_2_5_at A (Suc n') k'" using IH_k by blast
        have IH_n_at_k: "lemma_2_5_at A (Suc n' - 1) k" using Suc.hyps by simp
        have ii: "lemma_2_5_ii_clause A (Suc n') k"
          by (rule lemma_2_5_ii_main_v2[OF A_BMS A_ne])
        have iii: "lemma_2_5_iii_clause A (Suc n') k"
          by (rule lemma_2_5_iii_clause_step[OF A_BMS A_ne IH_at_n IH_n_at_k ii])
        have iv: "lemma_2_5_iv_clause A (Suc n') k"
          by (rule lemma_2_5_iv_clause_step[OF A_BMS A_ne IH_at_n ii iii])
        have i: "lemma_2_5_i_clause A (Suc n') k"
          by (rule lemma_2_5_i_clause_step[OF A_BMS A_ne IH_at_n ii iii iv])
        have v: "lemma_2_5_v_clause A (Suc n') k"
          by (rule lemma_2_5_v_clause_step[OF A_BMS A_ne IH_at_n i ii iii iv])
        show ?case unfolding lemma_2_5_at_def using i ii iii iv v by blast
      qed
    qed
  qed
  thus ?thesis by simp
qed


section \<open>Lemma 2.5 (i)--(v) as projections\<close>

lemma lemma_2_5_i:
  assumes "A \<in> BMS" "A \<noteq> []" "i < l0 A" "j < l1 A"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_G A i)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_G A i)"
  using lemma_2_5_at_main[OF assms(1,2), of n k] assms(3,4)
  unfolding lemma_2_5_at_def lemma_2_5_i_clause_def by blast

lemma lemma_2_5_ii:
  assumes "A \<in> BMS" "A \<noteq> []" "i < l1 A" "j < l1 A"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_B_in_expansion A n i)"
  using lemma_2_5_at_main[OF assms(1,2), of n k] assms(3,4)
  unfolding lemma_2_5_at_def lemma_2_5_ii_clause_def by blast

lemma lemma_2_5_iii:
  assumes "A \<in> BMS" "A \<noteq> []" "n > 0"
      and "max_parent_level A = Some m\<^sub>0" "k < m\<^sub>0" "i < l1 A"
  shows "m_ancestor A k (last_col_idx A) (idx_B0_in_orig A i)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n 0)
                                  (idx_B_in_expansion A (n - 1) i)"
  using lemma_2_5_at_main[OF assms(1,2), of n k] assms(3-)
  unfolding lemma_2_5_at_def lemma_2_5_iii_clause_def by blast

lemma lemma_2_5_iv:
  assumes "A \<in> BMS" "A \<noteq> []" "0 < i" "i < l1 A"
  shows "m_parent (A[n]) k (idx_B_in_expansion A n i) = None
       \<or> (\<exists>p. m_parent (A[n]) k (idx_B_in_expansion A n i) = Some p
              \<and> ((\<exists>j < l1 A. p = idx_B_in_expansion A n j)
                 \<or> (\<exists>j < l0 A. p = idx_G A j)))"
  using lemma_2_5_at_main[OF assms(1,2), of n k] assms(3,4)
  unfolding lemma_2_5_at_def lemma_2_5_iv_clause_def by blast

lemma lemma_2_5_v:
  assumes "A \<in> BMS" "A \<noteq> []" "i < l1 A" "j < l1 A"
      and "n\<^sub>0 < n\<^sub>1" "n\<^sub>1 < n"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A n\<^sub>1 j)
                              (idx_B_in_expansion A n\<^sub>0 i)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (n\<^sub>1 + 1) j)
                                  (idx_B_in_expansion A n\<^sub>0 i)"
  using lemma_2_5_at_main[OF assms(1,2), of n k] assms(3-)
  unfolding lemma_2_5_at_def lemma_2_5_v_clause_def by blast

text \<open>
  Joint (iv) \<and> (v) lemma kept for compatibility with downstream
  callers that referred to \<open>lemma_2_5_iv_and_v\<close>.
\<close>

lemma lemma_2_5_iv_and_v:
  assumes "A \<in> BMS" "A \<noteq> []"
  shows
    "(\<forall>i. 0 < i \<and> i < l1 A \<longrightarrow>
       (m_parent (A[n]) k (idx_B_in_expansion A n i) = None
        \<or> (\<exists>p. m_parent (A[n]) k (idx_B_in_expansion A n i) = Some p
               \<and> ((\<exists>j < l1 A. p = idx_B_in_expansion A n j)
                  \<or> (\<exists>j < l0 A. p = idx_G A j)))))
   \<and> (\<forall>i j n\<^sub>0 n\<^sub>1.
        i < l1 A \<and> j < l1 A \<and> n\<^sub>0 < n\<^sub>1 \<and> n\<^sub>1 < n \<longrightarrow>
        (m_ancestor (A[n]) k (idx_B_in_expansion A n\<^sub>1 j)
                              (idx_B_in_expansion A n\<^sub>0 i)
         \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (n\<^sub>1 + 1) j)
                                    (idx_B_in_expansion A n\<^sub>0 i)))"
  using lemma_2_5_at_main[OF assms, of n k]
  unfolding lemma_2_5_at_def lemma_2_5_iv_clause_def lemma_2_5_v_clause_def
  by blast


section \<open>Prose claims from Hunter's Lemma 2.5 proof (page 5), formalized\<close>

text \<open>
  These are statements Hunter makes in WORDS inside the proof of
  Lemma 2.5; we record them as formal lemmas so the Hunter layer also
  pins down the reasoning, not just the displayed clauses.
\<close>

text \<open>
  ``The \<open>k\<close>-th element of the \<open>j\<close>-th column in \<open>B\<^sub>0\<close> ascends iff the
  first column in \<open>B\<^sub>0\<close> is a \<open>k\<close>-ancestor of the \<open>j\<close>-th column''
  (Hunter, p.5).  This is exactly the meaning of @{const ascends} once
  the level bound \<open>m < m\<^sub>0\<close> is in force.
\<close>

lemma hunter_ascends_iff_first_b0_ancestor:
  assumes b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and m_lt: "m < m\<^sub>0"
  shows "ascends A j m \<longleftrightarrow> non_strict_ancestor A m (idx_B_in_expansion A 0 j) s"
proof -
  have l0_eq: "idx_B_in_expansion A 0 j = s + j"
  proof -
    have "l0 A = s"
    proof -
      have A_ne: "A \<noteq> []" using b0 unfolding b0_start_def max_parent_level_def
        by (auto split: if_splits)
      have "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
      hence "s \<le> arr_len A" using A_ne by (cases A) auto
      thus ?thesis using b0 unfolding l0_def G_block_def by simp
    qed
    thus ?thesis unfolding idx_B_in_expansion_def by simp
  qed
  show ?thesis
    using b0 mp m_lt l0_eq unfolding ascends_def by simp
qed

text \<open>
  Special case \<open>j = 0\<close>: ``the first column in \<open>B\<^sub>0\<close> is its own
  non-strict \<open>k\<close>-ancestor'', hence its \<open>k\<close>-th element ascends for
  EVERY level \<open>k < m\<^sub>0\<close> (Hunter, p.5).
\<close>

lemma hunter_first_b0_col_ascends:
  assumes b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
  shows "ascends A 0 m \<longleftrightarrow> m < m\<^sub>0"
  using b0 mp unfolding ascends_def non_strict_ancestor_def by simp

text \<open>
  ``For all \<open>k' < k\<close>, \<open>k'\<close>-ancestry is a total order on the columns
  [that are common \<open>k'\<close>-ancestors]'' (Hunter, p.5): any two \<open>m\<close>-ancestors
  of a common column are comparable.  (Re-export of the proven totality
  fact; this is the property Hunter relies on throughout the (ii)/(iv)
  arguments.)
\<close>

lemma hunter_m_ancestry_total_on_ancestors:
  assumes "m_ancestor A m i j" and "m_ancestor A m i k"
  shows "j = k \<or> m_ancestor A m j k \<or> m_ancestor A m k j"
  using m_ancestor_chain_linear assms by blast

end
