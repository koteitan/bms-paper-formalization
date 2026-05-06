(*
  BMS_Ancestry.thy

  Formalization of Lemma 2.5 of
    Rachel Hunter, "Well-Orderedness of the Bashicu Matrix System"
    (arXiv:2307.04606v3, 2024).

  Lemma 2.5 has five clauses (i)--(v), proved by simultaneous induction
  on `k`.

  Conventions used here (cf. github issue #1):
    Definition 1.1 establishes
        m_ancestor A m i j ==> j < i,
    i.e. our `m_ancestor A m later earlier` reads "earlier is the
    m-ancestor of later" (mirroring the paper's "X is m-ancestor of Y"
    with X earlier, Y later). Therefore every clause that the paper
    phrases as "X is k-ancestor of Y" is rendered as
        m_ancestor _ _ <position of Y> <position of X>.

  Structural deviation from the paper (cf. github issue #2):
    The paper's induction discharges (ii), (iii), (iv), (i), (v) at
    level k in that order, but its proof of (iv) at level k uses
    (v) at level k, and its proof of (v) at level k uses (iv) at
    level k. We therefore combine (iv) and (v) into one joint lemma
    `lemma_2_5_iv_and_v` proved at level k, then project (iv) and (v)
    out as separate top-level lemmas.

  Notation: in the lemmas below, `A` is a non-empty array, `n` a
  natural number, and from Definition 1.1 we have arrays
  G, B_0, B_1, ..., B_n, m_0 with
  A = G + B_0 + (C) and A[n] = G + B_0 + B_1 + ... + B_n
  (zero rows stripped). l_0 = arr_len G, l_1 = arr_len B_0.
*)

theory BMS_Ancestry
  imports BMS_Lex
begin

section \<open>Auxiliary: positions in A[n]\<close>

text \<open>
  We need to refer to the i-th column of G, of B_t (for 0 \<le> t \<le> n)
  inside both A and A[n]. The columns of G occupy the prefix
  [0..<l_0); B_t occupies [l_0 + t * l_1..<l_0 + (t+1) * l_1);
  the last column of A is at index l_0 + l_1 in A.
\<close>

definition idx_G :: "array \<Rightarrow> nat \<Rightarrow> nat" where
  "idx_G A i = i"

definition l0 :: "array \<Rightarrow> nat" where
  "l0 A = arr_len (G_block A)"

definition l1 :: "array \<Rightarrow> nat" where
  "l1 A = arr_len (B0_block A)"

definition idx_B_in_expansion :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "idx_B_in_expansion A t j = l0 A + t * l1 A + j"

definition idx_B0_in_orig :: "array \<Rightarrow> nat \<Rightarrow> nat" where
  "idx_B0_in_orig A j = l0 A + j"

text \<open>
  When \<open>b0_start A = None\<close>, the block \<open>B\<^sub>0\<close> is empty, so
  \<open>l1 A = 0\<close>. Equivalently, \<open>max_parent_level A = None\<close> implies
  \<open>b0_start A = None\<close>; the converse also holds because whenever
  \<open>max_parent_level A = Some m\<^sub>0\<close>, the maximality witness ensures
  \<open>m_parent A m\<^sub>0 (last_col_idx A) \<noteq> None\<close>.
\<close>

lemma l1_zero_of_no_b0:
  assumes "b0_start A = None"
  shows "l1 A = 0"
  using assms by (simp add: l1_def B0_block_def)

lemma max_parent_level_None_imp_b0_start_None:
  "max_parent_level A = None \<Longrightarrow> b0_start A = None"
  by (simp add: b0_start_def)

lemma b0_start_None_imp_max_parent_level_None:
  assumes "A \<noteq> []" "b0_start A = None"
  shows "max_parent_level A = None"
proof (rule ccontr)
  assume neq: "max_parent_level A \<noteq> None"
  then obtain m\<^sub>0 where mp_eq: "max_parent_level A = Some m\<^sub>0" by auto
  define C where "C = last_col_idx A"
  define H where "H = height A"
  define ms where "ms = [m \<leftarrow> [0..<H]. m_parent A m C \<noteq> None]"
  have eq: "max_parent_level A
          = (if ms = [] then None else Some (Max (set ms)))"
    using assms(1) unfolding max_parent_level_def C_def H_def ms_def
    by (simp add: Let_def)
  have ms_ne: "ms \<noteq> []"
  proof (rule ccontr)
    assume "\<not> ms \<noteq> []"
    hence "ms = []" by simp
    hence "max_parent_level A = None" using eq by simp
    with mp_eq show False by simp
  qed
  have m0_eq: "m\<^sub>0 = Max (set ms)"
    using eq mp_eq ms_ne by simp
  have fin: "finite (set ms)" by simp
  have set_ne: "set ms \<noteq> {}" using ms_ne by simp
  have "Max (set ms) \<in> set ms" using Max_in[OF fin set_ne] .
  hence "m\<^sub>0 \<in> set ms" using m0_eq by simp
  hence "m_parent A m\<^sub>0 C \<noteq> None"
    unfolding ms_def by auto
  with mp_eq have "b0_start A \<noteq> None"
    unfolding b0_start_def C_def by simp
  with assms(2) show False by simp
qed


section \<open>Lemma 2.5: simultaneous statement at level k\<close>

text \<open>
  Hunter's proof of Lemma 2.5 is a single induction on k that proves
  all five clauses jointly. We package the five clauses into one
  predicate \<open>lemma_2_5_at A n k\<close> and discharge it with
  \<open>nat\<close>-induction; the four named lemmas at the end of the file
  are then immediate projections.

  Within the inductive case the paper proves (ii), (iii), (iv), (i),
  (v) in that order, with (iv) using (ii)/(iii) at level k, (i) using
  (i) at level k' < k and (iv) at level k, and (v) using (iii) at
  level k and (iv) at level k together with the IH. Filling in the
  five sub-cases here is left as a single \<open>sorry\<close>; this collapses
  the four sorries that previously sat on each of the four named
  lemmas into a single sorry on the joint statement.
\<close>

definition lemma_2_5_i_clause :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lemma_2_5_i_clause A n k \<longleftrightarrow>
     (\<forall>i j. i < l0 A \<and> j < l1 A \<longrightarrow>
        (m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_G A i)
         \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_G A i)))"

definition lemma_2_5_ii_clause :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lemma_2_5_ii_clause A n k \<longleftrightarrow>
     (\<forall>i j. i < l1 A \<and> j < l1 A \<longrightarrow>
        (m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_B_in_expansion A 0 i)
         \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_B_in_expansion A n i)))"

definition lemma_2_5_iii_clause :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lemma_2_5_iii_clause A n k \<longleftrightarrow>
     (\<forall>m\<^sub>0 i. n > 0 \<and> max_parent_level A = Some m\<^sub>0 \<and> k < m\<^sub>0 \<and> i < l1 A \<longrightarrow>
        (m_ancestor A k (last_col_idx A) (idx_B0_in_orig A i)
         \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n 0)
                                 (idx_B_in_expansion A (n - 1) i)))"

definition lemma_2_5_iv_clause :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lemma_2_5_iv_clause A n k \<longleftrightarrow>
     (\<forall>i. 0 < i \<and> i < l1 A \<longrightarrow>
        (m_parent (A[n]) k (idx_B_in_expansion A n i) = None
         \<or> (\<exists>p. m_parent (A[n]) k (idx_B_in_expansion A n i) = Some p
                \<and> ((\<exists>j < l1 A. p = idx_B_in_expansion A n j)
                   \<or> (\<exists>j < l0 A. p = idx_G A j)))))"

definition lemma_2_5_v_clause :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lemma_2_5_v_clause A n k \<longleftrightarrow>
     (\<forall>i j n\<^sub>0 n\<^sub>1.
        i < l1 A \<and> j < l1 A \<and> n\<^sub>0 < n\<^sub>1 \<and> n\<^sub>1 < n \<longrightarrow>
        (m_ancestor (A[n]) k (idx_B_in_expansion A n\<^sub>1 j)
                              (idx_B_in_expansion A n\<^sub>0 i)
         \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (n\<^sub>1 + 1) j)
                                    (idx_B_in_expansion A n\<^sub>0 i)))"

definition lemma_2_5_at :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "lemma_2_5_at A n k \<longleftrightarrow>
     lemma_2_5_i_clause A n k
   \<and> lemma_2_5_ii_clause A n k
   \<and> lemma_2_5_iii_clause A n k
   \<and> lemma_2_5_iv_clause A n k
   \<and> lemma_2_5_v_clause A n k"

text \<open>
  Trivial cases. When \<open>b0_start A = None\<close>, the block \<open>B\<^sub>0\<close>
  is empty (\<open>l1 A = 0\<close>), making the universally-quantified
  \<open>i < l1 A\<close> / \<open>j < l1 A\<close> hypotheses of clauses (i), (ii), (iv),
  (v) all vacuous; clause (iii) similarly demands
  \<open>max_parent_level A = Some m\<^sub>0\<close>, which under
  \<open>b0_start A = None\<close> is impossible. Hence
  \<open>lemma_2_5_at A n k\<close> holds in the no-\<open>B\<^sub>0\<close> case for trivial
  reasons.
\<close>

lemma lemma_2_5_at_no_b0:
  assumes "A \<noteq> []" "b0_start A = None"
  shows "lemma_2_5_at A n k"
proof -
  have l1z: "l1 A = 0" by (rule l1_zero_of_no_b0[OF assms(2)])
  have mp: "max_parent_level A = None"
    by (rule b0_start_None_imp_max_parent_level_None[OF assms])
  have ci: "lemma_2_5_i_clause A n k"
    using l1z by (simp add: lemma_2_5_i_clause_def)
  have cii: "lemma_2_5_ii_clause A n k"
    using l1z by (simp add: lemma_2_5_ii_clause_def)
  have ciii: "lemma_2_5_iii_clause A n k"
    using mp by (simp add: lemma_2_5_iii_clause_def)
  have civ: "lemma_2_5_iv_clause A n k"
    using l1z by (simp add: lemma_2_5_iv_clause_def)
  have cv: "lemma_2_5_v_clause A n k"
    using l1z by (simp add: lemma_2_5_v_clause_def)
  show ?thesis
    unfolding lemma_2_5_at_def
    using ci cii ciii civ cv by blast
qed

text \<open>
  The substantive case: \<open>b0_start A = Some s\<close>. This is Hunter's
  ``relatively straightforward, but tedious'' simultaneous induction
  on \<open>k\<close>. The proof in the paper proceeds within the inductive
  step in the order (ii), (iii), (iv), (i), (v); each sub-case uses
  the IH at \<open>k' < k\<close>, plus earlier sub-cases at level \<open>k\<close>.
  Mechanizing it requires several auxiliary lemmas about how
  \<open>m_parent\<close>/\<open>m_ancestor\<close> interact with \<open>strip_zero_rows\<close>,
  with the bumping of ascending elements, and with the totality of
  k-ancestry on the set of k-ancestors of any column. We leave this
  as a single \<open>sorry\<close>; it is the only sorry remaining for
  Lemma 2.5.
\<close>

lemma lemma_2_5_at_main:
  fixes A :: array
  assumes "A \<in> BMS" "A \<noteq> []"
  shows "lemma_2_5_at A n k"
proof (cases "b0_start A")
  case None
  show ?thesis by (rule lemma_2_5_at_no_b0[OF assms(2) None])
next
  case (Some s)
  \<comment> \<open>Hunter's simultaneous induction on \<open>k\<close> in the substantive case.\<close>
  show ?thesis sorry
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

end
