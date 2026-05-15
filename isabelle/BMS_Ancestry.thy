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

text \<open>
  Column count of \<open>A[n]\<close> in \<open>l0\<close>/\<open>l1\<close> notation:
  projection of @{thm arr_len_expansion}.
\<close>

lemma arr_len_expansion_l01:
  assumes "A \<noteq> []"
  shows "arr_len (expansion A n) = l0 A + Suc n * l1 A"
  using arr_len_expansion[OF assms] unfolding l0_def l1_def by simp

text \<open>
  Pre-strip indexing of \<open>A[n]\<close>: for indices in the
  \<open>G_block\<close> range \<open>[0, l0)\<close>, the pre-strip column equals
  the corresponding \<open>G_block A\<close> column.
\<close>

lemma pre_strip_nth_G:
  assumes "i < l0 A"
  shows "(G_block A @ Bs_concat A n) ! i = G_block A ! i"
  using assms unfolding l0_def by (simp add: nth_append)

text \<open>
  Block indexing of @{const Bs_concat}: the \<open>(t * l1 + j)\<close>-th
  column equals the \<open>j\<close>-th column of \<open>Bi_block A t\<close>
  (for \<open>t \<le> n\<close>, \<open>j < l1\<close>). Induction on \<open>n\<close>
  via @{thm Bs_concat_Suc} and @{thm length_Bs_concat}.
\<close>

lemma Bs_concat_nth_block:
  assumes "t \<le> n" and "j < l1 A"
  shows "Bs_concat A n ! (t * l1 A + j) = Bi_block A t ! j"
  using assms
proof (induct n arbitrary: t)
  case 0
  hence t_eq: "t = 0" by simp
  have "Bs_concat A 0 = Bi_block A 0" by (simp add: Bs_concat_def)
  thus ?case using t_eq by simp
next
  case (Suc n)
  show ?case
  proof (cases "t \<le> n")
    case True
    have len_Bs: "length (Bs_concat A n) = Suc n * l1 A"
      using length_Bs_concat unfolding l1_def by simp
    have idx_lt: "t * l1 A + j < length (Bs_concat A n)"
    proof -
      have "t * l1 A + j < t * l1 A + l1 A" using Suc.prems(2) by simp
      also have "\<dots> = (Suc t) * l1 A" by simp
      also have "\<dots> \<le> (Suc n) * l1 A" using True by simp
      finally show ?thesis using len_Bs by simp
    qed
    have "Bs_concat A (Suc n) = Bs_concat A n @ Bi_block A (Suc n)"
      by (rule Bs_concat_Suc)
    hence "Bs_concat A (Suc n) ! (t * l1 A + j) = Bs_concat A n ! (t * l1 A + j)"
      using idx_lt by (simp add: nth_append)
    also have "\<dots> = Bi_block A t ! j"
      using Suc.hyps[OF True Suc.prems(2)] .
    finally show ?thesis .
  next
    case False
    hence t_eq: "t = Suc n" using Suc.prems(1) by linarith
    have len_Bs: "length (Bs_concat A n) = Suc n * l1 A"
      using length_Bs_concat unfolding l1_def by simp
    have idx_eq: "t * l1 A + j = Suc n * l1 A + j" using t_eq by simp
    have idx_ge: "Suc n * l1 A \<le> Suc n * l1 A + j" by simp
    have "Bs_concat A (Suc n) = Bs_concat A n @ Bi_block A (Suc n)"
      by (rule Bs_concat_Suc)
    hence "Bs_concat A (Suc n) ! (Suc n * l1 A + j)
         = Bi_block A (Suc n) ! ((Suc n * l1 A + j) - length (Bs_concat A n))"
      using idx_ge len_Bs by (simp add: nth_append)
    also have "(Suc n * l1 A + j) - length (Bs_concat A n) = j"
      using len_Bs by simp
    finally show ?thesis using t_eq idx_eq by simp
  qed
qed

text \<open>
  Pre-strip indexing for \<open>B_t\<close> block in the expansion of
  \<open>A[n]\<close>: the column at \<open>idx_B_in_expansion A t j\<close>
  (where \<open>t \<le> n\<close>, \<open>j < l1\<close>) equals
  \<open>Bi_block A t ! j\<close>.
\<close>

lemma pre_strip_nth_B:
  assumes "t \<le> n" and "j < l1 A"
  shows "(G_block A @ Bs_concat A n) ! (idx_B_in_expansion A t j)
       = Bi_block A t ! j"
proof -
  have idx_eq: "idx_B_in_expansion A t j = l0 A + (t * l1 A + j)"
    unfolding idx_B_in_expansion_def by simp
  have l0_eq: "l0 A = length (G_block A)" unfolding l0_def by simp
  have "(G_block A @ Bs_concat A n) ! (idx_B_in_expansion A t j)
      = Bs_concat A n ! (t * l1 A + j)"
    using idx_eq l0_eq by (simp add: nth_append)
  also have "\<dots> = Bi_block A t ! j"
    using assms by (rule Bs_concat_nth_block)
  finally show ?thesis .
qed

text \<open>
  Elem values in the expansion \<open>A[n]\<close> on row \<open>m\<close> below
  the strip cutoff: G-block range reduces to \<open>G_block A\<close>,
  B-block range reduces to \<open>Bi_block A t\<close>.
\<close>

lemma elem_expansion_G_lt_keep:
  assumes A_ne: "A \<noteq> []"
      and i_lt: "i < l0 A"
      and m_lt: "m < keep_of (G_block A @ Bs_concat A n)"
  shows "elem (expansion A n) i m = elem (G_block A) i m"
proof -
  let ?P = "G_block A @ Bs_concat A n"
  have exp_eq: "expansion A n = strip_zero_rows ?P"
    using A_ne unfolding expansion_def by simp
  have arr_len_pre: "arr_len ?P = l0 A + Suc n * l1 A"
    by (simp add: l0_def l1_def length_Bs_concat)
  have i_lt_pre: "i < arr_len ?P"
    using i_lt arr_len_pre by simp
  have pre_ne: "?P \<noteq> []" using i_lt_pre by auto
  have elem_strip: "elem (strip_zero_rows ?P) i m = elem ?P i m"
    using pre_ne i_lt_pre m_lt by (rule elem_strip_lt_keep)
  have nth_pre: "?P ! i = G_block A ! i"
    using i_lt by (rule pre_strip_nth_G)
  show ?thesis using exp_eq elem_strip nth_pre unfolding elem_def by simp
qed

lemma elem_expansion_B_lt_keep:
  assumes A_ne: "A \<noteq> []"
      and t_le: "t \<le> n" and j_lt: "j < l1 A"
      and m_lt: "m < keep_of (G_block A @ Bs_concat A n)"
  shows "elem (expansion A n) (idx_B_in_expansion A t j) m
       = elem (Bi_block A t) j m"
proof -
  let ?P = "G_block A @ Bs_concat A n"
  let ?i = "idx_B_in_expansion A t j"
  have exp_eq: "expansion A n = strip_zero_rows ?P"
    using A_ne unfolding expansion_def by simp
  have arr_len_pre: "arr_len ?P = l0 A + Suc n * l1 A"
    by (simp add: l0_def l1_def length_Bs_concat)
  have idx_eq: "?i = l0 A + (t * l1 A + j)"
    unfolding idx_B_in_expansion_def by simp
  have i_lt_pre: "?i < arr_len ?P"
  proof -
    have "t * l1 A + j < (Suc t) * l1 A" using j_lt by simp
    also have "\<dots> \<le> Suc n * l1 A" using t_le by simp
    finally have "t * l1 A + j < Suc n * l1 A" .
    thus ?thesis using idx_eq arr_len_pre by simp
  qed
  have pre_ne: "?P \<noteq> []" using i_lt_pre by auto
  have elem_strip: "elem (strip_zero_rows ?P) ?i m = elem ?P ?i m"
    using pre_ne i_lt_pre m_lt by (rule elem_strip_lt_keep)
  have nth_pre: "?P ! ?i = Bi_block A t ! j"
    using t_le j_lt by (rule pre_strip_nth_B)
  show ?thesis using exp_eq elem_strip nth_pre unfolding elem_def by simp
qed


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
  \<open>n = 0\<close> base case (independent of \<open>b0_start A\<close>):
  clauses (i), (ii) are trivially reflexive; (iii), (v) have
  vacuous premises (\<open>n > 0\<close> / \<open>n_1 < 0\<close>); (iv) is by
  classification of \<open>m_parent\<close>'s value into \<open>G\<close>- vs
  \<open>B_0\<close>-range.
\<close>

lemma lemma_2_5_at_n_zero:
  assumes A_ne: "A \<noteq> []"
  shows "lemma_2_5_at A 0 k"
proof -
  have ci: "lemma_2_5_i_clause A 0 k"
    unfolding lemma_2_5_i_clause_def by simp
  have cii: "lemma_2_5_ii_clause A 0 k"
    unfolding lemma_2_5_ii_clause_def by simp
  have ciii: "lemma_2_5_iii_clause A 0 k"
    unfolding lemma_2_5_iii_clause_def by simp
  have cv: "lemma_2_5_v_clause A 0 k"
    unfolding lemma_2_5_v_clause_def by simp
  have civ: "lemma_2_5_iv_clause A 0 k"
    unfolding lemma_2_5_iv_clause_def
  proof (intro allI impI)
    fix i assume i_cond: "0 < i \<and> i < l1 A"
    let ?idx = "idx_B_in_expansion A 0 i"
    show "m_parent (expansion A 0) k ?idx = None \<or>
          (\<exists>p. m_parent (expansion A 0) k ?idx = Some p \<and>
               ((\<exists>j<l1 A. p = idx_B_in_expansion A 0 j) \<or>
                (\<exists>j<l0 A. p = idx_G A j)))"
    proof (cases "m_parent (expansion A 0) k ?idx")
      case None
      thus ?thesis by simp
    next
      case (Some p)
      have p_lt: "p < ?idx" using Some by (rule m_parent_lt)
      have idx_eq: "?idx = l0 A + i" by (simp add: idx_B_in_expansion_def)
      have p_lt_arr: "p < l0 A + l1 A"
        using p_lt idx_eq i_cond by linarith
      show ?thesis
      proof (cases "p < l0 A")
        case True
        have "p = idx_G A p" by (simp add: idx_G_def)
        thus ?thesis using Some True by blast
      next
        case False
        let ?j = "p - l0 A"
        have j_lt: "?j < l1 A" using p_lt_arr False by simp
        have "p = idx_B_in_expansion A 0 ?j"
          using False by (simp add: idx_B_in_expansion_def)
        thus ?thesis using Some j_lt by blast
      qed
    qed
  qed
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
proof (cases n)
  case 0
  show ?thesis using lemma_2_5_at_n_zero[OF assms(2)] \<open>n = 0\<close> by simp
next
  case (Suc n')
  show ?thesis
  proof (cases "b0_start A")
    case None
    show ?thesis by (rule lemma_2_5_at_no_b0[OF assms(2) None])
  next
    case (Some s)
    \<comment> \<open>Hunter's simultaneous induction on \<open>k\<close> in the substantive case
        \<open>n \<ge> 1 \<and> b0_start A = Some s\<close>.\<close>
    show ?thesis sorry
  qed
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
