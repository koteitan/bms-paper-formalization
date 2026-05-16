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

text \<open>
  Elem of \<open>Bi_block A t\<close> at column \<open>j\<close> and row \<open>m\<close>
  equals \<open>bump_col A j t ! m\<close>.
\<close>

lemma elem_Bi_block_via_bump_col:
  assumes "j < l1 A"
  shows "elem (Bi_block A t) j m = (bump_col A j t) ! m"
proof -
  have "Bi_block A t ! j = bump_col A j t"
    using assms unfolding l1_def by (rule Bi_block_nth)
  thus ?thesis unfolding elem_def by simp
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

text \<open>
  Composed: elem of \<open>A[n]\<close> at \<open>idx_B_in_expansion A t j\<close>
  directly equals \<open>(bump_col A j t) ! m\<close> (below the strip
  cutoff).
\<close>

text \<open>
  Classification helpers for clause (iv)'s disjunction: an index
  \<open>p\<close> in the G range (\<open>p < l0\<close>) or in the B_n range
  (\<open>l0 + n*l1 \<le> p < l0 + n*l1 + l1\<close>) witnesses the
  corresponding disjunct.
\<close>

lemma clause_iv_G_case:
  assumes "p < l0 A"
  shows "\<exists>j < l0 A. p = idx_G A j"
  using assms by (auto simp: idx_G_def)

lemma clause_iv_B_n_case:
  assumes "l0 A + n * l1 A \<le> p"
      and "p < l0 A + n * l1 A + l1 A"
  shows "\<exists>j < l1 A. p = idx_B_in_expansion A n j"
proof -
  let ?j = "p - (l0 A + n * l1 A)"
  have j_lt: "?j < l1 A" using assms by simp
  have p_eq: "p = idx_B_in_expansion A n ?j"
    using assms(1) by (simp add: idx_B_in_expansion_def)
  show ?thesis using j_lt p_eq by blast
qed

text \<open>
  Full positional decomposition: any \<open>p\<close> in the range
  \<open>[0, l0 + (Suc n) * l1)\<close> -- which contains
  \<open>idx_B_in_expansion A n i\<close> for any \<open>i < l1\<close> -- is either
  a \<open>G\<close>-index or a \<open>B_t\<close>-index for some \<open>t \<le> n\<close>.
  Refines @{thm clause_iv_G_case} and @{thm clause_iv_B_n_case}
  by also classifying intermediate blocks \<open>B_t\<close> for \<open>0 \<le> t < n\<close>.
  Drives clause (iv)'s argument that a hypothetical \<open>p\<close> in
  \<open>B_t\<close> for \<open>0 \<le> t < n\<close> must be ruled out.
\<close>

lemma clause_iv_p_decomposition:
  assumes l1_pos: "0 < l1 A"
      and p_lt:   "p < l0 A + (Suc n) * l1 A"
  shows "p < l0 A
       \<or> (\<exists>t j. t \<le> n \<and> j < l1 A \<and> p = idx_B_in_expansion A t j)"
proof (cases "p < l0 A")
  case True
  thus ?thesis by blast
next
  case False
  let ?q = "p - l0 A"
  let ?t = "?q div (l1 A)"
  let ?j = "?q mod (l1 A)"
  have q_lt: "?q < Suc n * l1 A" using False p_lt by linarith
  have t_le: "?t \<le> n"
  proof -
    have "?t < Suc n"
    proof (rule ccontr)
      assume "\<not> ?t < Suc n"
      hence n_le: "Suc n \<le> ?t" by simp
      have mult_le: "Suc n * l1 A \<le> ?t * l1 A"
        using mult_le_mono1[OF n_le] by simp
      have div_le: "?t * l1 A \<le> ?q" by (rule div_times_less_eq_dividend)
      from mult_le div_le have "Suc n * l1 A \<le> ?q" by linarith
      thus False using q_lt by simp
    qed
    thus ?thesis by simp
  qed
  have j_lt: "?j < l1 A" using l1_pos by simp
  have q_eq: "?q = ?t * l1 A + ?j" by (simp add: div_mult_mod_eq)
  have p_eq: "p = l0 A + ?t * l1 A + ?j"
    using False q_eq by linarith
  have idx_eq: "idx_B_in_expansion A ?t ?j = l0 A + ?t * l1 A + ?j"
    by (simp add: idx_B_in_expansion_def)
  have "p = idx_B_in_expansion A ?t ?j" using p_eq idx_eq by simp
  thus ?thesis using t_le j_lt by blast
qed

lemma elem_expansion_B_via_bump:
  assumes A_ne: "A \<noteq> []"
      and t_le: "t \<le> n" and j_lt: "j < l1 A"
      and m_lt: "m < keep_of (G_block A @ Bs_concat A n)"
  shows "elem (expansion A n) (idx_B_in_expansion A t j) m
       = (bump_col A j t) ! m"
  using elem_expansion_B_lt_keep[OF A_ne t_le j_lt m_lt]
        elem_Bi_block_via_bump_col[OF j_lt] by simp

text \<open>
  At row \<open>k \<ge> t\<close> (no ascending), the elem at any B-block
  column equals the original B_0 column elem. Bumping has zero
  effect since \<open>ascends A x k = False\<close>.
\<close>

lemma elem_expansion_B_eq_orig_k_ge_t:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_ge: "t \<le> k"
      and a_le: "a \<le> n"
      and x_lt: "x < l1 A"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and k_lt_col: "k < length (A ! (s + x))"
  shows "elem (expansion A n) (idx_B_in_expansion A a x) k
       = (A ! (s + x)) ! k"
proof -
  have not_asc: "\<not> ascends A x k"
    unfolding ascends_def using b0 mp k_ge by simp
  have bump_eq: "(bump_col A x a) ! k = (A ! (s + x)) ! k"
    using bump_col_no_bump[OF b0 not_asc k_lt_col] .
  have "elem (expansion A n) (idx_B_in_expansion A a x) k
      = (bump_col A x a) ! k"
    using elem_expansion_B_via_bump[OF A_ne a_le x_lt k_lt_keep] .
  also have "\<dots> = (A ! (s + x)) ! k" using bump_eq .
  finally show ?thesis .
qed

text \<open>
  Column equality across blocks when \<open>max_parent_level A = Some 0\<close>:
  the \<open>x\<close>-th column of every \<open>B\<close>-block in \<open>A[n]\<close> is
  identical (independent of the block index \<open>c\<close>). Combines
  @{thm pre_strip_nth_B} (pre-strip indexing) with
  @{thm Bi_block_eq_B0_when_m0_zero} (no-bumping reduces every
  \<open>B_i\<close> to \<open>B_0\<close>) and the strip step (which trims uniformly
  per column).
\<close>

lemma AEn_nth_idx_B_eq_when_m0_zero:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp0: "max_parent_level A = Some 0"
      and a_le: "a \<le> n"
      and b_le: "b \<le> n"
      and x_lt: "x < l1 A"
  shows "(A[n]) ! (idx_B_in_expansion A a x)
       = (A[n]) ! (idx_B_in_expansion A b x)"
proof -
  let ?P = "G_block A @ Bs_concat A n"
  have exp_eq: "A[n] = strip_zero_rows ?P"
    using A_ne unfolding expansion_def by simp
  have l1_pos: "0 < l1 A"
    using x_lt by simp
  have len_P: "length ?P = l0 A + Suc n * l1 A"
    by (simp add: l0_def l1_def length_Bs_concat)
  have idx_a_lt: "idx_B_in_expansion A a x < length ?P"
  proof -
    have "a * l1 A + x < Suc a * l1 A" using x_lt by simp
    also have "\<dots> \<le> Suc n * l1 A" using a_le by simp
    finally have "a * l1 A + x < Suc n * l1 A" .
    thus ?thesis using len_P unfolding idx_B_in_expansion_def by simp
  qed
  have idx_b_lt: "idx_B_in_expansion A b x < length ?P"
  proof -
    have "b * l1 A + x < Suc b * l1 A" using x_lt by simp
    also have "\<dots> \<le> Suc n * l1 A" using b_le by simp
    finally have "b * l1 A + x < Suc n * l1 A" .
    thus ?thesis using len_P unfolding idx_B_in_expansion_def by simp
  qed
  have P_ne: "?P \<noteq> []" using idx_a_lt by auto
  have strip_eq: "strip_zero_rows ?P = map (\<lambda>c. take (keep_of ?P) c) ?P"
    using P_ne by (rule strip_zero_rows_eq_map_take)
  have nth_a: "?P ! idx_B_in_expansion A a x = Bi_block A a ! x"
    using a_le x_lt by (rule pre_strip_nth_B)
  have nth_b: "?P ! idx_B_in_expansion A b x = Bi_block A b ! x"
    using b_le x_lt by (rule pre_strip_nth_B)
  have bi_a: "Bi_block A a = B0_block A"
    using A_ne b0 mp0 by (rule Bi_block_eq_B0_when_m0_zero)
  have bi_b: "Bi_block A b = B0_block A"
    using A_ne b0 mp0 by (rule Bi_block_eq_B0_when_m0_zero)
  have pre_col_eq: "?P ! idx_B_in_expansion A a x = ?P ! idx_B_in_expansion A b x"
    using nth_a nth_b bi_a bi_b by simp
  have strip_a: "(A[n]) ! idx_B_in_expansion A a x
               = take (keep_of ?P) (?P ! idx_B_in_expansion A a x)"
  proof -
    have "(A[n]) ! idx_B_in_expansion A a x
        = (map (\<lambda>c. take (keep_of ?P) c) ?P) ! idx_B_in_expansion A a x"
      using exp_eq strip_eq by simp
    also have "\<dots> = (\<lambda>c. take (keep_of ?P) c) (?P ! idx_B_in_expansion A a x)"
      using nth_map[OF idx_a_lt] by simp
    finally show ?thesis by simp
  qed
  have strip_b: "(A[n]) ! idx_B_in_expansion A b x
               = take (keep_of ?P) (?P ! idx_B_in_expansion A b x)"
  proof -
    have "(A[n]) ! idx_B_in_expansion A b x
        = (map (\<lambda>c. take (keep_of ?P) c) ?P) ! idx_B_in_expansion A b x"
      using exp_eq strip_eq by simp
    also have "\<dots> = (\<lambda>c. take (keep_of ?P) c) (?P ! idx_B_in_expansion A b x)"
      using nth_map[OF idx_b_lt] by simp
    finally show ?thesis by simp
  qed
  show ?thesis using strip_a strip_b pre_col_eq by simp
qed

text \<open>
  Corollary of @{thm AEn_nth_idx_B_eq_when_m0_zero}: elem values
  at any row \<open>m\<close> are invariant in the block index.
\<close>

lemma elem_AEn_idx_B_eq_when_m0_zero:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp0: "max_parent_level A = Some 0"
      and a_le: "a \<le> n"
      and b_le: "b \<le> n"
      and x_lt: "x < l1 A"
  shows "elem (A[n]) (idx_B_in_expansion A a x) m
       = elem (A[n]) (idx_B_in_expansion A b x) m"
proof -
  have "(A[n]) ! (idx_B_in_expansion A a x) = (A[n]) ! (idx_B_in_expansion A b x)"
    by (rule AEn_nth_idx_B_eq_when_m0_zero[OF A_ne b0 mp0 a_le b_le x_lt])
  thus ?thesis unfolding elem_def by simp
qed

text \<open>
  Strict-less invariance across blocks at level \<open>k < t\<close>: by
  @{thm bump_col_uniform_k_lt_t} the bump amount at row \<open>k\<close>
  is uniform across all B_0 columns, so strict-less comparison
  between any two B-block columns at level \<open>k\<close> is invariant
  in the block index. Resolves the \<open>\<sigma>\<close>-equivariance issue for
  clause (ii) at levels \<open>k < t\<close>.
\<close>

lemma elem_expansion_B_lt_invariant_in_block:
  assumes A_BMS: "A \<in> BMS"
      and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_lt: "k < t"
      and a_le: "a \<le> n"
      and a'_le: "a' \<le> n"
      and x_lt: "x < l1 A"
      and y_lt: "y < l1 A"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and x_col_len: "k < length (A ! (s + x))"
      and y_col_len: "k < length (A ! (s + y))"
  shows "(elem (expansion A n) (idx_B_in_expansion A a y) k
        < elem (expansion A n) (idx_B_in_expansion A a x) k)
       \<longleftrightarrow>
         (elem (expansion A n) (idx_B_in_expansion A a' y) k
        < elem (expansion A n) (idx_B_in_expansion A a' x) k)"
proof -
  have x_b0: "x < length (B0_block A)" using x_lt unfolding l1_def by simp
  have y_b0: "y < length (B0_block A)" using y_lt unfolding l1_def by simp
  have bx_a: "elem (expansion A n) (idx_B_in_expansion A a x) k
            = (A ! (s + x)) ! k + a * delta A k"
    using elem_expansion_B_via_bump[OF A_ne a_le x_lt k_lt_keep]
          bump_col_uniform_k_lt_t[OF A_BMS b0 mp k_lt x_b0 x_col_len] by simp
  have by_a: "elem (expansion A n) (idx_B_in_expansion A a y) k
            = (A ! (s + y)) ! k + a * delta A k"
    using elem_expansion_B_via_bump[OF A_ne a_le y_lt k_lt_keep]
          bump_col_uniform_k_lt_t[OF A_BMS b0 mp k_lt y_b0 y_col_len] by simp
  have bx_a': "elem (expansion A n) (idx_B_in_expansion A a' x) k
             = (A ! (s + x)) ! k + a' * delta A k"
    using elem_expansion_B_via_bump[OF A_ne a'_le x_lt k_lt_keep]
          bump_col_uniform_k_lt_t[OF A_BMS b0 mp k_lt x_b0 x_col_len] by simp
  have by_a': "elem (expansion A n) (idx_B_in_expansion A a' y) k
             = (A ! (s + y)) ! k + a' * delta A k"
    using elem_expansion_B_via_bump[OF A_ne a'_le y_lt k_lt_keep]
          bump_col_uniform_k_lt_t[OF A_BMS b0 mp k_lt y_b0 y_col_len] by simp
  show ?thesis
    using bx_a by_a bx_a' by_a' by simp
qed

text \<open>
  Same B-column index \<open>j\<close>, different block index \<open>t < t'\<close>:
  elem strictly increases (at ascending row).
\<close>

text \<open>
  \<open>B_0\<close> columns of \<open>A[n]\<close> equal the corresponding
  columns of the original \<open>A\<close> (offset by \<open>s\<close>): no bumping
  at multiplier \<open>i = 0\<close>.
\<close>

lemma bump_col_zero_eq_orig:
  assumes b0: "b0_start A = Some s"
      and len_k: "k < length (A ! (s + d))"
  shows "(bump_col A d 0) ! k = (A ! (s + d)) ! k"
  using bump_col_nth_general[OF b0 len_k] by simp

lemma elem_expansion_B0_via_orig:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and j_lt: "j < l1 A"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and k_lt_len: "k < length (A ! (s + j))"
  shows "elem (expansion A n) (idx_B_in_expansion A 0 j) k
       = elem A (s + j) k"
proof -
  have bump_eq: "elem (expansion A n) (idx_B_in_expansion A 0 j) k
              = (bump_col A j 0) ! k"
    using elem_expansion_B_via_bump[OF A_ne _ j_lt k_lt_keep] by simp
  have orig: "(bump_col A j 0) ! k = (A ! (s + j)) ! k"
    using bump_col_zero_eq_orig[OF b0 k_lt_len] .
  show ?thesis using bump_eq orig unfolding elem_def by simp
qed

text \<open>
  Same block index \<open>t\<close>, different column indices \<open>j, i\<close>
  in \<open>B_t\<close> (both ascending at row \<open>k\<close>): the strict
  inequality \<open>(A!(s+j))!k < (A!(s+i))!k\<close> propagates to
  \<open>elem (A[n]) (idx_B t j) k < elem (A[n]) (idx_B t i) k\<close>.
\<close>

lemma elem_expansion_B_lt_same_block:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and t_le: "t \<le> n"
      and j_lt: "j < l1 A" and i_lt: "i < l1 A"
      and asc_j: "ascends A j k"
      and asc_i: "ascends A i k"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and j_len: "k < length (A ! (s + j))"
      and i_len: "k < length (A ! (s + i))"
      and base_lt: "(A ! (s + j)) ! k < (A ! (s + i)) ! k"
  shows "elem (expansion A n) (idx_B_in_expansion A t j) k
       < elem (expansion A n) (idx_B_in_expansion A t i) k"
proof -
  have bump_j: "elem (expansion A n) (idx_B_in_expansion A t j) k
              = (bump_col A j t) ! k"
    using elem_expansion_B_via_bump[OF A_ne t_le j_lt k_lt_keep] .
  have bump_i: "elem (expansion A n) (idx_B_in_expansion A t i) k
              = (bump_col A i t) ! k"
    using elem_expansion_B_via_bump[OF A_ne t_le i_lt k_lt_keep] .
  have val_j: "(bump_col A j t) ! k = (A ! (s + j)) ! k + t * delta A k"
    using bump_col_nth_general[OF b0 j_len] asc_j by simp
  have val_i: "(bump_col A i t) ! k = (A ! (s + i)) ! k + t * delta A k"
    using bump_col_nth_general[OF b0 i_len] asc_i by simp
  show ?thesis using bump_j bump_i val_j val_i base_lt by simp
qed

lemma elem_expansion_B_lt_step_same_j:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and j_lt: "j < l1 A"
      and t_lt: "t < t'" and t'_le: "t' \<le> n"
      and asc: "ascends A j k"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and k_lt_len: "k < length (A ! (s + j))"
  shows "elem (expansion A n) (idx_B_in_expansion A t j) k
       < elem (expansion A n) (idx_B_in_expansion A t' j) k"
proof -
  have t_le: "t \<le> n" using t_lt t'_le by linarith
  have bump_t: "elem (expansion A n) (idx_B_in_expansion A t j) k
              = (bump_col A j t) ! k"
    using elem_expansion_B_via_bump[OF A_ne t_le j_lt k_lt_keep] .
  have bump_t': "elem (expansion A n) (idx_B_in_expansion A t' j) k
              = (bump_col A j t') ! k"
    using elem_expansion_B_via_bump[OF A_ne t'_le j_lt k_lt_keep] .
  obtain m\<^sub>0 where mp_eq: "max_parent_level A = Some m\<^sub>0"
    using asc unfolding ascends_def using b0
    by (cases "max_parent_level A") auto
  have k_lt_m0: "k < m\<^sub>0"
    using asc unfolding ascends_def using b0 mp_eq by simp
  have delta_pos: "0 < delta A k"
    using b0 mp_eq k_lt_m0 by (rule delta_pos_of_lt_m0)
  have "(bump_col A j t) ! k < (bump_col A j t') ! k"
    using b0 asc delta_pos t_lt k_lt_len by (rule bump_col_lt_step)
  thus ?thesis using bump_t bump_t' by simp
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

text \<open>
  Clause (v) is vacuous when \<open>n \<le> 1\<close>: the conjunction
  \<open>n\<^sub>0 < n\<^sub>1 \<and> n\<^sub>1 < n\<close> forces \<open>n\<^sub>1 = 0\<close> and
  then \<open>n\<^sub>0 < 0\<close>, which is impossible. Extracted so the
  \<open>n = 1\<close> sub-case of \<open>lemma_2_5_at_main\<close> only has to deal with
  clauses (i)--(iv).
\<close>

lemma lemma_2_5_v_clause_n_le_one:
  assumes "n \<le> 1"
  shows "lemma_2_5_v_clause A n k"
  unfolding lemma_2_5_v_clause_def
proof (intro allI impI)
  fix i j n\<^sub>0 n\<^sub>1
  assume h: "i < l1 A \<and> j < l1 A \<and> n\<^sub>0 < n\<^sub>1 \<and> n\<^sub>1 < n"
  from h assms have False by linarith
  thus "m_ancestor (A[n]) k (idx_B_in_expansion A n\<^sub>1 j)
                              (idx_B_in_expansion A n\<^sub>0 i)
        \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (n\<^sub>1 + 1) j)
                                  (idx_B_in_expansion A n\<^sub>0 i)" by simp
qed

text \<open>
  Clause (iii) is vacuous when \<open>k\<close> is at or above the maximum
  parent level: the clause's premise demands
  \<open>max_parent_level A = Some m\<^sub>0 \<and> k < m\<^sub>0\<close>, so
  \<open>m\<^sub>0 \<le> k\<close> (in particular \<open>max_parent_level A = Some m\<^sub>0\<close>
  with \<open>k \<ge> m\<^sub>0\<close>) makes the implication trivially true.
  Useful inside the \<open>Some s\<close> sub-case of \<open>lemma_2_5_at_main\<close>
  when the induction reaches \<open>k \<ge> m\<^sub>0\<close>.
\<close>

lemma lemma_2_5_iii_clause_when_k_ge_m0:
  assumes "\<forall>m\<^sub>0. max_parent_level A = Some m\<^sub>0 \<longrightarrow> m\<^sub>0 \<le> k"
  shows "lemma_2_5_iii_clause A n k"
  unfolding lemma_2_5_iii_clause_def
proof (intro allI impI)
  fix m\<^sub>0 i
  assume h: "0 < n \<and> max_parent_level A = Some m\<^sub>0 \<and> k < m\<^sub>0 \<and> i < l1 A"
  from h assms have False by force
  thus "m_ancestor A k (last_col_idx A) (idx_B0_in_orig A i) \<longleftrightarrow>
        m_ancestor (A[n]) k (idx_B_in_expansion A n 0)
                            (idx_B_in_expansion A (n - 1) i)"
    by simp
qed

text \<open>
  Helper for clause (ii), \<open>k = 0\<close>, \<open>t = 0\<close> sub-case.
  When \<open>max_parent_level A = Some 0\<close>, no column ascends and
  \<open>bump_col\<close> is the identity at every row, so the B-blocks of
  \<open>A[n]\<close> are literal copies of \<open>B\<^sub>0\<close>. The row-0 values of
  any B-block column \<open>idx_B_in_expansion A c x\<close> are independent
  of the block index \<open>c\<close>. The m_parent of a B-block column at
  row 0 either lands in the same block (same B_0 index for any
  \<open>c\<close>) or leaves the block; chains that escape cannot return.
  Therefore the m_ancestor relation at row 0 between two columns
  of the same block is invariant under block shift.

  Two sub-helpers characterize \<open>m_parent (A[n]) 0 (idx_B_in_expansion A c j)\<close>:

  (M1a, within-block) If the filter
  \<open>[j' \<leftarrow> [0..<j]. elem A (s + j') 0 < elem A (s + j) 0]\<close> is
  non-empty, then the m_parent lands at column \<open>last\<close> of that
  filter in the same block \<open>c\<close>.

  (M1b, outside-block) If that filter is empty, then the m_parent
  is either \<open>None\<close> or lands at a row strictly less than
  \<open>idx_B_in_expansion A c 0\<close> (i.e., before block \<open>c\<close>
  starts).

  The sub-helpers are deferred (\<open>sorry\<close>); the main lemma is
  proved on top of them by strong induction on \<open>j\<close>.
\<close>

text \<open>
  Trivial corollary of @{thm AEn_nth_idx_B_eq_when_m0_zero}: row-0
  elem of B-block column \<open>idx_B A c j\<close> reduces to row-0 elem at
  block 0.
\<close>

lemma elem_AEn_idx_B_eq_block_zero_at_row_zero_when_m0_zero:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp0: "max_parent_level A = Some 0"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
  shows "elem (A[n]) (idx_B_in_expansion A c j) 0
       = elem (A[n]) (idx_B_in_expansion A 0 j) 0"
proof -
  have c_le': "c \<le> n" by (rule c_le)
  have z_le: "(0::nat) \<le> n" by simp
  have "(A[n]) ! (idx_B_in_expansion A c j) = (A[n]) ! (idx_B_in_expansion A 0 j)"
    by (rule AEn_nth_idx_B_eq_when_m0_zero[OF A_ne b0 mp0 c_le' z_le j_lt])
  thus ?thesis unfolding elem_def by simp
qed

lemma m_parent_AEn_zero_idx_B_within_block_when_t_zero:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp0: "max_parent_level A = Some 0"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and S_ne: "[j' \<leftarrow> [0..<j]. elem (A[n]) (idx_B_in_expansion A 0 j') 0
                            < elem (A[n]) (idx_B_in_expansion A 0 j) 0] \<noteq> []"
  shows "m_parent (A[n]) 0 (idx_B_in_expansion A c j)
       = Some (idx_B_in_expansion A c
            (last [j' \<leftarrow> [0..<j]. elem (A[n]) (idx_B_in_expansion A 0 j') 0
                            < elem (A[n]) (idx_B_in_expansion A 0 j) 0]))"
proof -
  let ?i = "idx_B_in_expansion A c j"
  let ?Cstart = "idx_B_in_expansion A c 0"
  let ?vi = "elem (A[n]) ?i 0"
  let ?cands = "[p \<leftarrow> [0..<?i]. elem (A[n]) p 0 < ?vi]"
  let ?S = "[j' \<leftarrow> [0..<j]. elem (A[n]) (idx_B_in_expansion A 0 j') 0
                        < elem (A[n]) (idx_B_in_expansion A 0 j) 0]"
  have mp_eq: "m_parent (A[n]) 0 ?i = (if ?cands = [] then None else Some (last ?cands))"
    by (simp add: Let_def)
  have i_eq: "?i = ?Cstart + j" unfolding idx_B_in_expansion_def by simp
  have range_split: "[0..<?i] = [0..<?Cstart] @ [?Cstart..<?i]"
    using upt_add_eq_append[OF le0, of ?Cstart j] i_eq by simp
  let ?pre = "filter (\<lambda>p. elem (A[n]) p 0 < ?vi) [0..<?Cstart]"
  let ?post = "filter (\<lambda>p. elem (A[n]) p 0 < ?vi) [?Cstart..<?i]"
  have cands_split: "?cands = ?pre @ ?post"
    using range_split by simp
  have post_range: "[?Cstart..<?i] = map (\<lambda>i. i + ?Cstart) [0..<j]"
    using i_eq map_add_upt[of ?Cstart j] by (simp add: add.commute)
  have post_map: "?post = map (\<lambda>i. i + ?Cstart)
                   (filter (\<lambda>i. elem (A[n]) (i + ?Cstart) 0 < ?vi) [0..<j])"
    using post_range by (simp add: filter_map o_def)
  have filter_cong_eq:
    "filter (\<lambda>i. elem (A[n]) (i + ?Cstart) 0 < ?vi) [0..<j] = ?S"
  proof (rule filter_cong[OF refl])
    fix i assume i_in: "i \<in> set [0..<j]"
    hence i_lt_j: "i < j" by simp
    hence i_lt_l1: "i < l1 A" using j_lt by linarith
    have idxBc_eq: "i + ?Cstart = idx_B_in_expansion A c i"
      unfolding idx_B_in_expansion_def by simp
    have elem_p: "elem (A[n]) (i + ?Cstart) 0 = elem (A[n]) (idx_B_in_expansion A 0 i) 0"
      using idxBc_eq
            elem_AEn_idx_B_eq_block_zero_at_row_zero_when_m0_zero
              [OF A_ne b0 mp0 c_le i_lt_l1] by simp
    have elem_j: "?vi = elem (A[n]) (idx_B_in_expansion A 0 j) 0"
      by (rule elem_AEn_idx_B_eq_block_zero_at_row_zero_when_m0_zero
               [OF A_ne b0 mp0 c_le j_lt])
    show "(elem (A[n]) (i + ?Cstart) 0 < ?vi)
       \<longleftrightarrow> (elem (A[n]) (idx_B_in_expansion A 0 i) 0
            < elem (A[n]) (idx_B_in_expansion A 0 j) 0)"
      using elem_p elem_j by simp
  qed
  have post_eq: "?post = map (\<lambda>i. i + ?Cstart) ?S"
    using post_map filter_cong_eq by simp
  have post_ne: "?post \<noteq> []" using post_eq S_ne by simp
  have cands_ne: "?cands \<noteq> []" using cands_split post_ne by simp
  have last_cands_eq: "last ?cands = last ?post"
    using cands_split post_ne by (simp add: last_append)
  have last_post_eq: "last ?post = last ?S + ?Cstart"
    using post_eq S_ne by (simp add: last_map)
  have last_S_idx: "last ?S + ?Cstart = idx_B_in_expansion A c (last ?S)"
    unfolding idx_B_in_expansion_def by simp
  show ?thesis
    using mp_eq cands_ne last_cands_eq last_post_eq last_S_idx by simp
qed

lemma m_parent_AEn_zero_idx_B_outside_block_when_t_zero:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp0: "max_parent_level A = Some 0"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and S_empty: "[j' \<leftarrow> [0..<j]. elem (A[n]) (idx_B_in_expansion A 0 j') 0
                            < elem (A[n]) (idx_B_in_expansion A 0 j) 0] = []"
  shows "(case m_parent (A[n]) 0 (idx_B_in_expansion A c j) of
             None \<Rightarrow> True
           | Some p \<Rightarrow> p < idx_B_in_expansion A c 0)"
proof -
  let ?i = "idx_B_in_expansion A c j"
  let ?Cstart = "idx_B_in_expansion A c 0"
  let ?vi = "elem (A[n]) ?i 0"
  let ?cands = "[p \<leftarrow> [0..<?i]. elem (A[n]) p 0 < ?vi]"
  have mp_eq: "m_parent (A[n]) 0 ?i
             = (if ?cands = [] then None else Some (last ?cands))"
    by (simp add: Let_def)
  have all_lt: "\<forall>p \<in> set ?cands. p < ?Cstart"
  proof
    fix p assume p_in: "p \<in> set ?cands"
    have p_lt_i: "p < ?i" using p_in by auto
    have v_lt: "elem (A[n]) p 0 < ?vi" using p_in by simp
    show "p < ?Cstart"
    proof (rule ccontr)
      assume "\<not> p < ?Cstart"
      hence p_ge: "?Cstart \<le> p" by simp
      define j' where "j' = p - ?Cstart"
      have p_eq: "p = ?Cstart + j'" using p_ge j'_def by simp
      have j'_lt_j: "j' < j"
      proof -
        have "?Cstart + j' < ?Cstart + j"
          using p_eq p_lt_i unfolding idx_B_in_expansion_def by simp
        thus ?thesis by simp
      qed
      have j'_lt_l1: "j' < l1 A" using j'_lt_j j_lt by linarith
      have p_as_idxB: "p = idx_B_in_expansion A c j'"
        using p_eq unfolding idx_B_in_expansion_def by simp
      have el_p: "elem (A[n]) p 0 = elem (A[n]) (idx_B_in_expansion A 0 j') 0"
      proof -
        have step1: "elem (A[n]) p 0 = elem (A[n]) (idx_B_in_expansion A c j') 0"
          using p_as_idxB by simp
        have step2: "elem (A[n]) (idx_B_in_expansion A c j') 0
                   = elem (A[n]) (idx_B_in_expansion A 0 j') 0"
          by (rule elem_AEn_idx_B_eq_block_zero_at_row_zero_when_m0_zero
                   [OF A_ne b0 mp0 c_le j'_lt_l1])
        show ?thesis using step1 step2 by simp
      qed
      have el_j: "?vi = elem (A[n]) (idx_B_in_expansion A 0 j) 0"
        by (rule elem_AEn_idx_B_eq_block_zero_at_row_zero_when_m0_zero
                 [OF A_ne b0 mp0 c_le j_lt])
      have val_lt: "elem (A[n]) (idx_B_in_expansion A 0 j') 0
                  < elem (A[n]) (idx_B_in_expansion A 0 j) 0"
        using v_lt el_p el_j by simp
      have "j' \<in> set [j' \<leftarrow> [0..<j]. elem (A[n]) (idx_B_in_expansion A 0 j') 0
                              < elem (A[n]) (idx_B_in_expansion A 0 j) 0]"
        using j'_lt_j val_lt by auto
      thus False using S_empty by simp
    qed
  qed
  show ?thesis
  proof (cases "?cands = []")
    case True
    thus ?thesis using mp_eq by simp
  next
    case False
    have "last ?cands \<in> set ?cands" using last_in_set[OF False] .
    hence "last ?cands < ?Cstart" using all_lt by simp
    thus ?thesis using mp_eq False by simp
  qed
qed

lemma m_anc_zero_idx_B_in_block_shift_when_t_zero:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp0: "max_parent_level A = Some 0"
      and a_le: "a \<le> n" and b_le: "b \<le> n"
      and i_lt: "i < l1 A"
      and j_lt: "j < l1 A"
      and i_lt_j: "i < j"
  shows "m_ancestor (A[n]) 0 (idx_B_in_expansion A a j) (idx_B_in_expansion A a i)
       \<longleftrightarrow> m_ancestor (A[n]) 0 (idx_B_in_expansion A b j) (idx_B_in_expansion A b i)"
  using i_lt j_lt i_lt_j
proof (induct j arbitrary: i rule: less_induct)
  case (less j)
  note IH = less.hyps
  note i_lt' = less.prems(1)
  note j_lt' = less.prems(2)
  note i_lt_j' = less.prems(3)
  let ?S = "[j' \<leftarrow> [0..<j]. elem (A[n]) (idx_B_in_expansion A 0 j') 0
                        < elem (A[n]) (idx_B_in_expansion A 0 j) 0]"
  show ?case
  proof (cases "?S = []")
    case True
    have outA: "(case m_parent (A[n]) 0 (idx_B_in_expansion A a j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A a 0)"
      using m_parent_AEn_zero_idx_B_outside_block_when_t_zero
            [OF A_BMS A_ne b0 mp0 a_le j_lt' True] .
    have outB: "(case m_parent (A[n]) 0 (idx_B_in_expansion A b j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A b 0)"
      using m_parent_AEn_zero_idx_B_outside_block_when_t_zero
            [OF A_BMS A_ne b0 mp0 b_le j_lt' True] .
    have lhs_F: "\<not> m_ancestor (A[n]) 0 (idx_B_in_expansion A a j)
                                          (idx_B_in_expansion A a i)"
    proof (cases "m_parent (A[n]) 0 (idx_B_in_expansion A a j)")
      case None
      thus ?thesis using m_anc_via_parent_none by metis
    next
      case (Some p)
      have p_lt: "p < idx_B_in_expansion A a 0"
        using outA Some by simp
      have tgt_ge: "idx_B_in_expansion A a 0 \<le> idx_B_in_expansion A a i"
        unfolding idx_B_in_expansion_def by simp
      have p_ne_tgt: "p \<noteq> idx_B_in_expansion A a i"
        using p_lt tgt_ge by linarith
      have no_anc: "\<not> m_ancestor (A[n]) 0 p (idx_B_in_expansion A a i)"
      proof
        assume "m_ancestor (A[n]) 0 p (idx_B_in_expansion A a i)"
        hence "idx_B_in_expansion A a i < p" by (rule m_ancestor_target_lt)
        thus False using p_lt tgt_ge by linarith
      qed
      have iff_via: "m_ancestor (A[n]) 0 (idx_B_in_expansion A a j)
                                          (idx_B_in_expansion A a i)
                  \<longleftrightarrow> p = idx_B_in_expansion A a i
                       \<or> m_ancestor (A[n]) 0 p (idx_B_in_expansion A a i)"
        using m_anc_via_parent_some[OF Some] .
      thus ?thesis using p_ne_tgt no_anc by blast
    qed
    have rhs_F: "\<not> m_ancestor (A[n]) 0 (idx_B_in_expansion A b j)
                                          (idx_B_in_expansion A b i)"
    proof (cases "m_parent (A[n]) 0 (idx_B_in_expansion A b j)")
      case None
      thus ?thesis using m_anc_via_parent_none by metis
    next
      case (Some p)
      have p_lt: "p < idx_B_in_expansion A b 0"
        using outB Some by simp
      have tgt_ge: "idx_B_in_expansion A b 0 \<le> idx_B_in_expansion A b i"
        unfolding idx_B_in_expansion_def by simp
      have p_ne_tgt: "p \<noteq> idx_B_in_expansion A b i"
        using p_lt tgt_ge by linarith
      have no_anc: "\<not> m_ancestor (A[n]) 0 p (idx_B_in_expansion A b i)"
      proof
        assume "m_ancestor (A[n]) 0 p (idx_B_in_expansion A b i)"
        hence "idx_B_in_expansion A b i < p" by (rule m_ancestor_target_lt)
        thus False using p_lt tgt_ge by linarith
      qed
      have iff_via: "m_ancestor (A[n]) 0 (idx_B_in_expansion A b j)
                                          (idx_B_in_expansion A b i)
                  \<longleftrightarrow> p = idx_B_in_expansion A b i
                       \<or> m_ancestor (A[n]) 0 p (idx_B_in_expansion A b i)"
        using m_anc_via_parent_some[OF Some] .
      thus ?thesis using p_ne_tgt no_anc by blast
    qed
    show ?thesis using lhs_F rhs_F by blast
  next
    case False
    let ?p = "last ?S"
    have p_in: "?p \<in> set ?S" using last_in_set[OF False] .
    have p_lt_j: "?p < j" using p_in by auto
    have p_lt_l1: "?p < l1 A" using p_lt_j j_lt' by linarith
    have mpA: "m_parent (A[n]) 0 (idx_B_in_expansion A a j)
             = Some (idx_B_in_expansion A a ?p)"
      using m_parent_AEn_zero_idx_B_within_block_when_t_zero
            [OF A_BMS A_ne b0 mp0 a_le j_lt' False] .
    have mpB: "m_parent (A[n]) 0 (idx_B_in_expansion A b j)
             = Some (idx_B_in_expansion A b ?p)"
      using m_parent_AEn_zero_idx_B_within_block_when_t_zero
            [OF A_BMS A_ne b0 mp0 b_le j_lt' False] .
    have lhs_iff: "m_ancestor (A[n]) 0 (idx_B_in_expansion A a j)
                                        (idx_B_in_expansion A a i)
                \<longleftrightarrow> idx_B_in_expansion A a ?p = idx_B_in_expansion A a i
                  \<or> m_ancestor (A[n]) 0 (idx_B_in_expansion A a ?p)
                                          (idx_B_in_expansion A a i)"
      using m_anc_via_parent_some[OF mpA] .
    have rhs_iff: "m_ancestor (A[n]) 0 (idx_B_in_expansion A b j)
                                        (idx_B_in_expansion A b i)
                \<longleftrightarrow> idx_B_in_expansion A b ?p = idx_B_in_expansion A b i
                  \<or> m_ancestor (A[n]) 0 (idx_B_in_expansion A b ?p)
                                          (idx_B_in_expansion A b i)"
      using m_anc_via_parent_some[OF mpB] .
    show ?thesis
    proof (cases "i = ?p")
      case True
      have eqA: "idx_B_in_expansion A a ?p = idx_B_in_expansion A a i"
        using True by simp
      have eqB: "idx_B_in_expansion A b ?p = idx_B_in_expansion A b i"
        using True by simp
      show ?thesis using lhs_iff rhs_iff eqA eqB by blast
    next
      case False
      hence i_ne_p: "i \<noteq> ?p" .
      have neqA: "idx_B_in_expansion A a ?p \<noteq> idx_B_in_expansion A a i"
        using i_ne_p unfolding idx_B_in_expansion_def by simp
      have neqB: "idx_B_in_expansion A b ?p \<noteq> idx_B_in_expansion A b i"
        using i_ne_p unfolding idx_B_in_expansion_def by simp
      show ?thesis
      proof (cases "i < ?p")
        case True
        have IH_at: "m_ancestor (A[n]) 0 (idx_B_in_expansion A a ?p)
                                          (idx_B_in_expansion A a i)
                   \<longleftrightarrow> m_ancestor (A[n]) 0 (idx_B_in_expansion A b ?p)
                                          (idx_B_in_expansion A b i)"
          using IH[OF p_lt_j i_lt' p_lt_l1 True] .
        show ?thesis using lhs_iff rhs_iff IH_at neqA neqB by blast
      next
        case False
        hence p_lt_i: "?p < i" using i_ne_p by linarith
        have no_ancA: "\<not> m_ancestor (A[n]) 0 (idx_B_in_expansion A a ?p)
                                                (idx_B_in_expansion A a i)"
        proof
          assume "m_ancestor (A[n]) 0 (idx_B_in_expansion A a ?p)
                                       (idx_B_in_expansion A a i)"
          hence "idx_B_in_expansion A a i < idx_B_in_expansion A a ?p"
            by (rule m_ancestor_target_lt)
          thus False using p_lt_i unfolding idx_B_in_expansion_def by simp
        qed
        have no_ancB: "\<not> m_ancestor (A[n]) 0 (idx_B_in_expansion A b ?p)
                                                (idx_B_in_expansion A b i)"
        proof
          assume "m_ancestor (A[n]) 0 (idx_B_in_expansion A b ?p)
                                       (idx_B_in_expansion A b i)"
          hence "idx_B_in_expansion A b i < idx_B_in_expansion A b ?p"
            by (rule m_ancestor_target_lt)
          thus False using p_lt_i unfolding idx_B_in_expansion_def by simp
        qed
        show ?thesis using lhs_iff rhs_iff neqA neqB no_ancA no_ancB by blast
      qed
    qed
  qed
qed

text \<open>
  Step lemma for clause (ii): assumes IH (= full lemma_2_5_at at k' < k)
  and proves clause (ii) at level k. Per dependency matrix, (ii) at k
  uses only IH (no other clause at same k).
\<close>

lemma lemma_2_5_ii_clause_step:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
  shows "lemma_2_5_ii_clause A n k"
proof (cases n)
  case 0
  \<comment> \<open>\<open>n = 0\<close>: \<open>idx_B(0, j) = idx_B(0, j)\<close> on both sides; the
      equivalence is reflexivity. Dispatch via @{thm lemma_2_5_at_n_zero}.\<close>
  show ?thesis
    using lemma_2_5_at_n_zero[OF A_ne, of k] \<open>n = 0\<close>
    unfolding lemma_2_5_at_def by simp
next
  case (Suc n')
  show ?thesis
  proof (cases "b0_start A")
    case None
    \<comment> \<open>\<open>b0_start A = None\<close>: \<open>l1 A = 0\<close>, all clause (ii)
        universals vacuous. Dispatch via @{thm lemma_2_5_at_no_b0}.\<close>
    show ?thesis
      using lemma_2_5_at_no_b0[OF A_ne None, of n k]
      unfolding lemma_2_5_at_def by simp
  next
    case (Some s)
    \<comment> \<open>Substantive case: \<open>n \<ge> 1 \<and> b0_start A = Some s\<close>.
        Per dependency matrix, (ii) at \<open>k\<close> uses only IH
        (no other clause at same \<open>k\<close>).\<close>
    show ?thesis
      unfolding lemma_2_5_ii_clause_def
    proof (intro allI impI)
      fix i j
      assume H: "i < l1 A \<and> j < l1 A"
      hence i_lt: "i < l1 A" and j_lt: "j < l1 A" by simp+
      show "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_B_in_expansion A 0 i)
          \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_B_in_expansion A n i)"
      proof (cases "i < j")
        case False
        \<comment> \<open>\<open>i \<ge> j\<close>: by @{thm m_ancestor_target_lt}, a chain
            \<open>m_ancestor _ _ src target\<close> requires \<open>target < src\<close>.
            Here \<open>target = idx_B(_, i)\<close>, \<open>src = idx_B(_, j)\<close>;
            \<open>idx_B\<close> is monotone in its 2nd argument, so \<open>i \<ge> j\<close>
            gives \<open>target \<ge> src\<close>, contradicting the chain.\<close>
        have not_lt: "\<not> i < j" using False .
        have lhs_F: "\<not> m_ancestor (A[n]) k (idx_B_in_expansion A 0 j)
                                              (idx_B_in_expansion A 0 i)"
        proof
          assume "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j)
                                       (idx_B_in_expansion A 0 i)"
          hence "idx_B_in_expansion A 0 i < idx_B_in_expansion A 0 j"
            by (rule m_ancestor_target_lt)
          thus False unfolding idx_B_in_expansion_def using not_lt by simp
        qed
        have rhs_F: "\<not> m_ancestor (A[n]) k (idx_B_in_expansion A n j)
                                              (idx_B_in_expansion A n i)"
        proof
          assume "m_ancestor (A[n]) k (idx_B_in_expansion A n j)
                                       (idx_B_in_expansion A n i)"
          hence "idx_B_in_expansion A n i < idx_B_in_expansion A n j"
            by (rule m_ancestor_target_lt)
          thus False unfolding idx_B_in_expansion_def using not_lt by simp
        qed
        show ?thesis using lhs_F rhs_F by blast
      next
        case True
        hence i_lt_j: "i < j" .
        \<comment> \<open>\<open>i < j\<close>: substantive case. Split on \<open>k = 0\<close>
            (base, no IH) vs \<open>k = Suc k'\<close> (use IH at \<open>k'\<close>).\<close>
        show ?thesis
        proof (cases k)
          case 0
          \<comment> \<open>Base \<open>k = 0\<close> with \<open>i < j\<close> requires \<open>l1 A \<ge> 2\<close>
              (from \<open>i < j < l1\<close>). Split further on \<open>max_parent_level\<close>
              to use uniform bumping (\<open>k=0 < t\<close>) or no bumping
              (\<open>t=0\<close>, no ascending).\<close>
          show ?thesis
          proof (cases "max_parent_level A")
            case None
            have "b0_start A = None" using None unfolding b0_start_def by simp
            with Some show ?thesis by simp
          next
            case (Some t)
            show ?thesis
            proof (cases "0 < t")
              case True
              \<comment> \<open>\<open>k=0 < t\<close>: all B_0 cols ascending at row 0 via
                  @{thm BMS_all_B0_ascending_below_t}, uniform bumping.
                  \<open>\<sigma>\<close>-equivariance + chain induction.\<close>
              show ?thesis sorry
            next
              case False
              hence t_eq: "t = 0" by simp
              \<comment> \<open>\<open>t = 0\<close>: \<open>k=0 \<ge> t\<close>, no ascending, no bumping.
                  Dispatch via @{thm m_anc_zero_idx_B_in_block_shift_when_t_zero}
                  (block-shift invariance at row 0).\<close>
              have mp_zero: "max_parent_level A = Some 0"
                using \<open>max_parent_level A = Some t\<close> t_eq by simp
              show ?thesis
                using m_anc_zero_idx_B_in_block_shift_when_t_zero
                        [OF A_BMS A_ne \<open>b0_start A = Some s\<close> mp_zero
                           order.refl le0
                           i_lt j_lt i_lt_j]
                      \<open>k = 0\<close>
                by simp
            qed
          qed
        next
          case (Suc k')
          \<comment> \<open>IH gives full \<open>lemma_2_5_at A n k'\<close>.
              Split further on \<open>max_parent_level A\<close> and \<open>k\<close> vs \<open>t\<close>.\<close>
          have IH_at_k': "lemma_2_5_at A n k'"
            using IH \<open>k = Suc k'\<close> by simp
          show ?thesis
          proof (cases "max_parent_level A")
            case None
            \<comment> \<open>\<open>max_parent_level = None\<close>: but \<open>b0_start = Some s\<close>
                forces it to be \<open>Some _\<close>. Contradiction.\<close>
            have "b0_start A = None" using None unfolding b0_start_def by simp
            with Some show ?thesis by simp
          next
            case (Some t)
            \<comment> \<open>\<open>max_parent_level = Some t\<close>. Split on \<open>k < t\<close>
                (active level, uniform bumping) vs \<open>k \<ge> t\<close>
                (inactive, no bumping).\<close>
            show ?thesis
            proof (cases "k < t")
              case True
              hence k_lt_t: "k < t" .
              \<comment> \<open>\<open>k < t\<close>: substantive. By
                  @{thm elem_expansion_B_lt_invariant_in_block} the
                  strict-less relation at row \<open>k\<close> between B-block
                  columns is invariant in the block index. Combined
                  with IH (ii) at \<open>k'\<close> (for m_anc-at-\<open>k'\<close>
                  constraint) and chain-length induction, the
                  m_ancestor equivalence follows.\<close>
              show ?thesis sorry
            next
              case False
              hence k_ge_t: "t \<le> k" by simp
              \<comment> \<open>\<open>k \<ge> t\<close>: no ascending, bumping=0 at row k.
                  Values unchanged, strict-less invariant trivially.
                  Combined with IH (ii) at \<open>k'\<close>, chain corresponds.\<close>
              show ?thesis sorry
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>
  Step lemma for clause (iii): assumes IH (= full lemma_2_5_at at k' < k)
  AND clause (ii) at same level k (per dependency matrix).
\<close>

lemma lemma_2_5_iii_clause_step:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
  shows "lemma_2_5_iii_clause A n k"
proof (cases n)
  case 0
  \<comment> \<open>\<open>n = 0\<close>: clause (iii) premise requires \<open>n > 0\<close>, vacuous.\<close>
  show ?thesis using \<open>n = 0\<close>
    unfolding lemma_2_5_iii_clause_def by simp
next
  case (Suc n')
  show ?thesis
  proof (cases "b0_start A")
    case None
    \<comment> \<open>\<open>b0_start = None\<close>: \<open>max_parent_level A = None\<close> by
        @{thm b0_start_None_imp_max_parent_level_None}, clause (iii)'s
        premise demands \<open>max_parent_level A = Some _\<close>, vacuous.\<close>
    show ?thesis
      using lemma_2_5_at_no_b0[OF A_ne None, of n k]
      unfolding lemma_2_5_at_def by simp
  next
    case (Some s)
    \<comment> \<open>Substantive case. Per matrix, (iii) at \<open>k\<close> uses
        IH (at \<open>k'<k\<close>) and (ii) at same \<open>k\<close>. Sub-cases on
        \<open>max_parent_level\<close> and \<open>k\<close> vs \<open>m\<^sub>0\<close>.\<close>
    show ?thesis
    proof (cases "max_parent_level A")
      case None
      show ?thesis unfolding lemma_2_5_iii_clause_def using None by simp
    next
      case (Some m\<^sub>0)
      \<comment> \<open>Substantive: split on \<open>k < m\<^sub>0\<close> (active) vs
          \<open>k \<ge> m\<^sub>0\<close> (vacuous via @{thm lemma_2_5_iii_clause_when_k_ge_m0}).\<close>
      show ?thesis
      proof (cases "k < m\<^sub>0")
        case False
        have all_ge: "\<forall>m'. max_parent_level A = Some m' \<longrightarrow> m' \<le> k"
          using Some False by simp
        show ?thesis by (rule lemma_2_5_iii_clause_when_k_ge_m0[OF all_ge])
      next
        case True
        \<comment> \<open>Truly substantive: \<open>k < m\<^sub>0\<close>. Hunter's proof uses
            (ii) at k for chain translation, plus IH for chain at k-1.\<close>
        show ?thesis sorry
      qed
    qed
  qed
qed

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
        \<open>n \<ge> 1 \<and> b0_start A = Some s\<close>. Structured with explicit
        \<open>nat_less_induct\<close> on \<open>k\<close> so that the IH at \<open>k' < k\<close>
        is available for clauses (i)--(v).\<close>
    show ?thesis using assms
    proof (induct k rule: nat_less_induct)
      case (1 k)
      \<comment> \<open>IH: \<open>\<forall> k' < k. lemma_2_5_at A n k'\<close>; conclude
          \<open>lemma_2_5_at A n k\<close> by Hunter's order (ii) (iii) (iv)
          (i) (v) within the inductive step.\<close>
      show ?case sorry
    qed
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
