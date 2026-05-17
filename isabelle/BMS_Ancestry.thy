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
  When \<open>max_parent_level A = Some t\<close> with \<open>0 < t\<close> and \<open>n \<ge> 1\<close>,
  the pre-strip array \<open>G_block A @ Bs_concat A n\<close> has at least
  one positive entry at row 0 (specifically,
  \<open>bump_col A 0 1 ! 0 = (A ! last_col_idx A) ! 0\<close> via
  @{thm bump_col_lt_step}, and the latter is positive because
  \<open>elem A s 0 < elem A (last_col_idx A) 0\<close> via the level-0
  ancestor chain), so \<open>keep_of > 0\<close>.
\<close>

lemma keep_of_pre_strip_pos_of_t_pos_and_n_pos:
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
      and n_pos: "0 < n"
  shows "0 < keep_of (G_block A @ Bs_concat A n)"
proof -
  let ?P = "G_block A @ Bs_concat A n"
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have s_lt_arr: "s < arr_len A" using s_lt_last last_lt_arr by simp
  have last_lt_arr2: "last_col_idx A < arr_len A" using last_lt_arr .
  have l1_pos: "0 < l1 A"
    using b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
  have height_pos: "0 < height A"
    using max_parent_level_lt[OF mp] t_pos by linarith
  have len_As: "length (A ! s) = height A"
    using length_col_arr[OF is_arr A_ne s_lt_arr] .
  have s_len_pos: "0 < length (A ! s)" using len_As height_pos by simp

  \<comment> \<open>\<open>bump_col A 0 1 ! 0 = (A ! last_col_idx A) ! 0\<close>\<close>
  have bump_eq: "bump_col A 0 1 ! 0 = (A ! last_col_idx A) ! 0"
    using bump_col_value_eq_below[OF b0 mp A_ne t_pos s_len_pos] .

  \<comment> \<open>\<open>(A ! last_col_idx A) ! 0 > 0\<close> from the level-0 ancestor chain
      \<open>m_ancestor A 0 (last_col_idx A) s\<close>.\<close>
  have parent: "m_parent A t (last_col_idx A) = Some s"
    using b0 mp unfolding b0_start_def by simp
  have m_anc_t: "m_ancestor A t (last_col_idx A) s" using parent by simp
  have m_anc_0: "m_ancestor A 0 (last_col_idx A) s"
    using m_ancestor_mono[OF less_imp_le_nat[OF t_pos] m_anc_t] .
  have base_lt: "elem A s 0 < elem A (last_col_idx A) 0"
    using m_ancestor_elem_lt[OF m_anc_0] .
  have last_pos: "0 < (A ! last_col_idx A) ! 0"
    using base_lt unfolding elem_def by simp
  have bump_pos: "0 < bump_col A 0 1 ! 0" using bump_eq last_pos by simp

  \<comment> \<open>Locate \<open>bump_col A 0 1\<close> in \<open>?P\<close> at position \<open>idx_B(1,0)\<close>.\<close>
  have one_le_n: "1 \<le> n" using n_pos by simp
  have P_at_idx: "?P ! (idx_B_in_expansion A 1 0) = bump_col A 0 1"
  proof -
    have "?P ! (idx_B_in_expansion A 1 0) = Bi_block A 1 ! 0"
      using pre_strip_nth_B[OF one_le_n l1_pos] .
    moreover have "Bi_block A 1 ! 0 = bump_col A 0 1"
      unfolding Bi_block_def Let_def using l1_pos unfolding l1_def by simp
    ultimately show ?thesis by simp
  qed

  have len_P: "length ?P = l0 A + Suc n * l1 A"
    by (simp add: l0_def l1_def length_Bs_concat)
  have idx_lt_P: "idx_B_in_expansion A 1 0 < length ?P"
  proof -
    have "idx_B_in_expansion A 1 0 = l0 A + l1 A"
      unfolding idx_B_in_expansion_def by simp
    also have "\<dots> < l0 A + Suc n * l1 A"
      using l1_pos n_pos by simp
    finally show ?thesis using len_P by simp
  qed
  have P_ne: "?P \<noteq> []" using idx_lt_P by auto
  have col_in: "bump_col A 0 1 \<in> set ?P"
    using P_at_idx idx_lt_P nth_mem by metis

  \<comment> \<open>All columns of \<open>?P\<close> have length \<open>= height A\<close>.\<close>
  have all_A: "\<forall>c \<in> set A. length c = height A"
    using is_arr unfolding is_array_def by blast
  have all_G: "\<forall>c \<in> set (G_block A). length c = height A"
    using G_block_subset_A all_A by blast
  have all_Bs: "\<forall>c \<in> set (Bs_concat A n). length c = height A"
    using Bs_concat_uniform[OF is_arr A_ne] .
  have P_cols_len: "\<forall>c \<in> set ?P. length c = height A"
    using all_G all_Bs by auto
  have hd_in: "hd ?P \<in> set ?P" using P_ne by (cases ?P) auto
  have hd_len: "length (hd ?P) = height A" using P_cols_len hd_in by blast
  have height_P_pos: "0 < height ?P"
    using P_ne hd_len height_pos by (cases ?P) auto

  show ?thesis
  proof (rule ccontr)
    assume "\<not> 0 < keep_of ?P"
    hence keep_zero: "keep_of ?P \<le> 0" by simp
    have "bump_col A 0 1 ! 0 = 0"
      using keep_of_row_zero[OF keep_zero height_P_pos col_in] .
    thus False using bump_pos by simp
  qed
qed

text \<open>
  Within-block characterization of @{term m_parent} at row 0 when
  \<open>0 < t = max_parent_level A\<close>: under uniform bumping at row 0
  (via @{thm bump_col_uniform_k_lt_t}), the strict-less relation
  between B-columns at row 0 is invariant in the block index
  (@{thm elem_expansion_B_lt_invariant_in_block}). So if the
  block-0 filter \<open>?S\<close> is nonempty, the \<open>m_parent\<close> of any block
  \<open>c\<close>'s \<open>j\<close>-th column at row 0 lands at \<open>idx_B(c, last ?S)\<close>.
\<close>

lemma m_parent_AEn_idx_B_within_block_at_row_zero_when_0_lt_t:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
      and n_pos: "0 < n"
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
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have height_pos: "0 < height A"
    using max_parent_level_lt[OF mp] t_pos by linarith
  have keep_pos: "0 < keep_of (G_block A @ Bs_concat A n)"
    using keep_of_pre_strip_pos_of_t_pos_and_n_pos[OF A_BMS A_ne b0 mp t_pos n_pos] .
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have col_len_x: "\<And>x. x < l1 A \<Longrightarrow> 0 < length (A ! (s + x))"
  proof -
    fix x assume x_lt: "x < l1 A"
    have x_arr: "s + x < arr_len A"
    proof -
      have "x < last_col_idx A - s"
        using x_lt b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
      hence "s + x < last_col_idx A" by linarith
      thus ?thesis using last_lt_arr by linarith
    qed
    show "0 < length (A ! (s + x))"
      using length_col_arr[OF is_arr A_ne x_arr] height_pos by simp
  qed
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
    fix x assume x_in: "x \<in> set [0..<j]"
    hence x_lt_j: "x < j" by simp
    hence x_lt_l1: "x < l1 A" using j_lt by linarith
    have idxBc_eq: "x + ?Cstart = idx_B_in_expansion A c x"
      unfolding idx_B_in_expansion_def by simp
    have x_col_pos: "0 < length (A ! (s + x))" using x_lt_l1 col_len_x by simp
    have j_col_pos: "0 < length (A ! (s + j))" using j_lt col_len_x by simp
    have lt_invar:
      "(elem (A[n]) (idx_B_in_expansion A c x) 0
          < elem (A[n]) (idx_B_in_expansion A c j) 0)
       \<longleftrightarrow>
       (elem (A[n]) (idx_B_in_expansion A 0 x) 0
          < elem (A[n]) (idx_B_in_expansion A 0 j) 0)"
      using elem_expansion_B_lt_invariant_in_block
              [OF A_BMS A_ne b0 mp t_pos c_le le0 j_lt x_lt_l1
                  keep_pos j_col_pos x_col_pos] by simp
    show "(elem (A[n]) (x + ?Cstart) 0 < ?vi)
       \<longleftrightarrow> (elem (A[n]) (idx_B_in_expansion A 0 x) 0
            < elem (A[n]) (idx_B_in_expansion A 0 j) 0)"
      using idxBc_eq lt_invar by simp
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

text \<open>
  Outside-block characterization of @{term m_parent} at row 0 when
  \<open>0 < t\<close>: if the block-0 filter \<open>?S\<close> is empty, then no in-block
  candidate satisfies the filter for any block \<open>c\<close> either, so all
  candidates have index \<open>< idx_B(c, 0)\<close> (i.e., they lie in the
  G-block or in earlier B-blocks).
\<close>

lemma m_parent_AEn_idx_B_outside_block_at_row_zero_when_0_lt_t:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
      and n_pos: "0 < n"
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
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have height_pos: "0 < height A"
    using max_parent_level_lt[OF mp] t_pos by linarith
  have keep_pos: "0 < keep_of (G_block A @ Bs_concat A n)"
    using keep_of_pre_strip_pos_of_t_pos_and_n_pos[OF A_BMS A_ne b0 mp t_pos n_pos] .
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have col_len_x: "\<And>x. x < l1 A \<Longrightarrow> 0 < length (A ! (s + x))"
  proof -
    fix x assume x_lt: "x < l1 A"
    have x_arr: "s + x < arr_len A"
    proof -
      have "x < last_col_idx A - s"
        using x_lt b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
      hence "s + x < last_col_idx A" by linarith
      thus ?thesis using last_lt_arr by linarith
    qed
    show "0 < length (A ! (s + x))"
      using length_col_arr[OF is_arr A_ne x_arr] height_pos by simp
  qed
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
      have p_as_idxBc: "p = idx_B_in_expansion A c j'"
        using p_eq unfolding idx_B_in_expansion_def by simp
      have x_col_pos: "0 < length (A ! (s + j'))" using j'_lt_l1 col_len_x by simp
      have j_col_pos: "0 < length (A ! (s + j))" using j_lt col_len_x by simp
      have lt_invar:
        "(elem (A[n]) (idx_B_in_expansion A c j') 0
            < elem (A[n]) (idx_B_in_expansion A c j) 0)
         \<longleftrightarrow>
         (elem (A[n]) (idx_B_in_expansion A 0 j') 0
            < elem (A[n]) (idx_B_in_expansion A 0 j) 0)"
        using elem_expansion_B_lt_invariant_in_block
                [OF A_BMS A_ne b0 mp t_pos c_le le0 j_lt j'_lt_l1
                    keep_pos j_col_pos x_col_pos] by simp
      have v_lt2: "elem (A[n]) (idx_B_in_expansion A c j') 0
                 < elem (A[n]) (idx_B_in_expansion A c j) 0"
        using v_lt p_as_idxBc by simp
      have block0_lt: "elem (A[n]) (idx_B_in_expansion A 0 j') 0
                     < elem (A[n]) (idx_B_in_expansion A 0 j) 0"
        using v_lt2 lt_invar by simp
      have "j' \<in> set [j' \<leftarrow> [0..<j]. elem (A[n]) (idx_B_in_expansion A 0 j') 0
                              < elem (A[n]) (idx_B_in_expansion A 0 j) 0]"
        using j'_lt_j block0_lt by auto
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

text \<open>
  Block-shift invariance of @{term m_ancestor} at row 0 when
  \<open>0 < t\<close>: a chain induction on \<open>j\<close> using the within / outside
  characterizations above, mirroring the analogous
  @{thm m_anc_zero_idx_B_in_block_shift_when_t_zero} for the
  \<open>t = 0\<close> case.
\<close>

lemma m_anc_idx_B_in_block_shift_at_row_zero_when_0_lt_t:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
      and n_pos: "0 < n"
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
      using m_parent_AEn_idx_B_outside_block_at_row_zero_when_0_lt_t
            [OF A_BMS A_ne b0 mp t_pos n_pos a_le j_lt' True] .
    have outB: "(case m_parent (A[n]) 0 (idx_B_in_expansion A b j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A b 0)"
      using m_parent_AEn_idx_B_outside_block_at_row_zero_when_0_lt_t
            [OF A_BMS A_ne b0 mp t_pos n_pos b_le j_lt' True] .
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
      using m_parent_AEn_idx_B_within_block_at_row_zero_when_0_lt_t
            [OF A_BMS A_ne b0 mp t_pos n_pos a_le j_lt' False] .
    have mpB: "m_parent (A[n]) 0 (idx_B_in_expansion A b j)
             = Some (idx_B_in_expansion A b ?p)"
      using m_parent_AEn_idx_B_within_block_at_row_zero_when_0_lt_t
            [OF A_BMS A_ne b0 mp t_pos n_pos b_le j_lt' False] .
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
  Stronger keep_of bound: when \<open>max_parent_level A = Some t\<close> and
  \<open>n \<ge> 1\<close>, every row \<open>m < t\<close> has at least one positive entry
  in the pre-strip array (specifically,
  \<open>bump_col A 0 1 ! m = (A ! last_col_idx A) ! m\<close> for \<open>m < t\<close>
  via @{thm bump_col_value_eq_below}, and \<open>(A ! last_col_idx A) ! m
  > 0\<close> via the level-\<open>m\<close> ancestor chain that always exists for
  \<open>m < t\<close>). Hence the trim point cannot cross row \<open>t - 1\<close>,
  giving \<open>t \<le> keep_of\<close>.
\<close>

lemma keep_of_pre_strip_ge_max_parent_level:
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and n_pos: "0 < n"
  shows "t \<le> keep_of (G_block A @ Bs_concat A n)"
proof (rule ccontr)
  assume "\<not> t \<le> keep_of (G_block A @ Bs_concat A n)"
  hence k_lt: "keep_of (G_block A @ Bs_concat A n) < t" by simp
  let ?P = "G_block A @ Bs_concat A n"
  let ?h = "keep_of ?P"
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have s_lt_arr: "s < arr_len A" using s_lt_last last_lt_arr by simp
  have l1_pos: "0 < l1 A"
    using b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
  have h_lt_t: "?h < t" using k_lt .
  have t_lt_H: "t < height A" using max_parent_level_lt[OF mp] .
  have h_lt_HA: "?h < height A" using h_lt_t t_lt_H by linarith
  \<comment> \<open>\<open>length (A ! s) = height A\<close>\<close>
  have len_As: "length (A ! s) = height A"
    using length_col_arr[OF is_arr A_ne s_lt_arr] .
  have h_lt_len: "?h < length (A ! s)" using h_lt_HA len_As by simp
  \<comment> \<open>\<open>bump_col A 0 1 ! ?h = (A ! last_col_idx A) ! ?h\<close>\<close>
  have bump_eq: "bump_col A 0 1 ! ?h = (A ! last_col_idx A) ! ?h"
    using bump_col_value_eq_below[OF b0 mp A_ne h_lt_t h_lt_len] .
  \<comment> \<open>\<open>(A ! last_col_idx A) ! ?h > 0\<close> from level-h ancestor chain\<close>
  have parent_t: "m_parent A t (last_col_idx A) = Some s"
    using b0 mp unfolding b0_start_def by simp
  have m_anc_t: "m_ancestor A t (last_col_idx A) s" using parent_t by simp
  have m_anc_h: "m_ancestor A ?h (last_col_idx A) s"
    using m_ancestor_mono[OF less_imp_le_nat[OF h_lt_t] m_anc_t] .
  have base_lt: "elem A s ?h < elem A (last_col_idx A) ?h"
    using m_ancestor_elem_lt[OF m_anc_h] .
  have last_pos: "0 < (A ! last_col_idx A) ! ?h"
    using base_lt unfolding elem_def by simp
  have bump_pos: "0 < bump_col A 0 1 ! ?h" using bump_eq last_pos by simp
  \<comment> \<open>\<open>bump_col A 0 1\<close> lives in pre-strip at position \<open>idx_B 1 0\<close>.\<close>
  have one_le_n: "1 \<le> n" using n_pos by simp
  have P_at: "?P ! (idx_B_in_expansion A 1 0) = bump_col A 0 1"
  proof -
    have "?P ! (idx_B_in_expansion A 1 0) = Bi_block A 1 ! 0"
      using pre_strip_nth_B[OF one_le_n l1_pos] .
    moreover have "Bi_block A 1 ! 0 = bump_col A 0 1"
      unfolding Bi_block_def Let_def using l1_pos unfolding l1_def by simp
    ultimately show ?thesis by simp
  qed
  have len_P: "length ?P = l0 A + Suc n * l1 A"
    by (simp add: l0_def l1_def length_Bs_concat)
  have idx_lt_P: "idx_B_in_expansion A 1 0 < length ?P"
  proof -
    have "idx_B_in_expansion A 1 0 = l0 A + l1 A"
      unfolding idx_B_in_expansion_def by simp
    also have "\<dots> < l0 A + Suc n * l1 A"
      using l1_pos n_pos by simp
    finally show ?thesis using len_P by simp
  qed
  have col_in: "bump_col A 0 1 \<in> set ?P"
    using P_at idx_lt_P nth_mem by metis
  \<comment> \<open>\<open>height ?P = height A\<close> via uniform col length.\<close>
  have P_ne: "?P \<noteq> []" using idx_lt_P by auto
  have all_A: "\<forall>c \<in> set A. length c = height A"
    using is_arr unfolding is_array_def by blast
  have all_G: "\<forall>c \<in> set (G_block A). length c = height A"
    using G_block_subset_A all_A by blast
  have all_Bs: "\<forall>c \<in> set (Bs_concat A n). length c = height A"
    using Bs_concat_uniform[OF is_arr A_ne] .
  have all_P: "\<forall>c \<in> set ?P. length c = height A"
    using all_G all_Bs by auto
  have hd_in: "hd ?P \<in> set ?P" using P_ne by (cases ?P) auto
  have hd_len: "length (hd ?P) = height A" using all_P hd_in by blast
  have height_P_eq: "height ?P = height A" using P_ne hd_len by (cases ?P) auto
  have h_lt_HP: "?h < height ?P" using h_lt_HA height_P_eq by simp
  \<comment> \<open>By definition of keep_of, row \<open>?h\<close> is in the zero zone.\<close>
  have h_le_h: "?h \<le> ?h" by simp
  have row_zero: "bump_col A 0 1 ! ?h = 0"
    using keep_of_row_zero[OF h_le_h h_lt_HP col_in] .
  thus False using bump_pos by simp
qed

text \<open>
  Within-block characterization of @{term m_parent} at row \<open>Suc k'\<close>
  when \<open>Suc k' < t = max_parent_level A\<close>. Compared with the row-0
  case, the @{term m_parent} filter now carries an extra
  \<open>m_ancestor A k' query cand\<close> conjunct; the helper takes the
  block-\<open>c\<close>-to-block-0 \<open>m_ancestor\<close> equivalence as a hypothesis
  (\<open>manc_inv\<close>), supplied trivially for \<open>c = 0\<close> and via IH (ii) at
  \<open>k'\<close> for \<open>c = n\<close>.
\<close>

lemma m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_lt_t: "Suc k' < t"
      and n_pos: "0 < n"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and manc_inv: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                                  (idx_B_in_expansion A c x)
                          \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)"
      and S_ne: "[x \<leftarrow> [0..<j].
                    elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                      < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                  \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 x)] \<noteq> []"
  shows "m_parent (A[n]) (Suc k') (idx_B_in_expansion A c j)
       = Some (idx_B_in_expansion A c
            (last [x \<leftarrow> [0..<j].
                    elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                      < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                  \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 x)]))"
proof -
  let ?i = "idx_B_in_expansion A c j"
  let ?Cstart = "idx_B_in_expansion A c 0"
  let ?vi = "elem (A[n]) ?i (Suc k')"
  let ?cands = "[p \<leftarrow> [0..<?i]. elem (A[n]) p (Suc k') < ?vi
                              \<and> m_ancestor (A[n]) k' ?i p]"
  let ?S = "[x \<leftarrow> [0..<j].
              elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
            \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                    (idx_B_in_expansion A 0 x)]"
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have t_pos: "0 < t" using k_lt_t by linarith
  have k_lt_t': "Suc k' < t" using k_lt_t .
  have height_pos: "0 < height A"
    using max_parent_level_lt[OF mp] t_pos by linarith
  have t_le_keep: "t \<le> keep_of (G_block A @ Bs_concat A n)"
    using keep_of_pre_strip_ge_max_parent_level[OF A_BMS A_ne b0 mp n_pos] .
  have keep_pos: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
    using k_lt_t' t_le_keep by linarith
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have col_len_x: "\<And>x. x < l1 A \<Longrightarrow> Suc k' < length (A ! (s + x))"
  proof -
    fix x assume x_lt: "x < l1 A"
    have x_arr: "s + x < arr_len A"
    proof -
      have "x < last_col_idx A - s"
        using x_lt b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
      hence "s + x < last_col_idx A" by linarith
      thus ?thesis using last_lt_arr by linarith
    qed
    have "length (A ! (s + x)) = height A"
      using length_col_arr[OF is_arr A_ne x_arr] .
    moreover have "Suc k' < height A"
      using k_lt_t max_parent_level_lt[OF mp] by linarith
    ultimately show "Suc k' < length (A ! (s + x))" by simp
  qed
  have mp_eq: "m_parent (A[n]) (Suc k') ?i
             = (if ?cands = [] then None else Some (last ?cands))"
    by (simp add: Let_def)
  have i_eq: "?i = ?Cstart + j" unfolding idx_B_in_expansion_def by simp
  have range_split: "[0..<?i] = [0..<?Cstart] @ [?Cstart..<?i]"
    using upt_add_eq_append[OF le0, of ?Cstart j] i_eq by simp
  let ?pre = "filter (\<lambda>p. elem (A[n]) p (Suc k') < ?vi
                       \<and> m_ancestor (A[n]) k' ?i p) [0..<?Cstart]"
  let ?post = "filter (\<lambda>p. elem (A[n]) p (Suc k') < ?vi
                        \<and> m_ancestor (A[n]) k' ?i p) [?Cstart..<?i]"
  have cands_split: "?cands = ?pre @ ?post"
    using range_split by simp
  have post_range: "[?Cstart..<?i] = map (\<lambda>i. i + ?Cstart) [0..<j]"
    using i_eq map_add_upt[of ?Cstart j] by (simp add: add.commute)
  have post_map: "?post = map (\<lambda>i. i + ?Cstart)
                   (filter (\<lambda>i. elem (A[n]) (i + ?Cstart) (Suc k') < ?vi
                              \<and> m_ancestor (A[n]) k' ?i (i + ?Cstart)) [0..<j])"
    using post_range by (simp add: filter_map o_def)
  have filter_cong_eq:
    "filter (\<lambda>i. elem (A[n]) (i + ?Cstart) (Suc k') < ?vi
              \<and> m_ancestor (A[n]) k' ?i (i + ?Cstart)) [0..<j] = ?S"
  proof (rule filter_cong[OF refl])
    fix x assume x_in: "x \<in> set [0..<j]"
    hence x_lt_j: "x < j" by simp
    hence x_lt_l1: "x < l1 A" using j_lt by linarith
    have idxBc_eq: "x + ?Cstart = idx_B_in_expansion A c x"
      unfolding idx_B_in_expansion_def by simp
    have x_col_pos: "Suc k' < length (A ! (s + x))" using x_lt_l1 col_len_x by simp
    have j_col_pos: "Suc k' < length (A ! (s + j))" using j_lt col_len_x by simp
    have zero_le_n: "(0::nat) \<le> n" by simp
    have lt_invar:
      "(elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
          < elem (A[n]) (idx_B_in_expansion A c j) (Suc k'))
       \<longleftrightarrow>
       (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
          < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k'))"
      using elem_expansion_B_lt_invariant_in_block
              [OF A_BMS A_ne b0 mp k_lt_t' c_le zero_le_n j_lt x_lt_l1
                  keep_pos j_col_pos x_col_pos] by simp
    have manc_x: "m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                        (idx_B_in_expansion A c x)
                \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                        (idx_B_in_expansion A 0 x)"
      using manc_inv x_lt_j by blast
    show "(elem (A[n]) (x + ?Cstart) (Suc k') < ?vi
            \<and> m_ancestor (A[n]) k' ?i (x + ?Cstart))
       \<longleftrightarrow>
          (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
              < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
           \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                   (idx_B_in_expansion A 0 x))"
      using idxBc_eq lt_invar manc_x by simp
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

text \<open>
  Outside-block characterization of @{term m_parent} at row
  \<open>Suc k'\<close> when \<open>Suc k' < t\<close>: if the block-0 filter is empty,
  every candidate has index \<open>< idx_B(c, 0)\<close>. Same parameterized
  shape as the within-block version, requires \<open>manc_inv\<close>.
\<close>

lemma m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_lt_t: "Suc k' < t"
      and n_pos: "0 < n"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and manc_inv: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                                  (idx_B_in_expansion A c x)
                          \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)"
      and S_empty: "[x \<leftarrow> [0..<j].
                       elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                         < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                     \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                             (idx_B_in_expansion A 0 x)] = []"
  shows "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A c j) of
             None \<Rightarrow> True
           | Some p \<Rightarrow> p < idx_B_in_expansion A c 0)"
proof -
  let ?i = "idx_B_in_expansion A c j"
  let ?Cstart = "idx_B_in_expansion A c 0"
  let ?vi = "elem (A[n]) ?i (Suc k')"
  let ?cands = "[p \<leftarrow> [0..<?i]. elem (A[n]) p (Suc k') < ?vi
                              \<and> m_ancestor (A[n]) k' ?i p]"
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have t_pos: "0 < t" using k_lt_t by linarith
  have height_pos: "0 < height A"
    using max_parent_level_lt[OF mp] t_pos by linarith
  have t_le_keep: "t \<le> keep_of (G_block A @ Bs_concat A n)"
    using keep_of_pre_strip_ge_max_parent_level[OF A_BMS A_ne b0 mp n_pos] .
  have keep_pos: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
    using k_lt_t t_le_keep by linarith
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have col_len_x: "\<And>x. x < l1 A \<Longrightarrow> Suc k' < length (A ! (s + x))"
  proof -
    fix x assume x_lt: "x < l1 A"
    have x_arr: "s + x < arr_len A"
    proof -
      have "x < last_col_idx A - s"
        using x_lt b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
      hence "s + x < last_col_idx A" by linarith
      thus ?thesis using last_lt_arr by linarith
    qed
    have "length (A ! (s + x)) = height A"
      using length_col_arr[OF is_arr A_ne x_arr] .
    moreover have "Suc k' < height A"
      using k_lt_t max_parent_level_lt[OF mp] by linarith
    ultimately show "Suc k' < length (A ! (s + x))" by simp
  qed
  have mp_eq: "m_parent (A[n]) (Suc k') ?i
             = (if ?cands = [] then None else Some (last ?cands))"
    by (simp add: Let_def)
  have all_lt: "\<forall>p \<in> set ?cands. p < ?Cstart"
  proof
    fix p assume p_in: "p \<in> set ?cands"
    have p_lt_i: "p < ?i" using p_in by auto
    have v_lt: "elem (A[n]) p (Suc k') < ?vi" using p_in by simp
    have manc_p: "m_ancestor (A[n]) k' ?i p" using p_in by simp
    show "p < ?Cstart"
    proof (rule ccontr)
      assume "\<not> p < ?Cstart"
      hence p_ge: "?Cstart \<le> p" by simp
      define x where "x = p - ?Cstart"
      have p_eq: "p = ?Cstart + x" using p_ge x_def by simp
      have x_lt_j: "x < j"
      proof -
        have "?Cstart + x < ?Cstart + j"
          using p_eq p_lt_i unfolding idx_B_in_expansion_def by simp
        thus ?thesis by simp
      qed
      have x_lt_l1: "x < l1 A" using x_lt_j j_lt by linarith
      have p_as_idxBc: "p = idx_B_in_expansion A c x"
        using p_eq unfolding idx_B_in_expansion_def by simp
      have x_col_pos: "Suc k' < length (A ! (s + x))" using x_lt_l1 col_len_x by simp
      have j_col_pos: "Suc k' < length (A ! (s + j))" using j_lt col_len_x by simp
      have zero_le_n: "(0::nat) \<le> n" by simp
      have lt_invar:
        "(elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
            < elem (A[n]) (idx_B_in_expansion A c j) (Suc k'))
         \<longleftrightarrow>
         (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
            < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k'))"
        using elem_expansion_B_lt_invariant_in_block
                [OF A_BMS A_ne b0 mp k_lt_t c_le zero_le_n j_lt x_lt_l1
                    keep_pos j_col_pos x_col_pos] by simp
      have v_lt2: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
                 < elem (A[n]) (idx_B_in_expansion A c j) (Suc k')"
        using v_lt p_as_idxBc by simp
      have block0_lt: "elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                     < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')"
        using v_lt2 lt_invar by simp
      have manc_at_c: "m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                              (idx_B_in_expansion A c x)"
        using manc_p p_as_idxBc by simp
      have manc_at_0: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                              (idx_B_in_expansion A 0 x)"
        using manc_at_c manc_inv x_lt_j by blast
      have x_in_upt: "x \<in> set [0..<j]" using x_lt_j by simp
      have all_neg: "\<forall>y \<in> set [0..<j]. \<not> (elem (A[n]) (idx_B_in_expansion A 0 y) (Suc k')
                            < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                          \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 y))"
        using S_empty filter_empty_conv by metis
      have neg_x: "\<not> (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                       < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                     \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                             (idx_B_in_expansion A 0 x))"
        using all_neg x_in_upt by blast
      thus False using block0_lt manc_at_0 by blast
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

text \<open>
  Block-shift invariance of @{term m_ancestor} at row \<open>Suc k'\<close>
  when \<open>Suc k' < t\<close>: chain induction on \<open>j\<close> applied at \<open>c = 0\<close>
  (trivial manc_inv) and \<open>c = n\<close> (manc_inv from IH (ii) at \<open>k'\<close>).
\<close>

lemma m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_lt_t: "Suc k' < t"
      and n_pos: "0 < n"
      and IH_ii_kp: "lemma_2_5_ii_clause A n k'"
      and i_lt: "i < l1 A"
      and j_lt: "j < l1 A"
      and i_lt_j: "i < j"
  shows "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j) (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j) (idx_B_in_expansion A n i)"
  using i_lt j_lt i_lt_j
proof (induct j arbitrary: i rule: less_induct)
  case (less j)
  note IH_chain = less.hyps
  note i_lt' = less.prems(1)
  note j_lt' = less.prems(2)
  note i_lt_j' = less.prems(3)
  let ?S = "[x \<leftarrow> [0..<j].
              elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
            \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                    (idx_B_in_expansion A 0 x)]"
  have manc_inv_0: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)
                          \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)"
    by simp
  have manc_inv_n: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A n j)
                                                  (idx_B_in_expansion A n x)
                          \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)"
  proof (intro allI impI)
    fix x assume x_lt_j: "x < j"
    have x_lt_l1: "x < l1 A" using x_lt_j j_lt' by linarith
    show "m_ancestor (A[n]) k' (idx_B_in_expansion A n j)
                                (idx_B_in_expansion A n x)
        \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                (idx_B_in_expansion A 0 x)"
      using IH_ii_kp x_lt_l1 j_lt' unfolding lemma_2_5_ii_clause_def by blast
  qed
  show ?case
  proof (cases "?S = []")
    case True
    have outA: "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A 0 j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A 0 0)"
      using m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t
            [OF A_BMS A_ne b0 mp k_lt_t n_pos le0 j_lt' manc_inv_0 True] .
    have outB: "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A n 0)"
      using m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t
            [OF A_BMS A_ne b0 mp k_lt_t n_pos order.refl j_lt' manc_inv_n True] .
    have lhs_F: "\<not> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 i)"
    proof (cases "m_parent (A[n]) (Suc k') (idx_B_in_expansion A 0 j)")
      case None
      thus ?thesis using m_anc_via_parent_none by metis
    next
      case (Some p)
      have p_lt: "p < idx_B_in_expansion A 0 0"
        using outA Some by simp
      have tgt_ge: "idx_B_in_expansion A 0 0 \<le> idx_B_in_expansion A 0 i"
        unfolding idx_B_in_expansion_def by simp
      have p_ne_tgt: "p \<noteq> idx_B_in_expansion A 0 i"
        using p_lt tgt_ge by linarith
      have no_anc: "\<not> m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A 0 i)"
      proof
        assume "m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A 0 i)"
        hence "idx_B_in_expansion A 0 i < p" by (rule m_ancestor_target_lt)
        thus False using p_lt tgt_ge by linarith
      qed
      have iff_via: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 i)
                  \<longleftrightarrow> p = idx_B_in_expansion A 0 i
                       \<or> m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A 0 i)"
        using m_anc_via_parent_some[OF Some] .
      thus ?thesis using p_ne_tgt no_anc by blast
    qed
    have rhs_F: "\<not> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j)
                                          (idx_B_in_expansion A n i)"
    proof (cases "m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j)")
      case None
      thus ?thesis using m_anc_via_parent_none by metis
    next
      case (Some p)
      have p_lt: "p < idx_B_in_expansion A n 0"
        using outB Some by simp
      have tgt_ge: "idx_B_in_expansion A n 0 \<le> idx_B_in_expansion A n i"
        unfolding idx_B_in_expansion_def by simp
      have p_ne_tgt: "p \<noteq> idx_B_in_expansion A n i"
        using p_lt tgt_ge by linarith
      have no_anc: "\<not> m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A n i)"
      proof
        assume "m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A n i)"
        hence "idx_B_in_expansion A n i < p" by (rule m_ancestor_target_lt)
        thus False using p_lt tgt_ge by linarith
      qed
      have iff_via: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j)
                                          (idx_B_in_expansion A n i)
                  \<longleftrightarrow> p = idx_B_in_expansion A n i
                       \<or> m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A n i)"
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
    have mpA: "m_parent (A[n]) (Suc k') (idx_B_in_expansion A 0 j)
             = Some (idx_B_in_expansion A 0 ?p)"
      using m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t
            [OF A_BMS A_ne b0 mp k_lt_t n_pos le0 j_lt' manc_inv_0 False] .
    have mpB: "m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j)
             = Some (idx_B_in_expansion A n ?p)"
      using m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t
            [OF A_BMS A_ne b0 mp k_lt_t n_pos order.refl j_lt' manc_inv_n False] .
    have lhs_iff: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j)
                                        (idx_B_in_expansion A 0 i)
                \<longleftrightarrow> idx_B_in_expansion A 0 ?p = idx_B_in_expansion A 0 i
                  \<or> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                          (idx_B_in_expansion A 0 i)"
      using m_anc_via_parent_some[OF mpA] .
    have rhs_iff: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j)
                                        (idx_B_in_expansion A n i)
                \<longleftrightarrow> idx_B_in_expansion A n ?p = idx_B_in_expansion A n i
                  \<or> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                          (idx_B_in_expansion A n i)"
      using m_anc_via_parent_some[OF mpB] .
    show ?thesis
    proof (cases "i = ?p")
      case True
      have eqA: "idx_B_in_expansion A 0 ?p = idx_B_in_expansion A 0 i"
        using True by simp
      have eqB: "idx_B_in_expansion A n ?p = idx_B_in_expansion A n i"
        using True by simp
      show ?thesis using lhs_iff rhs_iff eqA eqB by blast
    next
      case False
      hence i_ne_p: "i \<noteq> ?p" .
      have neqA: "idx_B_in_expansion A 0 ?p \<noteq> idx_B_in_expansion A 0 i"
        using i_ne_p unfolding idx_B_in_expansion_def by simp
      have neqB: "idx_B_in_expansion A n ?p \<noteq> idx_B_in_expansion A n i"
        using i_ne_p unfolding idx_B_in_expansion_def by simp
      show ?thesis
      proof (cases "i < ?p")
        case True
        have IH_at: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                          (idx_B_in_expansion A 0 i)
                   \<longleftrightarrow> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                          (idx_B_in_expansion A n i)"
          using IH_chain[OF p_lt_j i_lt' p_lt_l1 True] .
        show ?thesis using lhs_iff rhs_iff IH_at neqA neqB by blast
      next
        case False
        hence p_lt_i: "?p < i" using i_ne_p by linarith
        have no_ancA: "\<not> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                                (idx_B_in_expansion A 0 i)"
        proof
          assume "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                       (idx_B_in_expansion A 0 i)"
          hence "idx_B_in_expansion A 0 i < idx_B_in_expansion A 0 ?p"
            by (rule m_ancestor_target_lt)
          thus False using p_lt_i unfolding idx_B_in_expansion_def by simp
        qed
        have no_ancB: "\<not> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                                (idx_B_in_expansion A n i)"
        proof
          assume "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                       (idx_B_in_expansion A n i)"
          hence "idx_B_in_expansion A n i < idx_B_in_expansion A n ?p"
            by (rule m_ancestor_target_lt)
          thus False using p_lt_i unfolding idx_B_in_expansion_def by simp
        qed
        show ?thesis using lhs_iff rhs_iff neqA neqB no_ancA no_ancB by blast
      qed
    qed
  qed
qed

text \<open>
  Elem equality across blocks at row \<open>k \<ge> t\<close>: at non-bumping
  rows the value of any B-block column at row \<open>k\<close> is independent
  of the block index. In-bounds (\<open>k < keep_of\<close>) use
  @{thm elem_expansion_B_eq_orig_k_ge_t}; out-of-bounds use
  uniform column length under @{thm strip_zero_rows_eq_map_take}
  combined with @{thm nth_same_length_oob}.
\<close>

lemma elem_AEn_eq_at_row_k_ge_t_across_blocks:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_ge: "t \<le> k"
      and a_le: "a \<le> n"
      and b_le: "b \<le> n"
      and x_lt: "x < l1 A"
  shows "elem (A[n]) (idx_B_in_expansion A a x) k
       = elem (A[n]) (idx_B_in_expansion A b x) k"
proof -
  let ?P = "G_block A @ Bs_concat A n"
  let ?h = "keep_of ?P"
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have s_lt_arr: "s < arr_len A" using s_lt_last last_lt_arr by simp
  have l1_pos: "0 < l1 A" using x_lt by linarith
  have x_arr: "s + x < arr_len A"
  proof -
    have "x < last_col_idx A - s"
      using x_lt b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
    hence "s + x < last_col_idx A" by linarith
    thus ?thesis using last_lt_arr by linarith
  qed
  have len_Asx: "length (A ! (s + x)) = height A"
    using length_col_arr[OF is_arr A_ne x_arr] .

  have len_P: "length ?P = l0 A + Suc n * l1 A"
    by (simp add: l0_def l1_def length_Bs_concat)
  have idxBa_lt: "idx_B_in_expansion A a x < length ?P"
  proof -
    have "a * l1 A + x < Suc a * l1 A" using x_lt by simp
    also have "\<dots> \<le> Suc n * l1 A" using a_le by simp
    finally have "a * l1 A + x < Suc n * l1 A" .
    thus ?thesis using len_P unfolding idx_B_in_expansion_def by simp
  qed
  have idxBb_lt: "idx_B_in_expansion A b x < length ?P"
  proof -
    have "b * l1 A + x < Suc b * l1 A" using x_lt by simp
    also have "\<dots> \<le> Suc n * l1 A" using b_le by simp
    finally have "b * l1 A + x < Suc n * l1 A" .
    thus ?thesis using len_P unfolding idx_B_in_expansion_def by simp
  qed
  have P_ne: "?P \<noteq> []" using idxBa_lt by auto

  \<comment> \<open>All cols of \<open>?P\<close> have length \<open>height A\<close>; hence all cols of
      \<open>A[n]\<close> have length \<open>?h\<close>.\<close>
  have all_A: "\<forall>c \<in> set A. length c = height A"
    using is_arr unfolding is_array_def by blast
  have all_G: "\<forall>c \<in> set (G_block A). length c = height A"
    using G_block_subset_A all_A by blast
  have all_Bs: "\<forall>c \<in> set (Bs_concat A n). length c = height A"
    using Bs_concat_uniform[OF is_arr A_ne] .
  have all_P: "\<forall>c \<in> set ?P. length c = height A"
    using all_G all_Bs by auto

  have An_eq: "A[n] = strip_zero_rows ?P"
    using A_ne unfolding expansion_def by simp
  have strip_eq: "strip_zero_rows ?P = map (\<lambda>c. take ?h c) ?P"
    using P_ne by (rule strip_zero_rows_eq_map_take)
  have An_eq2: "A[n] = map (\<lambda>c. take ?h c) ?P"
    using An_eq strip_eq by simp
  have An_at_a: "(A[n]) ! (idx_B_in_expansion A a x) = take ?h (?P ! (idx_B_in_expansion A a x))"
  proof -
    have "(A[n]) ! (idx_B_in_expansion A a x)
        = (map (\<lambda>c. take ?h c) ?P) ! (idx_B_in_expansion A a x)"
      using An_eq2 by simp
    also have "\<dots> = take ?h (?P ! (idx_B_in_expansion A a x))"
      using idxBa_lt by (rule nth_map)
    finally show ?thesis .
  qed
  have An_at_b: "(A[n]) ! (idx_B_in_expansion A b x) = take ?h (?P ! (idx_B_in_expansion A b x))"
  proof -
    have "(A[n]) ! (idx_B_in_expansion A b x)
        = (map (\<lambda>c. take ?h c) ?P) ! (idx_B_in_expansion A b x)"
      using An_eq2 by simp
    also have "\<dots> = take ?h (?P ! (idx_B_in_expansion A b x))"
      using idxBb_lt by (rule nth_map)
    finally show ?thesis .
  qed

  \<comment> \<open>Pre-strip values at our positions equal \<open>bump_col A x a\<close>
      and \<open>bump_col A x b\<close>, which at row \<open>k \<ge> t\<close> have no
      ascending bump and reduce to \<open>(A ! (s + x)) ! k\<close>.\<close>
  have P_at_a: "?P ! (idx_B_in_expansion A a x) = bump_col A x a"
  proof -
    have "?P ! (idx_B_in_expansion A a x) = Bi_block A a ! x"
      using pre_strip_nth_B[OF a_le x_lt] .
    moreover have "Bi_block A a ! x = bump_col A x a"
      unfolding Bi_block_def Let_def using x_lt unfolding l1_def by simp
    ultimately show ?thesis by simp
  qed
  have P_at_b: "?P ! (idx_B_in_expansion A b x) = bump_col A x b"
  proof -
    have "?P ! (idx_B_in_expansion A b x) = Bi_block A b ! x"
      using pre_strip_nth_B[OF b_le x_lt] .
    moreover have "Bi_block A b ! x = bump_col A x b"
      unfolding Bi_block_def Let_def using x_lt unfolding l1_def by simp
    ultimately show ?thesis by simp
  qed
  have bump_a_len: "length (bump_col A x a) = length (A ! (s + x))"
    unfolding bump_col_def Let_def using b0 by simp
  have bump_b_len: "length (bump_col A x b) = length (A ! (s + x))"
    unfolding bump_col_def Let_def using b0 by simp
  have bump_a_len_H: "length (bump_col A x a) = height A"
    using bump_a_len len_Asx by simp
  have bump_b_len_H: "length (bump_col A x b) = height A"
    using bump_b_len len_Asx by simp

  \<comment> \<open>\<open>height ?P = height A\<close> via uniform col length.\<close>
  have hd_in: "hd ?P \<in> set ?P" using P_ne by (cases ?P) auto
  have hd_len: "length (hd ?P) = height A" using all_P hd_in by blast
  have height_P_eq: "height ?P = height A" using P_ne hd_len by (cases ?P) auto
  have h_le_HP: "?h \<le> height ?P" by (rule keep_of_le_height)
  have h_le_HA: "?h \<le> height A" using h_le_HP height_P_eq by simp

  show ?thesis
  proof (cases "k < ?h")
    case True
    \<comment> \<open>In-bounds for \<open>A[n]\<close>'s column length \<open>?h\<close>.
        Use @{thm elem_expansion_B_eq_orig_k_ge_t} on both sides.\<close>
    have k_lt_HA: "k < height A" using True h_le_HA by linarith
    have k_lt_col: "k < length (A ! (s + x))" using k_lt_HA len_Asx by simp
    have a_eq: "elem (A[n]) (idx_B_in_expansion A a x) k = (A ! (s + x)) ! k"
      using elem_expansion_B_eq_orig_k_ge_t[OF A_ne b0 mp k_ge a_le x_lt True k_lt_col] .
    have b_eq: "elem (A[n]) (idx_B_in_expansion A b x) k = (A ! (s + x)) ! k"
      using elem_expansion_B_eq_orig_k_ge_t[OF A_ne b0 mp k_ge b_le x_lt True k_lt_col] .
    show ?thesis using a_eq b_eq by simp
  next
    case False
    \<comment> \<open>Out-of-bounds: both columns of \<open>A[n]\<close> have length \<open>?h\<close>,
        and \<open>k \<ge> ?h\<close>; apply @{thm nth_same_length_oob}.\<close>
    hence k_ge_h: "?h \<le> k" by simp
    have len_a: "length ((A[n]) ! (idx_B_in_expansion A a x)) = ?h"
    proof -
      have "length ((A[n]) ! (idx_B_in_expansion A a x))
          = length (take ?h (?P ! (idx_B_in_expansion A a x)))"
        using An_at_a by simp
      also have "\<dots> = min ?h (length (?P ! (idx_B_in_expansion A a x)))" by simp
      also have "length (?P ! (idx_B_in_expansion A a x)) = length (bump_col A x a)"
        using P_at_a by simp
      also have "\<dots> = height A" using bump_a_len_H .
      finally show ?thesis using h_le_HA by simp
    qed
    have len_b: "length ((A[n]) ! (idx_B_in_expansion A b x)) = ?h"
    proof -
      have "length ((A[n]) ! (idx_B_in_expansion A b x))
          = length (take ?h (?P ! (idx_B_in_expansion A b x)))"
        using An_at_b by simp
      also have "\<dots> = min ?h (length (?P ! (idx_B_in_expansion A b x)))" by simp
      also have "length (?P ! (idx_B_in_expansion A b x)) = length (bump_col A x b)"
        using P_at_b by simp
      also have "\<dots> = height A" using bump_b_len_H .
      finally show ?thesis using h_le_HA by simp
    qed
    have lens_eq: "length ((A[n]) ! (idx_B_in_expansion A a x))
                 = length ((A[n]) ! (idx_B_in_expansion A b x))"
      using len_a len_b by simp
    have k_ge_a: "length ((A[n]) ! (idx_B_in_expansion A a x)) \<le> k"
      using k_ge_h len_a by simp
    have "((A[n]) ! (idx_B_in_expansion A a x)) ! k
        = ((A[n]) ! (idx_B_in_expansion A b x)) ! k"
      using nth_same_length_oob[OF lens_eq k_ge_a] .
    thus ?thesis unfolding elem_def by simp
  qed
qed

text \<open>
  Within-block characterization of @{term m_parent} at row \<open>Suc k'\<close>
  when \<open>Suc k' \<ge> t = max_parent_level A\<close>. The strict-less
  comparison at row \<open>Suc k'\<close> is invariant in the block index via
  @{thm elem_AEn_eq_at_row_k_ge_t_across_blocks}; the \<open>m_anc\<close>-at-\<open>k'\<close>
  filter conjunct is handled via the same \<open>manc_inv\<close> parameter
  technique as the \<open>k < t\<close> version.
\<close>

lemma m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_ge_t:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_ge_t: "t \<le> Suc k'"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and manc_inv: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                                  (idx_B_in_expansion A c x)
                          \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)"
      and S_ne: "[x \<leftarrow> [0..<j].
                    elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                      < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                  \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 x)] \<noteq> []"
  shows "m_parent (A[n]) (Suc k') (idx_B_in_expansion A c j)
       = Some (idx_B_in_expansion A c
            (last [x \<leftarrow> [0..<j].
                    elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                      < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                  \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 x)]))"
proof -
  let ?i = "idx_B_in_expansion A c j"
  let ?Cstart = "idx_B_in_expansion A c 0"
  let ?vi = "elem (A[n]) ?i (Suc k')"
  let ?cands = "[p \<leftarrow> [0..<?i]. elem (A[n]) p (Suc k') < ?vi
                              \<and> m_ancestor (A[n]) k' ?i p]"
  let ?S = "[x \<leftarrow> [0..<j].
              elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
            \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                    (idx_B_in_expansion A 0 x)]"
  have mp_eq: "m_parent (A[n]) (Suc k') ?i
             = (if ?cands = [] then None else Some (last ?cands))"
    by (simp add: Let_def)
  have i_eq: "?i = ?Cstart + j" unfolding idx_B_in_expansion_def by simp
  have range_split: "[0..<?i] = [0..<?Cstart] @ [?Cstart..<?i]"
    using upt_add_eq_append[OF le0, of ?Cstart j] i_eq by simp
  let ?pre = "filter (\<lambda>p. elem (A[n]) p (Suc k') < ?vi
                       \<and> m_ancestor (A[n]) k' ?i p) [0..<?Cstart]"
  let ?post = "filter (\<lambda>p. elem (A[n]) p (Suc k') < ?vi
                        \<and> m_ancestor (A[n]) k' ?i p) [?Cstart..<?i]"
  have cands_split: "?cands = ?pre @ ?post"
    using range_split by simp
  have post_range: "[?Cstart..<?i] = map (\<lambda>i. i + ?Cstart) [0..<j]"
    using i_eq map_add_upt[of ?Cstart j] by (simp add: add.commute)
  have post_map: "?post = map (\<lambda>i. i + ?Cstart)
                   (filter (\<lambda>i. elem (A[n]) (i + ?Cstart) (Suc k') < ?vi
                              \<and> m_ancestor (A[n]) k' ?i (i + ?Cstart)) [0..<j])"
    using post_range by (simp add: filter_map o_def)
  have filter_cong_eq:
    "filter (\<lambda>i. elem (A[n]) (i + ?Cstart) (Suc k') < ?vi
              \<and> m_ancestor (A[n]) k' ?i (i + ?Cstart)) [0..<j] = ?S"
  proof (rule filter_cong[OF refl])
    fix x assume x_in: "x \<in> set [0..<j]"
    hence x_lt_j: "x < j" by simp
    hence x_lt_l1: "x < l1 A" using j_lt by linarith
    have idxBc_eq: "x + ?Cstart = idx_B_in_expansion A c x"
      unfolding idx_B_in_expansion_def by simp
    \<comment> \<open>elem at row Suc k' across blocks (via eq across blocks)\<close>
    have elem_x_c: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
                  = elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')"
      using elem_AEn_eq_at_row_k_ge_t_across_blocks
              [OF A_BMS A_ne b0 mp k_ge_t c_le le0 x_lt_l1] .
    have elem_j_c: "elem (A[n]) (idx_B_in_expansion A c j) (Suc k')
                  = elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')"
      using elem_AEn_eq_at_row_k_ge_t_across_blocks
              [OF A_BMS A_ne b0 mp k_ge_t c_le le0 j_lt] .
    have manc_x: "m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                        (idx_B_in_expansion A c x)
                \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                        (idx_B_in_expansion A 0 x)"
      using manc_inv x_lt_j by blast
    show "(elem (A[n]) (x + ?Cstart) (Suc k') < ?vi
            \<and> m_ancestor (A[n]) k' ?i (x + ?Cstart))
       \<longleftrightarrow>
          (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
              < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
           \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                   (idx_B_in_expansion A 0 x))"
      using idxBc_eq elem_x_c elem_j_c manc_x by simp
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

text \<open>
  Outside-block characterization of @{term m_parent} at row
  \<open>Suc k'\<close> when \<open>Suc k' \<ge> t\<close>: same parameterized shape as
  within-block, with \<open>manc_inv\<close> hypothesis.
\<close>

lemma m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_ge_t:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_ge_t: "t \<le> Suc k'"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and manc_inv: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                                  (idx_B_in_expansion A c x)
                          \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)"
      and S_empty: "[x \<leftarrow> [0..<j].
                       elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                         < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                     \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                             (idx_B_in_expansion A 0 x)] = []"
  shows "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A c j) of
             None \<Rightarrow> True
           | Some p \<Rightarrow> p < idx_B_in_expansion A c 0)"
proof -
  let ?i = "idx_B_in_expansion A c j"
  let ?Cstart = "idx_B_in_expansion A c 0"
  let ?vi = "elem (A[n]) ?i (Suc k')"
  let ?cands = "[p \<leftarrow> [0..<?i]. elem (A[n]) p (Suc k') < ?vi
                              \<and> m_ancestor (A[n]) k' ?i p]"
  have mp_eq: "m_parent (A[n]) (Suc k') ?i
             = (if ?cands = [] then None else Some (last ?cands))"
    by (simp add: Let_def)
  have all_lt: "\<forall>p \<in> set ?cands. p < ?Cstart"
  proof
    fix p assume p_in: "p \<in> set ?cands"
    have p_lt_i: "p < ?i" using p_in by auto
    have v_lt: "elem (A[n]) p (Suc k') < ?vi" using p_in by simp
    have manc_p: "m_ancestor (A[n]) k' ?i p" using p_in by simp
    show "p < ?Cstart"
    proof (rule ccontr)
      assume "\<not> p < ?Cstart"
      hence p_ge: "?Cstart \<le> p" by simp
      define x where "x = p - ?Cstart"
      have p_eq: "p = ?Cstart + x" using p_ge x_def by simp
      have x_lt_j: "x < j"
      proof -
        have "?Cstart + x < ?Cstart + j"
          using p_eq p_lt_i unfolding idx_B_in_expansion_def by simp
        thus ?thesis by simp
      qed
      have x_lt_l1: "x < l1 A" using x_lt_j j_lt by linarith
      have p_as_idxBc: "p = idx_B_in_expansion A c x"
        using p_eq unfolding idx_B_in_expansion_def by simp
      have elem_x_c: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
                    = elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')"
        using elem_AEn_eq_at_row_k_ge_t_across_blocks
                [OF A_BMS A_ne b0 mp k_ge_t c_le le0 x_lt_l1] .
      have elem_j_c: "elem (A[n]) (idx_B_in_expansion A c j) (Suc k')
                    = elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')"
        using elem_AEn_eq_at_row_k_ge_t_across_blocks
                [OF A_BMS A_ne b0 mp k_ge_t c_le le0 j_lt] .
      have v_lt2: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
                 < elem (A[n]) (idx_B_in_expansion A c j) (Suc k')"
        using v_lt p_as_idxBc by simp
      have block0_lt: "elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                     < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')"
        using v_lt2 elem_x_c elem_j_c by simp
      have manc_at_c: "m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                              (idx_B_in_expansion A c x)"
        using manc_p p_as_idxBc by simp
      have manc_at_0: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                              (idx_B_in_expansion A 0 x)"
        using manc_at_c manc_inv x_lt_j by blast
      have x_in_upt: "x \<in> set [0..<j]" using x_lt_j by simp
      have all_neg: "\<forall>y \<in> set [0..<j]. \<not> (elem (A[n]) (idx_B_in_expansion A 0 y) (Suc k')
                            < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                          \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 y))"
        using S_empty filter_empty_conv by metis
      have neg_x: "\<not> (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                       < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                     \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                             (idx_B_in_expansion A 0 x))"
        using all_neg x_in_upt by blast
      thus False using block0_lt manc_at_0 by blast
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

text \<open>
  Block-shift invariance of @{term m_ancestor} at row \<open>Suc k'\<close>
  when \<open>Suc k' \<ge> t\<close>: chain induction applied at \<open>c = 0\<close>
  (trivial manc_inv) and \<open>c = n\<close> (manc_inv from IH (ii) at \<open>k'\<close>).
\<close>

lemma m_anc_idx_B_in_block_shift_at_Suc_k_when_k_ge_t:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_ge_t: "t \<le> Suc k'"
      and IH_ii_kp: "lemma_2_5_ii_clause A n k'"
      and i_lt: "i < l1 A"
      and j_lt: "j < l1 A"
      and i_lt_j: "i < j"
  shows "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j) (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j) (idx_B_in_expansion A n i)"
  using i_lt j_lt i_lt_j
proof (induct j arbitrary: i rule: less_induct)
  case (less j)
  note IH_chain = less.hyps
  note i_lt' = less.prems(1)
  note j_lt' = less.prems(2)
  note i_lt_j' = less.prems(3)
  let ?S = "[x \<leftarrow> [0..<j].
              elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
            \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                    (idx_B_in_expansion A 0 x)]"
  have manc_inv_0: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)
                          \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)"
    by simp
  have manc_inv_n: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A n j)
                                                  (idx_B_in_expansion A n x)
                          \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)"
  proof (intro allI impI)
    fix x assume x_lt_j: "x < j"
    have x_lt_l1: "x < l1 A" using x_lt_j j_lt' by linarith
    show "m_ancestor (A[n]) k' (idx_B_in_expansion A n j)
                                (idx_B_in_expansion A n x)
        \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                (idx_B_in_expansion A 0 x)"
      using IH_ii_kp x_lt_l1 j_lt' unfolding lemma_2_5_ii_clause_def by blast
  qed
  show ?case
  proof (cases "?S = []")
    case True
    have outA: "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A 0 j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A 0 0)"
      using m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_ge_t
            [OF A_BMS A_ne b0 mp k_ge_t le0 j_lt' manc_inv_0 True] .
    have outB: "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A n 0)"
      using m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_ge_t
            [OF A_BMS A_ne b0 mp k_ge_t order.refl j_lt' manc_inv_n True] .
    have lhs_F: "\<not> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 i)"
    proof (cases "m_parent (A[n]) (Suc k') (idx_B_in_expansion A 0 j)")
      case None
      thus ?thesis using m_anc_via_parent_none by metis
    next
      case (Some p)
      have p_lt: "p < idx_B_in_expansion A 0 0"
        using outA Some by simp
      have tgt_ge: "idx_B_in_expansion A 0 0 \<le> idx_B_in_expansion A 0 i"
        unfolding idx_B_in_expansion_def by simp
      have p_ne_tgt: "p \<noteq> idx_B_in_expansion A 0 i"
        using p_lt tgt_ge by linarith
      have no_anc: "\<not> m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A 0 i)"
      proof
        assume "m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A 0 i)"
        hence "idx_B_in_expansion A 0 i < p" by (rule m_ancestor_target_lt)
        thus False using p_lt tgt_ge by linarith
      qed
      have iff_via: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 i)
                  \<longleftrightarrow> p = idx_B_in_expansion A 0 i
                       \<or> m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A 0 i)"
        using m_anc_via_parent_some[OF Some] .
      thus ?thesis using p_ne_tgt no_anc by blast
    qed
    have rhs_F: "\<not> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j)
                                          (idx_B_in_expansion A n i)"
    proof (cases "m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j)")
      case None
      thus ?thesis using m_anc_via_parent_none by metis
    next
      case (Some p)
      have p_lt: "p < idx_B_in_expansion A n 0"
        using outB Some by simp
      have tgt_ge: "idx_B_in_expansion A n 0 \<le> idx_B_in_expansion A n i"
        unfolding idx_B_in_expansion_def by simp
      have p_ne_tgt: "p \<noteq> idx_B_in_expansion A n i"
        using p_lt tgt_ge by linarith
      have no_anc: "\<not> m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A n i)"
      proof
        assume "m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A n i)"
        hence "idx_B_in_expansion A n i < p" by (rule m_ancestor_target_lt)
        thus False using p_lt tgt_ge by linarith
      qed
      have iff_via: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j)
                                          (idx_B_in_expansion A n i)
                  \<longleftrightarrow> p = idx_B_in_expansion A n i
                       \<or> m_ancestor (A[n]) (Suc k') p (idx_B_in_expansion A n i)"
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
    have mpA: "m_parent (A[n]) (Suc k') (idx_B_in_expansion A 0 j)
             = Some (idx_B_in_expansion A 0 ?p)"
      using m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_ge_t
            [OF A_BMS A_ne b0 mp k_ge_t le0 j_lt' manc_inv_0 False] .
    have mpB: "m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j)
             = Some (idx_B_in_expansion A n ?p)"
      using m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_ge_t
            [OF A_BMS A_ne b0 mp k_ge_t order.refl j_lt' manc_inv_n False] .
    have lhs_iff: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j)
                                        (idx_B_in_expansion A 0 i)
                \<longleftrightarrow> idx_B_in_expansion A 0 ?p = idx_B_in_expansion A 0 i
                  \<or> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                          (idx_B_in_expansion A 0 i)"
      using m_anc_via_parent_some[OF mpA] .
    have rhs_iff: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j)
                                        (idx_B_in_expansion A n i)
                \<longleftrightarrow> idx_B_in_expansion A n ?p = idx_B_in_expansion A n i
                  \<or> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                          (idx_B_in_expansion A n i)"
      using m_anc_via_parent_some[OF mpB] .
    show ?thesis
    proof (cases "i = ?p")
      case True
      have eqA: "idx_B_in_expansion A 0 ?p = idx_B_in_expansion A 0 i"
        using True by simp
      have eqB: "idx_B_in_expansion A n ?p = idx_B_in_expansion A n i"
        using True by simp
      show ?thesis using lhs_iff rhs_iff eqA eqB by blast
    next
      case False
      hence i_ne_p: "i \<noteq> ?p" .
      have neqA: "idx_B_in_expansion A 0 ?p \<noteq> idx_B_in_expansion A 0 i"
        using i_ne_p unfolding idx_B_in_expansion_def by simp
      have neqB: "idx_B_in_expansion A n ?p \<noteq> idx_B_in_expansion A n i"
        using i_ne_p unfolding idx_B_in_expansion_def by simp
      show ?thesis
      proof (cases "i < ?p")
        case True
        have IH_at: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                          (idx_B_in_expansion A 0 i)
                   \<longleftrightarrow> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                          (idx_B_in_expansion A n i)"
          using IH_chain[OF p_lt_j i_lt' p_lt_l1 True] .
        show ?thesis using lhs_iff rhs_iff IH_at neqA neqB by blast
      next
        case False
        hence p_lt_i: "?p < i" using i_ne_p by linarith
        have no_ancA: "\<not> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                                (idx_B_in_expansion A 0 i)"
        proof
          assume "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                       (idx_B_in_expansion A 0 i)"
          hence "idx_B_in_expansion A 0 i < idx_B_in_expansion A 0 ?p"
            by (rule m_ancestor_target_lt)
          thus False using p_lt_i unfolding idx_B_in_expansion_def by simp
        qed
        have no_ancB: "\<not> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                                (idx_B_in_expansion A n i)"
        proof
          assume "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                       (idx_B_in_expansion A n i)"
          hence "idx_B_in_expansion A n i < idx_B_in_expansion A n ?p"
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
              \<comment> \<open>\<open>k=0 < t\<close>: uniform bumping at row 0 (via
                  @{thm elem_expansion_B_lt_invariant_in_block}).
                  Dispatch via @{thm m_anc_idx_B_in_block_shift_at_row_zero_when_0_lt_t}
                  (block-shift invariance at row 0 with 0 < t).\<close>
              have n_pos: "0 < n" using \<open>n = Suc n'\<close> by simp
              show ?thesis
                using m_anc_idx_B_in_block_shift_at_row_zero_when_0_lt_t
                        [OF A_BMS A_ne \<open>b0_start A = Some s\<close>
                            \<open>max_parent_level A = Some t\<close>
                            True n_pos le0 order.refl
                            i_lt j_lt i_lt_j]
                      \<open>k = 0\<close>
                by simp
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
              \<comment> \<open>\<open>k < t\<close>: substantive. Dispatch via
                  @{thm m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t}
                  (chain induction + block-shift invariance, using
                  IH (ii) at \<open>k'\<close> for the m_anc-at-\<open>k'\<close> filter
                  conjunct).\<close>
              have n_pos: "0 < n" using \<open>n = Suc n'\<close> by simp
              have IH_ii_kp: "lemma_2_5_ii_clause A n k'"
                using IH_at_k' unfolding lemma_2_5_at_def by blast
              have k_lt_t': "Suc k' < t" using k_lt_t \<open>k = Suc k'\<close> by simp
              show ?thesis
                using m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t
                        [OF A_BMS A_ne \<open>b0_start A = Some s\<close>
                            \<open>max_parent_level A = Some t\<close>
                            k_lt_t' n_pos IH_ii_kp
                            i_lt j_lt i_lt_j]
                      \<open>k = Suc k'\<close>
                by simp
            next
              case False
              hence k_ge_t: "t \<le> k" by simp
              \<comment> \<open>\<open>k \<ge> t\<close>: no bumping at row k. Dispatch via
                  @{thm m_anc_idx_B_in_block_shift_at_Suc_k_when_k_ge_t}
                  (chain induction + elem invariance at row \<open>\<ge> t\<close>,
                  using IH (ii) at \<open>k'\<close> for the m_anc-at-\<open>k'\<close>
                  filter conjunct).\<close>
              have IH_ii_kp: "lemma_2_5_ii_clause A n k'"
                using IH_at_k' unfolding lemma_2_5_at_def by blast
              have k_ge_t': "t \<le> Suc k'" using k_ge_t \<open>k = Suc k'\<close> by simp
              show ?thesis
                using m_anc_idx_B_in_block_shift_at_Suc_k_when_k_ge_t
                        [OF A_BMS A_ne \<open>b0_start A = Some s\<close>
                            \<open>max_parent_level A = Some t\<close>
                            k_ge_t' IH_ii_kp
                            i_lt j_lt i_lt_j]
                      \<open>k = Suc k'\<close>
                by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>
  === NEW SOUND APPROACH for (ii) (2026-05-17) ===

  The existing @{thm lemma_2_5_ii_clause_step} above relies on the
  unsound `bump_col_uniform_k_lt_t` (which derives bumping uniformity
  from a false universal-ascending claim, refuted by yaBMS for the BMS
  array \<open>(0,0,0)(1,1,1)(2,0,0)(1,1,1)\<close>).

  Below is a sound replacement following Hunter's paper (arXiv:2307.04606v3)
  page 5 case-split approach. Strategy:

  Fix \<open>i, j\<close>. If \<open>j = 0\<close> or \<open>i \<ge> j\<close>, trivial. For \<open>i < j\<close>:
  define \<open>I = {i' < j : \<forall>k' < k. i' is k'-ancestor of j in B_0}\<close>.
  By IH (ii) at \<open>k' < k\<close>, \<open>I\<close> is the same when measured in \<open>B_0\<close> or \<open>B_n\<close>.
  Case-split on whether the \<open>j\<close>-th col ascends at row \<open>k\<close>:
  \<^item> Case (A): all \<open>I\<close> cols ascend \<longrightarrow> differences uniform \<longrightarrow> k-ancestry preserved.
  \<^item> Case (B): \<open>j\<close>-th col doesn't ascend \<longrightarrow> no new k-ancestors in \<open>B_n\<close>.

  Takes only IH(ii) at \<open>k' < k\<close>, not the full lemma_2_5_at IH (which
  conflates 5 clauses, masking soundness defects).
\<close>

lemma lemma_2_5_ii_clause_step_v2:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH_ii: "\<forall>k'<k. lemma_2_5_ii_clause A n k'"
  shows "lemma_2_5_ii_clause A n k"
  sorry

text \<open>Independent k-induction on (ii) alone, using the v2 step lemma
  (sound, depends only on IH(ii)). Provides \<open>\<forall>k. (ii) at k\<close> without
  joint induction with other clauses.\<close>

lemma lemma_2_5_ii_main_v2:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
  shows "lemma_2_5_ii_clause A n k"
proof (induct k rule: nat_less_induct)
  case (1 k)
  have IH_ii: "\<forall>k'<k. lemma_2_5_ii_clause A n k'" using "1.hyps" by blast
  show ?case
    by (rule lemma_2_5_ii_clause_step_v2[OF A_BMS A_ne IH_ii])
qed

text \<open>
  Sub-helpers for clause (iii) at \<open>k < m\<^sub>0\<close>.

  Four lemmas factor out the chain-translation:
  \<^item> \<open>m_parent_orig_last_col_when_k_lt_m0\<close>: in original \<open>A\<close>,
    \<open>m_parent A k (last_col_idx A)\<close> returns the last \<open>B_0\<close> col.
  \<^item> \<open>m_parent_AEn_idx_B_n_zero_when_k_lt_m0\<close>: in expansion \<open>A[n]\<close>,
    \<open>m_parent (A[n]) k (idx_B_in_expansion A n 0)\<close> returns the last \<open>B_{n-1}\<close> col.
  \<^item> \<open>m_anc_orig_eq_AEn_shared_B0\<close> (Lemma A): \<open>m_ancestor A k p q\<close>
    matches \<open>m_ancestor (A[n]) k p q\<close> for cols \<open>p\<close> in the shared
    range \<open>[0..idx_B(0, l_1) - 1]\<close>.
  \<^item> \<open>m_anc_AEn_minus_1_eq_AEn_shared\<close> (Lemma A'): \<open>m_ancestor (A[n-1]) k p q\<close>
    matches \<open>m_ancestor (A[n]) k p q\<close> for cols \<open>p\<close> in the shared
    range \<open>[0..idx_B(n-1, l_1) - 1]\<close>.
\<close>

text \<open>Empirical structural conjecture: at row \<open>k < m_0\<close>, every B_0
  column has value strictly less than the last column's value. Analogous
  status to @{thm BMS_all_B0_ascending_below_t} (= "all B_0 cols ascend
  in the ancestor-relation sense"); this conjecture is the elem-ordering
  counterpart needed by the first-step characterizations. Formal proof
  requires BMS structural induction on @{thm BMS.induct}; left as sorry.\<close>

lemma elem_B0_lt_last_col_when_k_lt_m0:
  assumes A_BMS: "A \<in> BMS"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and k_lt: "k < m\<^sub>0"
      and x_lt: "x < l1 A"
  shows "elem A (s + x) k < elem A (last_col_idx A) k"
  sorry

lemma m_parent_orig_last_col_when_k_lt_m0:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and k_lt: "k < m\<^sub>0"
      and l1_pos: "0 < l1 A"
  shows "m_parent A k (last_col_idx A) = Some (idx_B0_in_orig A (l1 A - 1))"
  using k_lt
proof (induct k rule: less_induct)
  case (less k)
  note IH = less.hyps
  note k_lt' = less.prems
  let ?C = "last_col_idx A"
  let ?L = "l1 A - 1"
  let ?p = "idx_B0_in_orig A ?L"
  have s_lt_last: "s < ?C" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "?C < arr_len A" using A_ne by (cases A) auto
  have l0_eq: "l0 A = s"
    using b0 s_lt_last last_lt_arr unfolding l0_def G_block_def by simp
  have l1_eq: "l1 A = ?C - s"
    using s_lt_last b0 last_lt_arr unfolding l1_def B0_block_def by simp
  have C_pos: "0 < ?C" using s_lt_last by linarith
  have p_eq_C_pred: "?p = ?C - 1"
    unfolding idx_B0_in_orig_def using l0_eq l1_eq l1_pos s_lt_last by linarith
  have p_lt_C: "?p < ?C" using p_eq_C_pred C_pos by linarith
  have L_lt: "?L < l1 A" using l1_pos by simp
  \<comment> \<open>Elem cond at row \<open>k\<close> from the structural conjecture.\<close>
  have p_eq_sL: "?p = s + ?L"
    unfolding idx_B0_in_orig_def using l0_eq by simp
  have elem_cond: "elem A ?p k < elem A ?C k"
    using elem_B0_lt_last_col_when_k_lt_m0[OF A_BMS b0 mp k_lt' L_lt] p_eq_sL by simp
  \<comment> \<open>Range split: \<open>[0..<?C] = [0..<?C-1] @ [?C-1]\<close>.\<close>
  have C_eq_Suc: "?C = Suc (?C - 1)" using C_pos by simp
  have range_split: "[0..<?C] = [0..<?C - 1] @ [?C - 1]"
    using C_eq_Suc upt_Suc_append[of 0 "?C - 1"] by simp
  show ?case
  proof (cases k)
    case 0
    let ?P = "\<lambda>j. elem A j 0 < elem A ?C 0"
    have cand_X_pred: "?P (?C - 1)" using elem_cond p_eq_C_pred \<open>k = 0\<close> by simp
    have filter_eq: "filter ?P [0..<?C] = filter ?P [0..<?C-1] @ [?C-1]"
      using range_split cand_X_pred by simp
    have ne: "filter ?P [0..<?C] \<noteq> []" using filter_eq by simp
    have last_eq: "last (filter ?P [0..<?C]) = ?C - 1"
      using filter_eq by simp
    have "m_parent A 0 ?C =
            (let cands = filter ?P [0..<?C]
             in if cands = [] then None else Some (last cands))"
      by (simp add: Let_def)
    also have "\<dots> = Some (?C - 1)"
      using ne last_eq by simp
    also have "Some (?C - 1) = Some ?p" using p_eq_C_pred by simp
    finally show ?thesis using \<open>k = 0\<close> by simp
  next
    case (Suc k')
    have k'_lt: "k' < k" using \<open>k = Suc k'\<close> by simp
    have k'_lt_m0: "k' < m\<^sub>0" using k'_lt k_lt' by linarith
    have IH_at_k': "m_parent A k' ?C = Some ?p"
      using IH[OF k'_lt k'_lt_m0] .
    have manc_at_k': "m_ancestor A k' ?C ?p"
      using m_anc_via_parent_some[OF IH_at_k'] by simp
    let ?P = "\<lambda>j. elem A j (Suc k') < elem A ?C (Suc k') \<and> m_ancestor A k' ?C j"
    have cand_X_pred: "?P (?C - 1)"
      using elem_cond p_eq_C_pred manc_at_k' \<open>k = Suc k'\<close> by simp
    have filter_eq: "filter ?P [0..<?C] = filter ?P [0..<?C-1] @ [?C-1]"
      using range_split cand_X_pred by simp
    have ne: "filter ?P [0..<?C] \<noteq> []" using filter_eq by simp
    have last_eq: "last (filter ?P [0..<?C]) = ?C - 1"
      using filter_eq by simp
    have "m_parent A (Suc k') ?C =
            (let cands = filter ?P [0..<?C]
             in if cands = [] then None else Some (last cands))"
      by (simp add: Let_def)
    also have "\<dots> = Some (?C - 1)"
      using ne last_eq by simp
    also have "Some (?C - 1) = Some ?p" using p_eq_C_pred by simp
    finally show ?thesis using \<open>k = Suc k'\<close> by simp
  qed
qed

lemma m_parent_AEn_idx_B_n_zero_when_k_lt_m0:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and k_lt: "k < m\<^sub>0"
      and n_pos: "0 < n"
      and l1_pos: "0 < l1 A"
  shows "m_parent (A[n]) k (idx_B_in_expansion A n 0)
       = Some (idx_B_in_expansion A (n - 1) (l1 A - 1))"
  using k_lt
proof (induct k rule: less_induct)
  case (less k)
  note IH = less.hyps
  note k_lt' = less.prems
  let ?Q = "idx_B_in_expansion A n 0"
  let ?L = "l1 A - 1"
  let ?p = "idx_B_in_expansion A (n - 1) ?L"
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have l0_eq: "l0 A = s"
    using b0 s_lt_last last_lt_arr unfolding l0_def G_block_def by simp
  have l1_eq: "l1 A = last_col_idx A - s"
    using s_lt_last b0 last_lt_arr unfolding l1_def B0_block_def by simp
  \<comment> \<open>\<open>?p = ?Q - 1\<close> (the immediately preceding col index).\<close>
  have p_eq_Q_pred: "?p = ?Q - 1"
    unfolding idx_B_in_expansion_def using n_pos l1_pos by (cases n) auto
  have Q_pos: "0 < ?Q"
    unfolding idx_B_in_expansion_def using n_pos l1_pos by simp
  have L_lt: "?L < l1 A" using l1_pos by simp
  \<comment> \<open>\<open>k < keep_of\<close> + col-length bounds.\<close>
  have keep_ge_m0: "m\<^sub>0 \<le> keep_of (G_block A @ Bs_concat A n)"
    using keep_of_pre_strip_ge_max_parent_level[OF A_BMS A_ne b0 mp n_pos] .
  have k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
    using k_lt' keep_ge_m0 by linarith
  have sL_arr: "s + ?L < arr_len A"
  proof -
    have "?L < last_col_idx A - s" using L_lt l1_eq by simp
    hence "s + ?L < last_col_idx A" by linarith
    thus ?thesis using last_lt_arr by linarith
  qed
  have s_arr: "s < arr_len A" using s_lt_last last_lt_arr by linarith
  have k_lt_H: "k < height A" using k_lt' max_parent_level_lt[OF mp] by linarith
  have k_lt_col_sL: "k < length (A ! (s + ?L))"
    using length_col_arr[OF is_arr A_ne sL_arr] k_lt_H by simp
  have k_lt_col_s: "k < length (A ! s)"
    using length_col_arr[OF is_arr A_ne s_arr] k_lt_H by simp
  \<comment> \<open>Elem values at ?p and ?Q via bumping.\<close>
  have nm1_le_n: "n - 1 \<le> n" by simp
  have L_lt_B0: "?L < length (B0_block A)" using L_lt unfolding l1_def by simp
  have zero_lt_B0: "(0::nat) < length (B0_block A)" using l1_pos unfolding l1_def by simp
  have ek_p: "elem (A[n]) ?p k = (A!(s + ?L))!k + (n - 1) * delta A k"
  proof -
    have step1: "elem (A[n]) ?p k = (bump_col A ?L (n - 1)) ! k"
      using elem_expansion_B_via_bump[OF A_ne nm1_le_n L_lt k_lt_keep] .
    have step2: "(bump_col A ?L (n - 1)) ! k = (A!(s + ?L))!k + (n - 1) * delta A k"
      using bump_col_uniform_k_lt_t[OF A_BMS b0 mp k_lt' L_lt_B0 k_lt_col_sL] .
    show ?thesis using step1 step2 by simp
  qed
  have k_lt_col_s0: "k < length (A ! (s + 0))" using k_lt_col_s by simp
  have ek_Q: "elem (A[n]) ?Q k = (A!s)!k + n * delta A k"
  proof -
    have step1: "elem (A[n]) ?Q k = (bump_col A 0 n) ! k"
      using elem_expansion_B_via_bump[OF A_ne order.refl l1_pos k_lt_keep] by simp
    have step2: "(bump_col A 0 n) ! k = (A!(s + 0))!k + n * delta A k"
      using bump_col_uniform_k_lt_t[OF A_BMS b0 mp k_lt' zero_lt_B0 k_lt_col_s0] .
    show ?thesis using step1 step2 by simp
  qed
  \<comment> \<open>Elem cond \<open>?p < ?Q\<close> via structural conjecture.\<close>
  have delta_pos: "0 < delta A k"
    using delta_pos_of_lt_m0[OF b0 mp k_lt'] .
  have base: "(A!(s + ?L))!k < (A!(last_col_idx A))!k"
    using elem_B0_lt_last_col_when_k_lt_m0[OF A_BMS b0 mp k_lt' L_lt]
    unfolding elem_def by simp
  have delta_eq: "delta A k = (A!(last_col_idx A))!k - (A!s)!k"
    using b0 unfolding delta_def elem_def by simp
  have s_le_last_val: "(A!s)!k \<le> (A!(last_col_idx A))!k"
  proof -
    have parent_t: "m_parent A m\<^sub>0 (last_col_idx A) = Some s"
      using b0 mp unfolding b0_start_def by simp
    have m_anc_t: "m_ancestor A m\<^sub>0 (last_col_idx A) s" using parent_t by simp
    have m_anc_k: "m_ancestor A k (last_col_idx A) s"
      using m_ancestor_mono[OF less_imp_le_nat[OF k_lt'] m_anc_t] .
    have "elem A s k < elem A (last_col_idx A) k"
      using m_ancestor_elem_lt[OF m_anc_k] .
    thus ?thesis unfolding elem_def by simp
  qed
  have last_val_eq: "(A!(last_col_idx A))!k = (A!s)!k + delta A k"
    using delta_eq s_le_last_val by simp
  have base_alt: "(A!(s + ?L))!k < (A!s)!k + delta A k"
    using base last_val_eq by simp
  have elem_cond: "elem (A[n]) ?p k < elem (A[n]) ?Q k"
  proof -
    have lhs_lt: "(A!(s + ?L))!k + (n - 1) * delta A k
                < (A!s)!k + delta A k + (n - 1) * delta A k"
      using base_alt by simp
    have arith: "(A!s)!k + delta A k + (n - 1) * delta A k = (A!s)!k + n * delta A k"
      using n_pos by (cases n) auto
    show ?thesis using ek_p ek_Q lhs_lt arith by simp
  qed
  \<comment> \<open>Range split: \<open>[0..<?Q] = [0..<?Q - 1] @ [?Q - 1]\<close>.\<close>
  have Q_eq_Suc: "?Q = Suc (?Q - 1)" using Q_pos by simp
  have range_split: "[0..<?Q] = [0..<?Q - 1] @ [?Q - 1]"
    using Q_eq_Suc upt_Suc_append[of 0 "?Q - 1"] by simp
  show ?case
  proof (cases k)
    case 0
    let ?P = "\<lambda>j. elem (A[n]) j 0 < elem (A[n]) ?Q 0"
    have cand_X_pred: "?P (?Q - 1)" using elem_cond p_eq_Q_pred \<open>k = 0\<close> by simp
    have filter_eq: "filter ?P [0..<?Q] = filter ?P [0..<?Q-1] @ [?Q-1]"
      using range_split cand_X_pred by simp
    have ne: "filter ?P [0..<?Q] \<noteq> []" using filter_eq by simp
    have last_eq: "last (filter ?P [0..<?Q]) = ?Q - 1" using filter_eq by simp
    have "m_parent (A[n]) 0 ?Q =
            (let cands = filter ?P [0..<?Q]
             in if cands = [] then None else Some (last cands))"
      by (simp add: Let_def)
    also have "\<dots> = Some (?Q - 1)" using ne last_eq by simp
    also have "Some (?Q - 1) = Some ?p" using p_eq_Q_pred by simp
    finally show ?thesis using \<open>k = 0\<close> by simp
  next
    case (Suc k')
    have k'_lt: "k' < k" using \<open>k = Suc k'\<close> by simp
    have k'_lt_m0: "k' < m\<^sub>0" using k'_lt k_lt' by linarith
    have IH_at_k': "m_parent (A[n]) k' ?Q = Some ?p"
      using IH[OF k'_lt k'_lt_m0] .
    have manc_at_k': "m_ancestor (A[n]) k' ?Q ?p"
      using m_anc_via_parent_some[OF IH_at_k'] by simp
    let ?P = "\<lambda>j. elem (A[n]) j (Suc k') < elem (A[n]) ?Q (Suc k')
                  \<and> m_ancestor (A[n]) k' ?Q j"
    have cand_X_pred: "?P (?Q - 1)"
      using elem_cond p_eq_Q_pred manc_at_k' \<open>k = Suc k'\<close> by simp
    have filter_eq: "filter ?P [0..<?Q] = filter ?P [0..<?Q-1] @ [?Q-1]"
      using range_split cand_X_pred by simp
    have ne: "filter ?P [0..<?Q] \<noteq> []" using filter_eq by simp
    have last_eq: "last (filter ?P [0..<?Q]) = ?Q - 1" using filter_eq by simp
    have "m_parent (A[n]) (Suc k') ?Q =
            (let cands = filter ?P [0..<?Q]
             in if cands = [] then None else Some (last cands))"
      by (simp add: Let_def)
    also have "\<dots> = Some (?Q - 1)" using ne last_eq by simp
    also have "Some (?Q - 1) = Some ?p" using p_eq_Q_pred by simp
    finally show ?thesis using \<open>k = Suc k'\<close> by simp
  qed
qed

text \<open>Elem match between original \<open>A\<close> and expansion \<open>A[n]\<close>
  for cols in the shared range \<open>p < idx_B(0, l_1)\<close> at row \<open>k < m_0\<close>.
  Decomposed by \<open>p < l_0\<close> (G-col, uses @{thm elem_expansion_G_lt_keep})
  vs \<open>l_0 \<le> p\<close> (B_0-col, uses @{thm elem_expansion_B0_via_orig}).\<close>

lemma elem_orig_eq_AEn_shared_below_l1:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and n_pos: "0 < n"
      and p_lt: "p < idx_B_in_expansion A 0 (l1 A)"
      and k_lt: "k < m\<^sub>0"
  shows "elem A p k = elem (A[n]) p k"
proof -
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have s_le_arr: "s \<le> arr_len A" using s_lt_last last_lt_arr by linarith
  have l0_eq: "l0 A = s"
    using b0 s_le_arr unfolding l0_def G_block_def by simp
  have keep_ge_t: "m\<^sub>0 \<le> keep_of (G_block A @ Bs_concat A n)"
    using keep_of_pre_strip_ge_max_parent_level[OF A_BMS A_ne b0 mp n_pos] .
  have k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
    using k_lt keep_ge_t by linarith
  have p_lt_sum: "p < l0 A + l1 A"
    using p_lt unfolding idx_B_in_expansion_def by simp
  show ?thesis
  proof (cases "p < l0 A")
    case True
    have p_lt_s: "p < s" using True l0_eq by simp
    have eAEn: "elem (A[n]) p k = elem (G_block A) p k"
      by (rule elem_expansion_G_lt_keep[OF A_ne True k_lt_keep])
    have G_eq: "G_block A = take s A" using b0 unfolding G_block_def by simp
    have G_nth: "G_block A ! p = A ! p"
      using G_eq p_lt_s by simp
    have "elem (G_block A) p k = elem A p k"
      using G_nth unfolding elem_def by simp
    thus ?thesis using eAEn by simp
  next
    case False
    hence p_ge_l0: "l0 A \<le> p" by simp
    define j where "j = p - l0 A"
    have j_lt: "j < l1 A" using False p_lt_sum j_def by linarith
    have p_eq_idx: "p = idx_B_in_expansion A 0 j"
      using p_ge_l0 j_def unfolding idx_B_in_expansion_def by simp
    have sj_lt_last: "s + j < last_col_idx A"
    proof -
      have l1_eq: "l1 A = last_col_idx A - s"
        using s_lt_last b0 last_lt_arr
        unfolding l1_def B0_block_def by simp
      hence "j < last_col_idx A - s" using j_lt by simp
      thus ?thesis by linarith
    qed
    have sj_arr: "s + j < arr_len A" using sj_lt_last last_lt_arr by linarith
    have k_lt_col_len: "k < length (A ! (s + j))"
    proof -
      have "length (A ! (s + j)) = height A"
        using length_col_arr[OF is_arr A_ne sj_arr] .
      moreover have "k < height A" using k_lt max_parent_level_lt[OF mp] by linarith
      ultimately show ?thesis by simp
    qed
    have "elem (A[n]) p k = elem (A[n]) (idx_B_in_expansion A 0 j) k"
      using p_eq_idx by simp
    also have "\<dots> = elem A (s + j) k"
      using elem_expansion_B0_via_orig[OF A_ne b0 j_lt k_lt_keep k_lt_col_len] .
    also have "\<dots> = elem A p k"
      using j_def p_ge_l0 l0_eq unfolding elem_def by simp
    finally show ?thesis by simp
  qed
qed

text \<open>Lemma A (\<open>m_anc_orig_eq_AEn_shared_B0\<close>). For
  shared cols and \<open>k < m_0\<close>, \<open>m_parent\<close> matches in \<open>A\<close> and \<open>A[n]\<close>
  (via \<open>elem_orig_eq_AEn_shared_below_l1\<close> plus IH at \<open>k-1\<close>
  for the m_anc filter). Then \<open>m_anc\<close> matches by chain induction.\<close>

lemma m_anc_orig_eq_AEn_shared_B0:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and k_lt: "k < m\<^sub>0"
      and n_pos: "0 < n"
      and p_lt: "p < idx_B_in_expansion A 0 (l1 A)"
  shows "m_ancestor A k p q \<longleftrightarrow> m_ancestor (A[n]) k p q"
  using k_lt p_lt
proof (induct k arbitrary: p q rule: less_induct)
  case (less k)
  note IH_k = less.hyps
  note k_lt' = less.prems(1)
  note p_lt' = less.prems(2)
  \<comment> \<open>Step 1: \<open>m_parent A k p = m_parent (A[n]) k p\<close> via filter cong.\<close>
  have mp_match:
    "\<And>p'. p' < idx_B_in_expansion A 0 (l1 A) \<Longrightarrow>
           m_parent A k p' = m_parent (A[n]) k p'"
  proof -
    fix p'
    assume p'_lt: "p' < idx_B_in_expansion A 0 (l1 A)"
    show "m_parent A k p' = m_parent (A[n]) k p'"
    proof (cases k)
      case 0
      have cands_eq: "[j \<leftarrow> [0..<p']. elem A j 0 < elem A p' 0]
                    = [j \<leftarrow> [0..<p']. elem (A[n]) j 0 < elem (A[n]) p' 0]"
      proof (rule filter_cong[OF refl])
        fix j assume "j \<in> set [0..<p']"
        hence j_lt_p': "j < p'" by simp
        have j_lt_idx: "j < idx_B_in_expansion A 0 (l1 A)"
          using j_lt_p' p'_lt by linarith
        have ej: "elem A j 0 = elem (A[n]) j 0"
          using elem_orig_eq_AEn_shared_below_l1
                  [OF A_BMS A_ne b0 mp n_pos j_lt_idx k_lt'] \<open>k = 0\<close> by simp
        have ep: "elem A p' 0 = elem (A[n]) p' 0"
          using elem_orig_eq_AEn_shared_below_l1
                  [OF A_BMS A_ne b0 mp n_pos p'_lt k_lt'] \<open>k = 0\<close> by simp
        show "elem A j 0 < elem A p' 0 \<longleftrightarrow> elem (A[n]) j 0 < elem (A[n]) p' 0"
          using ej ep by simp
      qed
      thus ?thesis using \<open>k = 0\<close> by (simp add: Let_def)
    next
      case (Suc k')
      have k'_lt: "k' < k" using \<open>k = Suc k'\<close> by simp
      have k'_lt_m0: "k' < m\<^sub>0" using k'_lt k_lt' by linarith
      have cands_eq: "[j \<leftarrow> [0..<p']. elem A j (Suc k') < elem A p' (Suc k')
                                       \<and> m_ancestor A k' p' j]
                    = [j \<leftarrow> [0..<p']. elem (A[n]) j (Suc k') < elem (A[n]) p' (Suc k')
                                       \<and> m_ancestor (A[n]) k' p' j]"
      proof (rule filter_cong[OF refl])
        fix j assume "j \<in> set [0..<p']"
        hence j_lt_p': "j < p'" by simp
        have j_lt_idx: "j < idx_B_in_expansion A 0 (l1 A)"
          using j_lt_p' p'_lt by linarith
        have ej: "elem A j (Suc k') = elem (A[n]) j (Suc k')"
          using elem_orig_eq_AEn_shared_below_l1
                  [OF A_BMS A_ne b0 mp n_pos j_lt_idx k_lt'] \<open>k = Suc k'\<close> by simp
        have ep: "elem A p' (Suc k') = elem (A[n]) p' (Suc k')"
          using elem_orig_eq_AEn_shared_below_l1
                  [OF A_BMS A_ne b0 mp n_pos p'_lt k_lt'] \<open>k = Suc k'\<close> by simp
        have manc: "m_ancestor A k' p' j \<longleftrightarrow> m_ancestor (A[n]) k' p' j"
          using IH_k[OF k'_lt k'_lt_m0 p'_lt] by blast
        show "(elem A j (Suc k') < elem A p' (Suc k') \<and> m_ancestor A k' p' j)
            \<longleftrightarrow> (elem (A[n]) j (Suc k') < elem (A[n]) p' (Suc k')
                 \<and> m_ancestor (A[n]) k' p' j)"
          using ej ep manc by simp
      qed
      thus ?thesis using \<open>k = Suc k'\<close> by (simp add: Let_def)
    qed
  qed
  \<comment> \<open>Step 2: \<open>m_anc\<close> match by chain induction on \<open>p\<close>.\<close>
  show ?case using p_lt'
  proof (induct p arbitrary: q rule: less_induct)
    case (less p)
    note IH_p = less.hyps
    note p_lt'' = less.prems
    have mp_p: "m_parent A k p = m_parent (A[n]) k p"
      using mp_match[OF p_lt''] .
    show "m_ancestor A k p q \<longleftrightarrow> m_ancestor (A[n]) k p q"
    proof (cases "m_parent A k p")
      case None
      have mp_AEn_none: "m_parent (A[n]) k p = None" using None mp_p by simp
      have lhs_F: "\<not> m_ancestor A k p q" using m_anc_via_parent_none[OF None] .
      have rhs_F: "\<not> m_ancestor (A[n]) k p q" using m_anc_via_parent_none[OF mp_AEn_none] .
      show ?thesis using lhs_F rhs_F by simp
    next
      case (Some r)
      have mp_AEn_some: "m_parent (A[n]) k p = Some r" using Some mp_p by simp
      have r_lt: "r < p" using Some by (rule m_parent_lt)
      have r_lt_idx: "r < idx_B_in_expansion A 0 (l1 A)" using r_lt p_lt'' by linarith
      have iff_A: "m_ancestor A k p q \<longleftrightarrow> r = q \<or> m_ancestor A k r q"
        using m_anc_via_parent_some[OF Some] .
      have iff_AEn: "m_ancestor (A[n]) k p q \<longleftrightarrow> r = q \<or> m_ancestor (A[n]) k r q"
        using m_anc_via_parent_some[OF mp_AEn_some] .
      have rec: "m_ancestor A k r q \<longleftrightarrow> m_ancestor (A[n]) k r q"
        using IH_p[OF r_lt r_lt_idx] .
      show ?thesis using iff_A iff_AEn rec by blast
    qed
  qed
qed

text \<open>Elem match between adjacent expansions \<open>A[n-1]\<close> and \<open>A[n]\<close>
  for cols in the shared range \<open>p < idx_B(n-1, l_1)\<close> at row \<open>k < m_0\<close>.
  Requires \<open>n - 1 \<ge> 1\<close> (i.e., \<open>n \<ge> 2\<close>) so that both pre-strip arrays
  use @{thm keep_of_pre_strip_ge_max_parent_level}'s n-positive hypothesis.
  Pre-strip cols agree (G + Bi_block 0..n-1 same in both), after strip values
  match at row \<open>k < t \<le> keep_of(both)\<close>.\<close>

lemma elem_AEn_minus_1_eq_AEn_shared:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and n_minus_1_pos: "0 < n - 1"
      and p_lt: "p < idx_B_in_expansion A (n - 1) (l1 A)"
      and k_lt: "k < m\<^sub>0"
  shows "elem (expansion A (n - 1)) p k = elem (A[n]) p k"
proof -
  let ?Pn1 = "G_block A @ Bs_concat A (n - 1)"
  let ?Pn = "G_block A @ Bs_concat A n"
  have n_pos: "0 < n" using n_minus_1_pos by simp
  have keep_n1: "m\<^sub>0 \<le> keep_of ?Pn1"
    using keep_of_pre_strip_ge_max_parent_level
            [OF A_BMS A_ne b0 mp n_minus_1_pos] .
  have keep_n: "m\<^sub>0 \<le> keep_of ?Pn"
    using keep_of_pre_strip_ge_max_parent_level
            [OF A_BMS A_ne b0 mp n_pos] .
  have k_lt_keep_n1: "k < keep_of ?Pn1" using k_lt keep_n1 by linarith
  have k_lt_keep_n: "k < keep_of ?Pn" using k_lt keep_n by linarith
  have p_lt_sum: "p < l0 A + n * l1 A"
  proof -
    have "p < l0 A + (n - 1) * l1 A + l1 A"
      using p_lt unfolding idx_B_in_expansion_def by simp
    moreover have "(n - 1) * l1 A + l1 A = n * l1 A"
      using n_pos by (cases n) auto
    ultimately show ?thesis by linarith
  qed
  have len_Pn1: "length ?Pn1 = l0 A + n * l1 A"
  proof -
    have "length ?Pn1 = l0 A + Suc (n - 1) * l1 A"
      by (simp add: l0_def l1_def length_Bs_concat)
    moreover have "Suc (n - 1) = n" using n_pos by simp
    ultimately show ?thesis by simp
  qed
  have len_Pn: "length ?Pn = l0 A + Suc n * l1 A"
    by (simp add: l0_def l1_def length_Bs_concat)
  have p_lt_len_Pn1: "p < length ?Pn1" using p_lt_sum len_Pn1 by simp
  have p_lt_len_Pn: "p < length ?Pn"
  proof -
    have "n * l1 A \<le> Suc n * l1 A" by simp
    hence "l0 A + n * l1 A \<le> l0 A + Suc n * l1 A" by simp
    thus ?thesis using p_lt_sum len_Pn by linarith
  qed
  have Pn1_ne: "?Pn1 \<noteq> []" using p_lt_len_Pn1 by auto
  have Pn_ne: "?Pn \<noteq> []" using p_lt_len_Pn by auto
  have exp1: "expansion A (n - 1) = strip_zero_rows ?Pn1"
    using A_ne unfolding expansion_def by simp
  have exp_n: "(A[n]) = strip_zero_rows ?Pn"
    using A_ne unfolding expansion_def by simp
  have p_lt_arr_Pn1: "p < arr_len ?Pn1" using p_lt_len_Pn1 by simp
  have p_lt_arr_Pn: "p < arr_len ?Pn" using p_lt_len_Pn by simp
  have elem_strip_eq_Pn1: "elem (strip_zero_rows ?Pn1) p k = elem ?Pn1 p k"
    using Pn1_ne p_lt_arr_Pn1 k_lt_keep_n1 by (rule elem_strip_lt_keep)
  have elem_strip_eq_Pn: "elem (strip_zero_rows ?Pn) p k = elem ?Pn p k"
    using Pn_ne p_lt_arr_Pn k_lt_keep_n by (rule elem_strip_lt_keep)
  \<comment> \<open>Pre-strip cols match for shared range.\<close>
  have pre_eq: "?Pn1 ! p = ?Pn ! p"
  proof (cases "p < l0 A")
    case True
    have "?Pn1 ! p = G_block A ! p" by (rule pre_strip_nth_G[OF True])
    moreover have "?Pn ! p = G_block A ! p" by (rule pre_strip_nth_G[OF True])
    ultimately show ?thesis by simp
  next
    case False
    hence p_ge_l0: "l0 A \<le> p" by simp
    have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
    have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
    have l1_pos: "0 < l1 A"
      using b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
    define a where "a = (p - l0 A) div l1 A"
    define j where "j = (p - l0 A) mod l1 A"
    have j_lt: "j < l1 A" using l1_pos j_def by simp
    have a_lt_n: "a < n"
    proof -
      have "p - l0 A < n * l1 A" using p_ge_l0 p_lt_sum by linarith
      hence "(p - l0 A) div l1 A < n" using l1_pos by (simp add: less_mult_imp_div_less)
      thus ?thesis unfolding a_def .
    qed
    have a_le_n_1: "a \<le> n - 1" using a_lt_n by linarith
    have a_le_n: "a \<le> n" using a_le_n_1 by linarith
    have p_eq: "p = idx_B_in_expansion A a j"
    proof -
      have "p - l0 A = a * l1 A + j"
        using l1_pos by (simp add: a_def j_def)
      hence "p = l0 A + a * l1 A + j" using p_ge_l0 by linarith
      thus ?thesis unfolding idx_B_in_expansion_def by simp
    qed
    have eqn1: "?Pn1 ! p = Bi_block A a ! j"
      using p_eq pre_strip_nth_B[OF a_le_n_1 j_lt] by simp
    have eqn: "?Pn ! p = Bi_block A a ! j"
      using p_eq pre_strip_nth_B[OF a_le_n j_lt] by simp
    show ?thesis using eqn1 eqn by simp
  qed
  have "elem (expansion A (n - 1)) p k = elem ?Pn1 p k"
    using exp1 elem_strip_eq_Pn1 by simp
  also have "\<dots> = (?Pn1 ! p) ! k" unfolding elem_def by simp
  also have "\<dots> = (?Pn ! p) ! k" using pre_eq by simp
  also have "\<dots> = elem ?Pn p k" unfolding elem_def by simp
  also have "\<dots> = elem (A[n]) p k" using exp_n elem_strip_eq_Pn by simp
  finally show ?thesis .
qed

text \<open>Lemma A' (\<open>m_anc_AEn_minus_1_eq_AEn_shared\<close>). For shared cols
  \<open>p < idx_B(n-1, l_1)\<close> and \<open>k < m_0\<close>, \<open>m_anc\<close> matches in \<open>A[n-1]\<close>
  and \<open>A[n]\<close>. Requires \<open>n \<ge> 2\<close> (via \<open>n_minus_1_pos\<close>).\<close>

lemma m_anc_AEn_minus_1_eq_AEn_shared:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and k_lt: "k < m\<^sub>0"
      and n_minus_1_pos: "0 < n - 1"
      and p_lt: "p < idx_B_in_expansion A (n - 1) (l1 A)"
  shows "m_ancestor (expansion A (n - 1)) k p q \<longleftrightarrow> m_ancestor (A[n]) k p q"
  using k_lt p_lt
proof (induct k arbitrary: p q rule: less_induct)
  case (less k)
  note IH_k = less.hyps
  note k_lt' = less.prems(1)
  note p_lt' = less.prems(2)
  \<comment> \<open>Step 1: \<open>m_parent (A[n-1]) k p = m_parent (A[n]) k p\<close> via filter cong.\<close>
  have mp_match:
    "\<And>p'. p' < idx_B_in_expansion A (n - 1) (l1 A) \<Longrightarrow>
           m_parent (expansion A (n - 1)) k p' = m_parent (A[n]) k p'"
  proof -
    fix p'
    assume p'_lt: "p' < idx_B_in_expansion A (n - 1) (l1 A)"
    show "m_parent (expansion A (n - 1)) k p' = m_parent (A[n]) k p'"
    proof (cases k)
      case 0
      have cands_eq:
        "[j \<leftarrow> [0..<p']. elem (expansion A (n - 1)) j 0
                          < elem (expansion A (n - 1)) p' 0]
         = [j \<leftarrow> [0..<p']. elem (A[n]) j 0 < elem (A[n]) p' 0]"
      proof (rule filter_cong[OF refl])
        fix j assume "j \<in> set [0..<p']"
        hence j_lt_p': "j < p'" by simp
        have j_lt_idx: "j < idx_B_in_expansion A (n - 1) (l1 A)"
          using j_lt_p' p'_lt by linarith
        have ej: "elem (expansion A (n - 1)) j 0 = elem (A[n]) j 0"
          using elem_AEn_minus_1_eq_AEn_shared
                  [OF A_BMS A_ne b0 mp n_minus_1_pos j_lt_idx k_lt'] \<open>k = 0\<close> by simp
        have ep: "elem (expansion A (n - 1)) p' 0 = elem (A[n]) p' 0"
          using elem_AEn_minus_1_eq_AEn_shared
                  [OF A_BMS A_ne b0 mp n_minus_1_pos p'_lt k_lt'] \<open>k = 0\<close> by simp
        show "elem (expansion A (n - 1)) j 0 < elem (expansion A (n - 1)) p' 0
            \<longleftrightarrow> elem (A[n]) j 0 < elem (A[n]) p' 0"
          using ej ep by simp
      qed
      thus ?thesis using \<open>k = 0\<close> by (simp add: Let_def)
    next
      case (Suc k')
      have k'_lt: "k' < k" using \<open>k = Suc k'\<close> by simp
      have k'_lt_m0: "k' < m\<^sub>0" using k'_lt k_lt' by linarith
      have cands_eq:
        "[j \<leftarrow> [0..<p']. elem (expansion A (n - 1)) j (Suc k')
                          < elem (expansion A (n - 1)) p' (Suc k')
                       \<and> m_ancestor (expansion A (n - 1)) k' p' j]
         = [j \<leftarrow> [0..<p']. elem (A[n]) j (Suc k') < elem (A[n]) p' (Suc k')
                       \<and> m_ancestor (A[n]) k' p' j]"
      proof (rule filter_cong[OF refl])
        fix j assume "j \<in> set [0..<p']"
        hence j_lt_p': "j < p'" by simp
        have j_lt_idx: "j < idx_B_in_expansion A (n - 1) (l1 A)"
          using j_lt_p' p'_lt by linarith
        have ej: "elem (expansion A (n - 1)) j (Suc k') = elem (A[n]) j (Suc k')"
          using elem_AEn_minus_1_eq_AEn_shared
                  [OF A_BMS A_ne b0 mp n_minus_1_pos j_lt_idx k_lt'] \<open>k = Suc k'\<close> by simp
        have ep: "elem (expansion A (n - 1)) p' (Suc k') = elem (A[n]) p' (Suc k')"
          using elem_AEn_minus_1_eq_AEn_shared
                  [OF A_BMS A_ne b0 mp n_minus_1_pos p'_lt k_lt'] \<open>k = Suc k'\<close> by simp
        have manc: "m_ancestor (expansion A (n - 1)) k' p' j
                  \<longleftrightarrow> m_ancestor (A[n]) k' p' j"
          using IH_k[OF k'_lt k'_lt_m0 p'_lt] by blast
        show "(elem (expansion A (n - 1)) j (Suc k')
                 < elem (expansion A (n - 1)) p' (Suc k')
               \<and> m_ancestor (expansion A (n - 1)) k' p' j)
            \<longleftrightarrow> (elem (A[n]) j (Suc k') < elem (A[n]) p' (Suc k')
                  \<and> m_ancestor (A[n]) k' p' j)"
          using ej ep manc by simp
      qed
      thus ?thesis using \<open>k = Suc k'\<close> by (simp add: Let_def)
    qed
  qed
  \<comment> \<open>Step 2: \<open>m_anc\<close> match by chain induction on \<open>p\<close>.\<close>
  show ?case using p_lt'
  proof (induct p arbitrary: q rule: less_induct)
    case (less p)
    note IH_p = less.hyps
    note p_lt'' = less.prems
    have mp_p: "m_parent (expansion A (n - 1)) k p = m_parent (A[n]) k p"
      using mp_match[OF p_lt''] .
    show "m_ancestor (expansion A (n - 1)) k p q \<longleftrightarrow> m_ancestor (A[n]) k p q"
    proof (cases "m_parent (expansion A (n - 1)) k p")
      case None
      have mp_AEn_none: "m_parent (A[n]) k p = None" using None mp_p by simp
      have lhs_F: "\<not> m_ancestor (expansion A (n - 1)) k p q"
        using m_anc_via_parent_none[OF None] .
      have rhs_F: "\<not> m_ancestor (A[n]) k p q"
        using m_anc_via_parent_none[OF mp_AEn_none] .
      show ?thesis using lhs_F rhs_F by simp
    next
      case (Some r)
      have mp_AEn_some: "m_parent (A[n]) k p = Some r" using Some mp_p by simp
      have r_lt: "r < p" using Some by (rule m_parent_lt)
      have r_lt_idx: "r < idx_B_in_expansion A (n - 1) (l1 A)"
        using r_lt p_lt'' by linarith
      have iff_A: "m_ancestor (expansion A (n - 1)) k p q
                \<longleftrightarrow> r = q \<or> m_ancestor (expansion A (n - 1)) k r q"
        using m_anc_via_parent_some[OF Some] .
      have iff_AEn: "m_ancestor (A[n]) k p q
                  \<longleftrightarrow> r = q \<or> m_ancestor (A[n]) k r q"
        using m_anc_via_parent_some[OF mp_AEn_some] .
      have rec: "m_ancestor (expansion A (n - 1)) k r q
              \<longleftrightarrow> m_ancestor (A[n]) k r q"
        using IH_p[OF r_lt r_lt_idx] .
      show ?thesis using iff_A iff_AEn rec by blast
    qed
  qed
qed

text \<open>
  Step lemma for clause (iii): assumes IH (= full lemma_2_5_at at k' < k),
  IH at \<open>n-1\<close> for same \<open>k\<close>, AND clause (ii) at same level \<open>k\<close>
  (per dependency matrix; IH at \<open>n-1\<close> provides \<open>lemma_2_5_ii_clause A (n-1) k\<close>,
  used in chain translation).
\<close>

lemma lemma_2_5_iii_clause_step:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and IH_n_minus_1: "lemma_2_5_at A (n - 1) k"
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
        \<comment> \<open>Truly substantive: \<open>k < m\<^sub>0\<close>. Strategy combines four
            sub-helpers: first-step in \<open>A\<close>, first-step in \<open>A[n]\<close>,
            Lemma A (orig vs A[n] shared cols), Lemma A' (A[n-1] vs A[n] shared cols),
            plus (ii) for \<open>A[n-1]\<close> at \<open>k\<close> via IH at n-1.\<close>
        have k_lt_m0: "k < m\<^sub>0" using True .
        have n_pos: "0 < n" using \<open>n = Suc n'\<close> by simp
        show ?thesis
          unfolding lemma_2_5_iii_clause_def
        proof (intro allI impI)
          fix m_0' i
          assume h: "0 < n \<and> max_parent_level A = Some m_0' \<and> k < m_0' \<and> i < l1 A"
          hence i_lt: "i < l1 A" by simp
          have l1_pos: "0 < l1 A" using i_lt by linarith
          let ?L = "l1 A - 1"
          have L_lt: "?L < l1 A" using l1_pos by simp
          \<comment> \<open>First step in \<open>A\<close>.\<close>
          have first_A: "m_parent A k (last_col_idx A) = Some (idx_B0_in_orig A ?L)"
            by (rule m_parent_orig_last_col_when_k_lt_m0
                  [OF A_BMS A_ne \<open>b0_start A = Some s\<close>
                      \<open>max_parent_level A = Some m\<^sub>0\<close> k_lt_m0 l1_pos])
          \<comment> \<open>First step in \<open>A[n]\<close>.\<close>
          have first_AEn: "m_parent (A[n]) k (idx_B_in_expansion A n 0)
                         = Some (idx_B_in_expansion A (n - 1) ?L)"
            by (rule m_parent_AEn_idx_B_n_zero_when_k_lt_m0
                  [OF A_BMS A_ne \<open>b0_start A = Some s\<close>
                      \<open>max_parent_level A = Some m\<^sub>0\<close> k_lt_m0 n_pos l1_pos])
          \<comment> \<open>LHS chain decomposition.\<close>
          have LHS_iff: "m_ancestor A k (last_col_idx A) (idx_B0_in_orig A i)
                      \<longleftrightarrow> (idx_B0_in_orig A ?L = idx_B0_in_orig A i)
                          \<or> m_ancestor A k (idx_B0_in_orig A ?L) (idx_B0_in_orig A i)"
            using m_anc_via_parent_some[OF first_A] .
          \<comment> \<open>RHS chain decomposition.\<close>
          have RHS_iff: "m_ancestor (A[n]) k (idx_B_in_expansion A n 0)
                                              (idx_B_in_expansion A (n - 1) i)
                      \<longleftrightarrow> (idx_B_in_expansion A (n - 1) ?L = idx_B_in_expansion A (n - 1) i)
                          \<or> m_ancestor (A[n]) k (idx_B_in_expansion A (n - 1) ?L)
                                                (idx_B_in_expansion A (n - 1) i)"
            using m_anc_via_parent_some[OF first_AEn] .
          \<comment> \<open>Equality of the two disjuncts (both reduce to \<open>l_1 - 1 = i\<close>).\<close>
          have eq_iff: "(idx_B0_in_orig A ?L = idx_B0_in_orig A i)
                      \<longleftrightarrow> (idx_B_in_expansion A (n - 1) ?L = idx_B_in_expansion A (n - 1) i)"
            unfolding idx_B0_in_orig_def idx_B_in_expansion_def by simp
          \<comment> \<open>Identify \<open>idx_B0_in_orig\<close> with \<open>idx_B_in_expansion ... 0\<close>.\<close>
          have B0_eq_BEn0_L: "idx_B0_in_orig A ?L = idx_B_in_expansion A 0 ?L"
            unfolding idx_B0_in_orig_def idx_B_in_expansion_def by simp
          have B0_eq_BEn0_i: "idx_B0_in_orig A i = idx_B_in_expansion A 0 i"
            unfolding idx_B0_in_orig_def idx_B_in_expansion_def by simp
          \<comment> \<open>Step 1: Lemma A translates the original-A chain to A[n].\<close>
          have step1: "m_ancestor A k (idx_B0_in_orig A ?L) (idx_B0_in_orig A i)
                    \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A 0 ?L)
                                            (idx_B_in_expansion A 0 i)"
          proof -
            have p_lt: "idx_B0_in_orig A ?L < idx_B_in_expansion A 0 (l1 A)"
              using L_lt unfolding idx_B0_in_orig_def idx_B_in_expansion_def by simp
            have lemA: "m_ancestor A k (idx_B0_in_orig A ?L) (idx_B0_in_orig A i)
                      \<longleftrightarrow> m_ancestor (A[n]) k (idx_B0_in_orig A ?L) (idx_B0_in_orig A i)"
              by (rule m_anc_orig_eq_AEn_shared_B0
                    [OF A_BMS A_ne \<open>b0_start A = Some s\<close>
                        \<open>max_parent_level A = Some m\<^sub>0\<close> k_lt_m0 n_pos p_lt])
            show ?thesis using lemA B0_eq_BEn0_L B0_eq_BEn0_i by simp
          qed
          \<comment> \<open>Intermediate chain translation. Split on \<open>n - 1 = 0\<close> (n=1, chain
              collapses) vs \<open>0 < n - 1\<close> (n\<ge>2, full chain via Lemma A' +
              (ii) for \<open>A[n-1]\<close> at k).\<close>
          have intermediate:
            "m_ancestor A k (idx_B0_in_orig A ?L) (idx_B0_in_orig A i)
            \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (n - 1) ?L)
                                    (idx_B_in_expansion A (n - 1) i)"
          proof (cases "n - 1 = 0")
            case True
            \<comment> \<open>\<open>n = 1\<close>: \<open>idx_B(n-1, *) = idx_B(0, *)\<close>, intermediate
                reduces to step1 (Lemma A) with index rewrites.\<close>
            have nm1_eq_0: "n - 1 = 0" using True .
            have eq_L: "idx_B_in_expansion A (n - 1) ?L = idx_B_in_expansion A 0 ?L"
              using nm1_eq_0 by simp
            have eq_i: "idx_B_in_expansion A (n - 1) i = idx_B_in_expansion A 0 i"
              using nm1_eq_0 by simp
            show ?thesis using step1 eq_L eq_i by simp
          next
            case False
            \<comment> \<open>\<open>n \<ge> 2\<close>: Lemma A' applies. step2 + step3 + step4.\<close>
            have n_minus_1_pos: "0 < n - 1" using False by simp
            have step2: "m_ancestor (A[n]) k (idx_B_in_expansion A 0 ?L)
                                            (idx_B_in_expansion A 0 i)
                      \<longleftrightarrow> m_ancestor (expansion A (n - 1)) k (idx_B_in_expansion A 0 ?L)
                                                (idx_B_in_expansion A 0 i)"
            proof -
              have p_lt: "idx_B_in_expansion A 0 ?L < idx_B_in_expansion A (n - 1) (l1 A)"
                using L_lt n_minus_1_pos unfolding idx_B_in_expansion_def by simp
              show ?thesis
                using m_anc_AEn_minus_1_eq_AEn_shared
                        [OF A_BMS A_ne \<open>b0_start A = Some s\<close>
                            \<open>max_parent_level A = Some m\<^sub>0\<close> k_lt_m0 n_minus_1_pos p_lt]
                by blast
            qed
            have step3: "m_ancestor (expansion A (n - 1)) k (idx_B_in_expansion A 0 ?L)
                                              (idx_B_in_expansion A 0 i)
                      \<longleftrightarrow> m_ancestor (expansion A (n - 1)) k (idx_B_in_expansion A (n - 1) ?L)
                                                (idx_B_in_expansion A (n - 1) i)"
            proof -
              have ii_at_nm1: "lemma_2_5_ii_clause A (n - 1) k"
                using IH_n_minus_1 unfolding lemma_2_5_at_def by blast
              show ?thesis
                using ii_at_nm1 L_lt i_lt
                unfolding lemma_2_5_ii_clause_def by blast
            qed
            have step4: "m_ancestor (expansion A (n - 1)) k (idx_B_in_expansion A (n - 1) ?L)
                                              (idx_B_in_expansion A (n - 1) i)
                      \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (n - 1) ?L)
                                              (idx_B_in_expansion A (n - 1) i)"
            proof -
              have p_lt: "idx_B_in_expansion A (n - 1) ?L < idx_B_in_expansion A (n - 1) (l1 A)"
                using L_lt unfolding idx_B_in_expansion_def by simp
              show ?thesis
                by (rule m_anc_AEn_minus_1_eq_AEn_shared
                      [OF A_BMS A_ne \<open>b0_start A = Some s\<close>
                          \<open>max_parent_level A = Some m\<^sub>0\<close> k_lt_m0 n_minus_1_pos p_lt])
            qed
            show ?thesis using step1 step2 step3 step4 by simp
          qed
          show "m_ancestor A k (last_col_idx A) (idx_B0_in_orig A i)
              \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n 0)
                                      (idx_B_in_expansion A (n - 1) i)"
            using LHS_iff RHS_iff intermediate eq_iff by blast
        qed
      qed
    qed
  qed
qed

text \<open>
  Step lemma stubs for clauses (iv), (i), (v) per Hunter's
  dependency order (ii) \<rightarrow> (iii) \<rightarrow> (iv) \<rightarrow> (i) \<rightarrow> (v).
  Substantive proofs deferred; the assembly into
  \<open>lemma_2_5_at_main\<close> below uses them mechanically.
\<close>

lemma lemma_2_5_iv_clause_step:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
  shows "lemma_2_5_iv_clause A n k"
proof (cases n)
  case 0
  \<comment> \<open>\<open>n = 0\<close>: block 0 is the only B-block, so positions
      \<open>< idx_B(0, i) = l_0 + i\<close> are either G-cols (\<open>< l_0\<close>)
      or block-0 B-cols (\<open>l_0 \<le> ... < l_0 + i\<close>). Either way,
      the disjunctive structure is satisfied.\<close>
  show ?thesis
    unfolding lemma_2_5_iv_clause_def
  proof (intro allI impI)
    fix i assume h: "0 < i \<and> i < l1 A"
    hence i_pos: "0 < i" and i_lt: "i < l1 A" by simp+
    let ?tgt = "idx_B_in_expansion A n i"
    have tgt_eq: "?tgt = l0 A + i"
      using \<open>n = 0\<close> unfolding idx_B_in_expansion_def by simp
    show "m_parent (A[n]) k ?tgt = None
        \<or> (\<exists>p. m_parent (A[n]) k ?tgt = Some p
               \<and> ((\<exists>j<l1 A. p = idx_B_in_expansion A n j)
                  \<or> (\<exists>j<l0 A. p = idx_G A j)))"
    proof (cases "m_parent (A[n]) k ?tgt")
      case None thus ?thesis by simp
    next
      case (Some p)
      have p_lt: "p < ?tgt" using Some by (rule m_parent_lt)
      hence p_lt_b: "p < l0 A + i" using tgt_eq by simp
      show ?thesis
      proof (cases "p < l0 A")
        case True
        \<comment> \<open>\<open>p < l_0\<close>: G-col. \<open>idx_G A p = p\<close>.\<close>
        have "p = idx_G A p" unfolding idx_G_def by simp
        thus ?thesis using Some True by blast
      next
        case False
        hence p_ge: "l0 A \<le> p" by simp
        define j where "j = p - l0 A"
        have p_eq: "p = l0 A + j" using p_ge j_def by simp
        have j_lt_i: "j < i"
          using p_eq p_lt_b by simp
        hence j_lt_l1: "j < l1 A" using i_lt by linarith
        have p_as_idxB: "p = idx_B_in_expansion A n j"
          using p_eq \<open>n = 0\<close> unfolding idx_B_in_expansion_def by simp
        show ?thesis using Some j_lt_l1 p_as_idxB by blast
      qed
    qed
  qed
next
  case (Suc n')
  \<comment> \<open>\<open>n \<ge> 1\<close>: substantive case. Requires BMS structural
      property that block-\<open>n\<close> partial cand exists when any
      earlier-block cand is available (or that earlier-block
      cands are excluded for other structural reasons). Left
      as sorry pending @{thm BMS_all_B0_ascending_below_t}
      inductive case and additional infrastructure.\<close>
  show ?thesis sorry
qed

lemma lemma_2_5_i_clause_step:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and clause_iv_at_k: "lemma_2_5_iv_clause A n k"
  shows "lemma_2_5_i_clause A n k"
  sorry

lemma lemma_2_5_v_clause_step:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_i_at_k: "lemma_2_5_i_clause A n k"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and clause_iv_at_k: "lemma_2_5_iv_clause A n k"
  shows "lemma_2_5_v_clause A n k"
  sorry

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
          by (rule lemma_2_5_ii_clause_step[OF A_BMS A_ne IH_at_n])
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

end
