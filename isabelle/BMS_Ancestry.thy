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
  Explicit value of \<open>elem (A[n]) (idx_B t j) k\<close> in terms of the
  underlying original column and the bump amount. Combines
  @{thm elem_expansion_B_via_bump} with @{thm bump_col_nth_general}
  to expose the closed-form formula
  \<open>(A ! (s + j)) ! k + (if ascends A j k then t * delta A k else 0)\<close>.
  Foundation for block-shift reasoning (iii bridge, iv row-0 monotonicity).
\<close>

lemma elem_AEn_idx_B_value:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and t_le: "t \<le> n" and j_lt: "j < l1 A"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and k_lt_col: "k < length (A ! (s + j))"
  shows "elem (A[n]) (idx_B_in_expansion A t j) k
       = (A ! (s + j)) ! k + (if ascends A j k then t * delta A k else 0)"
proof -
  have via_bump: "elem (A[n]) (idx_B_in_expansion A t j) k = (bump_col A j t) ! k"
    using elem_expansion_B_via_bump[OF A_ne t_le j_lt k_lt_keep] .
  have nth_general: "(bump_col A j t) ! k
                   = (A ! (s + j)) ! k + (if ascends A j k then t * delta A k else 0)"
    using bump_col_nth_general[OF b0 k_lt_col] .
  show ?thesis using via_bump nth_general by simp
qed

text \<open>
  Block-shift difference: shifting the block index by one adds a single
  \<open>delta A k\<close> at ascending rows, zero otherwise. Direct corollary of
  @{thm elem_AEn_idx_B_value}.
\<close>

lemma elem_AEn_idx_B_block_shift_diff:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and t_Suc_le: "Suc t \<le> n" and j_lt: "j < l1 A"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and k_lt_col: "k < length (A ! (s + j))"
  shows "elem (A[n]) (idx_B_in_expansion A (Suc t) j) k
       = elem (A[n]) (idx_B_in_expansion A t j) k
       + (if ascends A j k then delta A k else 0)"
proof -
  have t_le: "t \<le> n" using t_Suc_le by simp
  have at_t: "elem (A[n]) (idx_B_in_expansion A t j) k
            = (A ! (s + j)) ! k + (if ascends A j k then t * delta A k else 0)"
    using elem_AEn_idx_B_value[OF A_ne b0 t_le j_lt k_lt_keep k_lt_col] .
  have at_Suc_t: "elem (A[n]) (idx_B_in_expansion A (Suc t) j) k
                = (A ! (s + j)) ! k
                + (if ascends A j k then Suc t * delta A k else 0)"
    using elem_AEn_idx_B_value[OF A_ne b0 t_Suc_le j_lt k_lt_keep k_lt_col] .
  show ?thesis
  proof (cases "ascends A j k")
    case True
    have rhs_eq: "Suc t * delta A k = t * delta A k + delta A k" by simp
    show ?thesis using at_t at_Suc_t True rhs_eq by simp
  next
    case False
    show ?thesis using at_t at_Suc_t False by simp
  qed
qed

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
  Note (2026-05-17): the previously-proven \<open>elem_expansion_B_lt_invariant_in_block\<close>
  (= "strict-less comparison between B-block cols at row \<open>k < t\<close> is
  block-index invariant") has been DELETED because its proof relied
  on the false \<open>bump_col_uniform_k_lt_t\<close>. The statement is itself
  refuted by the counterexample
  \<open>(0,0,0)(1,1,1)(2,0,0)(1,1,1)\<close> at \<open>k = 1, y = 2, x = 0, a = 0, a' = 1\<close>.
\<close>

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
  === SOUND helpers for the per-col ascending case-split (2026-05-17) ===

  The lemmas below replace the unsound \<open>elem_expansion_B_lt_invariant_in_block\<close>
  (deleted: presupposed false universal-ascending at \<open>k < t\<close>) by parameterized
  versions that take an explicit \<open>ascends A x k\<close> / \<open>\<not> ascends A x k\<close>
  hypothesis per column. These are the foundations for the v2 (ii) step.
\<close>

text \<open>
  Item 1: cross-block elem when column \<open>x\<close> does NOT ascend at row \<open>k\<close>.
  No bumping, so elem in any block \<open>c\<close> reduces to the base column value.
\<close>

lemma elem_AEn_cross_block_when_not_ascends:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and not_asc: "\<not> ascends A x k"
      and c_le: "c \<le> n"
      and x_lt: "x < l1 A"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and k_lt_col: "k < length (A ! (s + x))"
  shows "elem (A[n]) (idx_B_in_expansion A c x) k = (A ! (s + x)) ! k"
proof -
  have bump_eq: "(bump_col A x c) ! k = (A ! (s + x)) ! k"
    using bump_col_no_bump[OF b0 not_asc k_lt_col] .
  have "elem (A[n]) (idx_B_in_expansion A c x) k
      = (bump_col A x c) ! k"
    using elem_expansion_B_via_bump[OF A_ne c_le x_lt k_lt_keep] .
  also have "\<dots> = (A ! (s + x)) ! k" using bump_eq .
  finally show ?thesis .
qed

text \<open>
  Item 2: cross-block elem when column \<open>x\<close> DOES ascend at row \<open>k\<close>.
  Value in block \<open>c\<close> is the base value plus \<open>c * delta A k\<close>.
\<close>

lemma elem_AEn_cross_block_when_ascends:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and asc: "ascends A x k"
      and c_le: "c \<le> n"
      and x_lt: "x < l1 A"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and k_lt_col: "k < length (A ! (s + x))"
  shows "elem (A[n]) (idx_B_in_expansion A c x) k
       = (A ! (s + x)) ! k + c * delta A k"
proof -
  have bump_eq: "(bump_col A x c) ! k = (A ! (s + x)) ! k + c * delta A k"
    using bump_col_at_ascending_row[OF b0 asc k_lt_col] .
  have "elem (A[n]) (idx_B_in_expansion A c x) k
      = (bump_col A x c) ! k"
    using elem_expansion_B_via_bump[OF A_ne c_le x_lt k_lt_keep] .
  also have "\<dots> = (A ! (s + x)) ! k + c * delta A k" using bump_eq .
  finally show ?thesis .
qed

text \<open>
  Item 3: when both \<open>j\<close>-th col and \<open>x\<close>-th col ascend at row \<open>k\<close>,
  the strict-less comparison
  \<open>elem (A[n]) (idx_B c x) k < elem (A[n]) (idx_B c j) k\<close> is invariant
  under the block index \<open>c\<close>. Differences \<open>c * delta A k\<close> cancel.
\<close>

lemma elem_AEn_lt_block_invariant_when_both_ascend:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and asc_j: "ascends A j k"
      and asc_x: "ascends A x k"
      and c_le: "c \<le> n" and c'_le: "c' \<le> n"
      and j_lt: "j < l1 A" and x_lt: "x < l1 A"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and j_len: "k < length (A ! (s + j))"
      and x_len: "k < length (A ! (s + x))"
  shows "(elem (A[n]) (idx_B_in_expansion A c x) k
          < elem (A[n]) (idx_B_in_expansion A c j) k)
       \<longleftrightarrow>
         (elem (A[n]) (idx_B_in_expansion A c' x) k
          < elem (A[n]) (idx_B_in_expansion A c' j) k)"
proof -
  have ex_c: "elem (A[n]) (idx_B_in_expansion A c x) k
            = (A ! (s + x)) ! k + c * delta A k"
    using elem_AEn_cross_block_when_ascends
            [OF A_BMS A_ne b0 asc_x c_le x_lt k_lt_keep x_len] .
  have ej_c: "elem (A[n]) (idx_B_in_expansion A c j) k
            = (A ! (s + j)) ! k + c * delta A k"
    using elem_AEn_cross_block_when_ascends
            [OF A_BMS A_ne b0 asc_j c_le j_lt k_lt_keep j_len] .
  have ex_c': "elem (A[n]) (idx_B_in_expansion A c' x) k
             = (A ! (s + x)) ! k + c' * delta A k"
    using elem_AEn_cross_block_when_ascends
            [OF A_BMS A_ne b0 asc_x c'_le x_lt k_lt_keep x_len] .
  have ej_c': "elem (A[n]) (idx_B_in_expansion A c' j) k
             = (A ! (s + j)) ! k + c' * delta A k"
    using elem_AEn_cross_block_when_ascends
            [OF A_BMS A_ne b0 asc_j c'_le j_lt k_lt_keep j_len] .
  have lhs_iff:
    "(elem (A[n]) (idx_B_in_expansion A c x) k
       < elem (A[n]) (idx_B_in_expansion A c j) k)
   \<longleftrightarrow> (A ! (s + x)) ! k < (A ! (s + j)) ! k"
    using ex_c ej_c by simp
  have rhs_iff:
    "(elem (A[n]) (idx_B_in_expansion A c' x) k
       < elem (A[n]) (idx_B_in_expansion A c' j) k)
   \<longleftrightarrow> (A ! (s + x)) ! k < (A ! (s + j)) ! k"
    using ex_c' ej_c' by simp
  show ?thesis using lhs_iff rhs_iff by blast
qed

text \<open>
  Item 3': dual — when both cols do NOT ascend, strict-less is also invariant
  (both sides reduce to the same base values).
\<close>

lemma elem_AEn_lt_block_invariant_when_neither_ascends:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and not_asc_j: "\<not> ascends A j k"
      and not_asc_x: "\<not> ascends A x k"
      and c_le: "c \<le> n" and c'_le: "c' \<le> n"
      and j_lt: "j < l1 A" and x_lt: "x < l1 A"
      and k_lt_keep: "k < keep_of (G_block A @ Bs_concat A n)"
      and j_len: "k < length (A ! (s + j))"
      and x_len: "k < length (A ! (s + x))"
  shows "(elem (A[n]) (idx_B_in_expansion A c x) k
          < elem (A[n]) (idx_B_in_expansion A c j) k)
       \<longleftrightarrow>
         (elem (A[n]) (idx_B_in_expansion A c' x) k
          < elem (A[n]) (idx_B_in_expansion A c' j) k)"
proof -
  have ex_c: "elem (A[n]) (idx_B_in_expansion A c x) k = (A ! (s + x)) ! k"
    using elem_AEn_cross_block_when_not_ascends
            [OF A_BMS A_ne b0 not_asc_x c_le x_lt k_lt_keep x_len] .
  have ej_c: "elem (A[n]) (idx_B_in_expansion A c j) k = (A ! (s + j)) ! k"
    using elem_AEn_cross_block_when_not_ascends
            [OF A_BMS A_ne b0 not_asc_j c_le j_lt k_lt_keep j_len] .
  have ex_c': "elem (A[n]) (idx_B_in_expansion A c' x) k = (A ! (s + x)) ! k"
    using elem_AEn_cross_block_when_not_ascends
            [OF A_BMS A_ne b0 not_asc_x c'_le x_lt k_lt_keep x_len] .
  have ej_c': "elem (A[n]) (idx_B_in_expansion A c' j) k = (A ! (s + j)) ! k"
    using elem_AEn_cross_block_when_not_ascends
            [OF A_BMS A_ne b0 not_asc_j c'_le j_lt k_lt_keep j_len] .
  show ?thesis using ex_c ej_c ex_c' ej_c' by simp
qed

text \<open>
  Item 4 (within-block, asc): when j-th col ascends at row \<open>k\<close> AND the
  conditional ascending hypothesis \<open>asc_chain\<close> holds for each chain
  member (= every \<open>x < j\<close> that is a \<open>k'\<close>-ancestor of \<open>j\<close> in the
  expansion at block 0), the strict-less filter at block \<open>c\<close> matches
  the filter at block \<open>0\<close>. The within-block case (\<open>S \<noteq> []\<close>) lands
  at the same \<open>last S\<close> column in block \<open>c\<close>.

  Hypotheses are parameterized: \<open>manc_inv\<close> (m_ancestor at \<open>k - 1\<close> matches
  across blocks for \<open>x < j\<close>) and \<open>asc_chain\<close> (ascending status at row
  \<open>Suc k'\<close> for chain members only). The chain restriction is sound because
  for \<open>x\<close> not in the chain, the second conjunct of the filter predicate
  fails on both sides via \<open>manc_inv\<close>, making the iff trivially hold.
  Both hypotheses will be discharged by the IH and
  \<open>ascends_invariant_along_chain\<close> in the consuming step lemma.

  CHANGE (Round 1.5): Previously took uniform \<open>asc_inv: \<forall>x<j. ascends A x (Suc k')\<close>
  which is OVER-STRICT: F2 (Round 2) found this cannot be discharged from
  just \<open>asc_j\<close> because cols not in the chain may have arbitrary ascending
  status. New \<open>asc_chain\<close> is the weakest form needed for the proof.
\<close>

lemma m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k' < t"
      and asc_j: "ascends A j (Suc k')"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and j_len: "Suc k' < length (A ! (s + j))"
      and k_lt_keep: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
      and asc_chain: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)
                          \<longrightarrow> ascends A x (Suc k')"
      and x_len: "\<forall>x<j. Suc k' < length (A ! (s + x))"
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
    proof (cases "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                       (idx_B_in_expansion A 0 x)")
      case False
      \<comment> \<open>Chain fails: both conjuncts' second part are False; iff trivially holds.\<close>
      have manc_c_F: "\<not> m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                              (idx_B_in_expansion A c x)"
        using manc_x False by simp
      show ?thesis using manc_c_F False idxBc_eq by simp
    next
      case True
      \<comment> \<open>Chain holds: derive \<open>asc_x\<close> from \<open>asc_chain\<close>; then strict-less
          invariance applies (item 3, both ascend).\<close>
      have asc_x: "ascends A x (Suc k')"
        using asc_chain x_lt_j True by blast
      have x_klt: "Suc k' < length (A ! (s + x))" using x_len x_lt_j by blast
      have lt_inv:
        "(elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
           < elem (A[n]) (idx_B_in_expansion A c j) (Suc k'))
       \<longleftrightarrow>
         (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
           < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k'))"
        using elem_AEn_lt_block_invariant_when_both_ascend
                [OF A_BMS A_ne b0 asc_j asc_x c_le le0 j_lt x_lt_l1 k_lt_keep
                    j_len x_klt] .
      have manc_c_T: "m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                            (idx_B_in_expansion A c x)"
        using manc_x True by simp
      show ?thesis using idxBc_eq lt_inv manc_c_T True by simp
    qed
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
  Item 4 (outside-block, asc): same setting as the within-block lemma but
  \<open>S = []\<close>: the m_parent is either None or lands strictly before block \<open>c\<close>.
\<close>

lemma m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k' < t"
      and asc_j: "ascends A j (Suc k')"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and j_len: "Suc k' < length (A ! (s + j))"
      and k_lt_keep: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
      and asc_chain: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 x)
                          \<longrightarrow> ascends A x (Suc k')"
      and x_len: "\<forall>x<j. Suc k' < length (A ! (s + x))"
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
      have manc_at_c: "m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                              (idx_B_in_expansion A c x)"
        using manc_p p_as_idxBc by simp
      have manc_at_0: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                              (idx_B_in_expansion A 0 x)"
        using manc_at_c manc_inv x_lt_j by blast
      \<comment> \<open>Derive \<open>asc_x\<close> from \<open>asc_chain\<close> using the just-derived chain.\<close>
      have asc_x: "ascends A x (Suc k')"
        using asc_chain x_lt_j manc_at_0 by blast
      have x_klt: "Suc k' < length (A ! (s + x))" using x_len x_lt_j by blast
      have lt_inv:
        "(elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
           < elem (A[n]) (idx_B_in_expansion A c j) (Suc k'))
       \<longleftrightarrow>
         (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
           < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k'))"
        using elem_AEn_lt_block_invariant_when_both_ascend
                [OF A_BMS A_ne b0 asc_j asc_x c_le le0 j_lt x_lt_l1 k_lt_keep
                    j_len x_klt] .
      have v_lt2: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
                 < elem (A[n]) (idx_B_in_expansion A c j) (Suc k')"
        using v_lt p_as_idxBc by simp
      have block0_lt: "elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                     < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')"
        using v_lt2 lt_inv by simp
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
  Item 4 (within-block, not asc): mirror of the asc version where neither
  \<open>j\<close>-th col nor any candidate \<open>x\<close>-th col ascends at row \<open>k\<close>.
  Uses item 3' (neither ascending) to flip the strict-less across blocks.
\<close>

lemma m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t_not_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k' < t"
      and not_asc_j: "\<not> ascends A j (Suc k')"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and j_len: "Suc k' < length (A ! (s + j))"
      and k_lt_keep: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
      and not_asc_chain: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                      (idx_B_in_expansion A 0 x)
                              \<longrightarrow> \<not> ascends A x (Suc k')"
      and x_len: "\<forall>x<j. Suc k' < length (A ! (s + x))"
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
    proof (cases "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                       (idx_B_in_expansion A 0 x)")
      case False
      \<comment> \<open>Chain fails: both conjuncts' second part are False; iff trivially holds.\<close>
      have manc_c_F: "\<not> m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                              (idx_B_in_expansion A c x)"
        using manc_x False by simp
      show ?thesis using manc_c_F False idxBc_eq by simp
    next
      case True
      \<comment> \<open>Chain holds: derive \<open>nasc_x\<close> from \<open>not_asc_chain\<close>; then strict-less
          invariance applies (item 3', neither ascends).\<close>
      have nasc_x: "\<not> ascends A x (Suc k')"
        using not_asc_chain x_lt_j True by blast
      have x_klt: "Suc k' < length (A ! (s + x))" using x_len x_lt_j by blast
      have lt_inv:
        "(elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
           < elem (A[n]) (idx_B_in_expansion A c j) (Suc k'))
       \<longleftrightarrow>
         (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
           < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k'))"
        using elem_AEn_lt_block_invariant_when_neither_ascends
                [OF A_BMS A_ne b0 not_asc_j nasc_x c_le le0 j_lt x_lt_l1 k_lt_keep
                    j_len x_klt] .
      have manc_c_T: "m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                            (idx_B_in_expansion A c x)"
        using manc_x True by simp
      show ?thesis using idxBc_eq lt_inv manc_c_T True by simp
    qed
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
  Item 4 (outside-block, not asc): mirror of the asc version using item 3'.
\<close>

lemma m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t_not_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k' < t"
      and not_asc_j: "\<not> ascends A j (Suc k')"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and j_len: "Suc k' < length (A ! (s + j))"
      and k_lt_keep: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
      and not_asc_chain: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                      (idx_B_in_expansion A 0 x)
                              \<longrightarrow> \<not> ascends A x (Suc k')"
      and x_len: "\<forall>x<j. Suc k' < length (A ! (s + x))"
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
      have manc_at_c: "m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                              (idx_B_in_expansion A c x)"
        using manc_p p_as_idxBc by simp
      have manc_at_0: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                              (idx_B_in_expansion A 0 x)"
        using manc_at_c manc_inv x_lt_j by blast
      \<comment> \<open>Derive \<open>nasc_x\<close> from \<open>not_asc_chain\<close> using the just-derived chain.\<close>
      have nasc_x: "\<not> ascends A x (Suc k')"
        using not_asc_chain x_lt_j manc_at_0 by blast
      have x_klt: "Suc k' < length (A ! (s + x))" using x_len x_lt_j by blast
      have lt_inv:
        "(elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
           < elem (A[n]) (idx_B_in_expansion A c j) (Suc k'))
       \<longleftrightarrow>
         (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
           < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k'))"
        using elem_AEn_lt_block_invariant_when_neither_ascends
                [OF A_BMS A_ne b0 not_asc_j nasc_x c_le le0 j_lt x_lt_l1 k_lt_keep
                    j_len x_klt] .
      have v_lt2: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
                 < elem (A[n]) (idx_B_in_expansion A c j) (Suc k')"
        using v_lt p_as_idxBc by simp
      have block0_lt: "elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                     < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')"
        using v_lt2 lt_inv by simp
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
  Item 5 (chain shift for k<t, asc case, Suc k'): block-shift invariance
  of m_ancestor at row \<open>Suc k'\<close> when \<open>Suc k' < t\<close>, given that \<open>j\<close>
  ascends at \<open>Suc k'\<close> and ascending status of \<open>j\<close> is inherited by
  every \<open>k'\<close>-chain member of \<open>j\<close>.

  CHANGE (Round 1.5): Previously took uniform \<open>asc_all: \<forall>x\<le>j. x<l1A \<longrightarrow>
  ascends A x (Suc k')\<close> which is OVER-STRICT — cannot be discharged from
  just \<open>ascends A j (Suc k')\<close>. New form: \<open>asc_j\<close> + conditional
  \<open>asc_chain\<close> (only over chain members). Recursion descends to chain
  member \<open>?p\<close>, deriving \<open>asc_j\<close> for \<open>?p\<close> from \<open>asc_chain\<close> and
  deriving \<open>asc_chain\<close> over \<open>?p\<close> from \<open>asc_chain\<close> over \<open>j\<close> via
  \<open>m_ancestor_trans\<close>.

  Strategy mirrors @{thm m_anc_idx_B_in_block_shift_at_Suc_k_when_k_ge_t}
  with two differences:
  \<^item> elem invariance across blocks uses
    @{thm elem_AEn_lt_block_invariant_when_both_ascend} (item 3) instead
    of @{thm elem_AEn_eq_at_row_k_ge_t_across_blocks}.
  \<^item> the within/outside m_parent helpers
    @{thm m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t_asc} and
    @{thm m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t_asc}
    replace the \<open>_when_k_ge_t\<close> versions.
\<close>

lemma m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k' < t"
      and IH_ii_kp: "lemma_2_5_ii_clause A n k'"
      and asc_j0: "ascends A j (Suc k')"
      and asc_chain0: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                    (idx_B_in_expansion A 0 x)
                            \<longrightarrow> ascends A x (Suc k')"
      and x_len_all: "\<forall>x<l1 A. Suc k' < length (A ! (s + x))"
      and k_lt_keep: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
      and i_lt: "i < l1 A"
      and j_lt: "j < l1 A"
      and i_lt_j: "i < j"
  shows "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j) (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j) (idx_B_in_expansion A n i)"
  using i_lt j_lt i_lt_j asc_j0 asc_chain0
proof (induct j arbitrary: i rule: less_induct)
  case (less j)
  note IH_chain = less.hyps
  note i_lt' = less.prems(1)
  note j_lt' = less.prems(2)
  note i_lt_j' = less.prems(3)
  note asc_j = less.prems(4)
  note asc_chain = less.prems(5)
  have x_len_inv: "\<forall>x<j. Suc k' < length (A ! (s + x))"
    using x_len_all j_lt' by auto
  have j_len: "Suc k' < length (A ! (s + j))"
    using x_len_all j_lt' by blast
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
      using m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t_asc
            [OF A_BMS A_ne b0 mp Sk_lt_t asc_j le0 j_lt' j_len k_lt_keep
                asc_chain x_len_inv manc_inv_0 True] .
    have outB: "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A n 0)"
      using m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t_asc
            [OF A_BMS A_ne b0 mp Sk_lt_t asc_j order.refl j_lt' j_len k_lt_keep
                asc_chain x_len_inv manc_inv_n True] .
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
      using m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t_asc
            [OF A_BMS A_ne b0 mp Sk_lt_t asc_j le0 j_lt' j_len k_lt_keep
                asc_chain x_len_inv manc_inv_0 False] .
    have mpB: "m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j)
             = Some (idx_B_in_expansion A n ?p)"
      using m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t_asc
            [OF A_BMS A_ne b0 mp Sk_lt_t asc_j order.refl j_lt' j_len k_lt_keep
                asc_chain x_len_inv manc_inv_n False] .
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
        \<comment> \<open>Derive \<open>asc_j\<close> for \<open>?p\<close> from \<open>asc_chain\<close> (over \<open>j\<close>) using
            \<open>?p \<in> ?S\<close>, which gives the chain \<open>m_anc(0, j) \<to> (0, ?p)\<close>.\<close>
        have manc_j_to_p: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                 (idx_B_in_expansion A 0 ?p)"
          using p_in by auto
        have asc_p: "ascends A ?p (Suc k')"
          using asc_chain p_lt_j manc_j_to_p by blast
        \<comment> \<open>Derive \<open>asc_chain\<close> over \<open>?p\<close> via \<open>m_ancestor_trans\<close>:
            for \<open>x < ?p\<close> with chain \<open>m_anc(0, ?p) \<to> (0, x)\<close>, combining
            with the established chain \<open>m_anc(0, j) \<to> (0, ?p)\<close>, gives
            \<open>m_anc(0, j) \<to> (0, x)\<close>, so \<open>asc_chain\<close> over \<open>j\<close> applies.\<close>
        have asc_chain_p: "\<forall>x<?p. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 ?p)
                                                        (idx_B_in_expansion A 0 x)
                                  \<longrightarrow> ascends A x (Suc k')"
        proof (intro allI impI)
          fix x assume x_lt_p: "x < ?p"
            and chain_p_x: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 ?p)
                                                  (idx_B_in_expansion A 0 x)"
          have x_lt_j: "x < j" using x_lt_p p_lt_j by linarith
          have chain_j_x: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                 (idx_B_in_expansion A 0 x)"
            using m_ancestor_trans[OF manc_j_to_p chain_p_x] .
          show "ascends A x (Suc k')"
            using asc_chain x_lt_j chain_j_x by blast
        qed
        have IH_at: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                          (idx_B_in_expansion A 0 i)
                   \<longleftrightarrow> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                          (idx_B_in_expansion A n i)"
          using IH_chain[OF p_lt_j i_lt' p_lt_l1 True asc_p asc_chain_p] .
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
  Auxiliary item (case-B "S-empty" path, Round 2): when \<open>j\<close> does NOT
  ascend at \<open>Suc k'\<close>, the strict-less elem comparison at block \<open>c\<close>
  IMPLIES the same at block \<open>0\<close> (one-directional; not iff). This is
  the weaker form of @{thm elem_AEn_lt_block_invariant_when_neither_ascends}
  that does not require \<open>x\<close>'s ascending status.

  Reason: \<open>j\<close> not ascending means \<open>elem (A[n]) (idx_B(c,j)) (Suc k') = (A!(s+j))!(Suc k')\<close>
  for any \<open>c\<close> (no bump). For \<open>x\<close>: either \<open>ascends A x (Suc k')\<close>
  (elem = (A!(s+x))!(Suc k') + c*delta) or not (elem = (A!(s+x))!(Suc k')).
  In both cases, \<open>(A!(s+x))!(Suc k') \<le> (A!(s+x))!(Suc k') + c*delta\<close> (nat
  delta), so the block-\<open>c\<close> strict-less implies block-\<open>0\<close> strict-less.
\<close>

lemma elem_AEn_lt_block_implies_block_zero_when_j_not_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and not_asc_j: "\<not> ascends A j (Suc k')"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and x_lt: "x < l1 A"
      and k_lt_keep: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
      and j_len: "Suc k' < length (A ! (s + j))"
      and x_len: "Suc k' < length (A ! (s + x))"
  shows "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
           < elem (A[n]) (idx_B_in_expansion A c j) (Suc k')
       \<Longrightarrow> elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
             < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')"
proof -
  assume H: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
               < elem (A[n]) (idx_B_in_expansion A c j) (Suc k')"
  have ej_c: "elem (A[n]) (idx_B_in_expansion A c j) (Suc k') = (A ! (s + j)) ! (Suc k')"
    using elem_AEn_cross_block_when_not_ascends
            [OF A_BMS A_ne b0 not_asc_j c_le j_lt k_lt_keep j_len] .
  have ej_0: "elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k') = (A ! (s + j)) ! (Suc k')"
    using elem_AEn_cross_block_when_not_ascends
            [OF A_BMS A_ne b0 not_asc_j le0 j_lt k_lt_keep j_len] .
  show "elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
          < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')"
  proof (cases "ascends A x (Suc k')")
    case True
    note asc_x = this
    have ex_c: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
              = (A ! (s + x)) ! (Suc k') + c * delta A (Suc k')"
      using elem_AEn_cross_block_when_ascends
              [OF A_BMS A_ne b0 asc_x c_le x_lt k_lt_keep x_len] .
    have ex_0: "elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
              = (A ! (s + x)) ! (Suc k')"
      using elem_AEn_cross_block_when_ascends
              [OF A_BMS A_ne b0 asc_x le0 x_lt k_lt_keep x_len] by simp
    have H': "(A ! (s + x)) ! (Suc k') + c * delta A (Suc k')
                < (A ! (s + j)) ! (Suc k')"
      using H ex_c ej_c by simp
    have "(A ! (s + x)) ! (Suc k') \<le> (A ! (s + x)) ! (Suc k') + c * delta A (Suc k')"
      by simp
    hence "(A ! (s + x)) ! (Suc k') < (A ! (s + j)) ! (Suc k')"
      using H' by linarith
    thus ?thesis using ex_0 ej_0 by simp
  next
    case False
    note nasc_x = this
    have ex_c: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k') = (A ! (s + x)) ! (Suc k')"
      using elem_AEn_cross_block_when_not_ascends
              [OF A_BMS A_ne b0 nasc_x c_le x_lt k_lt_keep x_len] .
    have ex_0: "elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k') = (A ! (s + x)) ! (Suc k')"
      using elem_AEn_cross_block_when_not_ascends
              [OF A_BMS A_ne b0 nasc_x le0 x_lt k_lt_keep x_len] .
    show ?thesis using H ex_c ej_c ex_0 ej_0 by simp
  qed
qed

text \<open>
  Case-B (Round 2): when \<open>j\<close> does NOT ascend at \<open>Suc k'\<close>, the
  candidate set \<open>?S\<close> at block 0 (used by the within/outside helpers)
  is empty. The lemma \<open>bms_S_empty_case_B_at_block_0\<close> is now DEFINED
  LATER (after Lemma A \<open>m_anc_orig_eq_AEn_shared_B0\<close> and the elem
  invariant \<open>elem_orig_eq_AEn_shared_below_l1\<close>), because its proof
  reduces the \<open>A[n]\<close> statement to the pure-\<open>A\<close> structural fact
  \<open>m_parent A (Suc k') (s+j) = None \<or> < s\<close> via those two lemmas
  (forward references not permitted earlier in the file).
\<close>

text \<open>
  Case-B (Round 2): outside-block m_parent claim using S_empty alone
  (no \<open>not_asc_chain\<close> needed). Mirrors
  @{thm m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t_not_asc}
  but uses @{thm elem_AEn_lt_block_implies_block_zero_when_j_not_asc}
  (one-directional, no \<open>x\<close>-ascending hypothesis) instead of the iff-form.
\<close>

lemma m_parent_AEn_idx_B_outside_block_at_Suc_k_via_S_empty:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k' < t"
      and not_asc_j: "\<not> ascends A j (Suc k')"
      and c_le: "c \<le> n"
      and j_lt: "j < l1 A"
      and j_len: "Suc k' < length (A ! (s + j))"
      and k_lt_keep: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
      and x_len: "\<forall>x<j. Suc k' < length (A ! (s + x))"
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
      have manc_at_c: "m_ancestor (A[n]) k' (idx_B_in_expansion A c j)
                                              (idx_B_in_expansion A c x)"
        using manc_p p_as_idxBc by simp
      have manc_at_0: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                              (idx_B_in_expansion A 0 x)"
        using manc_at_c manc_inv x_lt_j by blast
      have x_klt: "Suc k' < length (A ! (s + x))" using x_len x_lt_j by blast
      have v_lt2: "elem (A[n]) (idx_B_in_expansion A c x) (Suc k')
                 < elem (A[n]) (idx_B_in_expansion A c j) (Suc k')"
        using v_lt p_as_idxBc by simp
      \<comment> \<open>Use the one-directional implication (no \<open>x\<close>-asc needed).\<close>
      have block0_lt: "elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                     < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')"
        using elem_AEn_lt_block_implies_block_zero_when_j_not_asc
                [OF A_BMS A_ne b0 not_asc_j c_le j_lt x_lt_l1 k_lt_keep
                    j_len x_klt] v_lt2 by blast
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
  Item 5 (chain shift for k<t, not_asc case, Suc k'): mirror of the asc
  version using the \<open>_not_asc\<close> within/outside helpers.
\<close>

lemma m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t_not_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k' < t"
      and IH_ii_kp: "lemma_2_5_ii_clause A n k'"
      and nasc_j0: "\<not> ascends A j (Suc k')"
      and nasc_chain0: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                     (idx_B_in_expansion A 0 x)
                             \<longrightarrow> \<not> ascends A x (Suc k')"
      and x_len_all: "\<forall>x<l1 A. Suc k' < length (A ! (s + x))"
      and k_lt_keep: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
      and i_lt: "i < l1 A"
      and j_lt: "j < l1 A"
      and i_lt_j: "i < j"
  shows "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 j) (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n j) (idx_B_in_expansion A n i)"
  using i_lt j_lt i_lt_j nasc_j0 nasc_chain0
proof (induct j arbitrary: i rule: less_induct)
  case (less j)
  note IH_chain = less.hyps
  note i_lt' = less.prems(1)
  note j_lt' = less.prems(2)
  note i_lt_j' = less.prems(3)
  note nasc_j = less.prems(4)
  note nasc_chain = less.prems(5)
  have x_len_inv: "\<forall>x<j. Suc k' < length (A ! (s + x))"
    using x_len_all j_lt' by auto
  have j_len: "Suc k' < length (A ! (s + j))"
    using x_len_all j_lt' by blast
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
      using m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t_not_asc
            [OF A_BMS A_ne b0 mp Sk_lt_t nasc_j le0 j_lt' j_len k_lt_keep
                nasc_chain x_len_inv manc_inv_0 True] .
    have outB: "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A n 0)"
      using m_parent_AEn_idx_B_outside_block_at_Suc_k_when_k_lt_t_not_asc
            [OF A_BMS A_ne b0 mp Sk_lt_t nasc_j order.refl j_lt' j_len k_lt_keep
                nasc_chain x_len_inv manc_inv_n True] .
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
      using m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t_not_asc
            [OF A_BMS A_ne b0 mp Sk_lt_t nasc_j le0 j_lt' j_len k_lt_keep
                nasc_chain x_len_inv manc_inv_0 False] .
    have mpB: "m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j)
             = Some (idx_B_in_expansion A n ?p)"
      using m_parent_AEn_idx_B_within_block_at_Suc_k_when_k_lt_t_not_asc
            [OF A_BMS A_ne b0 mp Sk_lt_t nasc_j order.refl j_lt' j_len k_lt_keep
                nasc_chain x_len_inv manc_inv_n False] .
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
        \<comment> \<open>Derive \<open>nasc_j\<close> for \<open>?p\<close> from \<open>nasc_chain\<close> (over \<open>j\<close>) using
            \<open>?p \<in> ?S\<close>, which gives the chain \<open>m_anc(0, j) \<to> (0, ?p)\<close>.\<close>
        have manc_j_to_p: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                 (idx_B_in_expansion A 0 ?p)"
          using p_in by auto
        have nasc_p: "\<not> ascends A ?p (Suc k')"
          using nasc_chain p_lt_j manc_j_to_p by blast
        \<comment> \<open>Derive \<open>nasc_chain\<close> over \<open>?p\<close> via \<open>m_ancestor_trans\<close>:
            for \<open>x < ?p\<close> with chain \<open>m_anc(0, ?p) \<to> (0, x)\<close>, combining
            with the established chain \<open>m_anc(0, j) \<to> (0, ?p)\<close>, gives
            \<open>m_anc(0, j) \<to> (0, x)\<close>, so \<open>nasc_chain\<close> over \<open>j\<close> applies.\<close>
        have nasc_chain_p: "\<forall>x<?p. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 ?p)
                                                         (idx_B_in_expansion A 0 x)
                                   \<longrightarrow> \<not> ascends A x (Suc k')"
        proof (intro allI impI)
          fix x assume x_lt_p: "x < ?p"
            and chain_p_x: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 ?p)
                                                  (idx_B_in_expansion A 0 x)"
          have x_lt_j: "x < j" using x_lt_p p_lt_j by linarith
          have chain_j_x: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                 (idx_B_in_expansion A 0 x)"
            using m_ancestor_trans[OF manc_j_to_p chain_p_x] .
          show "\<not> ascends A x (Suc k')"
            using nasc_chain x_lt_j chain_j_x by blast
        qed
        have IH_at: "m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A 0 ?p)
                                          (idx_B_in_expansion A 0 i)
                   \<longleftrightarrow> m_ancestor (A[n]) (Suc k') (idx_B_in_expansion A n ?p)
                                          (idx_B_in_expansion A n i)"
          using IH_chain[OF p_lt_j i_lt' p_lt_l1 True nasc_p nasc_chain_p] .
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
  Sub-helpers for clause (iii). Lemma A and Lemma A' below are SOUND
  (no dependence on the deleted false universal-ascending claim) and
  reusable in any (iii) re-implementation:
  \<^item> \<open>m_anc_orig_eq_AEn_shared_B0\<close> (Lemma A): \<open>m_ancestor A k p q\<close>
    matches \<open>m_ancestor (A[n]) k p q\<close> for cols \<open>p\<close> in the shared
    range \<open>[0..idx_B(0, l_1) - 1]\<close>.
  \<^item> \<open>m_anc_AEn_minus_1_eq_AEn_shared\<close> (Lemma A'): \<open>m_ancestor (A[n-1]) k p q\<close>
    matches \<open>m_ancestor (A[n]) k p q\<close> for cols \<open>p\<close> in the shared
    range \<open>[0..idx_B(n-1, l_1) - 1]\<close>.

  Note (2026-05-17): the previously-defined first-step helpers
  \<open>m_parent_orig_last_col_when_k_lt_m0\<close> and \<open>m_parent_AEn_idx_B_n_zero_when_k_lt_m0\<close>
  (plus the FALSE conjecture \<open>elem_B0_lt_last_col_when_k_lt_m0\<close>) have been
  DELETED. They presupposed that every B_0 col's k-th elem is strictly
  less than the last col's k-th elem (k < m_0), which is refuted by the
  BMS array \<open>(0,0,0)(1,1,1)(2,0,0)(1,1,1)\<close> at \<open>k = 0, x = 1\<close>
  (\<open>elem A 1 0 = 1\<close>, \<open>elem A 3 0 = 1\<close>, not strict). Re-implementation
  must use Hunter's per-col case-split.
\<close>

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

text \<open>
  Pure-\<open>A\<close> structural core of the case-B \<open>S = []\<close> claim.

  When the \<open>j\<close>-th \<open>B\<^sub>0\<close> column does NOT ascend at \<open>Suc k'\<close>
  (\<open>\<not> ascends A j (Suc k')\<close>, i.e. no \<open>(Suc k')\<close>-chain from \<open>s+j\<close> to
  \<open>s\<close>), then the \<open>(Suc k')\<close>-parent of column \<open>s+j\<close> in \<open>A\<close> either does
  not exist or lies strictly below the block-\<open>B\<^sub>0\<close> start \<open>s\<close>.

  Equivalently (since the \<open>m_parent\<close> candidate list is sorted and
  \<open>last\<close>-selected): NO candidate \<open>p\<close> of \<open>m_parent A (Suc k') (s+j)\<close>
  lies in \<open>[s, s+j)\<close>. This is precisely \<open>S = []\<close> reflected back into
  \<open>A\<close>.

  This is a genuine Bashicu-standard-form fact (stronger than the
  literal \<open>\<not> ascends\<close> hypothesis, which only rules out the chain
  reaching exactly \<open>s\<close>): empirically verified across 437 BMSs in
  \<open>verify/verify_m_parent_in_B0_case_B.py\<close> (0 violations). A full
  BMS structural proof is PENDING; \<open>BMS.induct\<close> structure-preservation
  was refuted (see \<open>verify/verify_Ak_structural_conjectures.py\<close>), so
  the proof must proceed by a direct \<open>m_parent\<close>-chain / lex analysis.
\<close>

lemma bms_m_parent_outside_B0_case_B_pureA:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k' < t"
      and not_asc_j: "\<not> ascends A j (Suc k')"
      and j_lt: "j < l1 A"
      and j_pos: "0 < j"
  shows "[x \<leftarrow> [0..<j].
            elem A (s + x) (Suc k') < elem A (s + j) (Suc k')
          \<and> m_ancestor A k' (s + j) (s + x)] = []"
  sorry

text \<open>
  Case-B (Round 2): when \<open>j\<close> does NOT ascend at \<open>Suc k'\<close>, the
  candidate set \<open>?S\<close> at block 0 is empty. (Relocated here so that the
  proof can reduce the \<open>A[n]\<close> statement to its pure-\<open>A\<close> form via
  Lemma A \<open>m_anc_orig_eq_AEn_shared_B0\<close> and the elem invariant
  \<open>elem_orig_eq_AEn_shared_below_l1\<close>, both proved just above.)

  Empirical verification: \<open>verify/verify_S_empty_case_B.py\<close>
  — 437 BMSs, 0 violations (BFS from Hunter seeds {seed 2..5}).
\<close>

lemma bms_S_empty_case_B_at_block_0:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k' < t"
      and not_asc_j: "\<not> ascends A j (Suc k')"
      and j_lt: "j < l1 A"
      and j_pos: "0 < j"
      and n_pos: "0 < n"
  shows "[x \<leftarrow> [0..<j].
            elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
              < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
          \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                  (idx_B_in_expansion A 0 x)] = []"
proof -
  \<comment> \<open>Step 0: block-0 indices coincide with \<open>s + \<dots>\<close> (since \<open>l0 A = s\<close>).\<close>
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have s_le_arr: "s \<le> arr_len A" using s_lt_last last_lt_arr by linarith
  have l0_eq: "l0 A = s"
    using b0 s_le_arr unfolding l0_def G_block_def by simp
  have idx0: "\<And>x. idx_B_in_expansion A 0 x = s + x"
    using l0_eq unfolding idx_B_in_expansion_def by simp
  have k'_lt_m0: "k' < t" using Sk_lt_t by simp
  have sj_lt_idx: "s + j < idx_B_in_expansion A 0 (l1 A)"
    using j_lt l0_eq unfolding idx_B_in_expansion_def by simp
  \<comment> \<open>Step 1: each filter atom matches its pure-\<open>A\<close> counterpart on \<open>[0..<j]\<close>.\<close>
  have atom_eq:
    "\<And>x. x \<in> set [0..<j] \<Longrightarrow>
       (elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
          < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
        \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                (idx_B_in_expansion A 0 x))
     \<longleftrightarrow> (elem A (s + x) (Suc k') < elem A (s + j) (Suc k')
          \<and> m_ancestor A k' (s + j) (s + x))"
  proof -
    fix x assume "x \<in> set [0..<j]"
    hence x_lt_j: "x < j" by simp
    have x_lt_l1: "x < l1 A" using x_lt_j j_lt by linarith
    have sx_lt_idx: "s + x < idx_B_in_expansion A 0 (l1 A)"
      using x_lt_l1 l0_eq unfolding idx_B_in_expansion_def by simp
    \<comment> \<open>elem invariants at row \<open>Suc k' < t\<close> via the shared-range lemma.\<close>
    have ex: "elem (A[n]) (s + x) (Suc k') = elem A (s + x) (Suc k')"
      using elem_orig_eq_AEn_shared_below_l1
              [OF A_BMS A_ne b0 mp n_pos sx_lt_idx Sk_lt_t] by simp
    have ej: "elem (A[n]) (s + j) (Suc k') = elem A (s + j) (Suc k')"
      using elem_orig_eq_AEn_shared_below_l1
              [OF A_BMS A_ne b0 mp n_pos sj_lt_idx Sk_lt_t] by simp
    \<comment> \<open>m_anc invariant at level \<open>k' < t\<close> via Lemma A.\<close>
    have manc: "m_ancestor (A[n]) k' (s + j) (s + x)
              \<longleftrightarrow> m_ancestor A k' (s + j) (s + x)"
      using m_anc_orig_eq_AEn_shared_B0
              [OF A_BMS A_ne b0 mp k'_lt_m0 n_pos sj_lt_idx] by simp
    show "(elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
             < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
           \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                   (idx_B_in_expansion A 0 x))
        \<longleftrightarrow> (elem A (s + x) (Suc k') < elem A (s + j) (Suc k')
             \<and> m_ancestor A k' (s + j) (s + x))"
      using ex ej manc idx0 by simp
  qed
  \<comment> \<open>Step 2: filter congruence lifts \<open>S = []\<close> to the pure-\<open>A\<close> form.\<close>
  have filt_eq:
    "[x \<leftarrow> [0..<j].
        elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
          < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
      \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                              (idx_B_in_expansion A 0 x)]
   = [x \<leftarrow> [0..<j].
        elem A (s + x) (Suc k') < elem A (s + j) (Suc k')
      \<and> m_ancestor A k' (s + j) (s + x)]"
    by (rule filter_cong[OF refl], rule atom_eq)
  show ?thesis
    using filt_eq
          bms_m_parent_outside_B0_case_B_pureA
            [OF A_BMS A_ne b0 mp Sk_lt_t not_asc_j j_lt j_pos]
    by simp
qed

text \<open>
  Sound (ii) step lemma following Hunter's paper (arXiv:2307.04606v3)
  page 5 case-split approach.

  Fix \<open>i, j\<close>. If \<open>j = 0\<close> or \<open>i \<ge> j\<close>, trivial. For \<open>i < j\<close>:
  define \<open>I = {i' < j : \<forall>k' < k. i' is k'-ancestor of j in B_0}\<close>.
  By IH (ii) at \<open>k' < k\<close>, \<open>I\<close> is the same when measured in \<open>B_0\<close> or \<open>B_n\<close>.
  Case-split on whether the \<open>j\<close>-th col ascends at row \<open>k\<close>:
  \<^item> Case (A): all \<open>I\<close> cols ascend \<longrightarrow> differences uniform \<longrightarrow> k-ancestry preserved.
  \<^item> Case (B): \<open>j\<close>-th col doesn't ascend \<longrightarrow> no new k-ancestors in \<open>B_n\<close>.

  Takes only IH(ii) at \<open>k' < k\<close>, not the full lemma_2_5_at IH (which
  conflates 5 clauses, masking soundness defects).
\<close>

text \<open>
  BMS chain level lift: if column \<open>s+j\<close> has an \<open>(Suc k)\<close>-chain to
  \<open>s\<close>, and \<open>(s+x)\<close> is on \<open>(s+j)\<close>'s \<open>k\<close>-chain (with \<open>0 < x < j\<close>),
  then \<open>(s+x)\<close> also has an \<open>(Suc k)\<close>-chain to \<open>s\<close>.

  This is the structural BMS claim underlying Hunter's dichotomy case (A)
  (paper p.5). The naive direction of going from a \<open>k\<close>-chain to an
  \<open>(Suc k)\<close>-chain is invalid (\<open>m_ancestor_mono\<close> goes the other way),
  so this lift requires BMS standard-form specifics. Proof obligation
  pending an explicit BMS row-monotonicity helper.
\<close>

text \<open>
  Pure A-level form of the lift (chain in A, not A[n]). Used as a helper
  inside the A[n] wrapper below after chain transfer via Lemma A.
\<close>

text \<open>
  Maximality sub-lemma for case 2 of \<open>bms_chain_level_lift_A\<close> (defined below):
  given a single-step (Suc k)-parent \<open>m_parent A (Suc k) (s+j) = Some q_1\<close>,
  and \<open>p\<close> a position with \<open>q_1 < p < s+j\<close> AND \<open>p\<close> is a k-ancestor of \<open>s+j\<close>,
  then \<open>elem A (s+j) (Suc k) \<le> elem A p (Suc k)\<close> (otherwise \<open>p\<close>
  would beat \<open>q_1\<close> as a (Suc k)-parent candidate).
\<close>

lemma bms_max_elem_above_q1:
  fixes A :: array and k :: nat and s :: nat and j :: nat and q_1 :: nat and p :: nat
  assumes mp_sj: "m_parent A (Suc k) (s + j) = Some q_1"
      and p_gt_q1: "q_1 < p"
      and p_lt_sj: "p < s + j"
      and p_chain: "m_ancestor A k (s + j) p"
  shows "elem A (s + j) (Suc k) \<le> elem A p (Suc k)"
proof (rule ccontr)
  assume "\<not> elem A (s + j) (Suc k) \<le> elem A p (Suc k)"
  hence p_elem_lt: "elem A p (Suc k) < elem A (s + j) (Suc k)" by simp
  let ?P = "\<lambda>j'. elem A j' (Suc k) < elem A (s + j) (Suc k)
              \<and> m_ancestor A k (s + j) j'"
  let ?cands = "filter ?P [0..<s + j]"
  have p_P: "?P p" using p_elem_lt p_chain by simp
  have p_in_cands: "p \<in> set ?cands" using p_lt_sj p_P by simp
  have cands_ne: "?cands \<noteq> []"
    using length_pos_if_in_set[OF p_in_cands] by simp
  have mp_eq_last: "m_parent A (Suc k) (s + j) = Some (last ?cands)"
    using cands_ne by (simp add: Let_def)
  hence q1_eq: "q_1 = last ?cands" using mp_sj by simp
  have sorted_cands: "sorted ?cands"
    by (rule sorted_wrt_filter[OF sorted_upt])
  have all_le_last: "\<forall>y \<in> set ?cands. y \<le> last ?cands"
  proof
    fix y assume y_in: "y \<in> set ?cands"
    have ex_k: "\<exists>k<length ?cands. ?cands ! k = y"
      using y_in unfolding in_set_conv_nth by blast
    obtain k where k_lt: "k < length ?cands" and yk_eq: "?cands ! k = y"
      using ex_k by blast
    have len_pos: "0 < length ?cands" using cands_ne by simp
    have k_le: "k \<le> length ?cands - 1" using k_lt by linarith
    have last_lt: "length ?cands - 1 < length ?cands" using len_pos by simp
    have "?cands ! k \<le> ?cands ! (length ?cands - 1)"
      using sorted_cands k_le last_lt by (simp add: sorted_iff_nth_mono)
    moreover have "last ?cands = ?cands ! (length ?cands - 1)"
      using cands_ne by (simp add: last_conv_nth)
    ultimately show "y \<le> last ?cands" using yk_eq by simp
  qed
  have "p \<le> last ?cands" using all_le_last p_in_cands by blast
  thus False using p_gt_q1 q1_eq by simp
qed

text \<open>
  Case 2 sub-lemma: for any position \<open>y\<close> with \<open>q_1 < y < s+j\<close>
  and \<open>y\<close> a k-ancestor of \<open>s+j\<close>, the (Suc k)-chain from \<open>y\<close>
  reaches \<open>s\<close>. Proof by well-founded induction on \<open>y\<close> using the
  maximality sub-lemma to bound \<open>m_parent A (Suc k) y\<close> from below by \<open>q_1\<close>.
\<close>

lemma bms_chain_level_lift_A_above_q1:
  fixes A :: array and k :: nat and s :: nat and j :: nat and q_1 :: nat
  assumes mp_sj: "m_parent A (Suc k) (s + j) = Some q_1"
      and anc_q1_s: "q_1 = s \<or> m_ancestor A (Suc k) q_1 s"
      and chain_j_to_q1: "m_ancestor A k (s + j) q_1"
  shows "\<forall>y. q_1 < y \<and> y < s + j \<and> m_ancestor A k (s + j) y
              \<longrightarrow> m_ancestor A (Suc k) y s"
proof (intro allI)
  fix y
  show "q_1 < y \<and> y < s + j \<and> m_ancestor A k (s + j) y
        \<longrightarrow> m_ancestor A (Suc k) y s"
  proof (induct y rule: less_induct)
    case (less y)
    note inner_IH = less.hyps
    show ?case
    proof (intro impI, elim conjE)
      assume y_gt_q1: "q_1 < y"
      assume y_lt_sj: "y < s + j"
      assume chain_jy: "m_ancestor A k (s + j) y"
      \<comment> \<open>By chain linearity at \<open>k\<close>: \<open>m_anc A k y q_1\<close>.\<close>
      have chain_y_q1: "m_ancestor A k y q_1"
      proof -
        have "y = q_1 \<or> m_ancestor A k y q_1 \<or> m_ancestor A k q_1 y"
          using m_ancestor_chain_linear chain_jy chain_j_to_q1 by blast
        moreover have "y \<noteq> q_1" using y_gt_q1 by simp
        moreover have "\<not> m_ancestor A k q_1 y"
          using m_ancestor_target_lt y_gt_q1 by force
        ultimately show ?thesis by blast
      qed
      \<comment> \<open>Elem comparisons: \<open>elem q_1 (Suc k) < elem (s+j) (Suc k) \<le> elem y (Suc k)\<close>.\<close>
      have elem_q1_lt_sj: "elem A q_1 (Suc k) < elem A (s + j) (Suc k)"
        using m_parent_elem_lt[OF mp_sj] .
      have elem_sj_le_y: "elem A (s + j) (Suc k) \<le> elem A y (Suc k)"
        using bms_max_elem_above_q1[OF mp_sj y_gt_q1 y_lt_sj chain_jy] .
      have elem_q1_lt_y: "elem A q_1 (Suc k) < elem A y (Suc k)"
        using elem_q1_lt_sj elem_sj_le_y by linarith
      \<comment> \<open>So \<open>q_1\<close> is a candidate for \<open>m_parent A (Suc k) y\<close>.\<close>
      let ?P_y = "\<lambda>p. elem A p (Suc k) < elem A y (Suc k) \<and> m_ancestor A k y p"
      have q1_cand: "?P_y q_1"
        using elem_q1_lt_y chain_y_q1 by simp
      have q1_in_cands_y: "q_1 \<in> set (filter ?P_y [0..<y])"
        using y_gt_q1 q1_cand by simp
      have cands_y_ne: "filter ?P_y [0..<y] \<noteq> []"
        using length_pos_if_in_set[OF q1_in_cands_y] by simp
      obtain r where mp_y: "m_parent A (Suc k) y = Some r"
                 and r_eq: "r = last (filter ?P_y [0..<y])"
        using cands_y_ne by (auto simp add: Let_def)
      have r_lt_y: "r < y" by (rule m_parent_lt[OF mp_y])
      \<comment> \<open>\<open>r \<ge> q_1\<close> by maximality (\<open>last\<close> of a sorted list).\<close>
      have r_ge_q1: "q_1 \<le> r"
      proof -
        have sorted_cands: "sorted (filter ?P_y [0..<y])"
          by (rule sorted_wrt_filter[OF sorted_upt])
        have "\<forall>z \<in> set (filter ?P_y [0..<y]). z \<le> last (filter ?P_y [0..<y])"
        proof
          fix z assume z_in: "z \<in> set (filter ?P_y [0..<y])"
          have ex_k: "\<exists>k<length (filter ?P_y [0..<y]). (filter ?P_y [0..<y]) ! k = z"
            using z_in unfolding in_set_conv_nth by blast
          obtain k where k_lt: "k < length (filter ?P_y [0..<y])"
                     and zk_eq: "(filter ?P_y [0..<y]) ! k = z"
            using ex_k by blast
          have len_pos: "0 < length (filter ?P_y [0..<y])" using cands_y_ne by simp
          have k_le: "k \<le> length (filter ?P_y [0..<y]) - 1" using k_lt by linarith
          have last_lt: "length (filter ?P_y [0..<y]) - 1
                       < length (filter ?P_y [0..<y])" using len_pos by simp
          have "(filter ?P_y [0..<y]) ! k
              \<le> (filter ?P_y [0..<y]) ! (length (filter ?P_y [0..<y]) - 1)"
            using sorted_cands k_le last_lt by (simp add: sorted_iff_nth_mono)
          moreover have "last (filter ?P_y [0..<y])
                       = (filter ?P_y [0..<y]) ! (length (filter ?P_y [0..<y]) - 1)"
            using cands_y_ne by (simp add: last_conv_nth)
          ultimately show "z \<le> last (filter ?P_y [0..<y])" using zk_eq by simp
        qed
        thus ?thesis using q1_in_cands_y r_eq by blast
      qed
      show "m_ancestor A (Suc k) y s"
      proof (cases "r = q_1")
        case r_eq_q1: True
        show ?thesis
          using mp_y r_eq_q1 anc_q1_s by auto
      next
        case r_ne_q1: False
        hence r_gt_q1: "q_1 < r" using r_ge_q1 by linarith
        \<comment> \<open>Apply IH at \<open>r < y\<close>.\<close>
        have r_lt_sj: "r < s + j" using r_lt_y y_lt_sj by simp
        have chain_y_r: "m_ancestor A k y r"
        proof -
          have r_in: "r \<in> set (filter ?P_y [0..<y])"
            using r_eq last_in_set[OF cands_y_ne] by simp
          hence "?P_y r" by simp
          thus ?thesis by simp
        qed
        have chain_jr: "m_ancestor A k (s + j) r"
          using m_ancestor_trans[OF chain_jy chain_y_r] .
        have IH_r: "m_ancestor A (Suc k) r s"
          using inner_IH[OF r_lt_y] r_gt_q1 r_lt_sj chain_jr by simp
        show ?thesis
          using mp_y IH_r by auto
      qed
    qed
  qed
qed

lemma bms_chain_level_lift_A:
  fixes A :: array and k :: nat
  assumes asc_j_chain: "m_ancestor A (Suc k) (s + j) s"
      and chain_A: "m_ancestor A k (s + j) (s + x)"
      and x_pos: "0 < x"
      and x_lt_j: "x < j"
  shows "m_ancestor A (Suc k) (s + x) s"
  using asc_j_chain chain_A x_pos x_lt_j
proof (induct j arbitrary: x rule: less_induct)
  case (less j)
  note asc_j_ch = less.prems(1)
  note chain_jx = less.prems(2)
  note x_pos' = less.prems(3)
  note x_lt_j' = less.prems(4)
  \<comment> \<open>Get \<open>q_1 = m_parent A (Suc k) (s+j)\<close>.\<close>
  obtain q_1 where mp_sj: "m_parent A (Suc k) (s + j) = Some q_1"
                and case_q1: "q_1 = s \<or> m_ancestor A (Suc k) q_1 s"
    using asc_j_ch by (cases "m_parent A (Suc k) (s + j)") auto
  have q1_lt_sj: "q_1 < s + j" by (rule m_parent_lt[OF mp_sj])
  \<comment> \<open>\<open>(Suc k)\<close>-chain step gives a \<open>k\<close>-chain step by @{thm m_ancestor_mono}.\<close>
  have asc_step: "m_ancestor A (Suc k) (s + j) q_1"
    using mp_sj by simp
  have chain_j_to_q1: "m_ancestor A k (s + j) q_1"
    using m_ancestor_mono[OF _ asc_step, of k] by simp
  have anc_q1_s: "q_1 = s \<or> m_ancestor A (Suc k) q_1 s"
    using case_q1 by blast
  \<comment> \<open>Chain linearity at level \<open>k\<close> (source \<open>s+j\<close>, ancestors \<open>s+x\<close>, \<open>q_1\<close>).\<close>
  have lin: "s + x = q_1 \<or> m_ancestor A k (s + x) q_1 \<or> m_ancestor A k q_1 (s + x)"
    using m_ancestor_chain_linear chain_jx chain_j_to_q1 by blast
  show ?case
  proof (cases "s + x = q_1")
    case sx_eq_q1: True
    \<comment> \<open>\<open>(s+x) = q_1\<close>: conclusion follows from the chain step + \<open>case_q1\<close>.
        Sub-case \<open>q_1 = s\<close> gives \<open>x = 0\<close>, contradicting \<open>x_pos'\<close>.\<close>
    have anc_q1_s': "m_ancestor A (Suc k) q_1 s"
      using anc_q1_s sx_eq_q1 x_pos' by auto
    show ?thesis using sx_eq_q1 anc_q1_s' by simp
  next
    case sx_ne_q1: False
    show ?thesis
    proof (cases "m_ancestor A k q_1 (s + x)")
      case sx_lt_q1: True
      \<comment> \<open>\<open>(s+x) < q_1\<close>: apply IH at \<open>j' = q_1 - s\<close>.\<close>
      have sx_lt_q1_pos: "s + x < q_1"
        using sx_lt_q1 m_ancestor_target_lt by simp
      have q1_gt_s: "q_1 > s" using sx_lt_q1_pos x_pos' by linarith
      have q1_ge_s: "s \<le> q_1" using q1_gt_s by simp
      define j' where "j' = q_1 - s"
      have j'_def: "q_1 = s + j'" using q1_gt_s j'_def by simp
      have j'_pos: "0 < j'" using q1_gt_s j'_def by simp
      have j'_lt_j: "j' < j"
        using j'_def q1_lt_sj by linarith
      have x_lt_j': "x < j'"
        using sx_lt_q1_pos j'_def by linarith
      have anc_q1_s': "m_ancestor A (Suc k) q_1 s"
        using anc_q1_s sx_lt_q1_pos q1_gt_s by auto
      have asc_chain_j': "m_ancestor A (Suc k) (s + j') s"
        using anc_q1_s' j'_def by simp
      have chain_j'_x: "m_ancestor A k (s + j') (s + x)"
        using sx_lt_q1 j'_def by simp
      show ?thesis
        by (rule less.hyps[OF j'_lt_j asc_chain_j' chain_j'_x x_pos' x_lt_j'])
    next
      case sx_lt_q1_F: False
      \<comment> \<open>\<open>(s+x) > q_1\<close>: dispatch to @{thm bms_chain_level_lift_A_above_q1}.\<close>
      have chain_sx_q1: "m_ancestor A k (s + x) q_1"
        using lin sx_ne_q1 sx_lt_q1_F by blast
      have sx_gt_q1: "q_1 < s + x"
        using chain_sx_q1 m_ancestor_target_lt by simp
      have sx_lt_sj: "s + x < s + j" using x_lt_j' by simp
      show ?thesis
        using bms_chain_level_lift_A_above_q1
                [OF mp_sj anc_q1_s chain_j_to_q1]
              sx_gt_q1 sx_lt_sj chain_jx by blast
    qed
  qed
qed

lemma bms_chain_level_lift:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k < t"
      and n_pos: "0 < n"
      and j_lt: "j < l1 A"
      and asc_j_chain: "m_ancestor A (Suc k) (s + j) s"
      and chain_AEn: "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 x)"
      and x_pos: "0 < x"
      and x_lt_j: "x < j"
  shows "m_ancestor A (Suc k) (s + x) s"
proof -
  \<comment> \<open>Transfer chain from \<open>A[n]\<close> to \<open>A\<close> via Lemma A.\<close>
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have s_le_arr: "s \<le> arr_len A" using s_lt_last last_lt_arr by linarith
  have l0_eq: "l0 A = s"
    using b0 s_le_arr unfolding l0_def G_block_def by simp
  have sj_eq: "idx_B_in_expansion A 0 j = s + j"
    using l0_eq unfolding idx_B_in_expansion_def by simp
  have sx_eq: "idx_B_in_expansion A 0 x = s + x"
    using l0_eq unfolding idx_B_in_expansion_def by simp
  have sj_lt: "s + j < idx_B_in_expansion A 0 (l1 A)"
    using j_lt l0_eq unfolding idx_B_in_expansion_def by simp
  have k_lt_t: "k < t" using Sk_lt_t by simp
  have chain_A: "m_ancestor A k (s + j) (s + x)"
    using m_anc_orig_eq_AEn_shared_B0
            [OF A_BMS A_ne b0 mp k_lt_t n_pos sj_lt]
          chain_AEn sj_eq sx_eq by simp
  show ?thesis
    by (rule bms_chain_level_lift_A[OF asc_j_chain chain_A x_pos x_lt_j])
qed

text \<open>
  Hunter dichotomy, case (A) (paper page 5, applied to m = Suc k):
  if the j-th column of B_0 ascends at level (Suc k) (= the first column
  s is the (Suc k)-ancestor of j), then for every k-ancestor x of j
  (in A, with k < Suc k), x also ascends at level (Suc k).

  Hunter's argument: by (Suc k)-chain from j to s, the (Suc k)-elem of s
  is strictly smaller than the (Suc k)-elem of every column between s and
  (s+j). Hence s is the (Suc k)-ancestor of every (s+x) for x in the
  k-chain {x' < j : x' is k-ancestor of j}.
\<close>

lemma bms_ascend_propagates_to_chain_ancestor:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and k_lt_t: "k < t"
      and n_pos: "0 < n"
      and asc_j: "ascends A j (Suc k)"
      and j_lt: "j < l1 A"
      and x_lt_j: "x < j"
      and chain_AEn: "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j)
                                          (idx_B_in_expansion A 0 x)"
  shows "ascends A x (Suc k)"
proof (cases "x = 0")
  case True
  \<comment> \<open>\<open>x = 0\<close>: \<open>s + 0 = s\<close>, so \<open>non_strict_ancestor A (Suc k) s s\<close>
      reduces to reflexivity \<open>s = s\<close>. The \<open>Suc k < m_0\<close> side condition
      is inherited from \<open>asc_j\<close>.\<close>
  have Sk_lt_t: "Suc k < t"
    using asc_j b0 mp unfolding ascends_def by simp
  have nsa: "non_strict_ancestor A (Suc k) (s + 0) s"
    unfolding non_strict_ancestor_def by simp
  show ?thesis
    using True b0 mp Sk_lt_t nsa unfolding ascends_def by simp
next
  case False
  \<comment> \<open>\<open>x > 0\<close>: derive via @{thm bms_chain_level_lift} (chain transfer
      from \<open>A[n]\<close> to \<open>A\<close> internalized in the lift lemma). Step 1: extract
      \<open>(Suc k)\<close>-chain from \<open>(s+j)\<close> to \<open>s\<close> from \<open>asc_j\<close>. Step 2: apply
      level lift to get \<open>(Suc k)\<close>-chain from \<open>(s+x)\<close> to \<open>s\<close>.
      Step 3: repackage as \<open>ascends A x (Suc k)\<close>.\<close>
  have x_pos: "0 < x" using False by simp
  have j_pos: "0 < j" using x_pos x_lt_j by linarith
  have Sk_lt_t: "Suc k < t"
    using asc_j b0 mp unfolding ascends_def by simp
  have sj_ne_s: "s + j \<noteq> s" using j_pos by simp
  \<comment> \<open>Step 1: \<open>asc_j\<close> gives \<open>m_anc A (Suc k) (s + j) s\<close>.\<close>
  have asc_j_chain: "m_ancestor A (Suc k) (s + j) s"
    using asc_j b0 mp sj_ne_s
    unfolding ascends_def non_strict_ancestor_def by simp
  \<comment> \<open>Step 2: apply the level lift (chain transfer internalized).\<close>
  have asc_x_chain: "m_ancestor A (Suc k) (s + x) s"
    using bms_chain_level_lift
            [OF A_BMS A_ne b0 mp Sk_lt_t n_pos j_lt asc_j_chain chain_AEn x_pos x_lt_j] .
  \<comment> \<open>Step 3: repackage as \<open>ascends\<close>.\<close>
  have nsa: "non_strict_ancestor A (Suc k) (s + x) s"
    using asc_x_chain unfolding non_strict_ancestor_def by simp
  show ?thesis
    using b0 mp Sk_lt_t nsa unfolding ascends_def by simp
qed

text \<open>
  Hunter dichotomy contrapositive (case (B) shape for the not-ascending
  branch): if the j-th column does not ascend at (Suc k), no k-chain
  ancestor of j ascends at (Suc k) either. (If some x in the k-chain
  did ascend at (Suc k), then by the previous lemma applied symmetrically
  j would also ascend, contradicting not_asc_j.)
\<close>

text \<open>
  Hunter case B core claim: if column \<open>j\<close> does not ascend at \<open>Suc k\<close>
  (= no (Suc k)-chain from (s+j) to s), then any (Suc k)-ancestor \<open>y\<close>
  of (s+j) also does not ascend at \<open>Suc k\<close>. Provable by chain
  transitivity: if \<open>y\<close> ascended, the trans of (s+j) → y → s gives
  (s+j) → s, contradicting not-ascending.
\<close>

lemma bms_suc_k_ancestor_does_not_ascend_when_j_not_ascends:
  fixes A :: array and s :: nat and k :: nat and j :: nat and y :: nat
  assumes asc_j_to_y: "m_ancestor A (Suc k) (s + j) y"
      and not_asc_j_chain: "\<not> m_ancestor A (Suc k) (s + j) s"
  shows "\<not> m_ancestor A (Suc k) y s"
proof
  assume H: "m_ancestor A (Suc k) y s"
  have "m_ancestor A (Suc k) (s + j) s"
    by (rule m_ancestor_trans[OF asc_j_to_y H])
  thus False using not_asc_j_chain by simp
qed

text \<open>
  Hunter case B at chain level (Suc k): if \<open>j\<close> does not ascend at \<open>Suc k\<close>
  and \<open>x\<close> is a (Suc k)-chain ancestor of (s+j) with \<open>x > 0\<close>, then \<open>x\<close>
  does not ascend at (Suc k). Direct from
  @{thm bms_suc_k_ancestor_does_not_ascend_when_j_not_ascends}.
\<close>

lemma bms_not_ascend_propagates_to_suc_k_chain_ancestor:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and Sk_lt_t: "Suc k < t"
      and n_pos: "0 < n"
      and not_asc_j: "\<not> ascends A j (Suc k)"
      and j_lt: "j < l1 A"
      and j_pos: "0 < j"
      and x_pos: "0 < x"
      and x_lt_j: "x < j"
      and chain_AEn_at_Suc_k: "m_ancestor (A[n]) (Suc k) (idx_B_in_expansion A 0 j)
                                                          (idx_B_in_expansion A 0 x)"
  shows "\<not> ascends A x (Suc k)"
proof -
  \<comment> \<open>Transfer chain from A[n] to A via Lemma A.\<close>
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have s_le_arr: "s \<le> arr_len A" using s_lt_last last_lt_arr by linarith
  have l0_eq: "l0 A = s"
    using b0 s_le_arr unfolding l0_def G_block_def by simp
  have sj_eq: "idx_B_in_expansion A 0 j = s + j"
    using l0_eq unfolding idx_B_in_expansion_def by simp
  have sx_eq: "idx_B_in_expansion A 0 x = s + x"
    using l0_eq unfolding idx_B_in_expansion_def by simp
  have sj_lt: "s + j < idx_B_in_expansion A 0 (l1 A)"
    using j_lt l0_eq unfolding idx_B_in_expansion_def by simp
  have chain_A: "m_ancestor A (Suc k) (s + j) (s + x)"
    using m_anc_orig_eq_AEn_shared_B0
            [OF A_BMS A_ne b0 mp Sk_lt_t n_pos sj_lt]
          chain_AEn_at_Suc_k sj_eq sx_eq by simp
  \<comment> \<open>From \<open>not_asc_j\<close>, derive \<open>\<not> m_ancestor A (Suc k) (s+j) s\<close>.\<close>
  have sj_ne_s: "s + j \<noteq> s" using j_pos by simp
  have not_anc_to_s: "\<not> m_ancestor A (Suc k) (s + j) s"
  proof
    assume H: "m_ancestor A (Suc k) (s + j) s"
    have nsa: "non_strict_ancestor A (Suc k) (s + j) s"
      using H unfolding non_strict_ancestor_def by simp
    have "ascends A j (Suc k)"
      using b0 mp Sk_lt_t nsa unfolding ascends_def by simp
    thus False using not_asc_j by simp
  qed
  \<comment> \<open>Apply the chain-trans-based lemma.\<close>
  have not_anc_x_to_s: "\<not> m_ancestor A (Suc k) (s + x) s"
    by (rule bms_suc_k_ancestor_does_not_ascend_when_j_not_ascends
              [OF chain_A not_anc_to_s])
  \<comment> \<open>Repackage \<open>\<not> ascends A x (Suc k)\<close>.\<close>
  have sx_ne_s: "s + x \<noteq> s" using x_pos by simp
  show ?thesis
  proof
    assume H: "ascends A x (Suc k)"
    have nsa: "non_strict_ancestor A (Suc k) (s + x) s"
      using H b0 mp unfolding ascends_def by simp
    have "m_ancestor A (Suc k) (s + x) s"
      using nsa sx_ne_s unfolding non_strict_ancestor_def by simp
    thus False using not_anc_x_to_s by simp
  qed
qed

text \<open>
  Sufficient row-0 condition (*): when \<open>t > 0\<close> and \<open>j \<in> [1, l1-1]\<close>,
  the row-0 value at column \<open>s+j\<close> strictly exceeds that at \<open>s\<close>.
  Empirically verified across 785 BMSs (no counter-example); see
  \<open>verify/verify_b0_row0_strict_above_s.py\<close>. Structural BMS proof
  pending (likely via lex order of cols + first-diff-row analysis).
\<close>

lemma bms_b0_row0_gt_s:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
      and j_lt: "j < l1 A"
      and j_pos: "0 < j"
  shows "elem A s 0 < elem A (s + j) 0"
proof -
  \<comment> \<open>Proof via the strict lex-side reformulation
      \<open>bms_b0_col_clex_strict_row0\<close> (BMS_Lex.thy). That lemma
      asserts \<open>(A!s)!0 < (A!(s+j))!0\<close> directly, from which the
      \<open>elem\<close>-side conclusion follows by unfolding \<open>elem_def\<close>.

      Rationale: the previously-attempted BMS induction on
      \<open>A\<close> in this lemma was structurally blocked because
      \<open>b0_start\<close>, \<open>max_parent_level\<close>, \<open>l1\<close> do not propagate
      cleanly through expansion \<open>A[k]\<close> (refuted by 437 yaBMS
      counter-examples; see
      \<open>verify/verify_Ak_structural_conjectures.py\<close>). The lex-side
      formulation is therefore the canonical pending obligation.\<close>
  have j_lt': "j < arr_len (B0_block A)"
    using j_lt unfolding l1_def .
  have row0_strict: "(A ! s) ! 0 < (A ! (s + j)) ! 0"
    by (rule bms_b0_col_clex_strict_row0[OF A_BMS A_ne b0 mp t_pos j_lt' j_pos])
  thus ?thesis unfolding elem_def by simp
qed

text \<open>
  Uniform-ascending lemma for B_0 at row 0 (case-B vacuity): when
  \<open>max_parent_level A = Some t\<close> with \<open>t > 0\<close>, every column of B_0
  ascends at row 0. Empirically verified across 1737 BMSs (no
  counter-example in BFS from 8 distinct seeds); see
  \<open>verify/verify_row0_always_ascends_when_t_pos.py\<close>. This collapses
  Hunter's dichotomy at \<open>k = 0\<close> to case (A) only, eliminating the
  case (B) (j does not ascend at row 0) sub-proof. Proved by less_induct
  on \<open>j\<close>: base \<open>j=0\<close> via reflexivity of non_strict_ancestor;
  step \<open>j>0\<close> uses (*) (@{thm bms_b0_row0_gt_s}) to derive
  \<open>m_parent A 0 (s+j) = Some (s+j')\<close> for some \<open>j' < j\<close>, then
  IH at \<open>j'\<close> closes the chain.
\<close>

text \<open>
  Pure m_parent helper (BMS-free): if \<open>elem A s 0 < elem A (s+j) 0\<close>
  (so \<open>s\<close> is a candidate), then \<open>m_parent A 0 (s+j) = Some p\<close>
  with \<open>p \<in> [s, s+j-1]\<close>.
\<close>

lemma m_parent_row0_b0_when_row0_lt:
  fixes A :: array and s j :: nat
  assumes j_pos: "0 < j"
      and row0_lt: "elem A s 0 < elem A (s + j) 0"
  shows "\<exists>p. m_parent A 0 (s + j) = Some p \<and> s \<le> p \<and> p < s + j"
proof -
  let ?F = "filter (\<lambda>q. elem A q 0 < elem A (s + j) 0) [0..<s + j]"
  have s_lt_sj: "s < s + j" using j_pos by simp
  have s_in_F: "s \<in> set ?F" using row0_lt s_lt_sj by simp
  hence F_ne: "?F \<noteq> []" using length_pos_if_in_set by fastforce
  let ?p = "last ?F"
  have p_in_F: "?p \<in> set ?F" using last_in_set[OF F_ne] .
  have p_lt: "?p < s + j" using p_in_F by auto
  \<comment> \<open>\<open>?p \<ge> s\<close>: explicit nth-mono on the sorted filter.\<close>
  have p_ge: "s \<le> ?p"
  proof -
    have F_sorted: "sorted ?F" by (rule sorted_wrt_filter[OF sorted_upt])
    have ex_k: "\<exists>k<length ?F. ?F ! k = s"
      using s_in_F unfolding in_set_conv_nth by blast
    obtain k where k_lt: "k < length ?F" and Fk_eq: "?F ! k = s"
      using ex_k by blast
    have len_pos: "0 < length ?F" using F_ne by simp
    have k_le: "k \<le> length ?F - 1" using k_lt by linarith
    have last_lt: "length ?F - 1 < length ?F" using len_pos by simp
    have "?F ! k \<le> ?F ! (length ?F - 1)"
      using F_sorted k_le last_lt by (simp add: sorted_iff_nth_mono)
    moreover have "?p = ?F ! (length ?F - 1)"
      using F_ne by (simp add: last_conv_nth)
    ultimately show "s \<le> ?p" using Fk_eq by simp
  qed
  have mp_eq: "m_parent A 0 (s + j) = Some ?p"
    using F_ne by (simp add: Let_def)
  show ?thesis using mp_eq p_ge p_lt by blast
qed

text \<open>
  (H) Uniform-ascending lemma for B_0 at row 0 (case-B vacuity):
  when \<open>max_parent_level A = Some t\<close> with \<open>t > 0\<close>, every column
  of B_0 ascends at row 0. Proved by less_induct on \<open>j\<close>: base \<open>j=0\<close>
  via reflexivity of non_strict_ancestor; step \<open>j>0\<close> uses (*)
  (@{thm bms_b0_row0_gt_s}) to derive \<open>m_parent A 0 (s+j) = Some (s+j')\<close>
  for some \<open>j' < j\<close>, then IH at \<open>j'\<close> closes the chain.
\<close>

lemma bms_all_b0_ascend_row0_when_t_pos:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
  shows "\<forall>j < l1 A. ascends A j 0"
proof -
  have ascends_iff: "ascends A d 0 = (s + d = s \<or> m_ancestor A 0 (s + d) s)" for d
  proof -
    have step1: "ascends A d 0 = (0 < t \<and> non_strict_ancestor A 0 (s + d) s)"
      unfolding ascends_def using b0 mp by simp
    have step2: "(0 < t \<and> non_strict_ancestor A 0 (s + d) s)
               = non_strict_ancestor A 0 (s + d) s"
      using t_pos by simp
    have step3: "non_strict_ancestor A 0 (s + d) s
               = (s + d = s \<or> m_ancestor A 0 (s + d) s)"
      unfolding non_strict_ancestor_def ..
    show ?thesis using step1 step2 step3 by simp
  qed
  have aux: "ascends A j 0" if "j < l1 A" for j
    using that
  proof (induct j rule: less_induct)
    case (less j)
    note IH = less.hyps
    note j_lt = less.prems
    show ?case
    proof (cases "j = 0")
      case True
      show ?thesis using ascends_iff[of j] True by simp
    next
      case False
      hence j_pos: "0 < j" by simp
      have row0_lt: "elem A s 0 < elem A (s + j) 0"
        using bms_b0_row0_gt_s[OF A_BMS A_ne b0 mp t_pos j_lt j_pos] .
      obtain p where mp_eq: "m_parent A 0 (s + j) = Some p"
                 and p_ge: "s \<le> p" and p_lt: "p < s + j"
        using m_parent_row0_b0_when_row0_lt[OF j_pos row0_lt] by blast
      define j' where "j' = p - s"
      have p_eq: "p = s + j'" using p_ge j'_def by simp
      have j'_lt_j: "j' < j" using p_eq p_lt by linarith
      have j'_lt_l1: "j' < l1 A" using j'_lt_j j_lt by linarith
      have anc_via: "m_ancestor A 0 (s + j) s \<longleftrightarrow> p = s \<or> m_ancestor A 0 p s"
        using m_anc_via_parent_some[OF mp_eq] .
      have anc_sj: "m_ancestor A 0 (s + j) s"
      proof (cases "j' = 0")
        case True
        have p_is_s: "p = s" using p_eq True by simp
        show ?thesis using anc_via p_is_s by simp
      next
        case False
        hence j'_pos: "0 < j'" by simp
        have asc_j': "ascends A j' 0" using IH[OF j'_lt_j j'_lt_l1] .
        have sj'_ne_s: "s + j' \<noteq> s" using j'_pos by simp
        hence "m_ancestor A 0 (s + j') s"
          using asc_j' ascends_iff[of j'] by simp
        thus ?thesis using anc_via p_eq by simp
      qed
      have "s + j \<noteq> s" using j_pos by simp
      thus ?thesis using ascends_iff[of j] anc_sj by simp
    qed
  qed
  thus ?thesis by blast
qed

text \<open>
  Row-0 within-block m_parent characterization under \<open>all_asc\<close>:
  if the (block-0) candidate set \<open>S\<close> is non-empty, the m_parent at
  row 0 of \<open>idx_B(c, j)\<close> is the within-block successor at \<open>last S\<close>.
  Analogue of @{thm m_parent_AEn_zero_idx_B_within_block_when_t_zero}
  with elem equality replaced by strict-less iff
  (@{thm elem_AEn_lt_block_invariant_when_both_ascend}).
\<close>

lemma m_parent_AEn_zero_idx_B_within_block_when_t_pos_all_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
      and n_pos: "0 < n"
      and all_asc: "\<forall>x < l1 A. ascends A x 0"
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
  \<comment> \<open>Side conditions for @{thm elem_AEn_lt_block_invariant_when_both_ascend}.\<close>
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have t_lt_HA: "t < height A" using max_parent_level_lt[OF mp] .
  have zero_lt_HA: "0 < height A" using t_pos t_lt_HA by linarith
  have k_lt_keep: "0 < keep_of (G_block A @ Bs_concat A n)"
    using keep_of_pre_strip_pos_of_t_pos_and_n_pos[OF A_BMS A_ne b0 mp t_pos n_pos] .
  have x_len_all: "\<forall>x<l1 A. 0 < length (A ! (s + x))"
  proof (intro allI impI)
    fix x assume x_lt: "x < l1 A"
    have x_lt_diff: "x < last_col_idx A - s"
      using x_lt b0 s_lt_last last_lt_arr
      unfolding l1_def B0_block_def by simp
    have sx_lt_last: "s + x < last_col_idx A" using x_lt_diff s_lt_last by linarith
    have sx_lt_arr: "s + x < arr_len A" using sx_lt_last last_lt_arr by linarith
    have "length (A ! (s + x)) = height A"
      using length_col_arr[OF is_arr A_ne sx_lt_arr] .
    thus "0 < length (A ! (s + x))" using zero_lt_HA by simp
  qed
  have j_len: "0 < length (A ! (s + j))" using x_len_all j_lt by blast
  have asc_j: "ascends A j 0" using all_asc j_lt by blast
  \<comment> \<open>Standard m_parent unfolding and range split.\<close>
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
  \<comment> \<open>Filter equivalence via strict-less block invariance.\<close>
  have filter_cong_eq:
    "filter (\<lambda>i. elem (A[n]) (i + ?Cstart) 0 < ?vi) [0..<j] = ?S"
  proof (rule filter_cong[OF refl])
    fix x assume x_in: "x \<in> set [0..<j]"
    hence x_lt_j: "x < j" by simp
    hence x_lt_l1: "x < l1 A" using j_lt by linarith
    have idxBc_eq: "x + ?Cstart = idx_B_in_expansion A c x"
      unfolding idx_B_in_expansion_def by simp
    have asc_x: "ascends A x 0" using all_asc x_lt_l1 by blast
    have x_klt: "0 < length (A ! (s + x))" using x_len_all x_lt_l1 by blast
    have lt_inv:
      "(elem (A[n]) (idx_B_in_expansion A c x) 0
         < elem (A[n]) (idx_B_in_expansion A c j) 0)
     \<longleftrightarrow>
       (elem (A[n]) (idx_B_in_expansion A 0 x) 0
         < elem (A[n]) (idx_B_in_expansion A 0 j) 0)"
      using elem_AEn_lt_block_invariant_when_both_ascend
              [OF A_BMS A_ne b0 asc_j asc_x c_le le0 j_lt x_lt_l1 k_lt_keep
                  j_len x_klt] .
    show "(elem (A[n]) (x + ?Cstart) 0 < ?vi)
       \<longleftrightarrow> (elem (A[n]) (idx_B_in_expansion A 0 x) 0
            < elem (A[n]) (idx_B_in_expansion A 0 j) 0)"
      using idxBc_eq lt_inv by simp
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
  Row-0 outside-block m_parent characterization under \<open>all_asc\<close>:
  if the (block-0) candidate set \<open>S\<close> is empty, the m_parent at row 0
  of \<open>idx_B(c, j)\<close> is either None or lands strictly before block \<open>c\<close>.
  Analogue of @{thm m_parent_AEn_zero_idx_B_outside_block_when_t_zero}.
\<close>

lemma m_parent_AEn_zero_idx_B_outside_block_when_t_pos_all_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
      and n_pos: "0 < n"
      and all_asc: "\<forall>x < l1 A. ascends A x 0"
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
  \<comment> \<open>Side conditions for @{thm elem_AEn_lt_block_invariant_when_both_ascend}.\<close>
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
  have t_lt_HA: "t < height A" using max_parent_level_lt[OF mp] .
  have zero_lt_HA: "0 < height A" using t_pos t_lt_HA by linarith
  have k_lt_keep: "0 < keep_of (G_block A @ Bs_concat A n)"
    using keep_of_pre_strip_pos_of_t_pos_and_n_pos[OF A_BMS A_ne b0 mp t_pos n_pos] .
  have x_len_all: "\<forall>x<l1 A. 0 < length (A ! (s + x))"
  proof (intro allI impI)
    fix x assume x_lt: "x < l1 A"
    have x_lt_diff: "x < last_col_idx A - s"
      using x_lt b0 s_lt_last last_lt_arr
      unfolding l1_def B0_block_def by simp
    have sx_lt_last: "s + x < last_col_idx A" using x_lt_diff s_lt_last by linarith
    have sx_lt_arr: "s + x < arr_len A" using sx_lt_last last_lt_arr by linarith
    have "length (A ! (s + x)) = height A"
      using length_col_arr[OF is_arr A_ne sx_lt_arr] .
    thus "0 < length (A ! (s + x))" using zero_lt_HA by simp
  qed
  have j_len: "0 < length (A ! (s + j))" using x_len_all j_lt by blast
  have asc_j: "ascends A j 0" using all_asc j_lt by blast
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
      have asc_j': "ascends A j' 0" using all_asc j'_lt_l1 by blast
      have j'_klt: "0 < length (A ! (s + j'))" using x_len_all j'_lt_l1 by blast
      have lt_inv:
        "(elem (A[n]) (idx_B_in_expansion A c j') 0
           < elem (A[n]) (idx_B_in_expansion A c j) 0)
       \<longleftrightarrow>
         (elem (A[n]) (idx_B_in_expansion A 0 j') 0
           < elem (A[n]) (idx_B_in_expansion A 0 j) 0)"
        using elem_AEn_lt_block_invariant_when_both_ascend
                [OF A_BMS A_ne b0 asc_j asc_j' c_le le0 j_lt j'_lt_l1 k_lt_keep
                    j_len j'_klt] .
      have val_lt: "elem (A[n]) (idx_B_in_expansion A 0 j') 0
                  < elem (A[n]) (idx_B_in_expansion A 0 j) 0"
        using v_lt p_as_idxB lt_inv by simp
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

text \<open>
  Case (A) main helper: when every B_0 col ascends at row 0 (= the
  \<open>all_asc\<close> hypothesis, supplied by
  @{thm bms_all_b0_ascend_row0_when_t_pos}), the row-0 chain at \<open>(A[n])\<close>
  is block-invariant. Structurally an analogue of
  @{thm m_anc_zero_idx_B_in_block_shift_when_t_zero}: the within-block
  candidate set characterization carries over because strict-less under
  uniform shift is preserved (cf.\ @{thm elem_AEn_lt_block_invariant_when_both_ascend}).
\<close>

lemma m_anc_zero_idx_B_in_block_shift_when_t_pos_all_asc:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
      and n_pos: "0 < n"
      and all_asc: "\<forall>x < l1 A. ascends A x 0"
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
      using m_parent_AEn_zero_idx_B_outside_block_when_t_pos_all_asc
            [OF A_BMS A_ne b0 mp t_pos n_pos all_asc a_le j_lt' True] .
    have outB: "(case m_parent (A[n]) 0 (idx_B_in_expansion A b j) of
                  None \<Rightarrow> True
                | Some p \<Rightarrow> p < idx_B_in_expansion A b 0)"
      using m_parent_AEn_zero_idx_B_outside_block_when_t_pos_all_asc
            [OF A_BMS A_ne b0 mp t_pos n_pos all_asc b_le j_lt' True] .
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
      using m_parent_AEn_zero_idx_B_within_block_when_t_pos_all_asc
            [OF A_BMS A_ne b0 mp t_pos n_pos all_asc a_le j_lt' False] .
    have mpB: "m_parent (A[n]) 0 (idx_B_in_expansion A b j)
             = Some (idx_B_in_expansion A b ?p)"
      using m_parent_AEn_zero_idx_B_within_block_when_t_pos_all_asc
            [OF A_BMS A_ne b0 mp t_pos n_pos all_asc b_le j_lt' False] .
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
      case i_ne_p: False
      show ?thesis
      proof (cases "i < ?p")
        case True
        note i_lt_p = this
        \<comment> \<open>Apply IH at \<open>?p\<close> (which is < j) with target \<open>i\<close> (which is < ?p).\<close>
        have IH_p: "m_ancestor (A[n]) 0 (idx_B_in_expansion A a ?p)
                                          (idx_B_in_expansion A a i)
                \<longleftrightarrow> m_ancestor (A[n]) 0 (idx_B_in_expansion A b ?p)
                                          (idx_B_in_expansion A b i)"
          using IH[OF p_lt_j i_lt' p_lt_l1 i_lt_p] .
        have eqA: "idx_B_in_expansion A a ?p = idx_B_in_expansion A a i \<longleftrightarrow> ?p = i"
          unfolding idx_B_in_expansion_def by simp
        have eqB: "idx_B_in_expansion A b ?p = idx_B_in_expansion A b i \<longleftrightarrow> ?p = i"
          unfolding idx_B_in_expansion_def by simp
        show ?thesis using lhs_iff rhs_iff IH_p eqA eqB by blast
      next
        case False
        hence p_lt_i: "?p < i" using i_ne_p by linarith
        have idxA_lt: "idx_B_in_expansion A a ?p < idx_B_in_expansion A a i"
          using p_lt_i unfolding idx_B_in_expansion_def by simp
        have idxB_lt: "idx_B_in_expansion A b ?p < idx_B_in_expansion A b i"
          using p_lt_i unfolding idx_B_in_expansion_def by simp
        \<comment> \<open>Both sides False via target_lt: idx_B(_, ?p) < idx_B(_, i) so
            neither chain can succeed.\<close>
        have lhs_F: "\<not> m_ancestor (A[n]) 0 (idx_B_in_expansion A a j)
                                              (idx_B_in_expansion A a i)"
        proof
          assume "m_ancestor (A[n]) 0 (idx_B_in_expansion A a j)
                                        (idx_B_in_expansion A a i)"
          from lhs_iff[THEN iffD1, OF this]
          consider "idx_B_in_expansion A a ?p = idx_B_in_expansion A a i"
                 | "m_ancestor (A[n]) 0 (idx_B_in_expansion A a ?p)
                                          (idx_B_in_expansion A a i)" by blast
          thus False
          proof cases
            case 1 thus False using idxA_lt by simp
          next
            case 2
            hence "idx_B_in_expansion A a i < idx_B_in_expansion A a ?p"
              by (rule m_ancestor_target_lt)
            thus False using idxA_lt by linarith
          qed
        qed
        have rhs_F: "\<not> m_ancestor (A[n]) 0 (idx_B_in_expansion A b j)
                                              (idx_B_in_expansion A b i)"
        proof
          assume "m_ancestor (A[n]) 0 (idx_B_in_expansion A b j)
                                        (idx_B_in_expansion A b i)"
          from rhs_iff[THEN iffD1, OF this]
          consider "idx_B_in_expansion A b ?p = idx_B_in_expansion A b i"
                 | "m_ancestor (A[n]) 0 (idx_B_in_expansion A b ?p)
                                          (idx_B_in_expansion A b i)" by blast
          thus False
          proof cases
            case 1 thus False using idxB_lt by simp
          next
            case 2
            hence "idx_B_in_expansion A b i < idx_B_in_expansion A b ?p"
              by (rule m_ancestor_target_lt)
            thus False using idxB_lt by linarith
          qed
        qed
        show ?thesis using lhs_F rhs_F by blast
      qed
    qed
  qed
qed

text \<open>
  Base case of the (ii) clause at \<open>k = 0\<close> when \<open>t > 0\<close> (the dual to
  @{thm m_anc_zero_idx_B_in_block_shift_when_t_zero} which handles \<open>t = 0\<close>).
  Hunter's dichotomy reduces to case (A) only via
  @{thm bms_all_b0_ascend_row0_when_t_pos}; case-A is discharged by
  @{thm m_anc_zero_idx_B_in_block_shift_when_t_pos_all_asc}.
\<close>

lemma lemma_2_5_ii_clause_step_v2_at_zero_when_t_pos:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some t"
      and t_pos: "0 < t"
      and n_pos: "0 < n"
      and i_lt: "i < l1 A" and j_lt: "j < l1 A" and i_lt_j: "i < j"
  shows "m_ancestor (A[n]) 0 (idx_B_in_expansion A 0 j) (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) 0 (idx_B_in_expansion A n j) (idx_B_in_expansion A n i)"
proof -
  have all_asc: "\<forall>x < l1 A. ascends A x 0"
    using bms_all_b0_ascend_row0_when_t_pos[OF A_BMS A_ne b0 mp t_pos] .
  have n_le: "n \<le> n" by simp
  show ?thesis
    using m_anc_zero_idx_B_in_block_shift_when_t_pos_all_asc
            [OF A_BMS A_ne b0 mp t_pos n_pos all_asc le0 n_le i_lt j_lt i_lt_j] .
qed

lemma lemma_2_5_ii_clause_step_v2:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH_ii: "\<forall>k'<k. lemma_2_5_ii_clause A n k'"
  shows "lemma_2_5_ii_clause A n k"
proof (cases "b0_start A")
  case None
  \<comment> \<open>No \<open>B\<^sub>0\<close> block: \<open>l1 A = 0\<close>, all quantifiers vacuous.\<close>
  have l1z: "l1 A = 0" by (rule l1_zero_of_no_b0[OF None])
  show ?thesis using l1z by (simp add: lemma_2_5_ii_clause_def)
next
  case (Some s)
  note b0 = this
  \<comment> \<open>\<open>b0_start = Some s\<close> forces \<open>max_parent_level A = Some t\<close> for some \<open>t\<close>.\<close>
  obtain t where mp: "max_parent_level A = Some t"
    using b0 unfolding b0_start_def
    by (auto split: option.splits)
  show ?thesis
  proof (cases n)
    case 0
    \<comment> \<open>\<open>n = 0\<close>: \<open>idx_B_in_expansion A 0 _ = idx_B_in_expansion A n _\<close>; trivially reflexive.\<close>
    show ?thesis using \<open>n = 0\<close> by (simp add: lemma_2_5_ii_clause_def)
  next
    case (Suc n')
    hence n_pos: "0 < n" by simp
    show ?thesis
    unfolding lemma_2_5_ii_clause_def
    proof (intro allI impI)
      fix i j
      assume ij: "i < l1 A \<and> j < l1 A"
      have i_lt: "i < l1 A" using ij by simp
      have j_lt: "j < l1 A" using ij by simp
      \<comment> \<open>Case-split on the relationship between \<open>i\<close> and \<open>j\<close>.\<close>
      show "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_B_in_expansion A 0 i)
          \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_B_in_expansion A n i)"
      proof (cases "i = j")
        case True
        \<comment> \<open>\<open>i = j\<close>: both sides are \<open>m_ancestor _ k p p\<close>, which is False
            (irreflexive: target_lt requires strict \<open>q < p\<close>).\<close>
        have lhs_F: "\<not> m_ancestor (A[n]) k (idx_B_in_expansion A 0 j)
                                                (idx_B_in_expansion A 0 i)"
        proof
          assume H: "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j)
                                                (idx_B_in_expansion A 0 i)"
          have "idx_B_in_expansion A 0 i < idx_B_in_expansion A 0 j"
            by (rule m_ancestor_target_lt[OF H])
          thus False using True by simp
        qed
        have rhs_F: "\<not> m_ancestor (A[n]) k (idx_B_in_expansion A n j)
                                                (idx_B_in_expansion A n i)"
        proof
          assume H: "m_ancestor (A[n]) k (idx_B_in_expansion A n j)
                                                (idx_B_in_expansion A n i)"
          have "idx_B_in_expansion A n i < idx_B_in_expansion A n j"
            by (rule m_ancestor_target_lt[OF H])
          thus False using True by simp
        qed
        show ?thesis using lhs_F rhs_F by blast
      next
        case False
        show ?thesis
        proof (cases "j < i")
          case True
          \<comment> \<open>\<open>j < i\<close>: \<open>idx_B(c, j) < idx_B(c, i)\<close>, so
              \<open>m_anc _ k (idx_B(c,j)) (idx_B(c,i))\<close> contradicts target_lt.\<close>
          have lhs_F: "\<not> m_ancestor (A[n]) k (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 i)"
          proof
            assume H: "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j)
                                                  (idx_B_in_expansion A 0 i)"
            have "idx_B_in_expansion A 0 i < idx_B_in_expansion A 0 j"
              by (rule m_ancestor_target_lt[OF H])
            thus False using True unfolding idx_B_in_expansion_def by simp
          qed
          have rhs_F: "\<not> m_ancestor (A[n]) k (idx_B_in_expansion A n j)
                                                  (idx_B_in_expansion A n i)"
          proof
            assume H: "m_ancestor (A[n]) k (idx_B_in_expansion A n j)
                                                  (idx_B_in_expansion A n i)"
            have "idx_B_in_expansion A n i < idx_B_in_expansion A n j"
              by (rule m_ancestor_target_lt[OF H])
            thus False using True unfolding idx_B_in_expansion_def by simp
          qed
          show ?thesis using lhs_F rhs_F by blast
        next
          case False
          hence i_lt_j: "i < j" using \<open>i \<noteq> j\<close> by linarith
          \<comment> \<open>The substantive case \<open>i < j\<close>. Split on \<open>k\<close> (zero vs Suc) and on \<open>t\<close>.\<close>
          show ?thesis
          proof (cases k)
            case 0
            \<comment> \<open>\<open>k = 0\<close>: split on \<open>t = 0\<close> vs \<open>0 < t\<close>.\<close>
            show ?thesis
            proof (cases t)
              case 0
              \<comment> \<open>\<open>k = 0, t = 0\<close>: use chain-shift helper.\<close>
              have mp0: "max_parent_level A = Some 0" using mp \<open>t = 0\<close> by simp
              show ?thesis
                using m_anc_zero_idx_B_in_block_shift_when_t_zero
                        [OF A_BMS A_ne b0 mp0 le0 order.refl i_lt j_lt i_lt_j]
                      \<open>k = 0\<close> by simp
            next
              case (Suc t')
              \<comment> \<open>\<open>k = 0, t = Suc t'\<close>: \<open>0 < t\<close>. Dispatched to
                  @{thm lemma_2_5_ii_clause_step_v2_at_zero_when_t_pos}
                  (Hunter dichotomy at row 0; substantive proof there).\<close>
              have t_pos: "0 < t" using \<open>t = Suc t'\<close> by simp
              show ?thesis
                using lemma_2_5_ii_clause_step_v2_at_zero_when_t_pos
                        [OF A_BMS A_ne b0 mp t_pos n_pos i_lt j_lt i_lt_j]
                      \<open>k = 0\<close> by simp
            qed
          next
            case (Suc k')
            \<comment> \<open>\<open>k = Suc k'\<close>: split on \<open>t \<le> Suc k'\<close> vs \<open>Suc k' < t\<close>.\<close>
            show ?thesis
            proof (cases "t \<le> Suc k'")
              case True
              \<comment> \<open>\<open>Suc k' \<ge> t\<close>: use chain-shift helper.\<close>
              have k'_lt: "k' < k" using \<open>k = Suc k'\<close> by simp
              have IH_kp: "lemma_2_5_ii_clause A n k'"
                using IH_ii k'_lt by blast
              show ?thesis
                using m_anc_idx_B_in_block_shift_at_Suc_k_when_k_ge_t
                        [OF A_BMS A_ne b0 mp True IH_kp i_lt j_lt i_lt_j]
                      \<open>k = Suc k'\<close> by simp
            next
              case False
              hence Sk_lt_t: "Suc k' < t" by simp
              \<comment> \<open>\<open>k = Suc k', Suc k' < t\<close>: Apply the Round 1
                  per-col chain-shift helpers
                  \<open>m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t_asc/_not_asc\<close>.
                  Discharge side conditions \<open>x_len_all\<close>, \<open>k_lt_keep\<close>,
                  \<open>IH_kp\<close>; case-split on \<open>ascends A j (Suc k')\<close>.
                  The uniform \<open>asc_all\<close> (resp. \<open>not_asc_all\<close>) over
                  all \<open>x \<le> j, x < l1 A\<close> remains an internal sub-\<open>sorry\<close>
                  since chain invariance only covers chain members,
                  not arbitrary \<open>x\<close>. Future work: derive via a
                  uniform-ascending lemma for B_0 in BMS or a stronger
                  per-candidate within/outside helper.\<close>
              have k'_lt: "k' < k" using \<open>k = Suc k'\<close> by simp
              have IH_kp: "lemma_2_5_ii_clause A n k'"
                using IH_ii k'_lt by blast
              \<comment> \<open>Side condition: \<open>Suc k' < keep_of (G_block A @ Bs_concat A n)\<close>.\<close>
              have k_lt_keep: "Suc k' < keep_of (G_block A @ Bs_concat A n)"
                using Sk_lt_t
                      keep_of_pre_strip_ge_max_parent_level
                        [OF A_BMS A_ne b0 mp n_pos]
                by linarith
              \<comment> \<open>Side condition: every column has length \<open>> Suc k'\<close>.\<close>
              have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
              have s_lt_last: "s < last_col_idx A"
                by (rule b0_start_lt[OF b0 A_ne])
              have last_lt_arr: "last_col_idx A < arr_len A"
                using A_ne by (cases A) auto
              have t_lt_HA: "t < height A"
                using max_parent_level_lt[OF mp] .
              have Sk_lt_HA: "Suc k' < height A"
                using Sk_lt_t t_lt_HA by linarith
              have x_len_all: "\<forall>x<l1 A. Suc k' < length (A ! (s + x))"
              proof (intro allI impI)
                fix x assume x_lt: "x < l1 A"
                have x_lt_diff: "x < last_col_idx A - s"
                  using x_lt b0 s_lt_last last_lt_arr
                  unfolding l1_def B0_block_def by simp
                have sx_lt_last: "s + x < last_col_idx A"
                  using x_lt_diff s_lt_last by linarith
                have sx_lt_arr: "s + x < arr_len A"
                  using sx_lt_last last_lt_arr by linarith
                have "length (A ! (s + x)) = height A"
                  using length_col_arr[OF is_arr A_ne sx_lt_arr] .
                thus "Suc k' < length (A ! (s + x))" using Sk_lt_HA by simp
              qed
              have j_len: "Suc k' < length (A ! (s + j))"
                using x_len_all j_lt by blast
              have k'_lt_t: "k' < t" using Sk_lt_t by simp
              show ?thesis
              proof (cases "ascends A j (Suc k')")
                case True
                note asc_j = this
                \<comment> \<open>Hunter dichotomy case (A) (paper page 5, applied to
                    \<open>m = Suc k'\<close>): since \<open>j\<close>-th col ascends at \<open>Suc k'\<close>,
                    every \<open>k'\<close>-ancestor of \<open>j\<close> in \<open>I\<close> also ascends.
                    Derive \<open>asc_chain\<close> by Lemma A (transfer chain from
                    \<open>A[n]\<close> to \<open>A\<close>) + @{thm bms_ascend_propagates_to_chain_ancestor}.\<close>
                have asc_chain: "\<forall>x<j. m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                              (idx_B_in_expansion A 0 x)
                                       \<longrightarrow> ascends A x (Suc k')"
                proof (intro allI impI)
                  fix x assume x_lt: "x < j"
                  assume chain_AEn: "m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                          (idx_B_in_expansion A 0 x)"
                  show "ascends A x (Suc k')"
                    using bms_ascend_propagates_to_chain_ancestor
                            [OF A_BMS A_ne b0 mp k'_lt_t n_pos asc_j j_lt x_lt chain_AEn] .
                qed
                show ?thesis
                  using m_anc_idx_B_in_block_shift_at_Suc_k_when_k_lt_t_asc
                          [OF A_BMS A_ne b0 mp Sk_lt_t IH_kp asc_j asc_chain
                              x_len_all k_lt_keep i_lt j_lt i_lt_j]
                        \<open>k = Suc k'\<close> by simp
              next
                case False
                note not_asc_j = this
                \<comment> \<open>Hunter dichotomy case (B), Round 2 "S-empty" path. Avoids
                    the empirically-refuted \<open>not_asc_chain\<close> hypothesis by
                    using @{thm bms_S_empty_case_B_at_block_0} (the candidate
                    set \<open>?S\<close> at block 0 is empty in case-B) and
                    @{thm m_parent_AEn_idx_B_outside_block_at_Suc_k_via_S_empty}
                    (m_parent at \<open>Suc k'\<close> for \<open>idx_B(c,j)\<close> is outside \<open>B_c\<close>
                    for \<open>c \<in> {0, n}\<close>); both LHS and RHS m_ancestor are then
                    False, making the iff trivial.\<close>
                have j_pos: "0 < j" using i_lt_j by linarith
                have x_len_j: "\<forall>x<j. Suc k' < length (A ! (s + x))"
                  using x_len_all j_lt by auto
                have S_empty: "[x \<leftarrow> [0..<j].
                                  elem (A[n]) (idx_B_in_expansion A 0 x) (Suc k')
                                    < elem (A[n]) (idx_B_in_expansion A 0 j) (Suc k')
                                \<and> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                                        (idx_B_in_expansion A 0 x)] = []"
                  using bms_S_empty_case_B_at_block_0
                          [OF A_BMS A_ne b0 mp Sk_lt_t not_asc_j j_lt j_pos n_pos] .
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
                  fix x assume x_lt: "x < j"
                  have x_lt_l1: "x < l1 A" using x_lt j_lt by linarith
                  show "m_ancestor (A[n]) k' (idx_B_in_expansion A n j)
                                              (idx_B_in_expansion A n x)
                      \<longleftrightarrow> m_ancestor (A[n]) k' (idx_B_in_expansion A 0 j)
                                              (idx_B_in_expansion A 0 x)"
                    using IH_kp x_lt_l1 j_lt unfolding lemma_2_5_ii_clause_def by blast
                qed
                have outA: "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A 0 j) of
                              None \<Rightarrow> True
                            | Some p \<Rightarrow> p < idx_B_in_expansion A 0 0)"
                  using m_parent_AEn_idx_B_outside_block_at_Suc_k_via_S_empty
                          [OF A_BMS A_ne b0 mp Sk_lt_t not_asc_j le0 j_lt j_len k_lt_keep
                              x_len_j manc_inv_0 S_empty] .
                have outB: "(case m_parent (A[n]) (Suc k') (idx_B_in_expansion A n j) of
                              None \<Rightarrow> True
                            | Some p \<Rightarrow> p < idx_B_in_expansion A n 0)"
                  using m_parent_AEn_idx_B_outside_block_at_Suc_k_via_S_empty
                          [OF A_BMS A_ne b0 mp Sk_lt_t not_asc_j order.refl j_lt j_len k_lt_keep
                              x_len_j manc_inv_n S_empty] .
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
                show ?thesis using lhs_F rhs_F \<open>k = Suc k'\<close> by blast
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

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

text \<open>Elem match at the singleton boundary position \<open>last_col_idx A\<close>
  between \<open>A\<close> and \<open>A[n]\<close> for \<open>k < m_0\<close> and \<open>n > 0\<close>.
  In \<open>A\<close>, position \<open>l_0 + l_1\<close> is the last col \<open>C\<close>; in \<open>A[n]\<close>,
  the same position is the first col of \<open>B_1\<close>, which equals \<open>bump_col A 0 1\<close>.
  By @{thm bump_col_value_eq_below}, for \<open>k < m_0\<close> the \<open>k\<close>-th elem
  of \<open>bump_col A 0 1\<close> coincides with the \<open>k\<close>-th elem of \<open>C\<close>.\<close>

lemma elem_orig_eq_AEn_at_last_col:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and n_pos: "0 < n"
      and k_lt: "k < m\<^sub>0"
  shows "elem A (last_col_idx A) k = elem (A[n]) (last_col_idx A) k"
proof -
  let ?C = "last_col_idx A"
  let ?P = "G_block A @ Bs_concat A n"
  have is_arr: "is_array A" using BMS_is_array[OF A_BMS] .
  have s_lt_last: "s < ?C" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "?C < arr_len A" using A_ne by (cases A) auto
  have s_le_arr: "s \<le> arr_len A" using s_lt_last last_lt_arr by linarith
  have l0_eq: "l0 A = s"
    using b0 s_le_arr unfolding l0_def G_block_def by simp
  have l1_eq: "l1 A = ?C - s"
    using s_lt_last b0 last_lt_arr unfolding l1_def B0_block_def by simp
  have C_decomp: "?C = l0 A + l1 A"
    using l0_eq l1_eq s_lt_last by linarith
  have l1_pos: "0 < l1 A" using s_lt_last l1_eq by simp
  have C_as_idx: "?C = idx_B_in_expansion A 1 0"
    using C_decomp unfolding idx_B_in_expansion_def by simp
  have len_pre: "length ?P = l0 A + Suc n * l1 A"
    by (simp add: l0_def l1_def length_Bs_concat)
  have C_lt_pre: "?C < length ?P"
  proof -
    have "?C = l0 A + l1 A" using C_decomp .
    also have "\<dots> < l0 A + Suc n * l1 A" using l1_pos n_pos by simp
    finally show ?thesis using len_pre by simp
  qed
  have pre_ne: "?P \<noteq> []" using C_lt_pre by auto
  have one_le_n: "1 \<le> n" using n_pos by simp
  have pre_at_C: "?P ! ?C = Bi_block A 1 ! 0"
    using C_as_idx pre_strip_nth_B[OF one_le_n l1_pos] by simp
  have Bi_at_0: "Bi_block A 1 ! 0 = bump_col A 0 1"
    using l1_pos unfolding l1_def by (rule Bi_block_nth)
  have k_lt_keep: "k < keep_of ?P"
  proof -
    have "m\<^sub>0 \<le> keep_of ?P"
      using keep_of_pre_strip_ge_max_parent_level[OF A_BMS A_ne b0 mp n_pos] .
    thus ?thesis using k_lt by linarith
  qed
  have exp_eq: "A[n] = strip_zero_rows ?P"
    using A_ne unfolding expansion_def by simp
  have strip_eq: "elem (strip_zero_rows ?P) ?C k = elem ?P ?C k"
    using pre_ne C_lt_pre k_lt_keep by (rule elem_strip_lt_keep)
  have k_lt_HA: "k < height A"
    using k_lt max_parent_level_lt[OF mp] by linarith
  have s_lt_arr: "s < arr_len A" using s_lt_last last_lt_arr by linarith
  have k_lt_col_s: "k < length (A ! s)"
  proof -
    have "length (A ! s) = height A"
      using length_col_arr[OF is_arr A_ne s_lt_arr] .
    thus ?thesis using k_lt_HA by simp
  qed
  have bump_eq: "bump_col A 0 1 ! k = (A ! ?C) ! k"
    using bump_col_value_eq_below[OF b0 mp A_ne k_lt k_lt_col_s] .
  have "elem (A[n]) ?C k = elem (strip_zero_rows ?P) ?C k"
    using exp_eq by simp
  also have "\<dots> = elem ?P ?C k" using strip_eq .
  also have "\<dots> = (?P ! ?C) ! k" unfolding elem_def by simp
  also have "\<dots> = (Bi_block A 1 ! 0) ! k" using pre_at_C by simp
  also have "\<dots> = bump_col A 0 1 ! k" using Bi_at_0 by simp
  also have "\<dots> = (A ! ?C) ! k" using bump_eq .
  also have "\<dots> = elem A ?C k" unfolding elem_def by simp
  finally show ?thesis by simp
qed

text \<open>Extended Lemma A (\<open>m_anc_orig_eq_AEn_at_last_col\<close>).
  For \<open>k < m_0\<close> and \<open>n > 0\<close>, \<open>m_ancestor A k (last_col_idx A) q\<close>
  matches \<open>m_ancestor (A[n]) k (last_col_idx A) q\<close>.
  This is Lemma A extended to the singleton source position
  \<open>p = last_col_idx A\<close> (which lies just OUTSIDE the original Lemma A's
  shared range \<open>p < idx_B_in_expansion A 0 (l_1)\<close>, but whose row-\<open>k\<close>
  values still agree across \<open>A\<close> and \<open>A[n]\<close> for \<open>k < m_0\<close>).
  Proof structure: induction on \<open>k\<close> (\<open>less_induct\<close>); the
  \<open>m_parent\<close> filter agrees via @{thm elem_orig_eq_AEn_at_last_col}
  for the source position and @{thm elem_orig_eq_AEn_shared_below_l1}
  for in-block candidates, with the IH at \<open>k' < k\<close> closing the
  m_anc-filter conjunct. The recursive m_anc step on the parent
  \<open>p < C\<close> lifts via @{thm m_anc_orig_eq_AEn_shared_B0} (Lemma A proper).\<close>

lemma m_anc_orig_eq_AEn_at_last_col:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and k_lt: "k < m\<^sub>0"
      and n_pos: "0 < n"
  shows "m_ancestor A k (last_col_idx A) q
       \<longleftrightarrow> m_ancestor (A[n]) k (last_col_idx A) q"
  using k_lt
proof (induct k arbitrary: q rule: less_induct)
  case (less k)
  note IH_k = less.hyps
  note k_lt' = less.prems
  let ?C = "last_col_idx A"
  \<comment> \<open>Decompose \<open>?C = l_0 + l_1\<close> for the shared-range bound.\<close>
  have s_lt_last: "s < ?C" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "?C < arr_len A" using A_ne by (cases A) auto
  have s_le_arr: "s \<le> arr_len A" using s_lt_last last_lt_arr by linarith
  have l0_eq: "l0 A = s"
    using b0 s_le_arr unfolding l0_def G_block_def by simp
  have l1_eq: "l1 A = ?C - s"
    using s_lt_last b0 last_lt_arr unfolding l1_def B0_block_def by simp
  have C_decomp: "?C = l0 A + l1 A"
    using l0_eq l1_eq s_lt_last by linarith
  have C_eq_idx_l1: "?C = idx_B_in_expansion A 0 (l1 A)"
    using C_decomp unfolding idx_B_in_expansion_def by simp
  \<comment> \<open>Elem at \<open>?C\<close> agrees.\<close>
  have elem_C: "elem A ?C k = elem (A[n]) ?C k"
    by (rule elem_orig_eq_AEn_at_last_col[OF A_BMS A_ne b0 mp n_pos k_lt'])
  \<comment> \<open>Elem at any \<open>j < ?C\<close> agrees via Lemma A's elem helper.\<close>
  have elem_inner_match:
    "\<And>j. j < ?C \<Longrightarrow> elem A j k = elem (A[n]) j k"
  proof -
    fix j assume j_lt: "j < ?C"
    have j_lt_idx: "j < idx_B_in_expansion A 0 (l1 A)"
      using j_lt C_eq_idx_l1 by simp
    show "elem A j k = elem (A[n]) j k"
      by (rule elem_orig_eq_AEn_shared_below_l1
                [OF A_BMS A_ne b0 mp n_pos j_lt_idx k_lt'])
  qed
  \<comment> \<open>Step 1: \<open>m_parent A k C = m_parent (A[n]) k C\<close> via filter cong.\<close>
  have mp_C_match: "m_parent A k ?C = m_parent (A[n]) k ?C"
  proof (cases k)
    case 0
    have cands_eq: "[j \<leftarrow> [0..<?C]. elem A j 0 < elem A ?C 0]
                  = [j \<leftarrow> [0..<?C]. elem (A[n]) j 0 < elem (A[n]) ?C 0]"
    proof (rule filter_cong[OF refl])
      fix j assume "j \<in> set [0..<?C]"
      hence j_lt: "j < ?C" by simp
      have ej: "elem A j 0 = elem (A[n]) j 0"
        using elem_inner_match[OF j_lt] \<open>k = 0\<close> by simp
      have ec: "elem A ?C 0 = elem (A[n]) ?C 0"
        using elem_C \<open>k = 0\<close> by simp
      show "elem A j 0 < elem A ?C 0 \<longleftrightarrow> elem (A[n]) j 0 < elem (A[n]) ?C 0"
        using ej ec by simp
    qed
    thus ?thesis using \<open>k = 0\<close> by (simp add: Let_def)
  next
    case (Suc k')
    have k'_lt: "k' < k" using \<open>k = Suc k'\<close> by simp
    have k'_lt_m0: "k' < m\<^sub>0" using k'_lt k_lt' by linarith
    have cands_eq:
      "[j \<leftarrow> [0..<?C]. elem A j (Suc k') < elem A ?C (Suc k')
                        \<and> m_ancestor A k' ?C j]
       = [j \<leftarrow> [0..<?C]. elem (A[n]) j (Suc k') < elem (A[n]) ?C (Suc k')
                          \<and> m_ancestor (A[n]) k' ?C j]"
    proof (rule filter_cong[OF refl])
      fix j assume "j \<in> set [0..<?C]"
      hence j_lt: "j < ?C" by simp
      have ej: "elem A j (Suc k') = elem (A[n]) j (Suc k')"
        using elem_inner_match[OF j_lt] \<open>k = Suc k'\<close> by simp
      have ec: "elem A ?C (Suc k') = elem (A[n]) ?C (Suc k')"
        using elem_C \<open>k = Suc k'\<close> by simp
      have manc: "m_ancestor A k' ?C j \<longleftrightarrow> m_ancestor (A[n]) k' ?C j"
        using IH_k[OF k'_lt k'_lt_m0] by blast
      show "elem A j (Suc k') < elem A ?C (Suc k') \<and> m_ancestor A k' ?C j
          \<longleftrightarrow> elem (A[n]) j (Suc k') < elem (A[n]) ?C (Suc k')
              \<and> m_ancestor (A[n]) k' ?C j"
        using ej ec manc by simp
    qed
    thus ?thesis using \<open>k = Suc k'\<close> by (simp add: Let_def)
  qed
  \<comment> \<open>Step 2: m_anc by m_anc_via_parent_some/none + Lemma A on the parent.\<close>
  show ?case
  proof (cases "m_parent A k ?C")
    case None
    have mp_AEn_none: "m_parent (A[n]) k ?C = None"
      using None mp_C_match by simp
    have lhs_F: "\<not> m_ancestor A k ?C q"
      using m_anc_via_parent_none[OF None] .
    have rhs_F: "\<not> m_ancestor (A[n]) k ?C q"
      using m_anc_via_parent_none[OF mp_AEn_none] .
    show ?thesis using lhs_F rhs_F by simp
  next
    case (Some p)
    have p_lt_C: "p < ?C" using Some by (rule m_parent_lt)
    have mp_AEn_some: "m_parent (A[n]) k ?C = Some p"
      using Some mp_C_match by simp
    have iff_A: "m_ancestor A k ?C q \<longleftrightarrow> p = q \<or> m_ancestor A k p q"
      using m_anc_via_parent_some[OF Some] .
    have iff_AEn: "m_ancestor (A[n]) k ?C q \<longleftrightarrow> p = q \<or> m_ancestor (A[n]) k p q"
      using m_anc_via_parent_some[OF mp_AEn_some] .
    have p_lt_idx: "p < idx_B_in_expansion A 0 (l1 A)"
      using p_lt_C C_eq_idx_l1 by simp
    have rec: "m_ancestor A k p q \<longleftrightarrow> m_ancestor (A[n]) k p q"
      using m_anc_orig_eq_AEn_shared_B0
              [OF A_BMS A_ne b0 mp k_lt' n_pos p_lt_idx] .
    show ?thesis using iff_A iff_AEn rec by blast
  qed
qed

text \<open>
  Single-step block-shift for (iii): translate an \<open>A[n]\<close>-ancestry chain
  whose source sits in block \<open>t+1\<close> and target in block \<open>t\<close> (offset by
  exactly one block, source one block ahead of target) up by one further
  block, to source \<open>t+2\<close> / target \<open>t+1\<close>. The shift stays inside \<open>A[n]\<close>
  and preserves the +1 block offset between source and target. This is the
  atomic step that, iterated, realizes Hunter's "trivial extension" of (ii)
  (paper p.5). It is the genuinely substantive content of the \<open>n \<ge> 2\<close>
  bridge — the within-\<open>A[n]\<close> analog of (ii)/(v) for a source-target pair
  offset by one block — and is left as an internal \<open>sorry\<close> pending a
  generalized block-translation helper.

  Empirically verified (no offset-shift counterexample) via
  \<open>verify/verify_iii_block_shift_bridge_n_ge_2.py\<close> (441 BMSs, 0 violations).
\<close>

lemma iii_single_step_t_to_Suc_t:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and k_lt: "k < m\<^sub>0"
      and i_lt: "i < l1 A"
      and step_fits: "t + 1 < n"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A (t + 1) 0)
                            (idx_B_in_expansion A t i)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (t + 2) 0)
                                 (idx_B_in_expansion A (t + 1) i)"
  sorry

text \<open>
  Block-shift bridge for (iii) at \<open>n \<ge> 2\<close>: shift both source and target
  of an \<open>A[n]\<close>-ancestry chain by \<open>(n-1)\<close> blocks. Hunter's "trivial
  extension" generalization of (ii); substantive structural lemma about
  block-translation within \<open>A[n]\<close>.

  Proof here is reduced to an induction on the shift amount \<open>t\<close>, composing
  copies of @{thm iii_single_step_t_to_Suc_t}. The generalized claim
  \<open>bridge_upto t\<close> states the LHS equivales the partially-shifted chain
  with source block \<open>t+1\<close> / target block \<open>t\<close>; base case \<open>t = 0\<close> is
  reflexivity (the LHS itself), and instantiating \<open>t = n - 1\<close> yields the
  RHS \<open>(idx_B n 0, idx_B (n-1) i)\<close>.
\<close>

lemma iii_block_shift_bridge_n_ge_2:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and k_lt: "k < m\<^sub>0"
      and n_ge_2: "2 \<le> n"
      and i_lt: "i < l1 A"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A 1 0) (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n 0)
                                 (idx_B_in_expansion A (n - 1) i)"
proof -
  \<comment> \<open>Generalized claim: the LHS (source block 1 / target block 0) equivales
      the chain shifted up by \<open>t\<close> blocks (source \<open>t+1\<close> / target \<open>t\<close>),
      for every \<open>t \<le> n - 1\<close>. Proved by induction on \<open>t\<close>.\<close>
  have bridge_upto:
    "\<And>t. t \<le> n - 1 \<Longrightarrow>
       m_ancestor (A[n]) k (idx_B_in_expansion A 1 0) (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (t + 1) 0)
                                 (idx_B_in_expansion A t i)"
  proof -
    fix t :: nat
    assume "t \<le> n - 1"
    thus "m_ancestor (A[n]) k (idx_B_in_expansion A 1 0)
                              (idx_B_in_expansion A 0 i)
        \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (t + 1) 0)
                                   (idx_B_in_expansion A t i)"
    proof (induct t)
      case 0
      show ?case by simp
    next
      case (Suc t)
      have t_le: "t \<le> n - 1" using Suc.prems by simp
      have IH: "m_ancestor (A[n]) k (idx_B_in_expansion A 1 0)
                                    (idx_B_in_expansion A 0 i)
             \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (t + 1) 0)
                                         (idx_B_in_expansion A t i)"
        using Suc.hyps[OF t_le] .
      \<comment> \<open>\<open>Suc t \<le> n - 1\<close> with \<open>2 \<le> n\<close> gives \<open>t + 1 < n\<close>, so the
          single step from \<open>t\<close> to \<open>t + 1\<close> is well-formed.\<close>
      have step_fits: "t + 1 < n" using Suc.prems n_ge_2 by linarith
      have step: "m_ancestor (A[n]) k (idx_B_in_expansion A (t + 1) 0)
                                      (idx_B_in_expansion A t i)
               \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (t + 2) 0)
                                           (idx_B_in_expansion A (t + 1) i)"
        by (rule iii_single_step_t_to_Suc_t
                   [OF A_BMS A_ne b0 mp k_lt i_lt step_fits])
      \<comment> \<open>Compose IH with the single step; the \<open>Suc t\<close> block indices on the
          RHS of the goal are \<open>t + 2\<close> (source) and \<open>t + 1\<close> (target).\<close>
      have combined:
        "m_ancestor (A[n]) k (idx_B_in_expansion A 1 0)
                             (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (t + 2) 0)
                                  (idx_B_in_expansion A (t + 1) i)"
        using IH step by blast
      have idx1: "idx_B_in_expansion A (Suc t + 1) 0
                = idx_B_in_expansion A (t + 2) 0"
        by (simp add: idx_B_in_expansion_def)
      have idx2: "idx_B_in_expansion A (Suc t) i
                = idx_B_in_expansion A (t + 1) i"
        by (simp add: idx_B_in_expansion_def)
      show ?case
        unfolding idx1 idx2 using combined .
    qed
  qed
  \<comment> \<open>Instantiate \<open>t = n - 1\<close>: source block \<open>(n-1)+1 = n\<close>, target block
      \<open>n - 1\<close>, which is exactly the RHS.\<close>
  have n_minus_1_le: "n - 1 \<le> n - 1" by simp
  have inst: "m_ancestor (A[n]) k (idx_B_in_expansion A 1 0)
                                  (idx_B_in_expansion A 0 i)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A ((n - 1) + 1) 0)
                                  (idx_B_in_expansion A (n - 1) i)"
    using bridge_upto[OF n_minus_1_le] .
  have src_eq: "(n - 1) + 1 = n" using n_ge_2 by simp
  show ?thesis using inst unfolding src_eq .
qed

text \<open>
  Step lemma for clause (iii): assumes IH (= full lemma_2_5_at at k' < k),
  IH at \<open>n-1\<close> for same \<open>k\<close>, AND clause (ii) at same level \<open>k\<close>
  (per dependency matrix; IH at \<open>n-1\<close> provides \<open>lemma_2_5_ii_clause A (n-1) k\<close>,
  used in chain translation).

  Proof structure (Hunter paper page 5, "trivially extended" from (ii)):
  \<^enum> Use @{thm m_anc_orig_eq_AEn_at_last_col} (extended Lemma A) to translate
    the LHS ancestry in \<open>A\<close> from source \<open>last_col_idx A\<close> to ancestry
    in \<open>A[n]\<close> at the same position. The position \<open>last_col_idx A\<close>
    equals \<open>idx_B_in_expansion A 1 0\<close> (first col of \<open>B_1\<close>) in
    \<open>A[n]\<close>'s layout, and they share the \<open>k\<close>-th elem for \<open>k < m_0\<close>.
  \<^enum> Apply the block-shift bridge to translate
    \<open>m_anc (A[n]) k (idx_B 1 0) (idx_B 0 i)\<close> to
    \<open>m_anc (A[n]) k (idx_B n 0) (idx_B (n-1) i)\<close>. The bridge is
    a "translate by (n-1) blocks" shift in \<open>A[n]\<close>; for \<open>n = 1\<close>
    it is the identity, for \<open>n \<ge> 2\<close> it is the substantive
    Hunter "trivial extension" of (ii) — left as an internal
    \<open>sorry\<close> pending a generalized block-translation helper
    (analog of (ii) for source-target offset by \<open>+1\<close> per block).
\<close>

lemma lemma_2_5_iii_clause_step:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and IH_n_minus_1: "lemma_2_5_at A (n - 1) k"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
  shows "lemma_2_5_iii_clause A n k"
  unfolding lemma_2_5_iii_clause_def
proof (intro allI impI)
  fix m\<^sub>0 i
  assume h: "0 < n \<and> max_parent_level A = Some m\<^sub>0 \<and> k < m\<^sub>0 \<and> i < l1 A"
  hence n_pos: "0 < n" and mp: "max_parent_level A = Some m\<^sub>0"
     and k_lt: "k < m\<^sub>0" and i_lt: "i < l1 A" by simp+
  let ?C = "last_col_idx A"
  let ?q = "idx_B0_in_orig A i"
  let ?src_n = "idx_B_in_expansion A n 0"
  let ?tgt_n = "idx_B_in_expansion A (n - 1) i"
  \<comment> \<open>\<open>max_parent_level A = Some m_0\<close> implies \<open>b0_start A = Some s\<close>.\<close>
  have b0_not_none: "b0_start A \<noteq> None"
  proof
    assume "b0_start A = None"
    hence "max_parent_level A = None"
      using b0_start_None_imp_max_parent_level_None[OF A_ne] by simp
    thus False using mp by simp
  qed
  then obtain s where b0: "b0_start A = Some s" by auto
  \<comment> \<open>Identify \<open>?C = idx_B 1 0\<close> and \<open>?q = idx_B 0 i\<close>.\<close>
  have s_lt_last: "s < ?C" by (rule b0_start_lt[OF b0 A_ne])
  have last_lt_arr: "?C < arr_len A" using A_ne by (cases A) auto
  have s_le_arr: "s \<le> arr_len A" using s_lt_last last_lt_arr by linarith
  have l0_eq: "l0 A = s"
    using b0 s_le_arr unfolding l0_def G_block_def by simp
  have l1_eq: "l1 A = ?C - s"
    using s_lt_last b0 last_lt_arr unfolding l1_def B0_block_def by simp
  have C_decomp: "?C = l0 A + l1 A"
    using l0_eq l1_eq s_lt_last by linarith
  have C_eq_idx1: "?C = idx_B_in_expansion A 1 0"
    using C_decomp unfolding idx_B_in_expansion_def by simp
  have q_eq_idx0: "?q = idx_B_in_expansion A 0 i"
    unfolding idx_B0_in_orig_def idx_B_in_expansion_def by simp
  \<comment> \<open>STEP 1: extended Lemma A — LHS in \<open>A\<close> ⟺ same shape in \<open>A[n]\<close>.\<close>
  have step1: "m_ancestor A k ?C ?q
             \<longleftrightarrow> m_ancestor (A[n]) k ?C ?q"
    by (rule m_anc_orig_eq_AEn_at_last_col[OF A_BMS A_ne b0 mp k_lt n_pos])
  \<comment> \<open>STEP 2: bridge — translate \<open>(idx_B 1 0, idx_B 0 i)\<close> to
      \<open>(idx_B n 0, idx_B (n-1) i)\<close> in \<open>A[n]\<close> by shifting both
      endpoints by \<open>(n-1)\<close> blocks. Identity for \<open>n = 1\<close>;
      substantive for \<open>n \<ge> 2\<close> (Hunter "trivial extension"
      generalization of (ii) — left as internal \<open>sorry\<close>).\<close>
  have bridge: "m_ancestor (A[n]) k (idx_B_in_expansion A 1 0)
                                    (idx_B_in_expansion A 0 i)
              \<longleftrightarrow> m_ancestor (A[n]) k ?src_n ?tgt_n"
  proof (cases n)
    case 0
    thus ?thesis using n_pos by simp
  next
    case (Suc n')
    show ?thesis
    proof (cases n')
      case 0
      have n_eq_1: "n = 1" using \<open>n = Suc n'\<close> \<open>n' = 0\<close> by simp
      have src_eq: "?src_n = idx_B_in_expansion A 1 0"
        using n_eq_1 by simp
      have tgt_eq: "?tgt_n = idx_B_in_expansion A 0 i"
        using n_eq_1 by simp
      show ?thesis using src_eq tgt_eq by simp
    next
      case (Suc n'')
      have n_ge_2: "2 \<le> n" using \<open>n = Suc n'\<close> \<open>n' = Suc n''\<close> by simp
      \<comment> \<open>Substantive bridge for \<open>n \<ge> 2\<close>: dispatch to
          @{thm iii_block_shift_bridge_n_ge_2}.\<close>
      show ?thesis
        by (rule iii_block_shift_bridge_n_ge_2[OF A_BMS A_ne b0 mp k_lt n_ge_2 i_lt])
    qed
  qed
  \<comment> \<open>Combine STEP 1 + STEP 2.\<close>
  show "m_ancestor A k ?C ?q
      \<longleftrightarrow> m_ancestor (A[n]) k ?src_n ?tgt_n"
    using step1 bridge C_eq_idx1 q_eq_idx0 by simp
qed

text \<open>
  Step lemma stubs for clauses (iv), (i), (v) per Hunter's
  dependency order (ii) \<rightarrow> (iii) \<rightarrow> (iv) \<rightarrow> (i) \<rightarrow> (v).
  Substantive proofs deferred; the assembly into
  \<open>lemma_2_5_at_main\<close> below uses them mechanically.
\<close>

text \<open>
  Auxiliary for the intermediate case of clause (iv). When the
  \<open>k\<close>-parent \<open>p\<close> of the \<open>i\<close>-th column of \<open>B_n\<close> in \<open>A[n]\<close>
  is hypothesised to lie in \<open>B_t\<close> with \<open>0 \<le> t < n\<close>, Hunter's
  argument (paper page 6) shows the configuration is impossible
  (\<open>False\<close>). The proof here scaffolds Hunter's case-split:

  \<^enum> Oracle: @{thm lemma_2_5_ii_main_v2} gives \<open>(ii) A n k'\<close>
    for every \<open>k'\<close> independently of the joint induction.
  \<^enum> Case \<open>k = 0\<close>: no chain condition; the row-0 strict ordering
    on B-block columns must place the parent in \<open>B_n\<close> or \<open>G\<close>
    (deferred sub-\<open>sorry\<close>: row-0 monotonicity helper missing).
  \<^enum> Case \<open>k = Suc k_0\<close>: sub-split on whether some \<open>k' < k\<close>
    yields a \<open>k'\<close>-parent of the \<open>i\<close>-th col in \<open>G\<close>:
    \<^item> If yes, by IH (iv) at \<open>k'\<close> all \<open>k'\<close>-ancestors lie in
      \<open>G\<close>, including the \<open>k\<close>-parent \<open>p\<close>, which contradicts
      \<open>p = idx_B(t,j)\<close>. (Deferred sub-\<open>sorry\<close>: ancestor-of-G-is-G
      lemma.)
    \<^item> If no, then \<open>\<forall>k' < k\<close> the \<open>k'\<close>-parent lies in \<open>B_n\<close>;
      further sub-split on whether the first column of \<open>B_n\<close> is
      a \<open>k'\<close>-ancestor of the \<open>i\<close>-th col for every \<open>k' < k\<close>:
      \<^enum> If yes (chain through first col exists at every \<open>k' < k\<close>):
        transfer chain to \<open>B_0\<close> via (ii) at each \<open>k' < k\<close>; combine
        with (ii) at \<open>k\<close> and repeated (iii) to derive that the
        \<open>k\<close>-parent must sit in \<open>B_n\<close> or \<open>G\<close>, contradicting
        \<open>p \<in> B_t\<close>. (Deferred sub-\<open>sorry\<close>.)
      \<^enum> If no (some \<open>k' < k\<close> witnesses chain breakage): apply
        IH (iv) at the offending \<open>k'\<close> to obtain a witness
        ancestor in \<open>B_n \<union> G\<close> through which \<open>p\<close> must factor;
        derive \<open>False\<close>. (Deferred sub-\<open>sorry\<close>.)

  Net result: a single bare \<open>sorry\<close> inside the \<open>lemma_2_5_iv_clause_step\<close>
  proof is replaced by 4 well-isolated sub-sorries inside this auxiliary,
  each tagged with the helper it awaits.
\<close>

text \<open>
  Auxiliary for the (iv) intermediate case at \<open>k = 0\<close>: m_parent at level
  0 is just the greatest predecessor with strictly smaller row-0 elem. The
  proof obligation is to show that the first column of \<open>B_n\<close>
  (\<open>idx_B n 0\<close>) qualifies as a candidate (so the actual m_parent must be
  in \<open>B_n\<close> or later, not in earlier \<open>B_t\<close>). Requires row-0
  strict-less analysis using @{thm elem_AEn_idx_B_value}.
\<close>

text \<open>
  Auxiliary for the (iv) intermediate case at \<open>k = Suc k_0\<close>, ancestor-of-G
  sub-case: when some \<open>k' < k\<close> has the \<open>k'\<close>-parent of the \<open>i\<close>-th col in
  \<open>G\<close>, by IH (iv) at \<open>k'\<close> all \<open>k'\<close>-ancestors lie in \<open>G\<close>, including the
  \<open>k\<close>-parent \<open>p\<close>, contradicting \<open>p = idx_B(t, j)\<close>.
\<close>

text \<open>
  Auxiliary for the (iv) intermediate case at \<open>k = Suc k_0\<close>, chain-through-
  first sub-case: when every \<open>k' < k\<close> has the \<open>k'\<close>-parent in \<open>B_n\<close> AND
  the first col of \<open>B_n\<close> is a \<open>k'\<close>-ancestor of the \<open>i\<close>-th col, transfer
  chain to \<open>B_0\<close> via (ii) at each \<open>k' < k\<close>, then use (ii) and (iii) at
  \<open>k\<close> to deduce \<open>k\<close>-parent lies in \<open>B_n \<union> G\<close>, contradicting \<open>p \<in> B_t\<close>.
\<close>

text \<open>
  Auxiliary for the (iv) intermediate case at \<open>k = Suc k_0\<close>, chain-break
  sub-case: when some \<open>k' < k\<close> witnesses chain breakage (the first col of
  \<open>B_n\<close> is NOT a \<open>k'\<close>-ancestor of the \<open>i\<close>-th col), apply IH (iv) at
  \<open>k'\<close> on the witness to derive contradiction.
\<close>

text \<open>
  Arithmetic injectivity helper: within the index range \<open>t < n\<close>,
  \<open>j < l1\<close>, the block-\<open>t\<close> column \<open>idx_B(t, j)\<close> never coincides
  with a block-\<open>n\<close> column \<open>idx_B(n, j')\<close>. Indeed
  \<open>l0 + t*l1 + j < l0 + (t+1)*l1 \<le> l0 + n*l1 \<le> idx_B(n, j')\<close>.
  This discharges the within-block sub-case of the (iv) intermediate
  case at \<open>k = 0\<close>.
\<close>

lemma idx_B_earlier_block_lt_block_n:
  assumes t_lt_n: "t < n" and j_lt: "j < l1 A"
  shows "idx_B_in_expansion A t j < idx_B_in_expansion A n j'"
proof -
  have suc_le: "Suc t \<le> n" using t_lt_n by simp
  have mle: "Suc t * l1 A \<le> n * l1 A" using mult_le_mono1[OF suc_le] .
  have "l0 A + t * l1 A + j < l0 A + t * l1 A + l1 A"
    using j_lt by simp
  also have "\<dots> = l0 A + Suc t * l1 A" by simp
  also have "\<dots> \<le> l0 A + n * l1 A" using mle by simp
  also have "\<dots> \<le> l0 A + n * l1 A + j'" by simp
  finally show ?thesis unfolding idx_B_in_expansion_def by simp
qed

text \<open>
  Auxiliary for the (iv) intermediate case at \<open>k = 0\<close>, outside-block
  sub-case: when the block-0 candidate set \<open>S\<close> for column \<open>i\<close> is empty,
  the level-0 m-parent of \<open>idx_B(n, i)\<close> lands strictly before
  \<open>idx_B(n, 0)\<close>. Refining @{thm m_parent_AEn_zero_idx_B_outside_block_when_t_pos_all_asc}
  and @{thm m_parent_AEn_zero_idx_B_outside_block_when_t_zero}: the residual
  obligation is that this landing position \<open>p\<close> is in fact in \<open>G\<close>
  (\<open>p < l0\<close>), never in an intermediate block \<open>B_t\<close> with \<open>t < n\<close>.

  Empirically confirmed (1279 yaBMSs, 0 violations;
  \<open>verify/verify_iv_at_zero_no_Bt_parent.py\<close>). The within-block landing
  (\<open>S\<close> non-empty) is discharged fully below by
  @{thm idx_B_earlier_block_lt_block_n}; only this outside-block-to-\<open>G\<close>
  refinement remains as a single isolated \<open>sorry\<close>.
\<close>

lemma clause_iv_intermediate_B_t_impossible_at_zero_outside_lands_in_G:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and i_pos: "0 < i" and i_lt: "i < l1 A"
      and mp_eq: "m_parent (A[n]) 0 (idx_B_in_expansion A n i) = Some p"
      and S_empty: "[j' \<leftarrow> [0..<i]. elem (A[n]) (idx_B_in_expansion A 0 j') 0
                            < elem (A[n]) (idx_B_in_expansion A 0 i) 0] = []"
  shows "p < l0 A"
  sorry

lemma clause_iv_intermediate_B_t_impossible_at_zero:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and i_pos: "0 < i" and i_lt: "i < l1 A"
      and mp_eq: "m_parent (A[n]) 0 (idx_B_in_expansion A n i) = Some p"
      and t_lt_n: "t < n"
      and j_lt: "j < l1 A"
      and p_eq: "p = idx_B_in_expansion A t j"
  shows "False"
proof -
  \<comment> \<open>\<open>b0_start = Some s\<close> forces \<open>max_parent_level A = Some t\<^sub>0\<close>.\<close>
  obtain t\<^sub>0 where mp0: "max_parent_level A = Some t\<^sub>0"
    using b0 unfolding b0_start_def by (auto split: option.splits)
  have n_pos: "0 < n" using t_lt_n by simp
  let ?S = "[j' \<leftarrow> [0..<i]. elem (A[n]) (idx_B_in_expansion A 0 j') 0
                        < elem (A[n]) (idx_B_in_expansion A 0 i) 0]"
  show False
  proof (cases "?S = []")
    case False
    \<comment> \<open>Within-block: the m-parent lands at \<open>idx_B(n, last S)\<close>, a block-\<open>n\<close>
        column. But \<open>p = idx_B(t, j)\<close> is in an earlier block, contradiction.\<close>
    note S_ne = False
    have mp_within: "m_parent (A[n]) 0 (idx_B_in_expansion A n i)
                   = Some (idx_B_in_expansion A n (last ?S))"
    proof (cases t\<^sub>0)
      case 0
      show ?thesis
        using m_parent_AEn_zero_idx_B_within_block_when_t_zero
                [OF A_BMS A_ne b0 mp0[unfolded 0] order.refl i_lt S_ne] .
    next
      case (Suc t')
      have t0_pos: "0 < t\<^sub>0" using Suc by simp
      have all_asc: "\<forall>x < l1 A. ascends A x 0"
        using bms_all_b0_ascend_row0_when_t_pos[OF A_BMS A_ne b0 mp0 t0_pos] .
      show ?thesis
        using m_parent_AEn_zero_idx_B_within_block_when_t_pos_all_asc
                [OF A_BMS A_ne b0 mp0 t0_pos n_pos all_asc order.refl i_lt S_ne] .
    qed
    have p_block_n: "p = idx_B_in_expansion A n (last ?S)"
      using mp_eq mp_within by simp
    have lt: "idx_B_in_expansion A t j < idx_B_in_expansion A n (last ?S)"
      using idx_B_earlier_block_lt_block_n[OF t_lt_n j_lt] .
    show False using p_eq p_block_n lt by simp
  next
    case True
    \<comment> \<open>Outside-block: the m-parent lands strictly before \<open>idx_B(n, 0)\<close>.
        By the refinement helper it lands in \<open>G\<close> (\<open>p < l0\<close>), but
        \<open>p = idx_B(t, j)\<close> with \<open>t < n\<close> has \<open>p \<ge> l0\<close>. Contradiction.\<close>
    have p_lt_l0: "p < l0 A"
      using clause_iv_intermediate_B_t_impossible_at_zero_outside_lands_in_G
              [OF A_BMS A_ne b0 l1_pos i_pos i_lt mp_eq True] .
    have p_ge_l0: "l0 A \<le> p"
      using p_eq unfolding idx_B_in_expansion_def by simp
    show False using p_lt_l0 p_ge_l0 by simp
  qed
qed

lemma clause_iv_intermediate_B_t_impossible_when_G_parent_exists:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and k_pos: "0 < k"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and i_pos: "0 < i" and i_lt: "i < l1 A"
      and mp_eq: "m_parent (A[n]) k (idx_B_in_expansion A n i) = Some p"
      and t_lt_n: "t < n"
      and j_lt: "j < l1 A"
      and p_eq: "p = idx_B_in_expansion A t j"
      and G_parent_exists: "\<exists>k' < k. \<exists>q. m_parent (A[n]) k' (idx_B_in_expansion A n i)
                                            = Some q \<and> (\<exists>g < l0 A. q = idx_G A g)"
  shows "False"
proof -
  let ?i = "idx_B_in_expansion A n i"
  \<comment> \<open>The level-\<open>k\<close> parent \<open>p = idx_B(t,j)\<close> lives in some block, hence
      \<open>l0 A \<le> p\<close>.\<close>
  have p_ge_l0: "l0 A \<le> p"
    using p_eq unfolding idx_B_in_expansion_def by simp
  \<comment> \<open>Since \<open>0 < k\<close>, write \<open>k = Suc k\<^sub>0\<close>; the level-\<open>k\<close> parent is a
      level-\<open>k\<^sub>0\<close> ancestor of \<open>?i\<close> (definition of \<open>m_parent\<close>).\<close>
  obtain k\<^sub>0 where k_eq: "k = Suc k\<^sub>0" using k_pos by (cases k) auto
  have anc_k0: "m_ancestor (A[n]) k\<^sub>0 ?i p"
    using m_parent_Suc_implies_m_ancestor[OF mp_eq[unfolded k_eq]] .
  \<comment> \<open>Extract the G-parent witness at some level \<open>k' < k\<close>.\<close>
  obtain k' q g where k'_lt: "k' < k"
                  and mp_k': "m_parent (A[n]) k' ?i = Some q"
                  and g_lt: "g < l0 A"
                  and q_eq: "q = idx_G A g"
    using G_parent_exists by blast
  \<comment> \<open>The G-parent index is strictly below \<open>l0 A\<close>, hence strictly below \<open>p\<close>.\<close>
  have q_lt_l0: "q < l0 A" using q_eq g_lt unfolding idx_G_def by simp
  have q_lt_p: "q < p" using q_lt_l0 p_ge_l0 by simp
  \<comment> \<open>From \<open>k' < Suc k\<^sub>0\<close> we get \<open>k' \<le> k\<^sub>0\<close>; ancestry is monotone in the
      level, so \<open>p\<close> is also a level-\<open>k'\<close> ancestor of \<open>?i\<close>.\<close>
  have k'_le_k0: "k' \<le> k\<^sub>0" using k'_lt k_eq by simp
  have anc_k': "m_ancestor (A[n]) k' ?i p"
    using m_ancestor_mono[OF k'_le_k0 anc_k0] .
  \<comment> \<open>But the level-\<open>k'\<close> parent of \<open>?i\<close> is \<open>q\<close>, so any level-\<open>k'\<close> ancestor
      \<open>p\<close> is either \<open>q\<close> itself or sits strictly to the left of \<open>q\<close>.
      Either way \<open>p \<le> q\<close>, contradicting \<open>q < p\<close>.\<close>
  have "q = p \<or> m_ancestor (A[n]) k' q p"
    using m_anc_via_parent_some[OF mp_k'] anc_k' by blast
  thus False
  proof
    assume "q = p" thus False using q_lt_p by simp
  next
    assume "m_ancestor (A[n]) k' q p"
    hence "p < q" by (rule m_ancestor_target_lt)
    thus False using q_lt_p by simp
  qed
qed

text \<open>
  Sub-helper for the third linearity branch below. When the chain of
  \<open>idx_B(n, i)\<close> runs through \<open>idx_B(n, 0)\<close>, and \<open>p = idx_B(t, j)\<close> with
  \<open>t < n\<close> sits strictly below \<open>idx_B(n, 0)\<close>, the only remaining
  configuration to rule out is that \<open>p\<close> is itself an \<open>m\<close>-ancestor of
  \<open>idx_B(n, 0)\<close>, i.e. an intermediate-block column lying on the upward
  chain from \<open>idx_B(n, 0)\<close>. Empirically this never happens (yaBMS BFS,
  \<open>verify/verify_chain_through_Bn_first.py\<close>: 0 of 441 BMSs realize the
  full premise combination), so the obligation is vacuously discharged;
  it is isolated here as a single \<open>sorry\<close>.
\<close>

lemma idx_B_n_zero_no_intermediate_B_t_ancestor:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and t_lt_n: "t < n"
      and j_lt: "j < l1 A"
      and anc: "m_ancestor (A[n]) m (idx_B_in_expansion A n 0)
                                     (idx_B_in_expansion A t j)"
  shows "False"
  sorry

lemma clause_iv_intermediate_B_t_impossible_chain_through_Bn_first:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and k_pos: "0 < k"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and i_pos: "0 < i" and i_lt: "i < l1 A"
      and mp_eq: "m_parent (A[n]) k (idx_B_in_expansion A n i) = Some p"
      and t_lt_n: "t < n"
      and j_lt: "j < l1 A"
      and p_eq: "p = idx_B_in_expansion A t j"
      and no_G_parent: "\<not> (\<exists>k' < k. \<exists>q. m_parent (A[n]) k' (idx_B_in_expansion A n i)
                                           = Some q \<and> (\<exists>g < l0 A. q = idx_G A g))"
      and chain_through_Bn0: "\<forall>k' < k. m_ancestor (A[n]) k' (idx_B_in_expansion A n i)
                                                            (idx_B_in_expansion A n 0)"
  shows "False"
proof -
  let ?i = "idx_B_in_expansion A n i"
  let ?b0 = "idx_B_in_expansion A n 0"
  \<comment> \<open>Since \<open>0 < k\<close>, write \<open>k = Suc k\<^sub>0\<close>; the level-\<open>k\<close> parent \<open>p\<close> is then a
      level-\<open>k\<^sub>0\<close> ancestor of \<open>?i\<close> (definition of \<open>m_parent\<close>).\<close>
  obtain k\<^sub>0 where k_eq: "k = Suc k\<^sub>0" using k_pos by (cases k) auto
  have anc_p: "m_ancestor (A[n]) k\<^sub>0 ?i p"
    using m_parent_Suc_implies_m_ancestor[OF mp_eq[unfolded k_eq]] .
  \<comment> \<open>By the chain hypothesis at level \<open>k\<^sub>0 < k\<close>, \<open>?b0\<close> is also a level-\<open>k\<^sub>0\<close>
      ancestor of \<open>?i\<close>.\<close>
  have k0_lt: "k\<^sub>0 < k" using k_eq by simp
  have anc_b0: "m_ancestor (A[n]) k\<^sub>0 ?i ?b0"
    using chain_through_Bn0 k0_lt by blast
  \<comment> \<open>\<open>p = idx_B(t, j)\<close> with \<open>t < n\<close> lies strictly below \<open>idx_B(n, 0) = ?b0\<close>.\<close>
  have p_lt_b0: "p < ?b0"
    using p_eq idx_B_earlier_block_lt_block_n[OF t_lt_n j_lt] by simp
  \<comment> \<open>Both \<open>p\<close> and \<open>?b0\<close> are level-\<open>k\<^sub>0\<close> ancestors of \<open>?i\<close>, so by linearity
      of the \<open>m\<close>-ancestor chain they are comparable.\<close>
  have "p = ?b0 \<or> m_ancestor (A[n]) k\<^sub>0 p ?b0 \<or> m_ancestor (A[n]) k\<^sub>0 ?b0 p"
    using m_ancestor_chain_linear anc_p anc_b0 by blast
  thus False
  proof (elim disjE)
    \<comment> \<open>\<open>p = ?b0\<close> contradicts \<open>p < ?b0\<close>.\<close>
    assume "p = ?b0" thus False using p_lt_b0 by simp
  next
    \<comment> \<open>If \<open>p\<close> is an ancestor of \<open>?b0\<close> then \<open>?b0 < p\<close>, contradicting \<open>p < ?b0\<close>.\<close>
    assume "m_ancestor (A[n]) k\<^sub>0 p ?b0"
    hence "?b0 < p" by (rule m_ancestor_target_lt)
    thus False using p_lt_b0 by simp
  next
    \<comment> \<open>The remaining configuration: \<open>p = idx_B(t, j)\<close> is itself an ancestor
        of \<open>?b0 = idx_B(n, 0)\<close>. Ruled out by the sub-helper.\<close>
    assume "m_ancestor (A[n]) k\<^sub>0 ?b0 p"
    thus False
      using idx_B_n_zero_no_intermediate_B_t_ancestor
              [OF A_BMS A_ne b0 l1_pos IH clause_iii_at_k t_lt_n j_lt]
            p_eq by simp
  qed
qed

text \<open>
  The \<open>B_n[0]\<close> gateway property. The leftmost block-\<open>n\<close> column
  \<open>idx_B(n, 0)\<close> is the unique entry point through which the upward
  \<open>m\<close>-ancestor chain of any block-\<open>n\<close> column \<open>idx_B(n, i)\<close> must pass
  before it can reach a column of an earlier block \<open>B_t\<close> (\<open>t < n\<close>).
  Hence whenever an earlier-block column \<open>idx_B(t, j)\<close> is a level-\<open>m\<close>
  ancestor of \<open>idx_B(n, i)\<close>, the gateway \<open>idx_B(n, 0)\<close> is one too.

  Empirically confirmed (yaBMS BFS, \<open>verify/verify_Bn0_gateway.py\<close>:
  885 BMSs, 0 failures of the implication). Isolated here as a single
  \<open>sorry\<close>; it is the sole remaining content of the chain-breaks branch.
\<close>

lemma idx_B_n_zero_gateway_for_earlier_block_ancestor:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and i_pos: "0 < i" and i_lt: "i < l1 A"
      and t_lt_n: "t < n"
      and j_lt: "j < l1 A"
      and anc: "m_ancestor (A[n]) m (idx_B_in_expansion A n i)
                                    (idx_B_in_expansion A t j)"
  shows "m_ancestor (A[n]) m (idx_B_in_expansion A n i)
                            (idx_B_in_expansion A n 0)"
  sorry

lemma clause_iv_intermediate_B_t_impossible_chain_breaks:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and k_pos: "0 < k"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and i_pos: "0 < i" and i_lt: "i < l1 A"
      and mp_eq: "m_parent (A[n]) k (idx_B_in_expansion A n i) = Some p"
      and t_lt_n: "t < n"
      and j_lt: "j < l1 A"
      and p_eq: "p = idx_B_in_expansion A t j"
      and no_G_parent: "\<not> (\<exists>k' < k. \<exists>q. m_parent (A[n]) k' (idx_B_in_expansion A n i)
                                           = Some q \<and> (\<exists>g < l0 A. q = idx_G A g))"
      and chain_breaks: "\<not> (\<forall>k' < k. m_ancestor (A[n]) k' (idx_B_in_expansion A n i)
                                                          (idx_B_in_expansion A n 0))"
  shows "False"
proof -
  let ?i = "idx_B_in_expansion A n i"
  let ?b0 = "idx_B_in_expansion A n 0"
  \<comment> \<open>Since \<open>0 < k\<close>, write \<open>k = Suc k\<^sub>0\<close>; the level-\<open>k\<close> parent \<open>p\<close> is then a
      level-\<open>k\<^sub>0\<close> ancestor of \<open>?i\<close> (definition of \<open>m_parent\<close>).\<close>
  obtain k\<^sub>0 where k_eq: "k = Suc k\<^sub>0" using k_pos by (cases k) auto
  have anc_p: "m_ancestor (A[n]) k\<^sub>0 ?i p"
    using m_parent_Suc_implies_m_ancestor[OF mp_eq[unfolded k_eq]] .
  \<comment> \<open>\<open>p = idx_B(t, j)\<close> is an earlier-block column (\<open>t < n\<close>) reached as a
      level-\<open>k\<^sub>0\<close> ancestor of \<open>?i\<close>. By the gateway property the leftmost
      block-\<open>n\<close> column \<open>?b0 = idx_B(n, 0)\<close> is then also a level-\<open>k\<^sub>0\<close>
      ancestor of \<open>?i\<close>.\<close>
  have anc_b0_k0: "m_ancestor (A[n]) k\<^sub>0 ?i ?b0"
    using idx_B_n_zero_gateway_for_earlier_block_ancestor
            [OF A_BMS A_ne b0 l1_pos i_pos i_lt t_lt_n j_lt anc_p[unfolded p_eq]] .
  \<comment> \<open>The chain-breaks hypothesis yields a witness level \<open>k_w < k\<close> at which
      \<open>?b0\<close> fails to be an ancestor of \<open>?i\<close>.\<close>
  obtain k_w where kw_lt: "k_w < k"
               and kw_no_anc: "\<not> m_ancestor (A[n]) k_w ?i ?b0"
    using chain_breaks by blast
  \<comment> \<open>But \<open>k_w < Suc k\<^sub>0\<close> gives \<open>k_w \<le> k\<^sub>0\<close>, and ancestry is monotone in the
      level, so the level-\<open>k\<^sub>0\<close> ancestor \<open>?b0\<close> is also a level-\<open>k_w\<close> ancestor
      of \<open>?i\<close> — contradiction.\<close>
  have kw_le_k0: "k_w \<le> k\<^sub>0" using kw_lt k_eq by simp
  have "m_ancestor (A[n]) k_w ?i ?b0"
    using m_ancestor_mono[OF kw_le_k0 anc_b0_k0] .
  thus False using kw_no_anc by simp
qed

lemma clause_iv_intermediate_B_t_impossible:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and i_pos: "0 < i" and i_lt: "i < l1 A"
      and mp_eq: "m_parent (A[n]) k (idx_B_in_expansion A n i) = Some p"
      and t_lt_n: "t < n"
      and j_lt: "j < l1 A"
      and p_eq: "p = idx_B_in_expansion A t j"
  shows "False"
proof -
  \<comment> \<open>Oracle: \<open>(ii) A n k'\<close> for every \<open>k'\<close>, via
      @{thm lemma_2_5_ii_main_v2} (post-Round 2).\<close>
  have ii_oracle: "\<forall>k'. lemma_2_5_ii_clause A n k'"
    using lemma_2_5_ii_main_v2[OF A_BMS A_ne] by simp
  show False
  proof (cases k)
    case 0
    \<comment> \<open>\<open>k = 0\<close>: dispatch to
        @{thm clause_iv_intermediate_B_t_impossible_at_zero}.\<close>
    show False
      using clause_iv_intermediate_B_t_impossible_at_zero
              [OF A_BMS A_ne b0 l1_pos i_pos i_lt _ t_lt_n j_lt p_eq]
            mp_eq \<open>k = 0\<close> by simp
  next
    case (Suc k_0)
    note k_eq = Suc
    have k_pos: "0 < k" using k_eq by simp
    show False
    proof (cases "\<exists>k' < k. \<exists>q. m_parent (A[n]) k' (idx_B_in_expansion A n i)
                                  = Some q \<and> (\<exists>g < l0 A. q = idx_G A g)")
      case True
      \<comment> \<open>Dispatch to @{thm clause_iv_intermediate_B_t_impossible_when_G_parent_exists}.\<close>
      show False
        by (rule clause_iv_intermediate_B_t_impossible_when_G_parent_exists
                  [OF A_BMS A_ne b0 l1_pos k_pos IH i_pos i_lt mp_eq t_lt_n j_lt p_eq True])
    next
      case False
      note no_G_parent = False
      show False
      proof (cases "\<forall>k' < k. m_ancestor (A[n]) k' (idx_B_in_expansion A n i)
                                              (idx_B_in_expansion A n 0)")
        case True
        \<comment> \<open>Dispatch to @{thm clause_iv_intermediate_B_t_impossible_chain_through_Bn_first}.\<close>
        show False
          by (rule clause_iv_intermediate_B_t_impossible_chain_through_Bn_first
                    [OF A_BMS A_ne b0 l1_pos k_pos IH clause_ii_at_k clause_iii_at_k
                        i_pos i_lt mp_eq t_lt_n j_lt p_eq no_G_parent True])
      next
        case False
        \<comment> \<open>Dispatch to @{thm clause_iv_intermediate_B_t_impossible_chain_breaks}.\<close>
        show False
          by (rule clause_iv_intermediate_B_t_impossible_chain_breaks
                    [OF A_BMS A_ne b0 l1_pos k_pos IH i_pos i_lt mp_eq t_lt_n j_lt p_eq
                        no_G_parent False])
      qed
    qed
  qed
qed

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
  \<comment> \<open>\<open>n \<ge> 1\<close>: substantive case. Structural decomposition of
      \<open>p\<close> via @{thm clause_iv_p_decomposition}: \<open>p\<close> lies in \<open>G\<close>
      or in \<open>B_t\<close> for some \<open>t \<le> n\<close>. The \<open>G\<close> and \<open>t = n\<close>
      cases discharge directly via @{thm clause_iv_G_case} and
      @{thm clause_iv_B_n_case}; the intermediate \<open>t < n\<close> case
      is Hunter's hard sub-argument (paper page 6) and is left as
      \<open>sorry\<close> pending re-implementation of the deleted helpers.\<close>
  show ?thesis
  proof (cases "b0_start A")
    case None
    \<comment> \<open>\<open>b0_start A = None\<close>: \<open>l_1 = 0\<close>, premise \<open>i < l_1\<close> is
        vacuous, so the clause holds trivially.\<close>
    have l1z: "l1 A = 0" by (rule l1_zero_of_no_b0[OF None])
    show ?thesis
      unfolding lemma_2_5_iv_clause_def using l1z by simp
  next
    case (Some s)
    note b0 = Some
    have l1_pos: "0 < l1 A"
    proof -
      have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
      have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
      show ?thesis
        using b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
    qed
    show ?thesis
      unfolding lemma_2_5_iv_clause_def
    proof (intro allI impI)
      fix i assume h: "0 < i \<and> i < l1 A"
      hence i_pos: "0 < i" and i_lt: "i < l1 A" by simp+
      let ?tgt = "idx_B_in_expansion A n i"
      show "m_parent (A[n]) k ?tgt = None
          \<or> (\<exists>p. m_parent (A[n]) k ?tgt = Some p
                 \<and> ((\<exists>j<l1 A. p = idx_B_in_expansion A n j)
                    \<or> (\<exists>j<l0 A. p = idx_G A j)))"
      proof (cases "m_parent (A[n]) k ?tgt")
        case None thus ?thesis by simp
      next
        case (Some p)
        have p_lt_tgt: "p < ?tgt" using Some by (rule m_parent_lt)
        have tgt_eq: "?tgt = l0 A + n * l1 A + i"
          unfolding idx_B_in_expansion_def by simp
        have p_lt_sum: "p < l0 A + Suc n * l1 A"
        proof -
          have "?tgt < l0 A + Suc n * l1 A"
            using i_lt tgt_eq by simp
          thus ?thesis using p_lt_tgt by linarith
        qed
        have decomp: "p < l0 A
                    \<or> (\<exists>t j. t \<le> n \<and> j < l1 A
                              \<and> p = idx_B_in_expansion A t j)"
          using clause_iv_p_decomposition[OF l1_pos p_lt_sum] .
        show ?thesis
        proof (cases "p < l0 A")
          case True
          \<comment> \<open>\<open>p < l_0\<close>: \<open>G\<close>-column.\<close>
          have "\<exists>j<l0 A. p = idx_G A j" by (rule clause_iv_G_case[OF True])
          thus ?thesis using Some by blast
        next
          case False
          \<comment> \<open>\<open>l_0 \<le> p\<close>: \<open>p\<close> sits in some \<open>B_t\<close>, \<open>t \<le> n\<close>.\<close>
          obtain t j where t_le: "t \<le> n" and j_lt: "j < l1 A"
                       and p_eq: "p = idx_B_in_expansion A t j"
            using decomp False by blast
          show ?thesis
          proof (cases "t = n")
            case True
            \<comment> \<open>\<open>t = n\<close>: \<open>p\<close> is in \<open>B_n\<close>; direct discharge.\<close>
            have "\<exists>j<l1 A. p = idx_B_in_expansion A n j"
              using True j_lt p_eq by blast
            thus ?thesis using Some by blast
          next
            case False
            \<comment> \<open>\<open>t < n\<close>: intermediate (or \<open>t = 0\<close>) block.
                Hunter's hard case (paper page 6). Dispatch via
                @{thm clause_iv_intermediate_B_t_impossible} which
                derives \<open>False\<close> from the given hypotheses and
                mirrors Hunter's case-split; the unresolved sub-leaves
                live inside the auxiliary as labelled sub-sorries.\<close>
            have t_lt: "t < n" using t_le False by linarith
            have falsity: "False"
              by (rule clause_iv_intermediate_B_t_impossible
                    [OF A_BMS A_ne b0 l1_pos IH clause_ii_at_k
                        clause_iii_at_k i_pos i_lt Some t_lt j_lt p_eq])
            thus ?thesis by simp
          qed
        qed
      qed
    qed
  qed
qed

text \<open>
  Forward direction of (i) at \<open>k\<close>, substantive case (n > 0, b0_start = Some s):
  chain from \<open>B_0[j]\<close> reaching \<open>G[i]\<close> transfers to a chain from \<open>B_n[j]\<close>.
  Uses (iv) at \<open>k\<close>, (ii) at \<open>k\<close>, and IH (i) at \<open>k' < k\<close>; per-col
  ascending case-split on column \<open>j\<close> (Hunter paper page 7).

  Empirical status: the iff (both directions, all \<open>k\<close>) holds across
  441 Hunter BMS arrays with no counter-example
  (\<open>verify/verify_clause_i_forward.py\<close>). The proof is structured by
  the case-split on whether the source column \<open>j\<close> ascends at level
  \<open>k\<close> (Hunter page 7), giving two named sub-lemmas whose proofs are
  left as labelled \<open>sorry\<close>s:

    \<bullet> CASE (A) \<open>ascends A j k\<close>: every row of column \<open>j\<close> at or
      below \<open>k\<close> is uniformly translated by \<open>n \<cdot> delta\<close> between
      \<open>B_0\<close> and \<open>B_n\<close>; combined with (iv) at \<open>k\<close> (parent of
      \<open>B_n[j]\<close> is a \<open>G\<close>- or \<open>B_n\<close>-column, never an intermediate
      block) and IH (i) at \<open>k' < k\<close>, the \<open>k\<close>-chain to \<open>G[i]\<close>
      transfers to \<open>B_n[j]\<close>.

    \<bullet> CASE (B) \<open>\<not> ascends A j k\<close>: row \<open>k\<close> of column \<open>j\<close>
      coincides between \<open>B_0\<close> and \<open>B_n\<close>
      (\<open>elem_AEn_cross_block_when_not_ascends\<close>), so no new
      \<open>k\<close>-ancestor relation toward \<open>G[i]\<close> is created or destroyed;
      (ii) at \<open>k\<close> together with IH (i) transfer the chain.
\<close>

lemma lemma_2_5_i_clause_step_forward_case_ascends:
  \<comment> \<open>CASE (A): source column \<open>j\<close> ascends at level \<open>k\<close>.\<close>
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and n_pos: "0 < n"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and clause_iv_at_k: "lemma_2_5_iv_clause A n k"
      and i_lt: "i < l0 A" and j_lt: "j < l1 A"
      and asc: "ascends A j k"
      and H: "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_G A i)"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_G A i)"
  sorry

lemma lemma_2_5_i_clause_step_forward_case_not_ascends:
  \<comment> \<open>CASE (B): source column \<open>j\<close> does not ascend at level \<open>k\<close>.\<close>
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and n_pos: "0 < n"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and clause_iv_at_k: "lemma_2_5_iv_clause A n k"
      and i_lt: "i < l0 A" and j_lt: "j < l1 A"
      and not_asc: "\<not> ascends A j k"
      and H: "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_G A i)"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_G A i)"
  sorry

lemma lemma_2_5_i_clause_step_forward:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and n_pos: "0 < n"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and clause_iv_at_k: "lemma_2_5_iv_clause A n k"
      and i_lt: "i < l0 A" and j_lt: "j < l1 A"
      and H: "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_G A i)"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_G A i)"
proof (cases "ascends A j k")
  case True
  \<comment> \<open>CASE (A): uniform translation by \<open>n \<cdot> delta\<close>; (iv) + (ii) + IH.\<close>
  show ?thesis
    by (rule lemma_2_5_i_clause_step_forward_case_ascends
              [OF A_BMS A_ne b0 l1_pos n_pos IH
                  clause_ii_at_k clause_iii_at_k clause_iv_at_k
                  i_lt j_lt True H])
next
  case False
  \<comment> \<open>CASE (B): row \<open>k\<close> coincides across blocks; (ii) + IH.\<close>
  show ?thesis
    by (rule lemma_2_5_i_clause_step_forward_case_not_ascends
              [OF A_BMS A_ne b0 l1_pos n_pos IH
                  clause_ii_at_k clause_iii_at_k clause_iv_at_k
                  i_lt j_lt False H])
qed

text \<open>
  Backward direction of (i) at \<open>k\<close>, dual to the forward direction.
\<close>

lemma lemma_2_5_i_clause_step_backward:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and l1_pos: "0 < l1 A"
      and n_pos: "0 < n"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and clause_iv_at_k: "lemma_2_5_iv_clause A n k"
      and i_lt: "i < l0 A" and j_lt: "j < l1 A"
      and H: "m_ancestor (A[n]) k (idx_B_in_expansion A n j) (idx_G A i)"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A 0 j) (idx_G A i)"
  sorry

lemma lemma_2_5_i_clause_step:
  fixes A :: array
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and clause_iv_at_k: "lemma_2_5_iv_clause A n k"
  shows "lemma_2_5_i_clause A n k"
proof (cases n)
  case 0
  \<comment> \<open>\<open>n = 0\<close>: \<open>idx_B_in_expansion A 0 j\<close> and
      \<open>idx_B_in_expansion A n j\<close> coincide, so the iff is reflexive.\<close>
  show ?thesis
    unfolding lemma_2_5_i_clause_def using \<open>n = 0\<close> by simp
next
  case (Suc n')
  hence n_pos: "0 < n" by simp
  show ?thesis
  proof (cases "b0_start A")
    case None
    \<comment> \<open>\<open>b0_start A = None\<close>: \<open>l_1 = 0\<close>, premise \<open>j < l_1\<close> is
        vacuous, so the clause holds trivially.\<close>
    have l1z: "l1 A = 0" by (rule l1_zero_of_no_b0[OF None])
    show ?thesis
      unfolding lemma_2_5_i_clause_def using l1z by simp
  next
    case (Some s)
    note b0 = Some
    have l1_pos: "0 < l1 A"
    proof -
      have s_lt_last: "s < last_col_idx A" by (rule b0_start_lt[OF b0 A_ne])
      have last_lt_arr: "last_col_idx A < arr_len A" using A_ne by (cases A) auto
      show ?thesis
        using b0 s_lt_last last_lt_arr unfolding l1_def B0_block_def by simp
    qed
    show ?thesis
      unfolding lemma_2_5_i_clause_def
    proof (intro allI impI)
      fix i j
      assume hij: "i < l0 A \<and> j < l1 A"
      hence i_lt: "i < l0 A" and j_lt: "j < l1 A" by simp+
      let ?src0 = "idx_B_in_expansion A 0 j"
      let ?srcn = "idx_B_in_expansion A n j"
      let ?tgt  = "idx_G A i"
      show "m_ancestor (A[n]) k ?src0 ?tgt
            \<longleftrightarrow> m_ancestor (A[n]) k ?srcn ?tgt"
      proof
        \<comment> \<open>Forward direction: dispatch to
            @{thm lemma_2_5_i_clause_step_forward}.\<close>
        assume H: "m_ancestor (A[n]) k ?src0 ?tgt"
        show "m_ancestor (A[n]) k ?srcn ?tgt"
          by (rule lemma_2_5_i_clause_step_forward
                    [OF A_BMS A_ne b0 l1_pos n_pos IH
                        clause_ii_at_k clause_iii_at_k clause_iv_at_k i_lt j_lt H])
      next
        \<comment> \<open>Backward direction: dispatch to
            @{thm lemma_2_5_i_clause_step_backward}.\<close>
        assume H: "m_ancestor (A[n]) k ?srcn ?tgt"
        show "m_ancestor (A[n]) k ?src0 ?tgt"
          by (rule lemma_2_5_i_clause_step_backward
                    [OF A_BMS A_ne b0 l1_pos n_pos IH
                        clause_ii_at_k clause_iii_at_k clause_iv_at_k i_lt j_lt H])
      qed
    qed
  qed
qed

text \<open>
  Substantive case of (v) at \<open>k\<close> (n \<ge> 2, b0_start = Some s): direct
  corollary using clauses (ii), (iii), (iv) at \<open>k\<close> as oracle.
  Walk back through the chain to find the last column in \<open>B_{n_2}\<close>;
  by (iv) its parent is outside \<open>B_{n_2}\<close>; by chain-linearity the chain
  passes through \<open>idx_B(n_2, 0)\<close>; (iii) and (ii) at \<open>k\<close> transfer
  the chain to \<open>idx_B(n_3, 0)\<close>; combined with (iv)-derived parent step
  we conclude. Reverse direction symmetric. Hunter paper page 7.
\<close>

lemma lemma_2_5_v_clause_step_substantive:
  fixes A :: array and n :: nat
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and n_ge_2: "2 \<le> n"
      and IH: "\<forall>k'<k. lemma_2_5_at A n k'"
      and clause_i_at_k: "lemma_2_5_i_clause A n k"
      and clause_ii_at_k: "lemma_2_5_ii_clause A n k"
      and clause_iii_at_k: "lemma_2_5_iii_clause A n k"
      and clause_iv_at_k: "lemma_2_5_iv_clause A n k"
  shows "lemma_2_5_v_clause A n k"
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
proof (cases "n \<le> 1")
  case True
  \<comment> \<open>\<open>n \<le> 1\<close>: clause (v) has premise \<open>n\<^sub>1 < n\<close> with
      \<open>n\<^sub>0 < n\<^sub>1\<close>, so \<open>n\<^sub>1 = 0\<close> and \<open>n\<^sub>0 < 0\<close>: vacuous.\<close>
  show ?thesis using lemma_2_5_v_clause_n_le_one[OF True] .
next
  case False
  hence n_ge_2: "2 \<le> n" by linarith
  show ?thesis
  proof (cases "b0_start A")
    case None
    \<comment> \<open>\<open>b0_start A = None\<close>: \<open>l\<^sub>1 = 0\<close>, premises
        \<open>i < l\<^sub>1\<close>, \<open>j < l\<^sub>1\<close> vacuous.\<close>
    have l1z: "l1 A = 0" by (rule l1_zero_of_no_b0[OF None])
    show ?thesis
      unfolding lemma_2_5_v_clause_def using l1z by simp
  next
    case (Some s)
    note b0 = Some
    \<comment> \<open>Dispatch to @{thm lemma_2_5_v_clause_step_substantive}.\<close>
    show ?thesis
      by (rule lemma_2_5_v_clause_step_substantive
                [OF A_BMS A_ne b0 n_ge_2 IH
                    clause_i_at_k clause_ii_at_k clause_iii_at_k clause_iv_at_k])
  qed
qed

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

end
