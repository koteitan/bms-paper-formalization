(*
  BMS_WellOrdered.thy

  Theorem 2.7 of
    Rachel Hunter, "Well-Orderedness of the Bashicu Matrix System"
    (arXiv:2307.04606v3, 2024).

  Theorem 2.7 (BMS is well-ordered).

  Proof sketch (paper, p.9):
    We will define a function o : BMS -> Ord in the following way.
    Consider an array A with length n. A *stable representation* of A
    is a function f : n -> Ord such that for all i, j < n,
        i < j  =>  f(i) < f(j),
    and for all m, if the i-th column of A is an m-ancestor of the
    j-th column of A, then f(i) <_m f(j).
    Let o(A) be the minimal alpha in Ord such that for some stable
    representation f of A, all outputs of f are smaller than alpha.

    This proof is similar to the proof of Lemma 2.3 -- we prove by
    induction on the number of expansions needed to reach an array,
    that o is defined and order-preserving on all of BMS, by starting
    from X_0 ... [induction step uses Lemma 2.6 to construct f_{n+1}
    from f_n; Lemma 2.5 ensures the constructed map is a stable
    representation].

    Then if BMS was not well-ordered, there would be an infinite
    descending sequence in BMS, which would get mapped to an infinite
    descending sequence of ordinals by o, and that cannot exist by the
    definition of ordinals. Therefore BMS is well-ordered.

  Sub-steps:
    2.7.a  Define o(A).
    2.7.b  o defined and order-preserving on the seed set
           X_0 = {seed n | n}.
    2.7.c  Inductive step: build f_{n+1} from f_n via Lemma 2.6.
    2.7.d  f_{n+1} is a stable representation (uses Lemma 2.5).
    2.7.e  Closure under expansion => o defined on all of BMS.
    2.7.f  Order-preserving o : BMS -> Ord => no infinite descent
           => BMS well-ordered.
*)

theory BMS_WellOrdered
  imports BMS_Stability
begin

section \<open>Stable representations\<close>

text \<open>
  Per Hunter (paper p.~9): if the \<open>i\<close>-th column is an
  \<open>m\<close>-ancestor of the \<open>j\<close>-th column (paper convention:
  \<open>i\<close> earlier, \<open>j\<close> later), then \<open>f(i) <\<^sub>m f(j)\<close>.
  Translating to our index convention (\<open>m_ancestor A m later earlier\<close>
  so that \<open>m_ancestor A m i j\<close> ⟹ \<open>j < i\<close>): the variable \<open>j\<close>
  here is the earlier (ancestor), \<open>i\<close> the later (descendant), and
  the requirement is \<open>stable_lt m (f j) (f i)\<close>, i.e.\ the
  ancestor's image is stable-below the descendant's image.
\<close>

definition stable_rep :: "array \<Rightarrow> (nat \<Rightarrow> Ord_t) \<Rightarrow> bool" where
  "stable_rep A f \<longleftrightarrow>
     (\<forall>i < arr_len A. \<forall>j < arr_len A. i < j \<longrightarrow> (f i) <\<^sub>o (f j)) \<and>
     (\<forall>i < arr_len A. \<forall>j < arr_len A. \<forall>m.
        m_ancestor A m i j \<longrightarrow> stable_lt m (f j) (f i))"

text \<open>
  Strict-mono projection from @{const stable_rep}.
  Helper purpose: small projection useful when reasoning about
  \<open>f i <\<^sub>o f j\<close> in any of the 3 sorry sub-cases.
\<close>

lemma stable_rep_imp_strict_mono:
  assumes "stable_rep A f"
      and "i < arr_len A" and "j < arr_len A" and "i < j"
  shows "f i <\<^sub>o f j"
  using assms unfolding stable_rep_def by blast

text \<open>
  Restriction principle: if \<open>B\<close> has length \<open>\<le>\<close> \<open>A\<close>'s and
  m-ancestry in \<open>B\<close> on indices \<open>< arr_len B\<close> implies
  m-ancestry in \<open>A\<close> (same indices, same level), then a stable
  representation of \<open>A\<close> restricts to one of \<open>B\<close>.
\<close>

lemma stable_rep_restrict:
  assumes "stable_rep A f"
          "arr_len B \<le> arr_len A"
          "\<forall>i j m. i < arr_len B \<and> j < arr_len B \<and> m_ancestor B m i j
                     \<longrightarrow> m_ancestor A m i j"
  shows "stable_rep B f"
proof -
  have mono: "\<forall>i < arr_len B. \<forall>j < arr_len B. i < j \<longrightarrow> f i <\<^sub>o f j"
  proof (intro allI impI)
    fix i j assume i_lt: "i < arr_len B" and j_lt: "j < arr_len B" and ij: "i < j"
    have iA: "i < arr_len A" using i_lt assms(2) by linarith
    have jA: "j < arr_len A" using j_lt assms(2) by linarith
    show "f i <\<^sub>o f j" using assms(1) iA jA ij
      unfolding stable_rep_def by blast
  qed
  have anc: "\<forall>i < arr_len B. \<forall>j < arr_len B. \<forall>m.
                m_ancestor B m i j \<longrightarrow> stable_lt m (f j) (f i)"
  proof (intro allI impI)
    fix i j m assume i_lt: "i < arr_len B" and j_lt: "j < arr_len B"
                and anc_B: "m_ancestor B m i j"
    have iA: "i < arr_len A" using i_lt assms(2) by linarith
    have jA: "j < arr_len A" using j_lt assms(2) by linarith
    have anc_A: "m_ancestor A m i j" using assms(3) i_lt j_lt anc_B by blast
    show "stable_lt m (f j) (f i)" using assms(1) iA jA anc_A
      unfolding stable_rep_def by blast
  qed
  show ?thesis using mono anc unfolding stable_rep_def by blast
qed

(*
  o_of axiomatized as the minimal alpha in Ord_t such that some stable
  representation of A maps below alpha. We do not use HOL's `LEAST`
  since Ord_t is not an instance of the `ord` type class; instead we
  postulate o_of and the relevant defining axiom.
*)

axiomatization
  o_of :: "array \<Rightarrow> Ord_t"
where
  o_of_def:
    \<comment> \<open>For \<open>A \<in> BMS\<close>, \<open>o_of A\<close> is the least \<open>\<beta>\<close>
        bounding some stable representation of \<open>A\<close>. Outside BMS
        the value of \<open>o_of A\<close> is unspecified; we never reason
        about it. Restricting the axiom is a soundness improvement:
        arrays with inconsistent \<open>m_ancestor\<close> structure may admit
        no stable representation, in which case the unconditional
        existence claim would be false.\<close>
    "A \<in> BMS \<Longrightarrow>
     \<exists>f. stable_rep A f \<and> (\<forall>i < arr_len A. (f i) <\<^sub>o o_of A) \<and>
         (\<forall>\<beta>. (\<exists>g. stable_rep A g \<and> (\<forall>i < arr_len A. (g i) <\<^sub>o \<beta>))
                \<longrightarrow> (o_of A = \<beta> \<or> o_of A <\<^sub>o \<beta>))"


section \<open>Sub-step 2.7.b: o on the seed set\<close>

text \<open>
  For \<open>seed n\<close>, the only non-vacuous \<open>m_ancestor\<close> entry in
  \<open>stable_rep\<close>'s second clause is \<open>m_ancestor (seed n) m 1 0\<close>
  for \<open>m < n\<close> (proven by @{thm m_parent_seed_succ} for the
  positive case and @{thm m_ancestor_seed_top} for \<open>m \<ge> n\<close>).
  Hence we only need an \<open>\<alpha> <\<^sub>o \<beta>\<close> with \<open>stable_lt m \<alpha> \<beta>\<close>
  for all \<open>m < n\<close>; this follows from the universal-stability
  axiom @{thm sigma_pair_exists}.
\<close>

lemma m_ancestor_seed_only_1_0:
  assumes "i < 2" "j < 2" "m_ancestor (seed n) m i j"
  shows "i = 1 \<and> j = 0 \<and> m < n"
proof -
  have "i \<noteq> 0"
  proof
    assume "i = 0"
    have "m_parent (seed n) m 0 = None"
      by (cases m) (simp_all add: Let_def)
    hence "\<not> m_ancestor (seed n) m 0 j" by simp
    thus False using assms(3) \<open>i = 0\<close> by simp
  qed
  hence i_eq: "i = 1" using assms(1) by auto
  have "j \<noteq> 1"
  proof
    assume "j = 1"
    have anc_0_1_false: "\<not> m_ancestor (seed n) m 0 1"
    proof -
      have "m_parent (seed n) m 0 = None"
        by (cases m) (simp_all add: Let_def)
      thus ?thesis by simp
    qed
    have not_anc_1_1: "\<not> m_ancestor (seed n) m 1 1"
    proof (cases "m_parent (seed n) m 1")
      case None
      thus ?thesis by simp
    next
      case (Some p)
      \<comment> \<open>From either \<open>m < n\<close> branch (\<open>p = 0\<close>) or
          \<open>m \<ge> n\<close> (which gives None, contradicting Some), we have
          \<open>p = 0\<close>.\<close>
      have "p = 0"
      proof (cases "m < n")
        case True
        hence "m_parent (seed n) m 1 = Some 0"
          using m_parent_seed_succ by blast
        thus ?thesis using Some by simp
      next
        case False
        hence "n \<le> m" by simp
        hence "m_parent (seed n) m 1 = None" by (rule m_parent_seed_top)
        thus ?thesis using Some by simp
      qed
      hence "m_ancestor (seed n) m 1 1
              \<longleftrightarrow> (p = 1 \<or> m_ancestor (seed n) m p 1)"
        using Some by simp
      thus ?thesis using \<open>p = 0\<close> anc_0_1_false by simp
    qed
    thus False using assms(3) i_eq \<open>j = 1\<close> by simp
  qed
  hence j_eq: "j = 0" using assms(2) by auto
  have "m < n"
  proof (rule ccontr)
    assume "\<not> m < n"
    hence "n \<le> m" by simp
    hence "\<not> m_ancestor (seed n) m 1 0" by (rule m_ancestor_seed_top)
    thus False using assms(3) i_eq j_eq by simp
  qed
  thus ?thesis using i_eq j_eq by simp
qed

lemma o_on_seed:
  shows "\<exists>f. stable_rep (seed n) f"
proof -
  obtain \<alpha> \<beta> where
        \<alpha>_in: "\<alpha> \<in> sigma_bound" and \<beta>_in: "\<beta> \<in> sigma_bound"
    and \<omega>_lt: "\<omega>_o <\<^sub>o \<alpha>"
    and lt: "\<alpha> <\<^sub>o \<beta>"
    and stab_all: "\<forall>m. stable_lt m \<alpha> \<beta>"
    using sigma_pair_exists by blast
  have stab: "\<forall>m < n. stable_lt m \<alpha> \<beta>" using stab_all by simp
  let ?f = "\<lambda>i. if i = 0 then \<alpha> else \<beta>"
  have arr_len_2: "arr_len (seed n) = 2" by (rule length_seed)
  have ord_part: "\<forall>i < arr_len (seed n). \<forall>j < arr_len (seed n).
                    i < j \<longrightarrow> ?f i <\<^sub>o ?f j"
    using lt arr_len_2 by auto
  have stable_part: "\<forall>i < arr_len (seed n). \<forall>j < arr_len (seed n). \<forall>m.
                       m_ancestor (seed n) m i j \<longrightarrow> stable_lt m (?f j) (?f i)"
  proof (intro allI impI)
    fix i j m
    assume i_lt: "i < arr_len (seed n)" and j_lt: "j < arr_len (seed n)"
       and anc: "m_ancestor (seed n) m i j"
    have i2: "i < 2" using i_lt arr_len_2 by simp
    have j2: "j < 2" using j_lt arr_len_2 by simp
    have "i = 1 \<and> j = 0 \<and> m < n"
      by (rule m_ancestor_seed_only_1_0[OF i2 j2 anc])
    hence "i = 1" "j = 0" "m < n" by auto
    thus "stable_lt m (?f j) (?f i)" using stab by simp
  qed
  have "stable_rep (seed n) ?f"
    unfolding stable_rep_def using ord_part stable_part by blast
  thus ?thesis by blast
qed


section \<open>Sub-step 2.7.c--d: induction step for the expansion\<close>

text \<open>
  Strict variant of \<open>stable_rep_extend\<close> (defined below):
  the new stable rep fits below some \<open>\<beta> <\<^sub>o o_of A\<close>,
  not merely below \<open>o_of A\<close> itself. Hunter's actual
  construction via Lemma 2.6 supplies such a \<open>\<beta>\<close> as the
  supremum of the bumped \<open>f\<close>-values plus the reflection bound
  from Lemma 2.6. The non-strict \<open>stable_rep_extend\<close> is then
  an immediate consequence.
\<close>

text \<open>
  Combined ancestry preservation: m-ancestry inside \<open>A[0]\<close> on
  indices below \<open>arr_len A - 1\<close> lifts to m-ancestry in \<open>A\<close>.
  Combines @{thm m_ancestor_strip_subsume} (proven) with
  @{thm m_ancestor_butlast_iff} (proven) via the structural
  identity \<open>A[0] = strip_zero_rows (butlast A)\<close>.
\<close>

lemma m_ancestor_A0_subsume_A:
  assumes "is_array A" "A \<noteq> []"
          "i < arr_len (expansion A 0)" "j < arr_len (expansion A 0)"
          "m_ancestor (expansion A 0) m i j"
  shows "m_ancestor A m i j"
proof -
  have A0_eq: "expansion A 0 = strip_zero_rows (butlast A)"
    by (rule expansion_zero_eq[OF assms(2)])
  have len_A0: "arr_len (expansion A 0) = arr_len (butlast A)"
    using A0_eq by (simp add: length_strip_zero_rows)
  have i_lt_bl: "i < arr_len (butlast A)" using assms(3) len_A0 by simp
  have j_lt_bl: "j < arr_len (butlast A)" using assms(4) len_A0 by simp
  show ?thesis
  proof (cases "butlast A = []")
    case True
    hence "arr_len (butlast A) = 0" by simp
    hence "i < 0" using i_lt_bl by simp
    thus ?thesis by simp
  next
    case False
    have is_arr_bl: "is_array (butlast A)"
      using assms(1) by (rule is_array_butlast)
    have anc_bl: "m_ancestor (butlast A) m i j"
      using m_ancestor_strip_subsume[OF is_arr_bl False i_lt_bl j_lt_bl]
            assms(5) A0_eq by simp
    have i_lt_A: "i < arr_len A - 1" using i_lt_bl by simp
    have j_lt_A: "j < arr_len A - 1" using j_lt_bl by simp
    show ?thesis
      using m_ancestor_butlast_iff[OF i_lt_A j_lt_A] anc_bl by simp
  qed
qed

text \<open>
  Base case of Hunter's 2.7.c--d recursion (\<open>n = 0\<close>). The
  restriction of \<open>f\<close> to indices below \<open>arr_len (A[0])\<close> is
  a stable representation of \<open>A[0]\<close>, bounded below
  \<open>f (arr_len A - 1)\<close>.
\<close>

lemma stable_rep_extend_strict_zero:
  assumes "A \<in> BMS" "A \<noteq> []" "stable_rep A f"
  shows "\<exists>g \<beta>. \<beta> <\<^sub>o o_of A
                \<and> stable_rep (expansion A 0) g
                \<and> (\<forall>i < arr_len (expansion A 0). g i <\<^sub>o \<beta>)"
proof -
  have is_arr: "is_array A" using BMS_is_array[OF assms(1)] .
  have len_A0: "arr_len (expansion A 0) = arr_len A - 1"
    by (simp add: expansion_zero_eq[OF assms(2)] length_strip_zero_rows)
  have A_len_pos: "0 < arr_len A" using assms(2) by simp
  have last_lt: "arr_len A - 1 < arr_len A" using A_len_pos by simp
  obtain f0 where f0_rep: "stable_rep A f0"
              and f0_lt: "\<forall>i < arr_len A. f0 i <\<^sub>o o_of A"
    using o_of_def[OF assms(1)] by blast
  have f0_strict: "\<forall>i j. i < arr_len A \<and> j < arr_len A \<and> i < j \<longrightarrow> f0 i <\<^sub>o f0 j"
    using f0_rep unfolding stable_rep_def by blast
  define \<beta> where "\<beta> = f0 (arr_len A - 1)"
  have \<beta>_lt: "\<beta> <\<^sub>o o_of A"
    using f0_lt last_lt \<beta>_def by blast
  have f0_lt_\<beta>: "\<forall>i. i < arr_len (expansion A 0) \<longrightarrow> f0 i <\<^sub>o \<beta>"
  proof (intro allI impI)
    fix i assume "i < arr_len (expansion A 0)"
    hence i_lt_A1: "i < arr_len A - 1" using len_A0 by simp
    hence i_lt_A: "i < arr_len A" using last_lt by linarith
    show "f0 i <\<^sub>o \<beta>"
      using f0_strict i_lt_A last_lt i_lt_A1 \<beta>_def by blast
  qed
  have g_stable: "stable_rep (expansion A 0) f0"
  proof (rule stable_rep_restrict[OF f0_rep])
    show "arr_len (expansion A 0) \<le> arr_len A" using len_A0 by simp
  next
    show "\<forall>i j m. i < arr_len (expansion A 0) \<and> j < arr_len (expansion A 0)
                    \<and> m_ancestor (expansion A 0) m i j
                    \<longrightarrow> m_ancestor A m i j"
      using m_ancestor_A0_subsume_A[OF is_arr assms(2)] by blast
  qed
  show ?thesis using \<beta>_lt g_stable f0_lt_\<beta> by blast
qed

text \<open>
  General \<open>n\<close>: Hunter's 2.7.c--d via Lemma 2.6 and Lemma 2.5.
  The \<open>n = 0\<close> case is dispatched to @{thm stable_rep_extend_strict_zero};
  the \<open>n > 0\<close> case remains as a single sorry (Hunter's reflection
  step via Lemma 2.6).
\<close>

text \<open>
  Minimality of \<open>o_of\<close> applied to an expansion: extracted from
  @{thm o_of_def} via @{thm expand_in_BMS}.
\<close>

lemma o_of_expansion_minimal:
  assumes A_BMS: "A \<in> BMS"
  shows "(\<exists>g. stable_rep (expansion A n) g
              \<and> (\<forall>i < arr_len (expansion A n). g i <\<^sub>o \<beta>))
       \<longrightarrow> o_of (expansion A n) = \<beta> \<or> o_of (expansion A n) <\<^sub>o \<beta>"
proof -
  have An_BMS: "expansion A n \<in> BMS" using A_BMS by (rule expand_in_BMS)
  from o_of_def[OF An_BMS] obtain f where
    "stable_rep (expansion A n) f"
    "\<forall>i < arr_len (expansion A n). f i <\<^sub>o o_of (expansion A n)"
    "\<forall>\<beta>. (\<exists>g. stable_rep (expansion A n) g
                \<and> (\<forall>i < arr_len (expansion A n). g i <\<^sub>o \<beta>))
          \<longrightarrow> o_of (expansion A n) = \<beta> \<or> o_of (expansion A n) <\<^sub>o \<beta>"
    by blast
  thus ?thesis by blast
qed

lemma stable_rep_extend_strict:
  assumes A_BMS: "A \<in> BMS" and A_ne: "A \<noteq> []" and f_rep: "stable_rep A f"
  shows "\<exists>g \<beta>. \<beta> <\<^sub>o o_of A
                \<and> stable_rep (A[n]) g
                \<and> (\<forall>i < arr_len (A[n]). g i <\<^sub>o \<beta>)"
proof (induct n)
  case 0
  show ?case using stable_rep_extend_strict_zero[OF assms] by simp
next
  case (Suc n')
  from Suc.hyps obtain g_n \<beta>_n where
        \<beta>_n_lt:  "\<beta>_n <\<^sub>o o_of A"
    and g_n_rep: "stable_rep (A[n']) g_n"
    and g_n_lt:  "\<forall>i < arr_len (A[n']). g_n i <\<^sub>o \<beta>_n"
    by blast
  show ?case
  proof (cases "b0_start A")
    case None
    \<comment> \<open>\<open>b0_start A = None\<close>: all \<open>B_i\<close> blocks are empty so
        \<open>A[Suc n'] = A[n'] = A[0]\<close>; reuse \<open>g_n\<close>, \<open>\<beta>_n\<close>.\<close>
    have eq1: "expansion A (Suc n') = expansion A 0"
      using expansion_no_b0_eq_zero[OF A_ne None, of "Suc n'"] .
    have eq2: "expansion A n' = expansion A 0"
      using expansion_no_b0_eq_zero[OF A_ne None, of n'] .
    have eq: "expansion A (Suc n') = expansion A n'"
      using eq1 eq2 by simp
    show ?thesis
      using \<beta>_n_lt g_n_rep g_n_lt eq by metis
  next
    case (Some s)
    \<comment> \<open>Hunter's 2.7.c--d via Lemma 2.6 + Lemma 2.5.\<close>
    show ?thesis sorry
  qed
qed

lemma stable_rep_extend:
  assumes "A \<in> BMS" "stable_rep A f"
  shows "\<exists>g. stable_rep (A[n]) g \<and> (\<forall>i < arr_len (A[n]). (g i) <\<^sub>o o_of A)"
proof (cases "A = []")
  case True
  hence "A[n] = []" by (simp add: expansion_def)
  hence "arr_len (A[n]) = 0" by simp
  have "stable_rep (A[n]) (\<lambda>_. undefined)"
    unfolding stable_rep_def using \<open>arr_len (A[n]) = 0\<close> by simp
  thus ?thesis using \<open>arr_len (A[n]) = 0\<close> by auto
next
  case False
  obtain g \<beta> where bnd: "\<beta> <\<^sub>o o_of A"
                     and g_rep: "stable_rep (A[n]) g"
                     and g_lt: "\<forall>i < arr_len (A[n]). g i <\<^sub>o \<beta>"
    using stable_rep_extend_strict[OF assms(1) False assms(2)] by blast
  have "\<forall>i < arr_len (A[n]). g i <\<^sub>o o_of A"
    using g_lt bnd ord_lt_trans by blast
  thus ?thesis using g_rep by blast
qed


section \<open>Sub-step 2.7.e: o is defined and order-preserving on BMS\<close>

lemma o_defined:
  assumes "A \<in> BMS"
  shows "\<exists>f. stable_rep A f"
  using assms
proof (induct rule: BMS.induct)
  case (seed_in_BMS n)
  show ?case by (rule o_on_seed)
next
  case (expand_in_BMS A k)
  obtain f where f_rep: "stable_rep A f" using expand_in_BMS.hyps(2) by blast
  obtain g where "stable_rep (A[k]) g
                   \<and> (\<forall>i < arr_len (A[k]). g i <\<^sub>o o_of A)"
    using stable_rep_extend[OF expand_in_BMS.hyps(1) f_rep] by blast
  thus ?case by blast
qed

text \<open>
  Non-strict variant: chained \<open>\<le>\<^sub>B\<close> implies \<open>=/<\<^sub>o\<close>.
  Proof by induction on \<open>A' \<le>\<^sub>B A\<close> using @{thm stable_rep_extend}
  at each expansion step (giving stable rep of \<open>A[n]\<close> with all values
  strictly below \<open>o_of A\<close>; minimality of @{const o_of} gives
  \<open>o_of (A[n]) = o_of A \<or> o_of (A[n]) <\<^sub>o o_of A\<close>).
  Each step's combination is via either equality substitution or
  @{thm ord_lt_trans}.
\<close>

lemma o_le_via_bms_le:
  assumes "A \<in> BMS" "A' \<le>\<^sub>B A"
  shows "o_of A' = o_of A \<or> o_of A' <\<^sub>o o_of A"
  using assms(2,1)
proof (induct rule: bms_le.induct)
  case bms_le_refl
  thus ?case by simp
next
  case (bms_le_step A' A n)
  have A_BMS: "A \<in> BMS" using bms_le_step.prems .
  have An_BMS: "A[n] \<in> BMS" using A_BMS by (rule expand_in_BMS)
  have IH_eq: "o_of A' = o_of (A[n]) \<or> o_of A' <\<^sub>o o_of (A[n])"
    using bms_le_step.hyps(2)[OF An_BMS] .
  obtain f where f_rep: "stable_rep A f"
    using o_defined[OF A_BMS] by blast
  obtain g where g_rep: "stable_rep (A[n]) g"
                  and g_lt: "\<forall>i < arr_len (A[n]). g i <\<^sub>o o_of A"
    using stable_rep_extend[OF A_BMS f_rep] by blast
  have An_le_A: "o_of (A[n]) = o_of A \<or> o_of (A[n]) <\<^sub>o o_of A"
  proof -
    have witness: "\<exists>g'. stable_rep (A[n]) g'
                       \<and> (\<forall>i < arr_len (A[n]). g' i <\<^sub>o o_of A)"
      using g_rep g_lt by blast
    obtain f' where mini:
      "\<forall>\<beta>. (\<exists>g'. stable_rep (A[n]) g'
                  \<and> (\<forall>i < arr_len (A[n]). g' i <\<^sub>o \<beta>))
            \<longrightarrow> o_of (A[n]) = \<beta> \<or> o_of (A[n]) <\<^sub>o \<beta>"
      using o_of_def[OF An_BMS] by blast
    show ?thesis using mini[rule_format, OF witness] .
  qed
  show ?case
  proof -
    consider (i_eq) "o_of A' = o_of (A[n])"
           | (i_lt) "o_of A' <\<^sub>o o_of (A[n])"
      using IH_eq by blast
    thus ?thesis
    proof cases
      case i_eq
      thus ?thesis using An_le_A by simp
    next
      case i_lt
      consider (j_eq) "o_of (A[n]) = o_of A"
             | (j_lt) "o_of (A[n]) <\<^sub>o o_of A"
        using An_le_A by blast
      thus ?thesis
      proof cases
        case j_eq
        thus ?thesis using i_lt by simp
      next
        case j_lt
        thus ?thesis using i_lt ord_lt_trans by blast
      qed
    qed
  qed
qed

text \<open>
  Strict variant of @{thm o_le_via_bms_le}: each expansion step
  strictly decreases @{const o_of}, by @{thm stable_rep_extend_strict}.
  We induct on \<open>A' \<le>\<^sub>B A\<close> with the predicate \<open>A \<in> BMS \<and>
  A \<noteq> A' \<longrightarrow> o_of A' <\<^sub>o o_of A\<close>; the refl case is vacuous and
  the step case combines the IH (or equality if \<open>A[n] = A'\<close>) with
  the strict bound \<open>o_of (A[n]) <\<^sub>o o_of A\<close>.
\<close>

lemma o_preserves:
  assumes "A \<in> BMS" "A' \<in> BMS" "A' <\<^sub>B A"
  shows "(o_of A') <\<^sub>o (o_of A)"
proof -
  have le: "A' \<le>\<^sub>B A" using assms(3) unfolding bms_lt_def by simp
  have ne: "A \<noteq> A'" using assms(3) unfolding bms_lt_def by auto
  show ?thesis using le assms(1) ne
  proof (induct rule: bms_le.induct)
    case (bms_le_refl A)
    thus ?case by simp
  next
    case (bms_le_step A' A n)
    have A_BMS: "A \<in> BMS" using bms_le_step.prems(1) .
    have An_BMS: "A[n] \<in> BMS" using A_BMS by (rule expand_in_BMS)
    \<comment> \<open>The \<open>A = []\<close> branch is vacuous: \<open>A[n] = []\<close>, then
        \<open>A' \<le>\<^sub>B []\<close> forces \<open>A' = []\<close>, contradicting
        \<open>A \<noteq> A'\<close>.\<close>
    have A_ne: "A \<noteq> []"
    proof
      assume "A = []"
      hence "A[n] = []" by (simp add: expansion_def)
      with bms_le_step.hyps(1) have "A' \<le>\<^sub>B []" by simp
      hence "A' = []" by (rule bms_le_empty)
      with \<open>A = []\<close> bms_le_step.prems(2) show False by simp
    qed
    obtain f where f_rep: "stable_rep A f"
      using o_defined[OF A_BMS] by blast
    obtain g \<beta> where bnd: "\<beta> <\<^sub>o o_of A"
                     and g_rep: "stable_rep (A[n]) g"
                     and g_lt: "\<forall>i < arr_len (A[n]). g i <\<^sub>o \<beta>"
      using stable_rep_extend_strict[OF A_BMS A_ne f_rep] by blast
    have An_lt_A: "o_of (A[n]) <\<^sub>o o_of A"
    proof -
      have witness: "\<exists>g'. stable_rep (A[n]) g'
                          \<and> (\<forall>i < arr_len (A[n]). g' i <\<^sub>o \<beta>)"
        using g_rep g_lt by blast
      obtain f' where mini:
        "\<forall>b. (\<exists>g'. stable_rep (A[n]) g'
                    \<and> (\<forall>i < arr_len (A[n]). g' i <\<^sub>o b))
              \<longrightarrow> o_of (A[n]) = b \<or> o_of (A[n]) <\<^sub>o b"
        using o_of_def[OF An_BMS] by blast
      hence "o_of (A[n]) = \<beta> \<or> o_of (A[n]) <\<^sub>o \<beta>"
        using witness by blast
      thus ?thesis using bnd ord_lt_trans by metis
    qed
    show ?case
    proof (cases "A[n] = A'")
      case True
      hence "o_of A' = o_of (A[n])" by simp
      thus ?thesis using An_lt_A by simp
    next
      case False
      hence ne_An: "A[n] \<noteq> A'" by simp
      have IH: "o_of A' <\<^sub>o o_of (A[n])"
        using bms_le_step.hyps(2)[OF An_BMS ne_An] .
      thus ?thesis using An_lt_A ord_lt_trans by metis
    qed
  qed
qed


section \<open>Theorem 2.7\<close>

text \<open>
  Order-preserving image of \<open>\<le>\<^sub>B\<close> on BMS, expressed as a relation
  inclusion. Suppose the BMS-relation is not well-founded; then there
  is an infinite descending chain in BMS, which maps via @{const o_of}
  to an infinite descending chain of @{typ Ord_t}, contradicting
  @{thm ord_wf}.
\<close>

theorem theorem_2_7_BMS_well_ordered:
  shows "wfP (\<lambda>A' A. A \<in> BMS \<and> A' <\<^sub>B A)"
proof (rule wfp_if_convertible_to_wfp)
  show "wfP ((<\<^sub>o) :: Ord_t \<Rightarrow> Ord_t \<Rightarrow> bool)" by (rule ord_wf)
next
  fix A A' :: array
  assume "A \<in> BMS \<and> A' <\<^sub>B A"
  hence "A \<in> BMS" "A' <\<^sub>B A" by auto
  hence "A' \<in> BMS" using bms_le_in_BMS unfolding bms_lt_def by blast
  thus "o_of A' <\<^sub>o o_of A" using o_preserves \<open>A \<in> BMS\<close> \<open>A' <\<^sub>B A\<close> by blast
qed

end
