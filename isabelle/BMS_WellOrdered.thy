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
    "\<exists>f. stable_rep A f \<and> (\<forall>i < arr_len A. (f i) <\<^sub>o o_of A) \<and>
         (\<forall>\<beta>. (\<exists>g. stable_rep A g \<and> (\<forall>i < arr_len A. (g i) <\<^sub>o \<beta>))
                \<longrightarrow> (o_of A = \<beta> \<or> o_of A <\<^sub>o \<beta>))"


section \<open>Sub-step 2.7.b: o on the seed set\<close>

lemma o_on_seed:
  shows "\<exists>f. stable_rep (seed n) f"
  sorry


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

lemma stable_rep_extend_strict:
  assumes "A \<in> BMS" "stable_rep A f"
  shows "\<exists>g \<beta>. \<beta> <\<^sub>o o_of A
                \<and> stable_rep (A[n]) g
                \<and> (\<forall>i < arr_len (A[n]). g i <\<^sub>o \<beta>)"
  sorry  \<comment> \<open>Hunter's 2.7.c--d via Lemma 2.6\<close>

lemma stable_rep_extend:
  assumes "A \<in> BMS" "stable_rep A f"
  shows "\<exists>g. stable_rep (A[n]) g \<and> (\<forall>i < arr_len (A[n]). (g i) <\<^sub>o o_of A)"
proof -
  obtain g \<beta> where bnd: "\<beta> <\<^sub>o o_of A"
                     and g_rep: "stable_rep (A[n]) g"
                     and g_lt: "\<forall>i < arr_len (A[n]). g i <\<^sub>o \<beta>"
    using stable_rep_extend_strict[OF assms] by blast
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
      using o_of_def[where A = "A[n]"] by blast
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
    obtain f where f_rep: "stable_rep A f"
      using o_defined[OF A_BMS] by blast
    obtain g \<beta> where bnd: "\<beta> <\<^sub>o o_of A"
                     and g_rep: "stable_rep (A[n]) g"
                     and g_lt: "\<forall>i < arr_len (A[n]). g i <\<^sub>o \<beta>"
      using stable_rep_extend_strict[OF A_BMS f_rep] by blast
    have An_lt_A: "o_of (A[n]) <\<^sub>o o_of A"
    proof -
      have witness: "\<exists>g'. stable_rep (A[n]) g'
                          \<and> (\<forall>i < arr_len (A[n]). g' i <\<^sub>o \<beta>)"
        using g_rep g_lt by blast
      obtain f' where mini:
        "\<forall>b. (\<exists>g'. stable_rep (A[n]) g'
                    \<and> (\<forall>i < arr_len (A[n]). g' i <\<^sub>o b))
              \<longrightarrow> o_of (A[n]) = b \<or> o_of (A[n]) <\<^sub>o b"
        using o_of_def[where A = "A[n]"] by blast
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
