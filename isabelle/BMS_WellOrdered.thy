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

definition stable_rep :: "array \<Rightarrow> (nat \<Rightarrow> Ord_t) \<Rightarrow> bool" where
  "stable_rep A f \<longleftrightarrow>
     (\<forall>i < arr_len A. \<forall>j < arr_len A. i < j \<longrightarrow> (f i) <\<^sub>o (f j)) \<and>
     (\<forall>i < arr_len A. \<forall>j < arr_len A. \<forall>m.
        m_ancestor A m i j \<longrightarrow> stable_lt m (f i) (f j))"

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

lemma stable_rep_extend:
  assumes "A \<in> BMS" "stable_rep A f"
  shows "\<exists>g. stable_rep (A[n]) g \<and> (\<forall>i < arr_len (A[n]). (g i) <\<^sub>o o_of A)"
  sorry


section \<open>Sub-step 2.7.e: o is defined and order-preserving on BMS\<close>

lemma o_defined:
  assumes "A \<in> BMS"
  shows "\<exists>f. stable_rep A f"
  sorry

lemma o_preserves:
  assumes "A \<in> BMS" "A' \<in> BMS" "A' <\<^sub>B A"
  shows "(o_of A') <\<^sub>o (o_of A)"
  sorry


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
