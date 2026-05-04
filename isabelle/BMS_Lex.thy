(*
  BMS_Lex.thy

  Formalization of:
    Lemma 2.1   : For all A \<in> BMS and n \<in> \<nat>, A[n] is lexicographically
                  smaller than A (with the columns also compared
                  lexicographically).
    Corollary 2.2: For all A, A' \<in> BMS, A' < A implies A' <_lex A.
    Lemma 2.3   : BMS is totally ordered.
    Corollary 2.4: The ordering of BMS coincides with the lexicographical
                  ordering with columns compared lexicographically.

  Reference: Rachel Hunter, "Well-Orderedness of the Bashicu Matrix
  System" (arXiv:2307.04606v3, 2024), \<section>2.
*)

theory BMS_Lex
  imports BMS_Defs
begin

section \<open>Sanity checks on the inductive set BMS\<close>

lemma seed_in_BMS_check: "seed n \<in> BMS"
  by (rule seed_in_BMS)

lemma expand_in_BMS_check: "A \<in> BMS \<Longrightarrow> A[n] \<in> BMS"
  by (rule expand_in_BMS)

lemma bms_le_refl_check: "A \<le>\<^sub>B A"
  by (rule bms_le_refl)


section \<open>Transitivity of \<open>\<le>\<^sub>B\<close>\<close>

lemma bms_le_trans:
  assumes "A \<le>\<^sub>B B" "B \<le>\<^sub>B C"
  shows "A \<le>\<^sub>B C"
  using assms(2,1)
proof (induct rule: bms_le.induct)
  case bms_le_refl thus ?case .
next
  case (bms_le_step A' A n)
  then show ?case using bms_le.bms_le_step by blast
qed

lemma bms_le_expand: "A[n] \<le>\<^sub>B A"
  by (rule bms_le.bms_le_step[OF bms_le.bms_le_refl])


section \<open>Lexicographic order on columns and arrays\<close>

text \<open>
  Columns are sequences of natural numbers. We compare them
  lexicographically using Isabelle's standard \<open>lexordp_eq\<close> on lists,
  specialised to \<open><\<close> on \<open>nat\<close>.
\<close>

definition col_lt :: "column \<Rightarrow> column \<Rightarrow> bool" (infix "<\<^sub>c\<^sub>l\<^sub>e\<^sub>x" 50) where
  "c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c' \<longleftrightarrow> (c, c') \<in> lex {(x, y). x < y}"

definition arr_lex :: "array \<Rightarrow> array \<Rightarrow> bool" (infix "<\<^sub>l\<^sub>e\<^sub>x" 50) where
  "A <\<^sub>l\<^sub>e\<^sub>x A' \<longleftrightarrow> (A, A') \<in> lex {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"


section \<open>Lemma 2.1\<close>

text \<open>
  Quote (paper, p.~3):
    ``For all \<open>A \<in> BMS\<close> and \<open>n \<in> \<nat>\<close>, \<open>A[n]\<close> is lexicographically
    smaller than \<open>A\<close> (with the columns also compared lexicographically).''

  Proof structure (paper):
    Using the variable names from the definition of BMS, we have
    \<open>A = G + B\<^sub>0 + (C)\<close> and \<open>A[n] = G + B\<^sub>0 + B\<^sub>1 + ... + B_n\<close>.
    Then \<open>A[n] <_lex A\<close> iff
      \<open>B\<^sub>1 + B\<^sub>2 + ... + B_n  <_lex  (C)\<close>,
    which is trivial if \<open>m\<^sub>0\<close> is undefined (the empty sequence is
    lexicographically smaller than all other sequences, including
    \<open>(C)\<close>), and otherwise equivalent to the first column in \<open>B\<^sub>1\<close>
    being lexicographically smaller than \<open>C\<close>.

    Let \<open>R_i\<close> be the first column in \<open>B_i\<close>. Since \<open>R\<^sub>0\<close> is the
    \<open>m\<^sub>0\<close>-parent of \<open>C\<close>, it is an \<open>m\<close>-ancestor of \<open>C\<close>
    for each \<open>m \<le> m\<^sub>0\<close>, thus the \<open>m\<close>-th element of \<open>R\<^sub>0\<close>
    is less than the \<open>m\<close>-th element of \<open>C\<close>. By definition,
    \<open>R\<^sub>1\<close> is a copy of \<open>R\<^sub>0\<close>, but for each \<open>m < m\<^sub>0\<close>,
    the \<open>m\<close>-th element is increased either by 0 or by the difference
    between itself and the \<open>m\<close>-th element of \<open>C\<close>. Then it is less
    than or equal to the \<open>m\<close>-th element of \<open>C\<close>, so the sequence
    of the first \<open>m\<^sub>0\<close> elements of \<open>R\<^sub>1\<close> is pointwise smaller
    than or equal to the sequence of the first \<open>m\<^sub>0\<close> elements of
    \<open>C\<close> (in fact, it is equal, but that is not necessary for this
    proof). However, the \<open>m\<^sub>0\<close>-th element of \<open>R\<^sub>1\<close> is
    necessarily equal to the \<open>m\<^sub>0\<close>-th element of \<open>R\<^sub>0\<close>
    since \<open>m\<^sub>0 < m\<^sub>0\<close> is false, thus it is strictly smaller
    than the \<open>m\<^sub>0\<close>-th element of \<open>C\<close>.

    Therefore \<open>R\<^sub>1 <_lex C\<close>, which implies
    \<open>B\<^sub>1 + B\<^sub>2 + ... + B_n  <_lex  (C)\<close>, and thus
    \<open>A[n] <_lex A\<close>.
\<close>

lemma lemma_2_1:
  fixes A :: array and n :: nat
  assumes "A \<in> BMS" "A \<noteq> []"
  shows "A[n] <\<^sub>l\<^sub>e\<^sub>x A"
  sorry  \<comment> \<open>To be proved by structural translation of the paper proof.
            Non-emptiness is needed because the paper's argument uses the
            decomposition \<open>A = G + B\<^sub>0 + (C)\<close>, which requires \<open>A \<noteq> []\<close>.
            For \<open>A = []\<close>, the expansion gives \<open>A[n] = A\<close> by definition.\<close>


section \<open>Corollary 2.2\<close>

text \<open>
  Quote: ``For all \<open>A, A' \<in> BMS\<close>, \<open>A' < A\<close> implies \<open>A' <_lex A\<close>.''

  This follows immediately from Lemma 2.1 by induction on the
  derivation of \<open>A' <\<^sub>B A\<close>, since each step replaces \<open>A\<close> by
  \<open>A[n]\<close> which is \<open><_lex A\<close>, and \<open><_lex\<close> is transitive.
\<close>

text \<open>
  Auxiliary: \<open><\<^sub>l\<^sub>e\<^sub>x\<close> is irreflexive and transitive. (Uses
  Isabelle's @{const lex} predicate; concrete library lemma lookup
  pending.)
\<close>

lemma col_lt_irrefl: "\<not> c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c"
  by (induct c) (auto simp: col_lt_def)

lemma arr_lex_irrefl: "\<not> A <\<^sub>l\<^sub>e\<^sub>x A"
  by (induct A) (auto simp: arr_lex_def col_lt_irrefl)

lemma trans_nat_lt: "trans {(x::nat, y). x < y}"
  by (auto simp: trans_def)

lemma col_lt_trans:
  "c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c' \<Longrightarrow> c' <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'' \<Longrightarrow> c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c''"
  using lex_transI[OF trans_nat_lt] unfolding col_lt_def trans_def by blast

lemma trans_col_lt_set: "trans {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
  using col_lt_trans by (auto simp: trans_def)

lemma arr_lex_trans:
  "A <\<^sub>l\<^sub>e\<^sub>x B \<Longrightarrow> B <\<^sub>l\<^sub>e\<^sub>x C \<Longrightarrow> A <\<^sub>l\<^sub>e\<^sub>x C"
  using lex_transI[OF trans_col_lt_set] unfolding arr_lex_def trans_def by blast

text \<open>
  Auxiliary: from \<open>A' \<le>\<^sub>B A\<close> we obtain either \<open>A' = A\<close> or
  \<open>A' <\<^sub>l\<^sub>e\<^sub>x A\<close>, by induction on the derivation and using
  Lemma 2.1.
\<close>

text \<open>
  Expansion of the empty array is the empty array (Definition 1.1).
\<close>
lemma expansion_empty: "[][n] = []"
  by (simp add: expansion_def)

lemma bms_le_empty: "A \<le>\<^sub>B [] \<Longrightarrow> A = []"
proof (induct A "[] :: array" rule: bms_le.induct)
  case bms_le_refl
  show ?case ..
next
  case (bms_le_step A n)
  thus ?case using expansion_empty by simp
qed

lemma bms_le_implies_lex:
  assumes "A \<in> BMS" "A' \<le>\<^sub>B A"
  shows "A' = A \<or> A' <\<^sub>l\<^sub>e\<^sub>x A"
  using assms(2,1)
proof (induct rule: bms_le.induct)
  case bms_le_refl
  thus ?case by simp
next
  case (bms_le_step A' A n)
  have An_BMS: "A[n] \<in> BMS" using bms_le_step.prems by (rule expand_in_BMS)
  show ?case
  proof (cases "A = []")
    case True
    hence "A[n] = A" by (simp add: expansion_empty)
    with bms_le_step.hyps(2)[OF An_BMS] show ?thesis by auto
  next
    case False
    have lex_step: "A[n] <\<^sub>l\<^sub>e\<^sub>x A"
      using lemma_2_1[OF bms_le_step.prems False] .
    from bms_le_step.hyps(2)[OF An_BMS]
    consider "A' = A[n]" | "A' <\<^sub>l\<^sub>e\<^sub>x A[n]" by blast
    thus ?thesis using lex_step arr_lex_trans by (cases) auto
  qed
qed

corollary corollary_2_2:
  assumes "A \<in> BMS" "A' <\<^sub>B A"
  shows "A' <\<^sub>l\<^sub>e\<^sub>x A"
proof -
  from \<open>A' <\<^sub>B A\<close> have le: "A' \<le>\<^sub>B A" and ne: "A' \<noteq> A"
    unfolding bms_lt_def by auto
  from bms_le_implies_lex[OF \<open>A \<in> BMS\<close> le] ne show ?thesis by blast
qed


section \<open>Lemma 2.3 (BMS is totally ordered)\<close>

text \<open>
  Quote (paper, p.~4):
    ``For every non-empty \<open>A \<in> BMS\<close>, \<open>A[0]\<close> is simply \<open>A\<close>
    without the last column, as it is equal to \<open>G + B\<^sub>0\<close>, and
    thus \<open>A = A[0] + (C)\<close>. Then it is trivial to prove by induction
    that for all \<open>A, A' \<in> BMS\<close>, if \<open>A'\<close> is a subsequence of
    \<open>A\<close>, then \<open>A' = A[0][0]...[0]\<close> for some \<open>n \<in> \<nat>\<close>, and
    thus \<open>A' \<le> A\<close>.

    Together with \<open>A[n]\<close> being a subsequence of \<open>A[n+1]\<close> for all
    \<open>A \<in> BMS\<close> and \<open>n \<in> \<nat>\<close>, this also means that for all
    \<open>A, A' \<in> BMS\<close> and \<open>n \<in> \<nat>\<close>, \<open>A[n] \<le> A[n+1]\<close>, and if
    \<open>A[n] < A' \<le> A[n+1]\<close>, then \<open>A[n] \<le> A'[0]\<close>. This implies that
    if some subset \<open>X\<close> of BMS is totally ordered, then
    \<open>X \<union> {A[n] : A \<in> X \<and> n \<in> \<nat>}\<close> is also totally ordered. By
    induction, it is clear that if \<open>X \<subseteq> BMS\<close> is totally ordered,
    then ... [closure under iterated expansion is totally ordered].
    So if \<open>X\<^sub>0\<close> is totally ordered, then BMS is totally ordered.

    It is now sufficient to prove that \<open>X\<^sub>0\<close> is totally ordered. ...''
\<close>

text \<open>
  Iterated \<open>[0]\<close>-expansion produces a descending \<open>\<le>\<^sub>B\<close>-chain.
\<close>

primrec iter_zero :: "array \<Rightarrow> nat \<Rightarrow> array" where
  "iter_zero A 0 = A"
| "iter_zero A (Suc k) = (iter_zero A k)[0]"

lemma iter_zero_le: "iter_zero A k \<le>\<^sub>B A"
proof (induct k)
  case 0 show ?case by (simp add: bms_le_refl)
next
  case (Suc k)
  have "iter_zero A (Suc k) = (iter_zero A k)[0]" by simp
  also have "(iter_zero A k)[0] \<le>\<^sub>B iter_zero A k" by (rule bms_le_expand)
  finally show ?case using Suc bms_le_trans by blast
qed

lemma lemma_2_3:
  shows "(\<forall>A \<in> BMS. \<forall>A' \<in> BMS. A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A)"
  sorry


section \<open>Corollary 2.4\<close>

text \<open>
  Quote: ``The ordering of BMS coincides with the lexicographical
  ordering with columns compared lexicographically.''
\<close>

corollary corollary_2_4:
  assumes "A \<in> BMS" "A' \<in> BMS"
  shows "A' <\<^sub>B A \<longleftrightarrow> A' <\<^sub>l\<^sub>e\<^sub>x A"
  sorry

end
