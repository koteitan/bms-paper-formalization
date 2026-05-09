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

text \<open>
  We use Isabelle's @{const lexord} to capture the paper's lexicographic
  order on lists, which compares lists of possibly differing length:
  a strict prefix is smaller than its extension. The earlier definition
  via @{const lex} only compared equal-length lists; switching to
  @{const lexord} matches the paper's intent (e.g.\ \<open>A[n]\<close> may have
  fewer columns than \<open>A\<close> when \<open>m\<^sub>0\<close> is undefined, and the paper
  considers it \<open><_lex A\<close>).
\<close>

definition col_lt :: "column \<Rightarrow> column \<Rightarrow> bool" (infix "<\<^sub>c\<^sub>l\<^sub>e\<^sub>x" 50) where
  "c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c' \<longleftrightarrow> (c, c') \<in> lexord {(x, y). x < y}"

definition arr_lex :: "array \<Rightarrow> array \<Rightarrow> bool" (infix "<\<^sub>l\<^sub>e\<^sub>x" 50) where
  "A <\<^sub>l\<^sub>e\<^sub>x A' \<longleftrightarrow> (A, A') \<in> lexord {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"


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

text \<open>
  Auxiliary: an empty list is strictly lex-less than any non-empty list,
  via @{const lexord} via prefix-extension.
\<close>

lemma arr_lex_Nil_lt: "A \<noteq> [] \<Longrightarrow> [] <\<^sub>l\<^sub>e\<^sub>x A"
  unfolding arr_lex_def by (cases A) auto

lemma butlast_arr_lex: "A \<noteq> [] \<Longrightarrow> butlast A <\<^sub>l\<^sub>e\<^sub>x A"
  unfolding arr_lex_def
  using lexord_append_rightI[where r = "{(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
                             and y = "[last A]" and x = "butlast A"]
        append_butlast_last_id
  by metis

lemma take_strict_prefix_col_lt:
  fixes c :: "nat list"
  assumes "k < length c"
  shows "take k c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c"
proof -
  have drop_ne: "drop k c \<noteq> []" using assms by simp
  then obtain b z where bz: "drop k c = b # z" by (cases "drop k c") auto
  have c_eq: "c = take k c @ drop k c" by simp
  have "(take k c, take k c @ drop k c) \<in> lexord {(x::nat, y). x < y}"
    using lexord_append_rightI[where r = "{(x::nat, y). x < y}"
                               and y = "drop k c" and x = "take k c"] bz
    by blast
  hence "(take k c, c) \<in> lexord {(x::nat, y). x < y}" using c_eq by simp
  thus ?thesis unfolding col_lt_def .
qed

text \<open>
  Map of \<open>take k\<close> over a non-empty array \<open>X\<close>: if the head column
  has length greater than \<open>k\<close>, then the resulting array has the
  head column shortened, hence is \<open><\<^sub>l\<^sub>e\<^sub>x\<close>-smaller.
\<close>

lemma map_take_arr_lex_lt:
  fixes X :: array
  assumes "X \<noteq> []" "k < length (hd X)"
  shows "map (take k) X <\<^sub>l\<^sub>e\<^sub>x X"
proof -
  obtain c rest where X_eq: "X = c # rest" using assms(1) by (cases X) auto
  have c_eq: "hd X = c" using X_eq by simp
  have "take k c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c" using assms(2) c_eq take_strict_prefix_col_lt by simp
  hence "(take k c, c) \<in> {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}" by simp
  hence "(take k c # map (take k) rest, c # rest)
           \<in> lexord {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
    by simp
  thus ?thesis using X_eq unfolding arr_lex_def by simp
qed

text \<open>
  General lemma: for any array \<open>X\<close> and any \<open>k\<close>, either
  \<open>map (take k) X = X\<close> (every column already has length \<open>\<le> k\<close>),
  or \<open>map (take k) X <\<^sub>l\<^sub>e\<^sub>x X\<close>. By induction on \<open>X\<close>.
\<close>

lemma map_take_arr_lex_le:
  fixes X :: array
  shows "map (take k) X = X \<or> map (take k) X <\<^sub>l\<^sub>e\<^sub>x X"
proof (induct X)
  case Nil
  show ?case by simp
next
  case (Cons c rest)
  show ?case
  proof (cases "length c \<le> k")
    case True
    hence take_c: "take k c = c" by simp
    from Cons.hyps show ?thesis
    proof
      assume rest_eq: "map (take k) rest = rest"
      have "map (take k) (c # rest) = c # rest"
        using take_c rest_eq by simp
      thus ?thesis by simp
    next
      assume rest_lt: "map (take k) rest <\<^sub>l\<^sub>e\<^sub>x rest"
      hence "(map (take k) rest, rest) \<in> lexord {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
        unfolding arr_lex_def by simp
      hence "(c # map (take k) rest, c # rest)
               \<in> lexord {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
        by simp
      hence "(map (take k) (c # rest), c # rest)
               \<in> lexord {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
        using take_c by simp
      thus ?thesis unfolding arr_lex_def by simp
    qed
  next
    case False
    hence "k < length c" by simp
    hence head_lt: "take k c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c"
      by (rule take_strict_prefix_col_lt)
    hence "(take k c, c) \<in> {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}" by simp
    hence "(take k c # map (take k) rest, c # rest)
             \<in> lexord {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
      by simp
    thus ?thesis unfolding arr_lex_def by simp
  qed
qed

lemma strip_zero_rows_le_lex:
  "strip_zero_rows X = X \<or> strip_zero_rows X <\<^sub>l\<^sub>e\<^sub>x X"
proof (cases "X = []")
  case True
  thus ?thesis by (simp add: strip_zero_rows_def)
next
  case False
  let ?H = "height X"
  let ?keep = "(LEAST h. h \<le> ?H \<and> (\<forall>m. h \<le> m \<and> m < ?H \<longrightarrow>
                                       (\<forall>c \<in> set X. c ! m = 0)))"
  have strip_eq: "strip_zero_rows X = map (\<lambda>c. take ?keep c) X"
    using False unfolding strip_zero_rows_def by (simp add: Let_def)
  have "map (take ?keep) X = X \<or> map (take ?keep) X <\<^sub>l\<^sub>e\<^sub>x X"
    by (rule map_take_arr_lex_le)
  thus ?thesis using strip_eq by simp
qed

text \<open>
  Totality of \<open><\<^sub>c\<^sub>l\<^sub>e\<^sub>x\<close> and \<open><\<^sub>l\<^sub>e\<^sub>x\<close> on arbitrary
  inputs (not just BMS), via @{thm lexord_linear}.
\<close>

lemma col_lt_total: "c = c' \<or> c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c' \<or> c' <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c"
  unfolding col_lt_def using lexord_linear[where r = "{(x::nat, y). x < y}"]
  by force

lemma arr_lex_total: "A = B \<or> A <\<^sub>l\<^sub>e\<^sub>x B \<or> B <\<^sub>l\<^sub>e\<^sub>x A"
  unfolding arr_lex_def
  using lexord_linear[where r = "{(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"] col_lt_total
  by blast

lemma lemma_2_1:
  fixes A :: array and n :: nat
  assumes "A \<in> BMS" "A \<noteq> []"
  shows "A[n] <\<^sub>l\<^sub>e\<^sub>x A"
  sorry  \<comment> \<open>The paper's full proof uses the decomposition
            \<open>A = G + B\<^sub>0 + (C)\<close> and case-splits on whether \<open>m\<^sub>0\<close>
            is defined. Computational details of the expansion are
            still being filled in.\<close>


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
  unfolding col_lt_def
  by (rule lexord_irreflexive) auto

lemma arr_lex_irrefl: "\<not> A <\<^sub>l\<^sub>e\<^sub>x A"
  unfolding arr_lex_def
  by (rule lexord_irreflexive) (auto simp: col_lt_irrefl)

lemma trans_nat_lt: "trans {(x::nat, y). x < y}"
  by (auto simp: trans_def)

lemma col_lt_trans:
  "c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c' \<Longrightarrow> c' <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'' \<Longrightarrow> c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c''"
  unfolding col_lt_def using lexord_trans[OF _ _ trans_nat_lt] .

lemma trans_col_lt_set: "trans {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
  using col_lt_trans by (auto simp: trans_def)

lemma arr_lex_trans:
  "A <\<^sub>l\<^sub>e\<^sub>x B \<Longrightarrow> B <\<^sub>l\<^sub>e\<^sub>x C \<Longrightarrow> A <\<^sub>l\<^sub>e\<^sub>x C"
  unfolding arr_lex_def using lexord_trans[OF _ _ trans_col_lt_set] .

lemma lemma_2_1_zero:
  fixes A :: array
  assumes "A \<noteq> []"
  shows "A[0] <\<^sub>l\<^sub>e\<^sub>x A"
  using expansion_zero_eq[OF assms] butlast_arr_lex[OF assms]
        strip_zero_rows_le_lex arr_lex_trans
  by metis

text \<open>
  Lemma 2.1 in the special case where \<open>m\<^sub>0\<close> is undefined
  (\<open>b0_start A = None\<close>): for any \<open>n\<close>, \<open>A[n] <\<^sub>l\<^sub>e\<^sub>x A\<close>.
\<close>

lemma lemma_2_1_no_b0:
  fixes A :: array
  assumes "A \<noteq> []" "b0_start A = None"
  shows "A[n] <\<^sub>l\<^sub>e\<^sub>x A"
proof -
  have "A[n] = A[0]" using expansion_no_b0_eq_zero[OF assms] .
  thus ?thesis using lemma_2_1_zero[OF assms(1)] by simp
qed

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

text \<open>
  Iterated \<open>[0]\<close>-expansion of a non-empty array is strictly
  \<open><\<^sub>l\<^sub>e\<^sub>x\<close>-less than the starting array, when applied at least
  once. Combines @{thm lemma_2_1_zero} with @{thm arr_lex_Nil_lt} for
  the case where iteration drives the array empty.
\<close>

lemma iter_zero_Suc_lex:
  assumes "A \<noteq> []"
  shows "iter_zero A (Suc k) <\<^sub>l\<^sub>e\<^sub>x A"
proof (induct k)
  case 0
  have "iter_zero A (Suc 0) = A[0]" by simp
  thus ?case using lemma_2_1_zero[OF assms] by simp
next
  case (Suc k)
  show ?case
  proof (cases "iter_zero A (Suc k) = []")
    case True
    have "iter_zero A (Suc (Suc k)) = (iter_zero A (Suc k))[0]" by simp
    also have "\<dots> = []" using True by (simp add: expansion_def)
    finally show ?thesis using arr_lex_Nil_lt[OF assms] by simp
  next
    case False
    have step: "(iter_zero A (Suc k))[0] <\<^sub>l\<^sub>e\<^sub>x iter_zero A (Suc k)"
      by (rule lemma_2_1_zero[OF False])
    have "iter_zero A (Suc (Suc k)) = (iter_zero A (Suc k))[0]" by simp
    thus ?thesis using step Suc arr_lex_trans by metis
  qed
qed


section \<open>Closure of BMS under \<open>\<le>\<^sub>B\<close>\<close>

lemma bms_le_in_BMS:
  assumes "A' \<le>\<^sub>B A" "A \<in> BMS"
  shows "A' \<in> BMS"
  using assms
proof (induct rule: bms_le.induct)
  case bms_le_refl thus ?case .
next
  case (bms_le_step A' A n)
  have "A[n] \<in> BMS" using bms_le_step.prems by (rule expand_in_BMS)
  thus ?case by (rule bms_le_step.hyps(2))
qed


section \<open>Strict order \<open><\<^sub>B\<close>: irreflexivity and transitivity\<close>

lemma bms_lt_irrefl: "\<not> A <\<^sub>B A"
  by (simp add: bms_lt_def)

lemma bms_lt_implies_lex:
  assumes "A \<in> BMS" "A' <\<^sub>B A"
  shows "A' <\<^sub>l\<^sub>e\<^sub>x A"
  using corollary_2_2[OF assms] .

lemma bms_lt_trans:
  assumes "A'' <\<^sub>B A'" "A' <\<^sub>B A" "A \<in> BMS"
  shows "A'' <\<^sub>B A"
proof -
  from assms have le1: "A'' \<le>\<^sub>B A'" and le2: "A' \<le>\<^sub>B A"
    unfolding bms_lt_def by auto
  have le: "A'' \<le>\<^sub>B A" using bms_le_trans[OF le1 le2] .
  have A'_BMS: "A' \<in> BMS" using bms_le_in_BMS[OF le2 \<open>A \<in> BMS\<close>] .
  have lex1: "A' <\<^sub>l\<^sub>e\<^sub>x A" using bms_lt_implies_lex[OF \<open>A \<in> BMS\<close> \<open>A' <\<^sub>B A\<close>] .
  have lex2: "A'' <\<^sub>l\<^sub>e\<^sub>x A'" using bms_lt_implies_lex[OF A'_BMS \<open>A'' <\<^sub>B A'\<close>] .
  have lex: "A'' <\<^sub>l\<^sub>e\<^sub>x A" using arr_lex_trans[OF lex2 lex1] .
  have ne: "A'' \<noteq> A" using lex arr_lex_irrefl by auto
  show "A'' <\<^sub>B A" using le ne unfolding bms_lt_def by blast
qed

lemma lemma_2_3:
  shows "(\<forall>A \<in> BMS. \<forall>A' \<in> BMS. A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A)"
  sorry


section \<open>Corollary 2.4\<close>

text \<open>
  Quote: ``The ordering of BMS coincides with the lexicographical
  ordering with columns compared lexicographically.''
\<close>

corollary corollary_2_4_forward:
  assumes "A \<in> BMS" "A' <\<^sub>B A"
  shows "A' <\<^sub>l\<^sub>e\<^sub>x A"
  using corollary_2_2[OF assms] .

corollary corollary_2_4_backward:
  assumes "A \<in> BMS" "A' \<in> BMS" "A' <\<^sub>l\<^sub>e\<^sub>x A"
  shows "A' <\<^sub>B A"
proof -
  from lemma_2_3 assms(1,2) consider "A \<le>\<^sub>B A'" | "A' \<le>\<^sub>B A" by blast
  thus ?thesis
  proof cases
    case 1
    have ne: "A \<noteq> A'" using assms(3) arr_lex_irrefl by auto
    hence "A <\<^sub>B A'" using 1 unfolding bms_lt_def by blast
    hence "A <\<^sub>l\<^sub>e\<^sub>x A'" using bms_lt_implies_lex[OF assms(2)] by blast
    hence "A' <\<^sub>l\<^sub>e\<^sub>x A'" using arr_lex_trans[OF assms(3)] by blast
    thus ?thesis using arr_lex_irrefl by simp
  next
    case 2
    have "A' \<noteq> A" using assms(3) arr_lex_irrefl by auto
    thus ?thesis using 2 unfolding bms_lt_def by blast
  qed
qed

corollary corollary_2_4:
  assumes "A \<in> BMS" "A' \<in> BMS"
  shows "A' <\<^sub>B A \<longleftrightarrow> A' <\<^sub>l\<^sub>e\<^sub>x A"
  using corollary_2_4_forward[OF assms(1)] corollary_2_4_backward[OF assms]
  by blast


section \<open>The seed set \<open>X\<^sub>0\<close> is linearly ordered\<close>

text \<open>
  \<open>replicate n 0\<close> is a strict prefix of \<open>replicate (Suc n) 0\<close>,
  hence smaller in @{const col_lt}. From this, \<open>seed n <\<^sub>l\<^sub>e\<^sub>x
  seed (Suc n)\<close>.
\<close>

lemma replicate_strict_prefix_col_lt:
  "(replicate n (0::nat)) <\<^sub>c\<^sub>l\<^sub>e\<^sub>x (replicate (Suc n) 0)"
proof -
  have "replicate (Suc n) (0::nat) = replicate n 0 @ [0]"
    by (induct n) auto
  thus ?thesis
    unfolding col_lt_def
    using lexord_append_rightI[where r = "{(x::nat, y). x < y}"
                               and y = "[0]" and x = "replicate n 0"]
    by simp
qed

lemma seed_lex_succ:
  shows "seed n <\<^sub>l\<^sub>e\<^sub>x seed (Suc n)"
proof -
  have c0_lt: "(seed n ! 0) <\<^sub>c\<^sub>l\<^sub>e\<^sub>x (seed (Suc n) ! 0)"
    using replicate_strict_prefix_col_lt by (simp add: seed_nth0)
  thus ?thesis
    unfolding arr_lex_def seed_def
    by simp
qed

text \<open>
  By transitivity, \<open>seed n <\<^sub>l\<^sub>e\<^sub>x seed m\<close> for any \<open>n < m\<close>.
\<close>

lemma seed_lex_lt:
  assumes "n < m"
  shows "seed n <\<^sub>l\<^sub>e\<^sub>x seed m"
proof -
  have rep_eq: "replicate n (0::nat) = take n (replicate m 0)"
    using assms by simp
  have len_rep: "n < length (replicate m (0::nat))"
    using assms by simp
  have "take n (replicate m (0::nat)) <\<^sub>c\<^sub>l\<^sub>e\<^sub>x replicate m 0"
    using take_strict_prefix_col_lt[OF len_rep] .
  hence rep_lt: "replicate n (0::nat) <\<^sub>c\<^sub>l\<^sub>e\<^sub>x replicate m 0"
    using rep_eq by simp
  hence pair_in: "(replicate n (0::nat), replicate m 0)
                  \<in> {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
    by simp
  have "(seed n, seed m) \<in> lexord {(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
    unfolding seed_def
    using pair_in by (rule lexord_cons_cons[THEN iffD2, OF disjI1])
  thus ?thesis unfolding arr_lex_def .
qed

text \<open>
  And the seeds are pairwise distinct: \<open>seed n = seed m \<Longrightarrow> n = m\<close>.
\<close>

lemma seed_inj: "seed n = seed m \<Longrightarrow> n = m"
  by (auto simp: seed_def)

text \<open>
  The seed set \<open>X\<^sub>0\<close> is linearly ordered by @{const arr_lex}.
\<close>

lemma X0_lex_total:
  "seed n = seed m \<or> seed n <\<^sub>l\<^sub>e\<^sub>x seed m \<or> seed m <\<^sub>l\<^sub>e\<^sub>x seed n"
proof (cases n m rule: linorder_cases)
  case less thus ?thesis using seed_lex_lt by blast
next
  case equal thus ?thesis by simp
next
  case greater thus ?thesis using seed_lex_lt by blast
qed


section \<open>Step 3: \<open>bump_col_lt_C\<close>\<close>

text \<open>
  The bumped first column \<open>B\<^sub>1[0]\<close> is strictly \<open><\<^sub>c\<^sub>l\<^sub>e\<^sub>x\<close>-less
  than the last column \<open>C\<close>: at row \<open>m\<^sub>0\<close> the bumped value is
  strictly smaller (Step 1, @{thm bump_col_value_lt_m0}), and at all
  earlier rows they agree (Step 2, @{thm bump_col_value_eq_below}).
\<close>

lemma bump_col_lt_C:
  assumes b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and ne: "A \<noteq> []"
      and len_s: "m\<^sub>0 < length (A ! s)"
      and len_C: "m\<^sub>0 < length (A ! last_col_idx A)"
  shows "(bump_col A 0 1) <\<^sub>c\<^sub>l\<^sub>e\<^sub>x (A ! last_col_idx A)"
proof -
  let ?bump = "bump_col A 0 1"
  let ?C = "A ! last_col_idx A"
  have len_bump: "length ?bump = length (A ! s)"
    using length_bump_col_eq[OF b0] .
  have m0_lt_min: "m\<^sub>0 < min (length ?bump) (length ?C)"
    using len_bump len_s len_C by simp
  have eq_below: "\<And>m. m < m\<^sub>0 \<Longrightarrow> ?bump ! m = ?C ! m"
  proof -
    fix m assume "m < m\<^sub>0"
    moreover from this len_s have "m < length (A ! s)" by simp
    ultimately show "?bump ! m = ?C ! m"
      using bump_col_value_eq_below[OF b0 mp ne] by simp
  qed
  have take_eq: "take m\<^sub>0 ?bump = take m\<^sub>0 ?C"
  proof (rule nth_equalityI)
    show "length (take m\<^sub>0 ?bump) = length (take m\<^sub>0 ?C)"
      using m0_lt_min by simp
    fix i assume "i < length (take m\<^sub>0 ?bump)"
    hence "i < m\<^sub>0" using m0_lt_min by simp
    thus "take m\<^sub>0 ?bump ! i = take m\<^sub>0 ?C ! i"
      using eq_below m0_lt_min by simp
  qed
  have lt_at_m0: "?bump ! m\<^sub>0 < ?C ! m\<^sub>0"
    using bump_col_value_lt_m0[OF b0 mp ne] .
  have pair_in: "(?bump ! m\<^sub>0, ?C ! m\<^sub>0) \<in> {(x::nat, y). x < y}"
    using lt_at_m0 by simp
  have "(?bump, ?C) \<in> lexord {(x::nat, y). x < y}"
    using lexord_take_index_conv[where r = "{(x::nat, y). x < y}"
                                 and x = ?bump and y = ?C]
          m0_lt_min take_eq pair_in
    by blast
  thus ?thesis unfolding col_lt_def .
qed

end
