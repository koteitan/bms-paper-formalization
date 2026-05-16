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

text \<open>
  Strict descent decomposes via an expansion: \<open>A <\<^sub>B B \<Longrightarrow>
  \<exists>n. A \<le>\<^sub>B B[n]\<close>. Direct from the inductive shape of
  \<open>bms_le\<close>: the \<open>bms_le_refl\<close> constructor gives \<open>A = B\<close>
  contradicting strictness, so the witness must come from
  \<open>bms_le_step\<close>.
\<close>

lemma bms_lt_imp_le_expansion:
  assumes "A <\<^sub>B B"
  shows "\<exists>n. A \<le>\<^sub>B expansion B n"
proof -
  have le: "A \<le>\<^sub>B B" using assms unfolding bms_lt_def by simp
  have ne: "A \<noteq> B" using assms unfolding bms_lt_def by simp
  show ?thesis using le ne by (cases rule: bms_le.cases) blast+
qed


text \<open>
  Seed chain: \<open>seed n \<le>\<^sub>B seed (Suc n)\<close> via @{thm seed_Suc_expand_one}
  (\<open>(seed (Suc n))[1] = seed n\<close>).
\<close>

lemma seed_le_B_succ: "seed n \<le>\<^sub>B seed (Suc n)"
proof -
  have "(seed (Suc n))[1] = seed n" by (rule seed_Suc_expand_one)
  thus ?thesis using bms_le_expand[where A = "seed (Suc n)" and n = 1] by simp
qed

lemma seed_chain_le_B_aux: "seed n \<le>\<^sub>B seed (n + k)"
proof (induct k)
  case 0 thus ?case by (simp add: bms_le_refl)
next
  case (Suc k)
  have step: "seed (n + k) \<le>\<^sub>B seed (Suc (n + k))"
    using seed_le_B_succ[where n = "n + k"] .
  have eq: "n + Suc k = Suc (n + k)" by simp
  show ?case using Suc step bms_le_trans eq by metis
qed

lemma seed_chain_le_B:
  assumes "n \<le> m"
  shows "seed n \<le>\<^sub>B seed m"
proof -
  obtain k where m_eq: "m = n + k" using assms le_Suc_ex by blast
  show ?thesis using seed_chain_le_B_aux m_eq by simp
qed

text \<open>
  Every \<open>A \<in> BMS\<close> is \<open>\<le>\<^sub>B\<close>-below some seed: this follows
  from BMS construction by induction (seeds are seeds; expansions
  preserve \<open>\<le>\<^sub>B\<close>-below-seed via @{thm bms_le_expand}).
\<close>

lemma bms_below_seed:
  assumes "A \<in> BMS"
  shows "\<exists>N. A \<le>\<^sub>B seed N"
  using assms
proof (induct rule: BMS.induct)
  case (seed_in_BMS n)
  show ?case using bms_le_refl by blast
next
  case (expand_in_BMS A k)
  then obtain N where "A \<le>\<^sub>B seed N" by blast
  hence "A[k] \<le>\<^sub>B seed N" using bms_le_expand bms_le_trans by blast
  thus ?case by blast
qed

text \<open>
  Two elements of \<open>BMS\<close> share a common seed-bound: the larger of
  the two seed-bounds is an upper bound of both.
\<close>

lemma bms_pair_below_seed:
  assumes "A \<in> BMS" "A' \<in> BMS"
  shows "\<exists>M. A \<le>\<^sub>B seed M \<and> A' \<le>\<^sub>B seed M"
proof -
  obtain N where N: "A \<le>\<^sub>B seed N" using bms_below_seed[OF assms(1)] by blast
  obtain N' where N': "A' \<le>\<^sub>B seed N'" using bms_below_seed[OF assms(2)] by blast
  let ?M = "max N N'"
  have "seed N \<le>\<^sub>B seed ?M" using seed_chain_le_B[where n = N and m = ?M] by simp
  hence "A \<le>\<^sub>B seed ?M" using N bms_le_trans by blast
  moreover have "seed N' \<le>\<^sub>B seed ?M"
    using seed_chain_le_B[where n = N' and m = ?M] by simp
  hence "A' \<le>\<^sub>B seed ?M" using N' bms_le_trans by blast
  ultimately show ?thesis by blast
qed


text \<open>
  Expansion chain on seeds: \<open>seed N [k] \<le>\<^sub>B seed N [Suc k]\<close>.

  The non-trivial case \<open>N = Suc n\<close> follows immediately from
  @{thm seed_expansion_succ_zero}: \<open>(seed N [Suc k])[0] = seed N [k]\<close>
  gives \<open>seed N [k] \<le>\<^sub>B seed N [Suc k]\<close> via @{thm bms_le_expand}.
  The \<open>N = 0\<close> case is trivial since every \<open>seed 0 [k]\<close> stays at
  \<open>[[]]\<close> (under our strip convention).
\<close>

lemma seed_step_le_B_succ:
  shows "(seed (Suc n))[k] \<le>\<^sub>B (seed (Suc n))[Suc k]"
proof -
  have eq: "(seed (Suc n))[Suc k][0] = (seed (Suc n))[k]"
    by (rule seed_expansion_succ_zero)
  have "(seed (Suc n))[Suc k][0] \<le>\<^sub>B (seed (Suc n))[Suc k]"
    by (rule bms_le_expand)
  thus ?thesis using eq by simp
qed

text \<open>
  Chain version: \<open>k \<le> k' \<Longrightarrow> seed (Suc n) [k] \<le>\<^sub>B seed (Suc n) [k']\<close>.
\<close>

lemma seed_chain_le_B_expansion_aux:
  shows "(seed (Suc n))[k] \<le>\<^sub>B (seed (Suc n))[k + d]"
proof (induct d)
  case 0 show ?case using bms_le_refl by simp
next
  case (Suc d)
  have step: "(seed (Suc n))[k + d] \<le>\<^sub>B (seed (Suc n))[Suc (k + d)]"
    by (rule seed_step_le_B_succ)
  have add_eq: "k + Suc d = Suc (k + d)" by simp
  show ?case using Suc step add_eq bms_le_trans by metis
qed

lemma seed_chain_le_B_expansion:
  assumes "k \<le> k'"
  shows "(seed (Suc n))[k] \<le>\<^sub>B (seed (Suc n))[k']"
proof -
  obtain d where k'_eq: "k' = k + d" using assms le_Suc_ex by blast
  show ?thesis using seed_chain_le_B_expansion_aux k'_eq by simp
qed

text \<open>
  Uniform length formula: \<open>arr_len ((seed (Suc n))[k]) = Suc k\<close>.
  Combines @{thm seed_expansion_zero} (\<open>k = 0\<close>) with
  @{thm seed_expansion_form} (\<open>k \<ge> 1\<close>).
\<close>

lemma arr_len_seed_expansion:
  shows "arr_len ((seed (Suc n))[k]) = Suc k"
proof (cases k)
  case 0
  have "(seed (Suc n))[k] = [[]]" using 0 by (simp add: seed_expansion_zero)
  thus ?thesis using 0 by simp
next
  case (Suc k')
  hence k_ge: "1 \<le> k" by simp
  have "(seed (Suc n))[k] = map (\<lambda>j. replicate n j) [0..<Suc k]"
    by (rule seed_expansion_form[OF k_ge])
  thus ?thesis by simp
qed

text \<open>
  Strict version: distinct \<open>k, k'\<close> give distinct expansions
  (since lengths differ), hence \<open>k < k' \<Longrightarrow> (seed (Suc n))[k]
  <\<^sub>B (seed (Suc n))[k']\<close>.
\<close>

lemma seed_chain_lt_B_expansion:
  assumes "k < k'"
  shows "(seed (Suc n))[k] <\<^sub>B (seed (Suc n))[k']"
proof -
  have le: "(seed (Suc n))[k] \<le>\<^sub>B (seed (Suc n))[k']"
    using seed_chain_le_B_expansion assms by simp
  have len_diff: "arr_len ((seed (Suc n))[k]) \<noteq> arr_len ((seed (Suc n))[k'])"
    using arr_len_seed_expansion assms by simp
  hence ne: "(seed (Suc n))[k] \<noteq> (seed (Suc n))[k']" by auto
  show ?thesis using le ne unfolding bms_lt_def by blast
qed


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


subsection \<open>Step 3: \<open>bump_col_lt_C\<close>\<close>

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
    using bump_col_value_lt_m0[OF b0 mp ne len_s] .
  have pair_in: "(?bump ! m\<^sub>0, ?C ! m\<^sub>0) \<in> {(x::nat, y). x < y}"
    using lt_at_m0 by simp
  have "(?bump, ?C) \<in> lexord {(x::nat, y). x < y}"
    using lexord_take_index_conv[where r = "{(x::nat, y). x < y}"
                                 and x = ?bump and y = ?C]
          m0_lt_min take_eq pair_in
    by blast
  thus ?thesis unfolding col_lt_def .
qed


subsection \<open>Step 4: \<open>expansion_some_lt_orig\<close>\<close>

text \<open>
  When \<open>m\<^sub>0\<close> is defined and \<open>n \<ge> 1\<close>, the unstripped
  expansion content \<open>X = G + Bs_concat A n\<close> is \<open><\<^sub>l\<^sub>e\<^sub>x\<close>-less
  than \<open>A\<close>: at index \<open>l\<^sub>0 + l\<^sub>1 = last_col_idx A\<close> the
  first column of \<open>B\<^sub>1\<close> is \<open><\<^sub>c\<^sub>l\<^sub>e\<^sub>x\<close>-less than \<open>C\<close>
  (Step 3, @{thm bump_col_lt_C}), and at all earlier positions
  \<open>X\<close> matches \<open>butlast A\<close>. After stripping trailing
  zero rows, \<open>A[n] \<le>\<^sub>l\<^sub>e\<^sub>x X\<close>, hence \<open>A[n] <\<^sub>l\<^sub>e\<^sub>x A\<close>.
\<close>

lemma expansion_some_lt_orig:
  fixes A :: array and n :: nat
  assumes ne: "A \<noteq> []"
      and is_arr: "is_array A"
      and b0: "b0_start A = Some s"
      and nge: "1 \<le> n"
  shows "A[n] <\<^sub>l\<^sub>e\<^sub>x A"
proof -
  obtain m\<^sub>0 where mp: "max_parent_level A = Some m\<^sub>0"
    using b0 unfolding b0_start_def
    by (cases "max_parent_level A") auto

  let ?H = "height A"
  let ?lc = "last_col_idx A"
  have m0_lt_H: "m\<^sub>0 < ?H" using max_parent_level_lt[OF mp] .

  have s_lt_last: "s < ?lc" using b0_start_lt[OF b0 ne] .
  have last_lt_len: "?lc < length A" using ne by (cases A) auto
  have s_lt_len: "s < length A" using s_lt_last last_lt_len by simp

  have hd_in: "hd A \<in> set A" using ne by simp
  have As_in: "A ! s \<in> set A" using s_lt_len by simp
  have AC_in: "A ! ?lc \<in> set A" using last_lt_len by simp
  have len_As: "length (A ! s) = ?H"
    using is_arr As_in unfolding is_array_def by blast
  have len_AC: "length (A ! ?lc) = ?H"
    using is_arr AC_in unfolding is_array_def by blast
  have m0_lt_s: "m\<^sub>0 < length (A ! s)" using m0_lt_H len_As by simp
  have m0_lt_C: "m\<^sub>0 < length (A ! ?lc)" using m0_lt_H len_AC by simp

  let ?X = "G_block A @ Bs_concat A n"
  let ?l\<^sub>0 = "length (G_block A)"
  let ?l\<^sub>1 = "length (B0_block A)"

  have G_len: "?l\<^sub>0 = s"
    using b0 s_lt_len by (simp add: G_block_def)
  have B0_len: "?l\<^sub>1 = ?lc - s"
    using b0 s_lt_last last_lt_len by (simp add: B0_block_def)
  have l1_pos: "0 < ?l\<^sub>1" using s_lt_last B0_len by simp

  let ?i = "s + ?l\<^sub>1"

  have i_eq_last: "?i = ?lc" using B0_len s_lt_last by simp
  have i_lt_A: "?i < length A" using i_eq_last last_lt_len by simp

  have len_X: "length ?X = s + Suc n * ?l\<^sub>1"
    using length_Bs_concat G_len by simp
  have i_lt_X: "?i < length ?X"
    using nge l1_pos len_X by simp

  have bump_pos: "?X ! ?i = bump_col A 0 1"
  proof -
    have "?X ! ?i = Bs_concat A n ! ?l\<^sub>1"
      using G_len by (simp add: nth_append)
    also have "\<dots> = bump_col A 0 1"
      using Bs_concat_nth_first_B1[OF nge l1_pos] .
    finally show ?thesis .
  qed

  have take_X: "take ?i ?X = butlast A"
  proof -
    have "take ?i ?X = G_block A @ take ?l\<^sub>1 (Bs_concat A n)"
      using G_len by (simp add: take_append)
    also have "\<dots> = G_block A @ B0_block A"
      using Bs_concat_take_l1[OF ne] by simp
    also have "\<dots> = butlast A" using G_block_B0_block[OF ne] .
    finally show ?thesis .
  qed

  have take_A: "take ?i A = butlast A"
    using i_eq_last ne by (simp add: butlast_conv_take)

  have take_eq: "take ?i ?X = take ?i A"
    using take_X take_A by simp

  have lt_clex: "?X ! ?i <\<^sub>c\<^sub>l\<^sub>e\<^sub>x A ! ?i"
    using bump_col_lt_C[OF b0 mp ne m0_lt_s m0_lt_C]
          bump_pos i_eq_last by simp

  have X_lt_A: "?X <\<^sub>l\<^sub>e\<^sub>x A"
  proof -
    let ?R = "{(c, c'). c <\<^sub>c\<^sub>l\<^sub>e\<^sub>x c'}"
    have i_lt_min: "?i < min (length ?X) (length A)"
      using i_lt_X i_lt_A by simp
    have pair_in: "(?X ! ?i, A ! ?i) \<in> ?R" using lt_clex by simp
    have "(?X, A) \<in> lexord ?R"
      using lexord_take_index_conv[where r = ?R and x = ?X and y = A]
            i_lt_min take_eq pair_in
      by blast
    thus ?thesis unfolding arr_lex_def .
  qed

  have An_eq: "A[n] = strip_zero_rows ?X"
    unfolding expansion_def using ne by simp
  hence "A[n] = ?X \<or> A[n] <\<^sub>l\<^sub>e\<^sub>x ?X"
    using strip_zero_rows_le_lex by simp
  thus ?thesis using X_lt_A arr_lex_trans by metis
qed


subsection \<open>Bridge: \<open>A \<in> BMS \<Longrightarrow> is_array A\<close>\<close>

text \<open>
  Connects the inductive set @{const BMS} with the rectangular-shape
  invariant @{const is_array}. Used to discharge \<open>is_array\<close>
  hypothesis in @{thm expansion_some_lt_orig}.
\<close>

lemma is_array_seed: "is_array (seed n)"
  unfolding is_array_def seed_def by simp

lemma G_block_subset_A: "set (G_block A) \<subseteq> set A"
  unfolding G_block_def
  by (cases "b0_start A") (auto dest: in_set_butlastD set_take_subset[THEN subsetD])

lemma bump_col_length_some:
  assumes "b0_start A = Some s"
  shows "length (bump_col A d i) = length (A ! (s + d))"
  using assms unfolding bump_col_def Let_def by simp

lemma bump_col_len_height:
  assumes is_arr: "is_array A"
      and ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and d_lt: "d < length (B0_block A)"
  shows "length (bump_col A d i) = height A"
proof -
  have s_lt: "s < length A" using b0_start_le_length[OF b0 ne] .
  have last_lt: "last_col_idx A < length A" using ne by (cases A) auto
  have B0_eq: "length (B0_block A) = last_col_idx A - s"
    using b0 s_lt last_lt by (simp add: B0_block_def)
  have sd_lt: "s + d < length A" using d_lt B0_eq last_lt by simp
  hence "A ! (s+d) \<in> set A" by simp
  hence "length (A ! (s+d)) = height A"
    using is_arr unfolding is_array_def by blast
  thus ?thesis using bump_col_length_some[OF b0] by simp
qed

lemma Bi_block_uniform:
  assumes is_arr: "is_array A" and ne: "A \<noteq> []"
  shows "\<forall>c \<in> set (Bi_block A i). length c = height A"
proof (cases "b0_start A")
  case None
  hence "Bi_block A i = []" by (rule Bi_block_no_b0)
  thus ?thesis by simp
next
  case (Some s)
  show ?thesis
  proof
    fix c assume c_in: "c \<in> set (Bi_block A i)"
    then obtain d where d_lt: "d < length (B0_block A)"
                     and c_eq: "c = bump_col A d i"
      unfolding Bi_block_def Let_def by auto
    show "length c = height A"
      using bump_col_len_height[OF is_arr ne Some d_lt] c_eq by simp
  qed
qed

lemma Bs_concat_uniform:
  assumes is_arr: "is_array A" and ne: "A \<noteq> []"
  shows "\<forall>c \<in> set (Bs_concat A k). length c = height A"
  unfolding Bs_concat_def
  using Bi_block_uniform[OF is_arr ne] by auto

lemma is_array_expansion:
  fixes A :: array and k :: nat
  assumes is_arr: "is_array A"
  shows "is_array (A[k])"
proof (cases "A = []")
  case True
  hence "A[k] = []" using assms unfolding expansion_def by simp
  thus ?thesis unfolding is_array_def by simp
next
  case A_ne: False
  let ?X = "G_block A @ Bs_concat A k"
  let ?H = "height A"
  have all_A: "\<forall>c \<in> set A. length c = ?H"
    using is_arr unfolding is_array_def by blast
  have all_G: "\<forall>c \<in> set (G_block A). length c = ?H"
    using G_block_subset_A all_A by blast
  have all_Bs: "\<forall>c \<in> set (Bs_concat A k). length c = ?H"
    using Bs_concat_uniform[OF is_arr A_ne] .
  have all_X: "\<forall>c \<in> set ?X. length c = ?H"
    using all_G all_Bs by auto
  show ?thesis
  proof (cases "?X = []")
    case True
    hence "A[k] = []"
      using A_ne unfolding expansion_def by (simp add: strip_zero_rows_def)
    thus ?thesis unfolding is_array_def by simp
  next
    case X_ne: False
    have An_eq: "A[k] = strip_zero_rows ?X"
      using A_ne unfolding expansion_def by simp
    let ?HX = "height ?X"
    let ?P = "\<lambda>h. h \<le> ?HX \<and> (\<forall>m. h \<le> m \<and> m < ?HX \<longrightarrow>
                                   (\<forall>c \<in> set ?X. c ! m = 0))"
    let ?keep = "Least ?P"
    have wit: "?P ?HX" by simp
    hence keep_le_HX: "?keep \<le> ?HX" by (rule Least_le)
    have hd_X_in: "hd ?X \<in> set ?X" using X_ne by (cases ?X) auto
    have hX_eq: "?HX = ?H"
    proof -
      have "?HX = length (hd ?X)" using X_ne by (cases ?X) auto
      also have "\<dots> = ?H" using hd_X_in all_X by blast
      finally show ?thesis .
    qed
    have keep_le_H: "?keep \<le> ?H" using keep_le_HX hX_eq by simp
    have strip_eq: "strip_zero_rows ?X = map (\<lambda>c. take ?keep c) ?X"
      using X_ne unfolding strip_zero_rows_def by (simp add: Let_def)
    have strip_ne: "strip_zero_rows ?X \<noteq> []"
      using X_ne strip_eq by simp
    have all_strip: "\<forall>c' \<in> set (strip_zero_rows ?X). length c' = ?keep"
    proof
      fix c' assume "c' \<in> set (strip_zero_rows ?X)"
      then obtain c where c_in: "c \<in> set ?X" and c'_eq: "c' = take ?keep c"
        using strip_eq by auto
      have "length c = ?H" using c_in all_X by auto
      thus "length c' = ?keep" using c'_eq keep_le_H by simp
    qed
    have hd_strip: "hd (strip_zero_rows ?X) = take ?keep (hd ?X)"
      using strip_eq X_ne by (cases ?X) auto
    have len_hd_X: "length (hd ?X) = ?H" using hd_X_in all_X by blast
    have h_strip: "height (strip_zero_rows ?X) = ?keep"
    proof -
      have "height (strip_zero_rows ?X) = length (hd (strip_zero_rows ?X))"
        using strip_ne by (cases "strip_zero_rows ?X") auto
      also have "\<dots> = length (take ?keep (hd ?X))" using hd_strip by simp
      also have "\<dots> = ?keep" using len_hd_X keep_le_H by simp
      finally show ?thesis .
    qed
    show ?thesis
      using An_eq strip_ne all_strip h_strip
      unfolding is_array_def by simp
  qed
qed

lemma BMS_is_array: "A \<in> BMS \<Longrightarrow> is_array A"
proof (induct rule: BMS.induct)
  case (seed_in_BMS n)
  show ?case by (rule is_array_seed)
next
  case (expand_in_BMS A k)
  have IH: "is_array A" by fact
  show ?case by (rule is_array_expansion[OF IH])
qed


subsection \<open>Lemma 2.1\<close>

text \<open>
  Quote (paper, p.~3):
    ``For all \<open>A \<in> BMS\<close> and \<open>n \<in> \<nat>\<close>, \<open>A[n]\<close> is lexicographically
    smaller than \<open>A\<close> (with the columns also compared lexicographically).''

  Proof: case-split on whether \<open>m\<^sub>0\<close> is defined and on \<open>n\<close>.
  The \<open>m\<^sub>0\<close>-undefined case follows from @{thm lemma_2_1_no_b0};
  the \<open>n = 0\<close> case follows from @{thm lemma_2_1_zero}; the
  remaining \<open>m\<^sub>0\<close>-defined, \<open>n \<ge> 1\<close> case follows from
  @{thm expansion_some_lt_orig}, which needs \<open>is_array A\<close>
  via @{thm BMS_is_array}.
\<close>

lemma lemma_2_1:
  fixes A :: array and n :: nat
  assumes "A \<in> BMS" "A \<noteq> []"
  shows "A[n] <\<^sub>l\<^sub>e\<^sub>x A"
proof (cases "b0_start A")
  case None
  show ?thesis using lemma_2_1_no_b0[OF assms(2) None] .
next
  case (Some s)
  show ?thesis
  proof (cases "n = 0")
    case True
    thus ?thesis using lemma_2_1_zero[OF assms(2)] by simp
  next
    case False
    hence nge: "1 \<le> n" by simp
    have is_arr: "is_array A" using BMS_is_array[OF assms(1)] .
    show ?thesis
      using expansion_some_lt_orig[OF assms(2) is_arr Some nge] .
  qed
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

text \<open>
  Seed-pair total: any two seeds are \<open>\<le>\<^sub>B\<close>-comparable.
\<close>

lemma seed_pair_le_B_total:
  shows "seed n \<le>\<^sub>B seed m \<or> seed m \<le>\<^sub>B seed n"
proof (cases "n \<le> m")
  case True
  thus ?thesis using seed_chain_le_B by simp
next
  case False
  hence "m \<le> n" by simp
  thus ?thesis using seed_chain_le_B by simp
qed

text \<open>
  \<open>lex_implies_le_B\<close>: Hunter's key bridge between the lex order
  and the BMS order \<open>\<le>\<^sub>B\<close> on \<open>BMS\<close>.  Equivalent to
  Corollary 2.4 (backward).  The forward direction is
  @{thm bms_le_implies_lex}.  This is the only direction whose proof
  is not yet filled in; once filled in, both Lemma 2.3 and
  Corollary 2.4 are immediate.
\<close>

text \<open>
  Degenerate base \<open>N = 0\<close>: enumerate descendants of \<open>seed 0\<close>.
  Using @{thm seed_0_expansion} and @{thm empty_col_expansion},
  the expansion ladder from \<open>seed 0\<close> is the 3-element chain
  \<open>seed 0 \<rightarrow> [[]] \<rightarrow> []\<close>.
\<close>

lemma descendants_of_empty_col:
  shows "A \<le>\<^sub>B [[]] \<Longrightarrow> A = [[]] \<or> A = []"
proof (induct A "[[]] :: array" rule: bms_le.induct)
  case bms_le_refl
  show ?case by simp
next
  case (bms_le_step A n)
  have "[[]][n] = []" by (rule empty_col_expansion)
  with bms_le_step.hyps have "A \<le>\<^sub>B []" by simp
  hence "A = []" by (rule bms_le_empty)
  thus ?case by simp
qed

lemma descendants_of_seed_0:
  shows "A \<le>\<^sub>B seed 0 \<Longrightarrow> A = seed 0 \<or> A = [[]] \<or> A = []"
proof (induct A "seed 0" rule: bms_le.induct)
  case bms_le_refl
  show ?case by simp
next
  case (bms_le_step A n)
  have "(seed 0)[n] = [[]]" by (rule seed_0_expansion)
  with bms_le_step.hyps have "A \<le>\<^sub>B [[]]" by simp
  hence "A = [[]] \<or> A = []" by (rule descendants_of_empty_col)
  thus ?case by simp
qed

text \<open>
  Chain elements for \<open>seed 0\<close>'s 3-element subtree.
\<close>

lemma empty_le_empty_col: "[] \<le>\<^sub>B ([[]] :: array)"
proof -
  have "[[]][0] = []" by (rule empty_col_expansion)
  hence "[] \<le>\<^sub>B [[]][0]" using bms_le_refl by simp
  thus ?thesis using bms_le_step by blast
qed

lemma empty_col_le_seed_0: "[[]] \<le>\<^sub>B seed 0"
proof -
  have "(seed 0)[0] = [[]]" by (rule seed_0_expansion)
  hence "[[]] \<le>\<^sub>B (seed 0)[0]" using bms_le_refl by simp
  thus ?thesis using bms_le_step by blast
qed

text \<open>
  Degenerate case \<open>N = 1\<close>: descendants of \<open>seed 1\<close> are
  the chain \<open>... \<le>\<^sub>B seed 1[0] \<le>\<^sub>B seed 1[1] \<le>\<^sub>B ... \<le>\<^sub>B seed 1\<close>
  where each \<open>seed 1[k] = replicate (Suc k) []\<close>
  (via @{thm seed_1_expansion}).  Because expansion of any
  \<open>replicate (Suc k) []\<close> collapses to \<open>replicate k []\<close>
  (via @{thm replicate_empty_expansion}), every descendant takes
  the form \<open>replicate j []\<close>.
\<close>

lemma descendants_of_replicate_empty:
  assumes "A \<le>\<^sub>B replicate (Suc k) ([] :: nat list)"
  shows "\<exists>j \<le> Suc k. A = replicate j ([] :: nat list)"
  using assms
proof (induct k arbitrary: A)
  case 0
  have "A \<le>\<^sub>B [[]]" using "0.prems" by simp
  hence "A = [[]] \<or> A = []" by (rule descendants_of_empty_col)
  thus ?case
  proof
    assume "A = [[]]"
    hence "A = replicate (Suc 0) []" by simp
    thus ?thesis by blast
  next
    assume "A = []"
    hence "A = replicate 0 ([] :: nat list)" by simp
    thus ?thesis by blast
  qed
next
  case (Suc k)
  from Suc.prems show ?case
  proof (cases rule: bms_le.cases)
    case bms_le_refl
    have "A = replicate (Suc (Suc k)) ([] :: nat list)" using bms_le_refl by simp
    thus ?thesis by blast
  next
    case (bms_le_step n)
    have eq: "(replicate (Suc (Suc k)) ([] :: nat list))[n]
                = replicate (Suc k) []"
      by (rule replicate_empty_expansion)
    have le: "A \<le>\<^sub>B replicate (Suc k) ([] :: nat list)"
      using bms_le_step eq by simp
    have "\<exists>j \<le> Suc k. A = replicate j ([] :: nat list)"
      by (rule Suc.hyps[OF le])
    then obtain j where j_le: "j \<le> Suc k" and A_eq: "A = replicate j []"
      by blast
    have "j \<le> Suc (Suc k)" using j_le by simp
    thus ?thesis using A_eq by blast
  qed
qed

lemma descendants_of_seed_1:
  shows "A \<le>\<^sub>B seed 1
         \<Longrightarrow> A = seed 1 \<or> (\<exists>j. A = replicate j ([] :: nat list))"
proof (induct A "seed 1" rule: bms_le.induct)
  case bms_le_refl
  show ?case by simp
next
  case (bms_le_step A n)
  have "(seed 1)[n] = replicate (Suc n) []" by (rule seed_1_expansion)
  with bms_le_step.hyps have "A \<le>\<^sub>B replicate (Suc n) []" by simp
  hence "\<exists>j \<le> Suc n. A = replicate j ([] :: nat list)"
    by (rule descendants_of_replicate_empty)
  then obtain j where "A = replicate j ([] :: nat list)" by blast
  thus ?case by blast
qed

lemma replicate_step_le_B:
  shows "replicate k ([] :: nat list) \<le>\<^sub>B replicate (Suc k) []"
proof -
  have eq: "(replicate (Suc k) ([] :: nat list))[0] = replicate k []"
    by (rule replicate_empty_expansion)
  have "replicate k ([] :: nat list) \<le>\<^sub>B (replicate (Suc k) [])[0]"
    using eq bms_le_refl by simp
  thus ?thesis using bms_le_step by blast
qed

lemma replicate_chain_le_aux:
  shows "replicate j ([] :: nat list) \<le>\<^sub>B replicate (j + d) []"
proof (induct d)
  case 0 show ?case using bms_le_refl by simp
next
  case (Suc d)
  have step: "replicate (j + d) ([] :: nat list) \<le>\<^sub>B replicate (j + Suc d) []"
  proof -
    have "replicate (j + d) ([] :: nat list) \<le>\<^sub>B replicate (Suc (j + d)) []"
      by (rule replicate_step_le_B)
    moreover have "Suc (j + d) = j + Suc d" by simp
    ultimately show ?thesis by metis
  qed
  show ?case using Suc step bms_le_trans by blast
qed

lemma replicate_chain_le:
  assumes "j \<le> k"
  shows "replicate j ([] :: nat list) \<le>\<^sub>B replicate k []"
proof -
  obtain d where k_eq: "k = j + d" using assms le_Suc_ex by blast
  show ?thesis using replicate_chain_le_aux k_eq by simp
qed

lemma replicate_le_seed_1:
  shows "replicate j ([] :: nat list) \<le>\<^sub>B seed 1"
proof -
  have "replicate (Suc j) ([] :: nat list) = (seed 1)[j]"
    using seed_1_expansion by simp
  hence step1: "replicate (Suc j) ([] :: nat list) \<le>\<^sub>B seed 1"
    using bms_le_refl bms_le_step by metis
  have step2: "replicate j ([] :: nat list) \<le>\<^sub>B replicate (Suc j) []"
    by (rule replicate_step_le_B)
  show ?thesis using step1 step2 bms_le_trans by blast
qed

lemma seed_1_descendants_total:
  assumes "A \<le>\<^sub>B seed 1" "A' \<le>\<^sub>B seed 1"
  shows "A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A"
proof -
  have hA: "A = seed 1 \<or> (\<exists>j. A = replicate j ([] :: nat list))"
    by (rule descendants_of_seed_1[OF assms(1)])
  have hA': "A' = seed 1 \<or> (\<exists>j'. A' = replicate j' ([] :: nat list))"
    by (rule descendants_of_seed_1[OF assms(2)])
  show ?thesis
  proof (cases "A = seed 1")
    case True
    hence "A' \<le>\<^sub>B A" using assms(2) by simp
    thus ?thesis by simp
  next
    case A_rep: False
    show ?thesis
    proof (cases "A' = seed 1")
      case True
      hence "A \<le>\<^sub>B A'" using assms(1) by simp
      thus ?thesis by simp
    next
      case A'_rep: False
      obtain j where j_eq: "A = replicate j ([] :: nat list)"
        using hA A_rep by blast
      obtain j' where j'_eq: "A' = replicate j' ([] :: nat list)"
        using hA' A'_rep by blast
      consider (le) "j \<le> j'" | (ge) "j' \<le> j" by linarith
      thus ?thesis
      proof cases
        case le
        hence "replicate j ([] :: nat list) \<le>\<^sub>B replicate j' []"
          by (rule replicate_chain_le)
        thus ?thesis using j_eq j'_eq by simp
      next
        case ge
        hence "replicate j' ([] :: nat list) \<le>\<^sub>B replicate j []"
          by (rule replicate_chain_le)
        thus ?thesis using j_eq j'_eq by simp
      qed
    qed
  qed
qed

text \<open>
  Seed-tree totality (open in general): every two descendants of
  \<open>seed N\<close> are \<open>\<le>\<^sub>B\<close>-comparable.  This is the strict-totality
  content that Hunter establishes inside the proof of Lemma 2.3 by
  closure-under-expansion induction; with @{thm seed_chain_le_B_expansion}
  (the chain along a single seed) and Hunter's "(\<gamma>)" cross-step
  lemma the argument decomposes into iterative comparisons within
  each \<open>(seed N)[k]\<close>-subtree.

  Note: in our (strip-faithful) reading some of Hunter's intermediate
  identities require the workarounds documented in \<open>bug.md\<close>
  (entry B-1).
\<close>

lemma seed_0_descendants_total:
  assumes "A \<le>\<^sub>B seed 0" "A' \<le>\<^sub>B seed 0"
  shows "A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A"
proof -
  have hA: "A = seed 0 \<or> A = [[]] \<or> A = []"
    by (rule descendants_of_seed_0[OF assms(1)])
  have hA': "A' = seed 0 \<or> A' = [[]] \<or> A' = []"
    by (rule descendants_of_seed_0[OF assms(2)])
  \<comment> \<open>Both lie in the chain \<open>[] \<le>\<^sub>B [[]] \<le>\<^sub>B seed 0\<close>; enumerate.\<close>
  show ?thesis
  proof -
    have e_le_ec: "[] \<le>\<^sub>B ([[]] :: array)" by (rule empty_le_empty_col)
    have ec_le_s0: "[[]] \<le>\<^sub>B seed 0" by (rule empty_col_le_seed_0)
    have e_le_s0: "[] \<le>\<^sub>B seed 0" using e_le_ec ec_le_s0 bms_le_trans by blast
    from hA hA' show ?thesis
      using bms_le_refl e_le_ec ec_le_s0 e_le_s0 by metis
  qed
qed

text \<open>
  Strong induction on \<open>N\<close>: for the substantive case
  (\<open>N \<ge> 2\<close>, both \<open>A, A'\<close> strict descendants), we
  apply @{thm bms_lt_imp_le_expansion} to obtain \<open>k, k'\<close>
  with \<open>A \<le>\<^sub>B (seed N)[k]\<close> and
  \<open>A' \<le>\<^sub>B (seed N)[k']\<close>. WLOG \<open>k \<le> k'\<close>;
  @{thm seed_chain_le_B_expansion} gives both
  \<open>A, A' \<le>\<^sub>B (seed N)[k']\<close>. Cases on \<open>k'\<close>:
  \<open>k' = 0\<close> reduces to descendants of \<open>[[]]\<close>
  (@{thm descendants_of_empty_col}); \<open>k' = 1\<close> reduces to
  descendants of \<open>seed (N - 1)\<close> via
  @{thm seed_Suc_expand_one} and the IH at \<open>N - 1\<close>;
  \<open>k' \<ge> 2\<close> sorried.
\<close>

lemma seed_descendants_total_strong:
  shows "\<forall>A A'. A \<le>\<^sub>B seed N \<and> A' \<le>\<^sub>B seed N
                 \<longrightarrow> A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A"
proof (induct N rule: nat_less_induct)
  case (1 N)
  have IH: "\<And>M A A'. M < N \<Longrightarrow> A \<le>\<^sub>B seed M \<Longrightarrow> A' \<le>\<^sub>B seed M
              \<Longrightarrow> A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A"
    using 1 by blast
  show ?case
  proof (intro allI impI)
    fix A A' assume H: "A \<le>\<^sub>B seed N \<and> A' \<le>\<^sub>B seed N"
    have aH: "A \<le>\<^sub>B seed N" and a'H: "A' \<le>\<^sub>B seed N" using H by simp+
    show "A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A"
    proof (cases "A = seed N")
      case True
      hence "A' \<le>\<^sub>B A" using a'H by simp
      thus ?thesis by blast
    next
      case A_ne: False
      show ?thesis
      proof (cases "A' = seed N")
        case True
        hence "A \<le>\<^sub>B A'" using aH by simp
        thus ?thesis by blast
      next
        case A'_ne: False
        show ?thesis
        proof (cases "N \<le> 1")
          case True
          consider "N = 0" | "N = 1" using True by linarith
          thus ?thesis
          proof cases
            case 1
            have a1: "A \<le>\<^sub>B seed 0" using aH \<open>N = 0\<close> by simp
            have a2: "A' \<le>\<^sub>B seed 0" using a'H \<open>N = 0\<close> by simp
            show ?thesis by (rule seed_0_descendants_total[OF a1 a2])
          next
            case 2
            have a1: "A \<le>\<^sub>B seed 1" using aH \<open>N = 1\<close> by simp
            have a2: "A' \<le>\<^sub>B seed 1" using a'H \<open>N = 1\<close> by simp
            show ?thesis by (rule seed_1_descendants_total[OF a1 a2])
          qed
        next
          case False
          hence N_ge: "2 \<le> N" by simp
          then obtain N' where N_eq: "N = Suc N'" and N'_ge: "1 \<le> N'"
            by (cases N) auto
          have A_lt: "A <\<^sub>B seed N" using aH A_ne unfolding bms_lt_def by blast
          have A'_lt: "A' <\<^sub>B seed N" using a'H A'_ne unfolding bms_lt_def by blast
          obtain k where Ak: "A \<le>\<^sub>B (seed N)[k]"
            using bms_lt_imp_le_expansion[OF A_lt] by blast
          obtain k' where A'k': "A' \<le>\<^sub>B (seed N)[k']"
            using bms_lt_imp_le_expansion[OF A'_lt] by blast
          \<comment> \<open>WLOG \<open>k \<le> k'\<close> via case analysis (polymorphic in B, B').\<close>
          have key: "\<And>k k' B B'. k \<le> k' \<Longrightarrow> B \<le>\<^sub>B (seed N)[k]
                       \<Longrightarrow> B' \<le>\<^sub>B (seed N)[k']
                       \<Longrightarrow> B \<le>\<^sub>B B' \<or> B' \<le>\<^sub>B B"
          proof -
            fix k k' :: nat
            fix B B' :: array
            assume k_le: "k \<le> k'" and Bk: "B \<le>\<^sub>B (seed N)[k]"
                            and B'k': "B' \<le>\<^sub>B (seed N)[k']"
            have step: "(seed N)[k] \<le>\<^sub>B (seed N)[k']"
              using N_eq seed_chain_le_B_expansion k_le by simp
            have B_le_k': "B \<le>\<^sub>B (seed N)[k']"
              using Bk step bms_le_trans by blast
            show "B \<le>\<^sub>B B' \<or> B' \<le>\<^sub>B B"
            proof (cases k')
              case 0
              have empty_eq: "(seed N)[0] = [[]]" by (rule seed_expansion_zero)
              have B_le_e: "B \<le>\<^sub>B [[]]" using B_le_k' \<open>k' = 0\<close> empty_eq by simp
              have B'_le_e: "B' \<le>\<^sub>B [[]]" using B'k' \<open>k' = 0\<close> empty_eq by simp
              have B_in: "B = [[]] \<or> B = []"
                by (rule descendants_of_empty_col[OF B_le_e])
              have B'_in: "B' = [[]] \<or> B' = []"
                by (rule descendants_of_empty_col[OF B'_le_e])
              have e_le_ec: "[] \<le>\<^sub>B ([[]] :: array)" by (rule empty_le_empty_col)
              from B_in B'_in show ?thesis
                using e_le_ec bms_le_refl by metis
            next
              case (Suc k'')
              show ?thesis
              proof (cases k'')
                case 0
                have seed_eq: "(seed N)[1] = seed N'"
                  using N_eq seed_Suc_expand_one by simp
                have B_le_s: "B \<le>\<^sub>B seed N'"
                  using B_le_k' \<open>k' = Suc k''\<close> \<open>k'' = 0\<close> seed_eq by simp
                have B'_le_s: "B' \<le>\<^sub>B seed N'"
                  using B'k' \<open>k' = Suc k''\<close> \<open>k'' = 0\<close> seed_eq by simp
                show ?thesis using IH[OF _ B_le_s B'_le_s] N_eq by simp
              next
                case (Suc k''')
                show ?thesis sorry
              qed
            qed
          qed
          show ?thesis
          proof (cases "k \<le> k'")
            case True
            show ?thesis using key[OF True Ak A'k'] .
          next
            case False
            hence k'_le: "k' \<le> k" by linarith
            have "A' \<le>\<^sub>B A \<or> A \<le>\<^sub>B A'" using key[OF k'_le A'k' Ak] .
            thus ?thesis by blast
          qed
        qed
      qed
    qed
  qed
qed

corollary seed_descendants_total:
  assumes "A \<le>\<^sub>B seed N" "A' \<le>\<^sub>B seed N"
  shows "A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A"
  using seed_descendants_total_strong assms by blast

text \<open>
  Descendants of any BMS array are pairwise lex-comparable
  (= \<open>=\<close> or \<open><\<^sub>l\<^sub>e\<^sub>x\<close> in either direction).
  Combines @{thm bms_le_implies_lex} (one-direction conversion)
  with @{thm arr_lex_total} (total order on arrays).
  Helper purpose: provides the lex-side totality input needed
  to attack the k' \<ge> 2 sub-case of \<open>seed_descendants_total_strong\<close>
  (the missing direction would convert lex back to \<open>\<le>\<^sub>B\<close>).
\<close>

lemma bms_descendants_lex_total:
  assumes "C \<in> BMS" "B \<le>\<^sub>B C" "B' \<le>\<^sub>B C"
  shows "B = B' \<or> B <\<^sub>l\<^sub>e\<^sub>x B' \<or> B' <\<^sub>l\<^sub>e\<^sub>x B"
  using arr_lex_total by blast

text \<open>
  Every descendant of \<open>seed N\<close> is \<open>=\<close> or \<open><\<^sub>l\<^sub>e\<^sub>x\<close>
  \<open>seed N\<close> (via @{thm bms_le_implies_lex} applied at
  \<open>seed N \<in> BMS\<close>). Helper purpose: provides the lex-anchor
  characterization for the k' \<ge> 2 sub-case of
  \<open>seed_descendants_total_strong\<close>.
\<close>

lemma descendant_of_seed_lex_le:
  assumes "B \<le>\<^sub>B seed N"
  shows "B = seed N \<or> B <\<^sub>l\<^sub>e\<^sub>x seed N"
  using bms_le_implies_lex[OF seed_in_BMS assms] .

text \<open>
  \<open>seed_lex_implies_le_B\<close> reduces to totality via
  @{thm bms_le_implies_lex}: if \<open>A' \<le>\<^sub>B A\<close>, then either
  \<open>A' = A\<close> or \<open>A' <\<^sub>l\<^sub>e\<^sub>x A\<close>, both contradicting
  \<open>A <\<^sub>l\<^sub>e\<^sub>x A'\<close>.
\<close>

lemma seed_lex_implies_le_B:
  assumes "A \<le>\<^sub>B seed N" "A' \<le>\<^sub>B seed N" "A <\<^sub>l\<^sub>e\<^sub>x A'"
  shows "A \<le>\<^sub>B A'"
proof -
  have seed_BMS: "seed N \<in> BMS" by (rule seed_in_BMS)
  have A_BMS: "A \<in> BMS" using bms_le_in_BMS[OF assms(1) seed_BMS] .
  have tot: "A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A"
    by (rule seed_descendants_total[OF assms(1,2)])
  show ?thesis
  proof (cases "A \<le>\<^sub>B A'")
    case True thus ?thesis .
  next
    case False
    hence A'_le_A: "A' \<le>\<^sub>B A" using tot by blast
    from bms_le_implies_lex[OF A_BMS A'_le_A]
    consider "A' = A" | "A' <\<^sub>l\<^sub>e\<^sub>x A" by blast
    thus ?thesis
    proof cases
      case 1
      thus ?thesis using assms(3) arr_lex_irrefl by auto
    next
      case 2
      hence "A <\<^sub>l\<^sub>e\<^sub>x A" using assms(3) arr_lex_trans by metis
      thus ?thesis using arr_lex_irrefl by simp
    qed
  qed
qed

lemma lex_implies_le_B:
  assumes "A \<in> BMS" "A' \<in> BMS" "A <\<^sub>l\<^sub>e\<^sub>x A'"
  shows "A \<le>\<^sub>B A'"
proof -
  obtain M where M: "A \<le>\<^sub>B seed M" "A' \<le>\<^sub>B seed M"
    using bms_pair_below_seed[OF assms(1,2)] by blast
  show ?thesis using seed_lex_implies_le_B[OF M(1) M(2) assms(3)] .
qed

text \<open>
  Lemma 2.3 follows: by @{thm arr_lex_total} for any \<open>A, A' \<in> BMS\<close>
  one of \<open>A = A'\<close>, \<open>A <\<^sub>l\<^sub>e\<^sub>x A'\<close>, \<open>A' <\<^sub>l\<^sub>e\<^sub>x A\<close> holds.
  In each case we conclude \<open>A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A\<close> using
  reflexivity or @{thm lex_implies_le_B}.
\<close>

lemma lemma_2_3:
  shows "(\<forall>A \<in> BMS. \<forall>A' \<in> BMS. A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A)"
proof (intro ballI)
  fix A A'
  assume A_in: "A \<in> BMS" and A'_in: "A' \<in> BMS"
  consider "A = A'" | "A <\<^sub>l\<^sub>e\<^sub>x A'" | "A' <\<^sub>l\<^sub>e\<^sub>x A"
    using arr_lex_total by blast
  thus "A \<le>\<^sub>B A' \<or> A' \<le>\<^sub>B A"
  proof cases
    case 1
    thus ?thesis using bms_le_refl by simp
  next
    case 2
    hence "A \<le>\<^sub>B A'" using lex_implies_le_B[OF A_in A'_in] by simp
    thus ?thesis by simp
  next
    case 3
    hence "A' \<le>\<^sub>B A" using lex_implies_le_B[OF A'_in A_in] by simp
    thus ?thesis by simp
  qed
qed


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
  have le: "A' \<le>\<^sub>B A" using lex_implies_le_B[OF assms(2,1,3)] .
  have ne: "A' \<noteq> A" using assms(3) arr_lex_irrefl by auto
  show ?thesis using le ne unfolding bms_lt_def by blast
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


end
