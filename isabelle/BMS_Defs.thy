(*
  BMS_Defs.thy

  Faithful formalization of Definition 1.1 of
    Rachel Hunter, "Well-Orderedness of the Bashicu Matrix System"
    (arXiv:2307.04606v3, 2024).

  The definitions below mirror the paper word-for-word; we do not
  rewrite, simplify, or "improve" any of them.
*)

theory BMS_Defs
  imports Main
begin

section \<open>Arrays (Definition 1.1)\<close>

text \<open>
  Quote (Definition 1.1, paraphrased to fit Isabelle types):
    ``An array is a sequence of equal-length sequences of natural
    numbers, i.e. an element of \<open>(\<nat>\<^sup>n)\<^sup>m\<close> for some
    \<open>n, m \<in> \<nat>\<close>. For every array \<open>A \<in> (\<nat>\<^sup>n)\<^sup>m\<close>, the
    columns of \<open>A\<close> are its elements, and for each \<open>n' < n\<close>,
    the \<open>n'\<close>-th row of \<open>A\<close> is the sequence of length \<open>m\<close>
    such that for each \<open>m' < m\<close>, the \<open>m'\<close>-th element of the
    \<open>n'\<close>-th row is the \<open>n'\<close>-th element of the \<open>m'\<close>-th column.
    We will denote concatenation of sequences by \<open>+\<close>.''
\<close>

type_synonym column = "nat list"
type_synonym array  = "column list"

definition is_array :: "array \<Rightarrow> bool" where
  "is_array A \<longleftrightarrow> (\<forall>c \<in> set A. length c = (if A = [] then 0 else length (hd A)))"

abbreviation height :: "array \<Rightarrow> nat" where
  "height A \<equiv> (if A = [] then 0 else length (hd A))"

abbreviation arr_len :: "array \<Rightarrow> nat" where
  "arr_len A \<equiv> length A"

text \<open>The \<open>m\<close>-th element of the \<open>i\<close>-th column of A.\<close>
definition elem :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "elem A i m = (A ! i) ! m"


section \<open>m-parent and m-ancestor (Definition 1.1, continued)\<close>

text \<open>
  Quote:
    ``Let \<open>A\<close> be any array and \<open>n\<close> be any natural number.
    For every \<open>m\<close> smaller than the length of \<open>A\<close>'s columns and
    every \<open>i\<close> smaller than the length of \<open>A\<close>, the \<open>m\<close>-parent
    of the \<open>i\<close>-th column is the last column before it whose
    \<open>m\<close>-th element is smaller than the \<open>m\<close>-th element of the
    \<open>i\<close>-th column, and which is an \<open>(m-1)\<close>-ancestor of the
    \<open>i\<close>-th column if \<open>m > 0\<close>, if such a column exists. If no
    such column exists, then the \<open>i\<close>-th column does not have an
    \<open>m\<close>-parent. The \<open>m\<close>-ancestors (also called strict
    \<open>m\<close>-ancestors) of a column are its \<open>m\<close>-parent and the
    \<open>m\<close>-ancestors of its parent. The non-strict \<open>m\<close>-ancestors of
    a column are the column itself and its \<open>m\<close>-ancestors.''

  We render this as a mutually recursive pair (\<open>m_parent\<close>,
  \<open>m_ancestor\<close>). Termination is by the lexicographic measure
    \<open>(m, i)\<close> with the column index \<open>i\<close> strictly decreasing inside
  \<open>m_ancestor\<close>'s self-call (because \<open>m_parent A m i = Some p\<close>
  forces \<open>p < i\<close>) and \<open>m\<close> strictly decreasing on the call from
  \<open>m_parent A (Suc m) _\<close> to \<open>m_ancestor A m _ _\<close>.
\<close>

function (sequential)
  m_parent   :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" and
  m_ancestor :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "m_parent A 0 i =
     (let cands = [j \<leftarrow> [0..<i]. elem A j 0 < elem A i 0]
      in if cands = [] then None else Some (last cands))"
| "m_parent A (Suc m) i =
     (let cands = [j \<leftarrow> [0..<i].
                     elem A j (Suc m) < elem A i (Suc m)
                   \<and> m_ancestor A m i j]
      in if cands = [] then None else Some (last cands))"
| "m_ancestor A m i j \<longleftrightarrow>
     (case m_parent A m i of
        None   \<Rightarrow> False
      | Some p \<Rightarrow> p = j \<or> m_ancestor A m p j)"
  by pat_completeness auto

text \<open>
  Termination measure: triple \<open>(m, i, tag)\<close> where \<open>tag = 0\<close> for
  \<open>m_parent\<close> and \<open>tag = 1\<close> for \<open>m_ancestor\<close>; ordered
  lexicographically. The recursive calls decrease as follows:
    \<bullet> \<open>m_parent (Suc m) i \<rightarrow> m_ancestor m i j\<close>:
      first component strictly decreases.
    \<bullet> \<open>m_ancestor m i j \<rightarrow> m_parent m i\<close>:
      first two components equal, third (\<open>1 \<rightarrow> 0\<close>) decreases.
    \<bullet> \<open>m_ancestor m i j \<rightarrow> m_ancestor m p j\<close> with \<open>p < i\<close>
      (because \<open>m_parent A m i = Some p\<close> only with \<open>p < i\<close>):
      first equal, second strictly decreases.

  Discharging this in Isabelle requires the auxiliary fact
  ``\<open>m_parent A m i = Some p \<Longrightarrow> p < i\<close>'', which follows
  immediately from the \<open>cands \<subseteq> [0..<i]\<close> filter.
\<close>

lemma m_parent_lt_aux:
  "cands = [j \<leftarrow> [0..<i]. P j] \<Longrightarrow> cands \<noteq> [] \<Longrightarrow> last cands < i"
proof -
  assume *: "cands = [j \<leftarrow> [0..<i]. P j]" and **: "cands \<noteq> []"
  have "set cands \<subseteq> set [0..<i]" using * by auto
  hence "set cands \<subseteq> {0..<i}" by simp
  moreover have "last cands \<in> set cands" using ** by (simp add: last_in_set)
  ultimately show "last cands < i" by auto
qed

termination
  sorry  \<comment> \<open>The termination obligation requires proving
            \<open>m_parent A m i = Some p \<Longrightarrow> p < i\<close> within the
            termination proof, which is a meta-property of the
            function being defined. The natural workaround is to
            prove it after the fact using the function's induction
            principle, then close termination retroactively, but
            this requires either \<open>partial_function\<close> reformulation
            or an explicit dom-induction. Left as TODO.\<close>


section \<open>Non-strict ancestry\<close>

definition non_strict_ancestor :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "non_strict_ancestor A m i j \<longleftrightarrow> i = j \<or> m_ancestor A m i j"


section \<open>Expansion \<open>A[n]\<close> (Definition 1.1, continued)\<close>

text \<open>
  Quote:
    ``If \<open>A\<close> is empty, then the expansion of \<open>A\<close> at \<open>n\<close> is
    \<open>A[n] = A\<close>. Otherwise let \<open>C\<close> be the last element of \<open>A\<close>
    and let \<open>m\<^sub>0\<close> be maximal such that \<open>C\<close> has an
    \<open>m\<^sub>0\<close>-parent, if such an \<open>m\<^sub>0\<close> exists, otherwise
    \<open>m\<^sub>0\<close> is undefined. Let arrays \<open>G, B\<^sub>0, B\<^sub>1, ..., B\<^sub>n\<close>
    be such that:
      \<bullet> \<open>A = G + B\<^sub>0 + (C)\<close>.
      \<bullet> The first element of \<open>B\<^sub>0\<close> is the \<open>m\<^sub>0\<close>-parent of
        \<open>C\<close> if \<open>m\<^sub>0\<close> is defined and otherwise \<open>B\<^sub>0\<close> is
        empty.
      \<bullet> For each \<open>D\<close> in \<open>B\<^sub>0\<close> and \<open>m < m\<^sub>0\<close>, if the
        first column in \<open>B\<^sub>0\<close> is \<open>D\<close> or an \<open>m\<close>-th ancestor
        of \<open>D\<close>, then the \<open>m\<close>-th element of \<open>D\<close> is said to
        ascend.
      \<bullet> \<open>B_i\<close> is a copy of \<open>B\<^sub>0\<close>, but for each ascending
        element of each column in \<open>B\<^sub>0\<close>, its copy in \<open>B_i\<close>
        is increased by
        \<open>i \<cdot> ((m-th element of C) - (m-th element of the first column in B\<^sub>0))\<close>,
        where \<open>m\<close> is the index of the row in which that element is.
    Then the expansion \<open>A[n]\<close> of \<open>A\<close> at \<open>n\<close> is
    \<open>G + B\<^sub>0 + B\<^sub>1 + ... + B_n\<close>, with all rows of zeroes at
    the bottom removed.''

  We will define \<open>expansion\<close> by case-splitting on whether
  \<open>m\<^sub>0\<close> is defined; both cases are spelled out below as
  placeholders to be filled in directly from the quoted text without
  modification.
\<close>

text \<open>
  Index of the last column of a non-empty array.
\<close>
abbreviation last_col_idx :: "array \<Rightarrow> nat" where
  "last_col_idx A \<equiv> length A - 1"

text \<open>
  ``\<open>m\<^sub>0\<close> maximal such that \<open>C\<close> has an \<open>m\<^sub>0\<close>-parent.''
  Returns \<open>None\<close> if \<open>A\<close> is empty or no such \<open>m\<^sub>0\<close> exists.
\<close>
definition max_parent_level :: "array \<Rightarrow> nat option" where
  "max_parent_level A =
     (if A = [] then None else
        let C = last_col_idx A; H = height A;
            ms = [m \<leftarrow> [0..<H]. m_parent A m C \<noteq> None]
        in if ms = [] then None else Some (Max (set ms)))"

text \<open>
  Index in \<open>A\<close> of the first column of \<open>B\<^sub>0\<close>, equivalently the
  \<open>m\<^sub>0\<close>-parent of the last column \<open>C\<close>. \<open>None\<close> if \<open>m\<^sub>0\<close>
  is undefined; in that case \<open>B\<^sub>0\<close> is empty.
\<close>
definition b0_start :: "array \<Rightarrow> nat option" where
  "b0_start A =
     (case max_parent_level A of
        None     \<Rightarrow> None
      | Some m\<^sub>0  \<Rightarrow> m_parent A m\<^sub>0 (last_col_idx A))"

text \<open>
  The blocks \<open>G\<close>, \<open>B\<^sub>0\<close>, and the singleton \<open>(C)\<close> from the
  decomposition \<open>A = G + B\<^sub>0 + (C)\<close>.
\<close>
definition G_block :: "array \<Rightarrow> array" where
  "G_block A =
     (case b0_start A of
        None   \<Rightarrow> butlast A    \<comment> \<open>\<open>B\<^sub>0\<close> empty: \<open>G = A \<setminus> (C)\<close>\<close>
      | Some s \<Rightarrow> take s A)"

definition B0_block :: "array \<Rightarrow> array" where
  "B0_block A =
     (case b0_start A of
        None   \<Rightarrow> []
      | Some s \<Rightarrow> take (last_col_idx A - s) (drop s A))"

abbreviation last_col :: "array \<Rightarrow> column" where
  "last_col A \<equiv> A ! last_col_idx A"

text \<open>
  ``For each \<open>D\<close> in \<open>B\<^sub>0\<close> and \<open>m < m\<^sub>0\<close>, if the first
  column in \<open>B\<^sub>0\<close> is \<open>D\<close> or an \<open>m\<close>-th ancestor of \<open>D\<close>,
  then the \<open>m\<close>-th element of \<open>D\<close> is said to ascend.''

  Predicate \<open>ascends A d_idx m\<close>: in array \<open>A\<close>, the \<open>m\<close>-th
  element of the column whose index in \<open>B\<^sub>0\<close> is \<open>d_idx\<close>
  ascends. (We pass the \<open>B\<^sub>0\<close>-local index so the predicate
  works directly on the original array.)
\<close>
definition ascends :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "ascends A d_idx m \<longleftrightarrow>
     (case b0_start A of
        None    \<Rightarrow> False
      | Some s  \<Rightarrow>
          (case max_parent_level A of
             None     \<Rightarrow> False
           | Some m\<^sub>0  \<Rightarrow>
               m < m\<^sub>0 \<and> non_strict_ancestor A m (s + d_idx) s))"

text \<open>
  ``\<open>B_i\<close> is a copy of \<open>B\<^sub>0\<close>, but for each ascending element
  of each column in \<open>B\<^sub>0\<close>, its copy in \<open>B_i\<close> is increased by
  \<open>i \<cdot> ((m-th element of C) - (m-th element of the first column in B\<^sub>0))\<close>,
  where \<open>m\<close> is the index of the row in which that element is.''

  \<open>delta A m\<close> = \<open>(m\<close>-th element of \<open>C)\<close> -- \<open>(m\<close>-th element of
  the first column in \<open>B\<^sub>0)\<close>.
\<close>
definition delta :: "array \<Rightarrow> nat \<Rightarrow> nat" where
  "delta A m =
     (case b0_start A of
        None   \<Rightarrow> 0
      | Some s \<Rightarrow> elem A (last_col_idx A) m - elem A s m)"

text \<open>
  Bumping a single column of \<open>B\<^sub>0\<close>: index \<open>d_idx\<close> in
  \<open>B\<^sub>0\<close>, multiplier \<open>i\<close>.
\<close>
definition bump_col :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> column" where
  "bump_col A d_idx i =
     (let s = (case b0_start A of None \<Rightarrow> 0 | Some s \<Rightarrow> s);
          c = A ! (s + d_idx)
      in map (\<lambda>m. c ! m + (if ascends A d_idx m then i * delta A m else 0))
             [0..<length c])"

text \<open>The \<open>i\<close>-th block \<open>B_i\<close>.\<close>
definition Bi_block :: "array \<Rightarrow> nat \<Rightarrow> array" where
  "Bi_block A i =
     (let B0 = B0_block A
      in map (\<lambda>d. bump_col A d i) [0..<length B0])"

text \<open>Concatenation of \<open>B\<^sub>0, B\<^sub>1, ..., B_n\<close>.\<close>
definition Bs_concat :: "array \<Rightarrow> nat \<Rightarrow> array" where
  "Bs_concat A n = concat (map (Bi_block A) [0..<Suc n])"

text \<open>
  ``...with all rows of zeroes at the bottom removed.''  We strip
  trailing rows that are uniformly zero across all columns.
\<close>
definition strip_zero_rows :: "array \<Rightarrow> array" where
  "strip_zero_rows A =
     (if A = [] then A else
        let H = height A;
            keep = (LEAST h. h \<le> H \<and> (\<forall>m. h \<le> m \<and> m < H \<longrightarrow>
                                          (\<forall>c \<in> set A. c ! m = 0)))
        in map (\<lambda>c. take keep c) A)"

definition expansion :: "array \<Rightarrow> nat \<Rightarrow> array" ("_[_]" [80,0] 80) where
  "A[n] =
     (if A = [] then A
      else strip_zero_rows (G_block A @ Bs_concat A n))"


text \<open>
  Auxiliary computations for the \<open>i = 0\<close> case of the expansion.
  When \<open>i = 0\<close>, the term \<open>i \<cdot> delta A m\<close> vanishes, so each
  \<open>bump_col A d 0\<close> just returns the corresponding column of \<open>A\<close>
  unchanged. Consequently \<open>Bi_block A 0 = B0_block A\<close> and
  \<open>Bs_concat A 0 = B0_block A\<close>.
\<close>

lemma bump_col_zero:
  assumes s_def: "s = (case b0_start A of None \<Rightarrow> 0 | Some s \<Rightarrow> s)"
  shows "bump_col A d 0 = A ! (s + d)"
proof -
  let ?c = "A ! (s + d)"
  have "bump_col A d 0 = map (\<lambda>m. ?c ! m + 0) [0..<length ?c]"
    unfolding bump_col_def Let_def using s_def by simp
  also have "\<dots> = map ((!) ?c) [0..<length ?c]" by simp
  also have "\<dots> = ?c" by (simp add: map_nth)
  finally show ?thesis .
qed

lemma map_nth_offset:
  assumes "s + n \<le> length xs"
  shows "map (\<lambda>d. xs ! (s + d)) [0..<n] = take n (drop s xs)"
proof (rule nth_equalityI)
  show "length (map (\<lambda>d. xs ! (s + d)) [0..<n]) = length (take n (drop s xs))"
    using assms by simp
next
  fix i assume "i < length (map (\<lambda>d. xs ! (s + d)) [0..<n])"
  hence "i < n" by simp
  thus "map (\<lambda>d. xs ! (s + d)) [0..<n] ! i = take n (drop s xs) ! i"
    using assms by simp
qed

text \<open>
  An m-parent of column \<open>i\<close> is always at an earlier position.
\<close>
lemma m_parent_lt:
  "m_parent A m i = Some p \<Longrightarrow> p < i"
  by (cases m)
     (auto simp: Let_def split: if_split_asm intro: m_parent_lt_aux)

lemma b0_start_lt:
  assumes "b0_start A = Some s" "A \<noteq> []"
  shows "s < last_col_idx A"
proof -
  from assms obtain m\<^sub>0 where
    "max_parent_level A = Some m\<^sub>0"
    "m_parent A m\<^sub>0 (last_col_idx A) = Some s"
    unfolding b0_start_def by (auto split: option.splits)
  thus ?thesis using m_parent_lt by blast
qed

lemma b0_start_le_length:
  assumes "b0_start A = Some s" "A \<noteq> []"
  shows "s < length A"
  using b0_start_lt[OF assms] assms(2) by (cases A) auto

lemma Bi_block_zero:
  assumes "A \<noteq> []"
  shows "Bi_block A 0 = B0_block A"
proof (cases "b0_start A")
  case None
  hence "B0_block A = []" by (simp add: B0_block_def)
  thus ?thesis using None by (simp add: Bi_block_def Let_def)
next
  case (Some s)
  hence b0_def: "B0_block A = take (last_col_idx A - s) (drop s A)"
    by (simp add: B0_block_def)
  have s_lt: "s < length A" using b0_start_le_length[OF Some assms] .
  have eq_col: "bump_col A d 0 = A ! (s + d)" for d
    using bump_col_zero[where A = A and d = d and s = s] Some by simp
  have len_b0_le: "s + length (B0_block A) \<le> length A"
    using b0_def s_lt by simp
  have "Bi_block A 0 = map (\<lambda>d. A ! (s + d)) [0..<length (B0_block A)]"
    unfolding Bi_block_def Let_def using eq_col by simp
  also have "\<dots> = take (length (B0_block A)) (drop s A)"
    by (rule map_nth_offset[OF len_b0_le])
  also have "\<dots> = B0_block A" using b0_def by simp
  finally show ?thesis .
qed

lemma Bs_concat_zero: "A \<noteq> [] \<Longrightarrow> Bs_concat A 0 = B0_block A"
  unfolding Bs_concat_def using Bi_block_zero by simp

text \<open>
  \<open>G_block A @ B0_block A = butlast A\<close> for any non-empty array.
\<close>

lemma G_block_B0_block:
  assumes "A \<noteq> []"
  shows "G_block A @ B0_block A = butlast A"
proof (cases "b0_start A")
  case None
  thus ?thesis using assms by (simp add: G_block_def B0_block_def)
next
  case (Some s)
  have s_lt: "s < length A" using b0_start_le_length[OF Some assms] .
  have last_lt: "last_col_idx A < length A" using assms by (cases A) auto
  have s_lt_last: "s < last_col_idx A" using b0_start_lt[OF Some assms] .
  have G_eq: "G_block A = take s A" using Some by (simp add: G_block_def)
  have B0_eq: "B0_block A = take (last_col_idx A - s) (drop s A)"
    using Some by (simp add: B0_block_def)
  have "G_block A @ B0_block A = take s A @ take (last_col_idx A - s) (drop s A)"
    using G_eq B0_eq by simp
  also have "\<dots> = take (s + (last_col_idx A - s)) A"
    by (simp add: take_add)
  also have "\<dots> = take (last_col_idx A) A"
    using s_lt_last by simp
  also have "\<dots> = butlast A"
    using assms by (simp add: butlast_conv_take)
  finally show ?thesis .
qed

text \<open>
  \<open>A[0]\<close> equals \<open>butlast A\<close> after stripping trailing zero rows
  (Definition 1.1, expansion).
\<close>

lemma expansion_zero_eq:
  assumes "A \<noteq> []"
  shows "A[0] = strip_zero_rows (butlast A)"
  unfolding expansion_def
  using assms Bs_concat_zero[OF assms] G_block_B0_block[OF assms]
  by simp

text \<open>
  When \<open>m\<^sub>0\<close> is undefined (\<open>b0_start A = None\<close>), the blocks
  \<open>B_i\<close> are all empty for every \<open>i\<close>; consequently the expansion
  \<open>A[n]\<close> does not depend on \<open>n\<close>, and equals \<open>A[0]\<close>.
\<close>

lemma Bi_block_no_b0:
  assumes "b0_start A = None"
  shows "Bi_block A i = []"
proof -
  have "B0_block A = []" using assms by (simp add: B0_block_def)
  thus ?thesis by (simp add: Bi_block_def Let_def)
qed

lemma Bs_concat_no_b0:
  assumes "b0_start A = None"
  shows "Bs_concat A n = []"
  unfolding Bs_concat_def
  using assms Bi_block_no_b0 by simp

lemma expansion_no_b0_eq_zero:
  fixes A :: array
  assumes "A \<noteq> []" "b0_start A = None"
  shows "A[n] = A[0]"
proof -
  have "A[n] = strip_zero_rows (G_block A @ Bs_concat A n)"
    unfolding expansion_def using assms(1) by simp
  also have "\<dots> = strip_zero_rows (G_block A @ [])"
    using Bs_concat_no_b0[OF assms(2)] by simp
  also have "\<dots> = strip_zero_rows (G_block A)" by simp
  also have "\<dots> = strip_zero_rows (G_block A @ B0_block A)"
    using assms(2) by (simp add: B0_block_def)
  also have "\<dots> = strip_zero_rows (G_block A @ Bs_concat A 0)"
    using Bs_concat_zero[OF assms(1)] by simp
  also have "\<dots> = A[0]"
    unfolding expansion_def using assms(1) by simp
  finally show ?thesis .
qed


section \<open>The set BMS (Definition 1.1, last paragraph)\<close>

text \<open>
  Quote:
    ``BMS is the closure of
      \<open>{((0,0,...,0,0), (1,1,...,1,1)) : n \<in> \<nat>}\<close>
    under expansion at each natural number, ordered by the
    \<open>\<subseteq>\<close>-minimal partial order such that \<open>A[n] \<le> A\<close> for each
    \<open>n \<in> \<nat>\<close> and \<open>A \<in> BMS\<close>. Here, a partial order \<open>\<le>\<close> is
    the set of pairs \<open>(x, y)\<close> such that \<open>x \<le> y\<close>.''
\<close>

definition seed :: "nat \<Rightarrow> array" where
  "seed n = [replicate n 0, replicate n 1]"

lemma length_seed: "length (seed n) = 2"
  by (simp add: seed_def)

lemma height_seed: "height (seed n) = n"
  by (simp add: seed_def)

lemma seed_nonempty: "seed n \<noteq> []"
  by (simp add: seed_def)

lemma seed_nth0: "(seed n) ! 0 = replicate n 0"
  by (simp add: seed_def)

lemma seed_nth1: "(seed n) ! 1 = replicate n 1"
  by (simp add: seed_def)

lemma elem_seed_0: "m < n \<Longrightarrow> elem (seed n) 0 m = 0"
  unfolding elem_def seed_def by simp

lemma elem_seed_1: "m < n \<Longrightarrow> elem (seed n) 1 m = 1"
  unfolding elem_def seed_def by simp

lemma m_parent_seed_zero:
  assumes "0 < n"
  shows "m_parent (seed n) 0 1 = Some 0"
proof -
  have "[j \<leftarrow> [0..<1]. elem (seed n) j 0 < elem (seed n) 1 0] = [0]"
    using assms unfolding elem_def seed_def by simp
  thus ?thesis by (simp add: Let_def)
qed

lemma m_ancestor_seed_zero:
  assumes "0 < n"
  shows "m_ancestor (seed n) 0 1 0"
  using m_parent_seed_zero[OF assms]
  by simp

lemma m_parent_seed_succ:
  assumes "m < n"
  shows "m_parent (seed n) m 1 = Some 0 \<and> m_ancestor (seed n) m 1 0"
  using assms
proof (induct m)
  case 0
  show ?case using m_parent_seed_zero[OF \<open>0 < n\<close>] m_ancestor_seed_zero[OF \<open>0 < n\<close>]
    by simp
next
  case (Suc m)
  hence "m < n" by simp
  with Suc.hyps have anc: "m_ancestor (seed n) m 1 0" by simp
  have lt: "elem (seed n) 0 (Suc m) < elem (seed n) 1 (Suc m)"
    using \<open>Suc m < n\<close> unfolding elem_def seed_def by simp
  have "[j \<leftarrow> [0..<1]. elem (seed n) j (Suc m) < elem (seed n) 1 (Suc m)
                       \<and> m_ancestor (seed n) m 1 j] = [0]"
    using lt anc by simp
  hence par: "m_parent (seed n) (Suc m) 1 = Some 0"
    by (simp add: Let_def)
  hence "m_ancestor (seed n) (Suc m) 1 0" by simp
  thus ?case using par by simp
qed

lemma max_parent_level_seed:
  assumes "0 < n"
  shows "max_parent_level (seed n) = Some (n - 1)"
proof -
  have last_idx: "last_col_idx (seed n) = 1" by (simp add: length_seed)
  have height_eq: "height (seed n) = n" by (rule height_seed)
  have "[m \<leftarrow> [0..<n]. m_parent (seed n) m 1 \<noteq> None] = [0..<n]"
    using m_parent_seed_succ by (simp add: filter_True)
  hence ms_eq: "[m \<leftarrow> [0..<height (seed n)]. m_parent (seed n) m (last_col_idx (seed n)) \<noteq> None] = [0..<n]"
    using last_idx height_eq by simp
  have "max_parent_level (seed n) = Some (Max (set [0..<n]))"
    using assms ms_eq seed_nonempty
    unfolding max_parent_level_def
    by (simp add: Let_def)
  also have "Max (set [0..<n]) = n - 1"
  proof -
    have "Max {0..<n} = n - 1"
      using assms
      by (intro Max_eqI) auto
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma b0_start_seed:
  assumes "0 < n"
  shows "b0_start (seed n) = Some 0"
proof -
  have "max_parent_level (seed n) = Some (n - 1)"
    using max_parent_level_seed[OF assms] .
  moreover have "m_parent (seed n) (n - 1) (last_col_idx (seed n)) = Some 0"
    using m_parent_seed_succ[where m = "n - 1" and n = n] assms
    by (simp add: length_seed)
  ultimately show ?thesis
    unfolding b0_start_def by simp
qed

lemma ascends_seed_succ:
  assumes "m < n"
  shows "ascends (seed (Suc n)) 0 m"
proof -
  have b0: "b0_start (seed (Suc n)) = Some 0" using b0_start_seed by simp
  have mp: "max_parent_level (seed (Suc n)) = Some n"
    using max_parent_level_seed[where n = "Suc n"] by simp
  have nsa: "non_strict_ancestor (seed (Suc n)) m 0 0"
    by (simp add: non_strict_ancestor_def)
  show ?thesis
    unfolding ascends_def using b0 mp assms nsa by simp
qed

lemma not_ascends_seed_succ_top:
  shows "\<not> ascends (seed (Suc n)) 0 n"
proof -
  have b0: "b0_start (seed (Suc n)) = Some 0" using b0_start_seed by simp
  have mp: "max_parent_level (seed (Suc n)) = Some n"
    using max_parent_level_seed[where n = "Suc n"] by simp
  show ?thesis
    unfolding ascends_def using b0 mp by simp
qed

lemma delta_seed_succ:
  assumes "m < Suc n"
  shows "delta (seed (Suc n)) m = 1"
proof -
  have b0: "b0_start (seed (Suc n)) = Some 0" using b0_start_seed by simp
  have last_idx: "last_col_idx (seed (Suc n)) = 1" by (simp add: length_seed)
  have e1: "elem (seed (Suc n)) 1 m = 1" using assms by (rule elem_seed_1)
  have e0: "elem (seed (Suc n)) 0 m = 0" using assms by (rule elem_seed_0)
  show ?thesis
    unfolding delta_def using b0 last_idx e1 e0 by simp
qed

text \<open>
  Bumping the single column of \<open>B_0\<close> in \<open>seed (Suc n)\<close> with
  multiplier \<open>1\<close> yields the column \<open>(1, 1, ..., 1, 0)\<close> of
  length \<open>Suc n\<close>: the first \<open>n\<close> rows ascend (each gaining
  \<open>1 \<cdot> 1 = 1\<close>) and the last row stays at \<open>0\<close>.
\<close>

lemma bump_col_seed_one:
  shows "bump_col (seed (Suc n)) 0 1 = replicate n 1 @ [0]"
  sorry  \<comment> \<open>computational proof; rep_eq substitution dance with simp.
            Suspended: all the inputs (b0_start, ascends, delta) are
            already proved; what remains is a list/arith manipulation.\<close>

inductive_set BMS :: "array set" where
  seed_in_BMS:   "seed n \<in> BMS"
| expand_in_BMS: "A \<in> BMS \<Longrightarrow> A[n] \<in> BMS"

inductive bms_le :: "array \<Rightarrow> array \<Rightarrow> bool" (infix "\<le>\<^sub>B" 50) where
  bms_le_refl: "A \<le>\<^sub>B A"
| bms_le_step: "A' \<le>\<^sub>B A[n] \<Longrightarrow> A' \<le>\<^sub>B A"

definition bms_lt :: "array \<Rightarrow> array \<Rightarrow> bool" (infix "<\<^sub>B" 50) where
  "A' <\<^sub>B A \<longleftrightarrow> A' \<le>\<^sub>B A \<and> A' \<noteq> A"

end
