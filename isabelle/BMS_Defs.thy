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
proof (relation "inv_image (less_than <*lex*> less_than <*lex*> less_than)
                            (\<lambda>x. case x of
                                   Inl (A, m, i) \<Rightarrow> (m, i, 0::nat)
                                 | Inr (A, m, i, j) \<Rightarrow> (m, i, Suc 0))",
        goal_cases)
  case 1 show ?case by auto
next
  case (2 A m i j) show ?case by auto
next
  case (3 A m i j) show ?case by auto
next
  case (4 A m i j x2)
  \<comment> \<open>The recursive call in \<open>m_ancestor\<close>'s \<open>Some p\<close> branch.
      We need \<open>x2 < i\<close>. From \<open>m_parent_m_ancestor_dom\<close> we can
      apply \<open>m_parent.psimps\<close> to expose the body and use
      \<open>m_parent_lt_aux\<close>.\<close>
  from 4 have parent_eq: "m_parent A m i = Some x2"
            and dom: "m_parent_m_ancestor_dom (Inl (A, m, i))"
    by auto
  show ?case
  proof (cases m)
    case 0
    let ?cands = "[j \<leftarrow> [0..<i]. elem A j 0 < elem A i 0]"
    from dom 0 have body: "m_parent A 0 i =
        (if ?cands = [] then None else Some (last ?cands))"
      by (simp add: m_parent.psimps Let_def)
    with parent_eq 0 have ne: "?cands \<noteq> []" and eq: "x2 = last ?cands"
      by (auto split: if_splits)
    have "x2 < i" using ne eq m_parent_lt_aux[OF refl ne] by simp
    thus ?thesis by simp
  next
    case (Suc m')
    let ?cands = "[j \<leftarrow> [0..<i]. elem A j (Suc m') < elem A i (Suc m')
                                  \<and> m_ancestor A m' i j]"
    from dom Suc have body: "m_parent A (Suc m') i =
        (if ?cands = [] then None else Some (last ?cands))"
      by (simp add: m_parent.psimps Let_def)
    with parent_eq Suc have ne: "?cands \<noteq> []" and eq: "x2 = last ?cands"
      by (auto split: if_splits)
    have "x2 < i" using ne eq m_parent_lt_aux[OF refl ne] by simp
    thus ?thesis by simp
  qed
qed


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

text \<open>
  The \<open>m\<close>-th element of an \<open>m\<close>-parent is strictly smaller than
  the \<open>m\<close>-th element of the column itself: this comes directly from
  the candidate filter in the definition of \<open>m_parent\<close>.
\<close>

lemma last_filter_satisfies:
  "filter P xs \<noteq> [] \<Longrightarrow> P (last (filter P xs))"
  using last_in_set[of "filter P xs"] by auto

lemma m_parent_elem_lt:
  "m_parent A m i = Some p \<Longrightarrow> elem A p m < elem A i m"
proof (cases m)
  case 0
  assume H: "m_parent A m i = Some p"
  with 0 have cands_ne: "filter (\<lambda>j. elem A j 0 < elem A i 0) [0..<i] \<noteq> []"
                  and p_eq: "p = last (filter (\<lambda>j. elem A j 0 < elem A i 0) [0..<i])"
    by (auto simp: Let_def split: if_split_asm)
  have "elem A p 0 < elem A i 0"
    using last_filter_satisfies[OF cands_ne] p_eq by simp
  thus ?thesis using 0 by simp
next
  case (Suc m')
  assume H: "m_parent A m i = Some p"
  let ?P = "\<lambda>j. elem A j (Suc m') < elem A i (Suc m') \<and> m_ancestor A m' i j"
  from H Suc have cands_ne: "filter ?P [0..<i] \<noteq> []"
                and p_eq: "p = last (filter ?P [0..<i])"
    by (auto simp: Let_def split: if_split_asm)
  have "?P p"
    using last_filter_satisfies[OF cands_ne] p_eq by simp
  thus ?thesis using Suc by simp
qed

text \<open>
  An m-ancestor's m-th element is strictly smaller, by induction along
  the m-parent chain.
\<close>

text \<open>
  An m-ancestor's column index is strictly smaller. Follows from
  the m-parent chain decreasing strictly in column index (each step
  uses @{thm m_parent_lt}).
\<close>

lemma m_ancestor_target_lt:
  "m_ancestor A m i j \<Longrightarrow> j < i"
proof (induct i arbitrary: j rule: nat_less_induct)
  fix i j assume IH: "\<forall>k<i. \<forall>j'. m_ancestor A m k j' \<longrightarrow> j' < k"
  assume H: "m_ancestor A m i j"
  obtain p where mp: "m_parent A m i = Some p"
              and case_p: "p = j \<or> m_ancestor A m p j"
    using H by (cases "m_parent A m i") auto
  have p_lt_i: "p < i" using mp m_parent_lt by simp
  show "j < i"
  proof (cases "p = j")
    case True thus ?thesis using p_lt_i by simp
  next
    case False
    hence "m_ancestor A m p j" using case_p by simp
    hence "j < p" using IH p_lt_i by blast
    thus ?thesis using p_lt_i by simp
  qed
qed

lemma m_ancestor_elem_lt:
  "m_ancestor A m i j \<Longrightarrow> elem A j m < elem A i m"
proof (induct i arbitrary: j rule: nat_less_induct)
  fix i j assume IH: "\<forall>k<i. \<forall>j'. m_ancestor A m k j' \<longrightarrow> elem A j' m < elem A k m"
  assume H: "m_ancestor A m i j"
  obtain p where mp: "m_parent A m i = Some p"
              and case_p: "p = j \<or> m_ancestor A m p j"
    using H by (cases "m_parent A m i") auto
  have p_lt_i: "p < i" using mp m_parent_lt by simp
  have elem_p_lt: "elem A p m < elem A i m" using mp m_parent_elem_lt by simp
  show "elem A j m < elem A i m"
  proof (cases "p = j")
    case True thus ?thesis using elem_p_lt by simp
  next
    case False
    hence "m_ancestor A m p j" using case_p by simp
    hence "elem A j m < elem A p m" using IH p_lt_i by blast
    thus ?thesis using elem_p_lt by simp
  qed
qed

text \<open>
  Transitivity of m-ancestry at a fixed level m.
\<close>

lemma m_ancestor_trans_aux:
  "\<forall>j k. m_ancestor A m i j \<longrightarrow> m_ancestor A m j k \<longrightarrow> m_ancestor A m i k"
proof (induct i rule: nat_less_induct)
  fix i
  assume IH: "\<forall>i' < i. \<forall>j k. m_ancestor A m i' j \<longrightarrow> m_ancestor A m j k
                              \<longrightarrow> m_ancestor A m i' k"
  show "\<forall>j k. m_ancestor A m i j \<longrightarrow> m_ancestor A m j k
              \<longrightarrow> m_ancestor A m i k"
  proof (intro allI impI)
    fix j k
    assume Hij: "m_ancestor A m i j" and Hjk: "m_ancestor A m j k"
    obtain p where mp: "m_parent A m i = Some p"
                and case_p: "p = j \<or> m_ancestor A m p j"
      using Hij by (cases "m_parent A m i") auto
    have p_lt_i: "p < i" using mp m_parent_lt by simp
    have goal_iff: "m_ancestor A m i k \<longleftrightarrow> (p = k \<or> m_ancestor A m p k)"
      using mp by simp
    show "m_ancestor A m i k"
    proof (cases "p = j")
      case True
      hence "p = k \<or> m_ancestor A m p k" using Hjk by simp
      thus ?thesis using goal_iff by simp
    next
      case False
      hence "m_ancestor A m p j" using case_p by simp
      hence "m_ancestor A m p k" using IH p_lt_i Hjk by blast
      thus ?thesis using goal_iff by simp
    qed
  qed
qed

lemma m_ancestor_trans:
  "m_ancestor A m i j \<Longrightarrow> m_ancestor A m j k \<Longrightarrow> m_ancestor A m i k"
  using m_ancestor_trans_aux by blast

text \<open>
  Linearity of the m-ancestor chain: any two m-ancestors of the same
  source \<open>i\<close> are comparable (one is an ancestor of the other, or
  they are equal). Follows from \<open>P_m\<close> being deterministic.
\<close>

lemma m_ancestor_chain_linear:
  "\<forall>j k. m_ancestor A m i j \<longrightarrow> m_ancestor A m i k
        \<longrightarrow> j = k \<or> m_ancestor A m j k \<or> m_ancestor A m k j"
proof (induct i rule: nat_less_induct)
  fix i
  assume IH: "\<forall>i'<i. \<forall>j k. m_ancestor A m i' j \<longrightarrow> m_ancestor A m i' k
                          \<longrightarrow> j = k \<or> m_ancestor A m j k \<or> m_ancestor A m k j"
  show "\<forall>j k. m_ancestor A m i j \<longrightarrow> m_ancestor A m i k
              \<longrightarrow> j = k \<or> m_ancestor A m j k \<or> m_ancestor A m k j"
  proof (intro allI impI)
    fix j k
    assume H1: "m_ancestor A m i j"
    assume H2: "m_ancestor A m i k"
    obtain p where mp: "m_parent A m i = Some p"
                and case_j: "p = j \<or> m_ancestor A m p j"
      using H1 by (cases "m_parent A m i") auto
    obtain p' where mp': "m_parent A m i = Some p'"
                and case_k: "p' = k \<or> m_ancestor A m p' k"
      using H2 by (cases "m_parent A m i") auto
    have p_eq: "p = p'" using mp mp' by simp
    have p_lt: "p < i" using mp m_parent_lt by simp
    show "j = k \<or> m_ancestor A m j k \<or> m_ancestor A m k j"
    proof (cases "p = j")
      case pj: True
      show ?thesis
      proof (cases "p = k")
        case True thus ?thesis using pj by simp
      next
        case False
        hence "m_ancestor A m p k" using case_k p_eq by simp
        thus ?thesis using pj by simp
      qed
    next
      case pj_False: False
      hence anc_pj: "m_ancestor A m p j" using case_j by simp
      show ?thesis
      proof (cases "p = k")
        case True
        hence "m_ancestor A m k j" using anc_pj by simp
        thus ?thesis by simp
      next
        case False
        hence anc_pk: "m_ancestor A m p k" using case_k p_eq by simp
        show ?thesis using IH p_lt anc_pj anc_pk by blast
      qed
    qed
  qed
qed

text \<open>
  Ascending status is preserved along m-ancestor chains in \<open>B\<^sub>0\<close>:
  if \<open>s + y\<close> is an \<open>m\<close>-ancestor of \<open>s + x\<close>, then
  \<open>ascends A x m = ascends A y m\<close>. Proof uses
  @{thm m_ancestor_chain_linear} for the \<open>\<Rightarrow>\<close> direction and
  @{thm m_ancestor_trans} for the \<open>\<Leftarrow>\<close> direction.
\<close>

lemma ascends_invariant_along_chain:
  assumes b0: "b0_start A = Some s"
      and chain: "m_ancestor A k (s + x) (s + y)"
  shows "ascends A x k = ascends A y k"
proof (cases "max_parent_level A")
  case None
  \<comment> \<open>\<open>max_parent_level A = None\<close>: but assumption gives
      \<open>b0_start A = Some s\<close>, which by \<open>b0_start_def\<close> forces
      \<open>max_parent_level A = Some _\<close>. Contradiction.\<close>
  have b_None: "b0_start A = None"
    using None unfolding b0_start_def by simp
  with b0 show ?thesis by simp
next
  case (Some m\<^sub>0)
  show ?thesis
  proof (cases "k < m\<^sub>0")
    case False
    \<comment> \<open>\<open>k \<ge> m\<^sub>0\<close>: ascends is False for any column.\<close>
    have nx: "\<not> ascends A x k" using False Some b0 unfolding ascends_def by simp
    have ny: "\<not> ascends A y k" using False Some b0 unfolding ascends_def by simp
    show ?thesis using nx ny by simp
  next
    case True
    hence k_lt: "k < m\<^sub>0" .
    have asc_x: "ascends A x k = non_strict_ancestor A k (s + x) s"
      using b0 Some k_lt by (simp add: ascends_def)
    have asc_y: "ascends A y k = non_strict_ancestor A k (s + y) s"
      using b0 Some k_lt by (simp add: ascends_def)
    \<comment> \<open>Show non_strict_ancestor A k (s+x) s ⟷ non_strict_ancestor A k (s+y) s.\<close>
    have nsa_eq: "non_strict_ancestor A k (s + x) s
                = non_strict_ancestor A k (s + y) s"
    proof
      assume nx: "non_strict_ancestor A k (s + x) s"
      \<comment> \<open>\<open>nx\<close>: \<open>s+x = s\<close> (x = 0) or m_anc \<open>s+x \<to> s\<close>.\<close>
      show "non_strict_ancestor A k (s + y) s"
      proof (cases "x = 0")
        case True
        \<comment> \<open>x = 0: chain \<open>s \<to> s+y\<close>, but m_anc requires target < source.
            \<open>s + y \<ge> s\<close>, so chain implies \<open>s + y < s\<close>, contradiction.\<close>
        have "s + y < s + x" using chain by (rule m_ancestor_target_lt)
        with True show ?thesis by simp
      next
        case False
        hence "x \<noteq> 0" .
        hence sx_ne: "s + x \<noteq> s" by simp
        have x_to_s: "m_ancestor A k (s + x) s"
          using nx sx_ne unfolding non_strict_ancestor_def by simp
        \<comment> \<open>Apply linearity: chain \<open>s+x \<to> s+y\<close> and chain \<open>s+x \<to> s\<close>;
            so \<open>s+y = s\<close>, m_anc \<open>s+y \<to> s\<close>, or m_anc \<open>s \<to> s+y\<close>.
            The last is impossible (target \<ge> source).\<close>
        have "s + y = s \<or> m_ancestor A k (s + y) s \<or> m_ancestor A k s (s + y)"
          using m_ancestor_chain_linear[of A k "s + x"] chain x_to_s by blast
        moreover have "\<not> m_ancestor A k s (s + y)"
          using m_ancestor_target_lt by fastforce
        ultimately have "s + y = s \<or> m_ancestor A k (s + y) s" by blast
        thus ?thesis unfolding non_strict_ancestor_def by blast
      qed
    next
      assume ny: "non_strict_ancestor A k (s + y) s"
      \<comment> \<open>\<open>ny\<close>: \<open>s+y = s\<close> (y = 0) or m_anc \<open>s+y \<to> s\<close>.\<close>
      show "non_strict_ancestor A k (s + x) s"
      proof (cases "y = 0")
        case True
        have "m_ancestor A k (s + x) s" using chain True by simp
        thus ?thesis unfolding non_strict_ancestor_def by blast
      next
        case False
        hence "y \<noteq> 0" .
        hence sy_ne: "s + y \<noteq> s" by simp
        have y_to_s: "m_ancestor A k (s + y) s"
          using ny sy_ne unfolding non_strict_ancestor_def by simp
        have "m_ancestor A k (s + x) s"
          using m_ancestor_trans[OF chain y_to_s] .
        thus ?thesis unfolding non_strict_ancestor_def by blast
      qed
    qed
    show ?thesis using asc_x asc_y nsa_eq by simp
  qed
qed

text \<open>
  An (Suc m)-parent of \<open>i\<close> is, by definition, an m-ancestor of \<open>i\<close>.
\<close>

lemma m_parent_Suc_implies_m_ancestor:
  "m_parent A (Suc m) i = Some p \<Longrightarrow> m_ancestor A m i p"
proof -
  assume H: "m_parent A (Suc m) i = Some p"
  let ?P = "\<lambda>j. elem A j (Suc m) < elem A i (Suc m) \<and> m_ancestor A m i j"
  from H have cands_ne: "filter ?P [0..<i] \<noteq> []"
              and p_eq: "p = last (filter ?P [0..<i])"
    by (auto simp: Let_def split: if_split_asm)
  have "?P p" using last_filter_satisfies[OF cands_ne] p_eq by simp
  thus ?thesis by simp
qed

text \<open>
  An (Suc m)-ancestor of \<open>i\<close> is also an m-ancestor.
\<close>

lemma m_ancestor_Suc_implies_m_ancestor_aux:
  "\<forall>j. m_ancestor A (Suc m) i j \<longrightarrow> m_ancestor A m i j"
proof (induct i rule: nat_less_induct)
  fix i
  assume IH: "\<forall>i' < i. \<forall>j. m_ancestor A (Suc m) i' j
                              \<longrightarrow> m_ancestor A m i' j"
  show "\<forall>j. m_ancestor A (Suc m) i j \<longrightarrow> m_ancestor A m i j"
  proof (intro allI impI)
    fix j assume H: "m_ancestor A (Suc m) i j"
    obtain p where mp: "m_parent A (Suc m) i = Some p"
                and case_p: "p = j \<or> m_ancestor A (Suc m) p j"
      using H by (cases "m_parent A (Suc m) i") auto
    have p_lt_i: "p < i" using mp m_parent_lt by blast
    have m_anc_p: "m_ancestor A m i p"
      using m_parent_Suc_implies_m_ancestor[OF mp] .
    show "m_ancestor A m i j"
    proof (cases "p = j")
      case True thus ?thesis using m_anc_p by simp
    next
      case False
      hence "m_ancestor A (Suc m) p j" using case_p by simp
      hence "m_ancestor A m p j" using IH p_lt_i by blast
      thus ?thesis using m_anc_p m_ancestor_trans by blast
    qed
  qed
qed

lemma m_ancestor_Suc_implies_m_ancestor:
  "m_ancestor A (Suc m) i j \<Longrightarrow> m_ancestor A m i j"
  using m_ancestor_Suc_implies_m_ancestor_aux by blast

text \<open>
  Monotonicity in the level: an \<open>m'\<close>-ancestor for \<open>m \<le> m'\<close> is also
  an \<open>m\<close>-ancestor.
\<close>

lemma m_ancestor_mono:
  assumes "m \<le> m'"
  shows "m_ancestor A m' i j \<Longrightarrow> m_ancestor A m i j"
proof -
  obtain d where d_eq: "m' = m + d" using assms le_Suc_ex by blast
  show "m_ancestor A m' i j \<Longrightarrow> m_ancestor A m i j"
    using d_eq
  proof (induct d arbitrary: m')
    case 0 thus ?case by simp
  next
    case (Suc d)
    have m'_eq: "m' = Suc (m + d)" using Suc(3) by simp
    have anc: "m_ancestor A (Suc (m + d)) i j" using Suc(2) m'_eq by simp
    hence "m_ancestor A (m + d) i j"
      using m_ancestor_Suc_implies_m_ancestor by blast
    thus ?case using Suc.hyps[where m' = "m + d"] by simp
  qed
qed


text \<open>
  Ancestry preservation under \<open>butlast\<close>. For all indices
  \<open>i, j < arr_len A - 1\<close> (i.e.\ inside \<open>butlast A\<close>), the
  m-parent and m-ancestor relations of \<open>A\<close> and \<open>butlast A\<close>
  coincide. The proof is a nested induction: outer on the stability
  level \<open>m\<close>, inner on the column index \<open>i\<close> (the m-ancestor
  recursion descends along the m-parent chain).
\<close>

lemma elem_butlast:
  assumes "i < arr_len A - 1"
  shows "elem (butlast A) i m = elem A i m"
proof -
  from assms have "i < length (butlast A)" by simp
  hence "butlast A ! i = A ! i" by (rule nth_butlast)
  thus ?thesis unfolding elem_def by simp
qed

lemma m_parent_m_ancestor_butlast:
  shows "(\<forall>i. i < arr_len A - 1 \<longrightarrow> m_parent (butlast A) m i = m_parent A m i)
       \<and> (\<forall>i j. i < arr_len A - 1 \<longrightarrow> j < arr_len A - 1 \<longrightarrow>
            (m_ancestor (butlast A) m i j \<longleftrightarrow> m_ancestor A m i j))"
proof (induct m)
  case 0
  have parent: "\<forall>i. i < arr_len A - 1 \<longrightarrow> m_parent (butlast A) 0 i = m_parent A 0 i"
  proof (intro allI impI)
    fix i assume i_lt: "i < arr_len A - 1"
    have e_i: "elem (butlast A) i 0 = elem A i 0" by (rule elem_butlast[OF i_lt])
    have "[j \<leftarrow> [0..<i]. elem (butlast A) j 0 < elem (butlast A) i 0]
        = [j \<leftarrow> [0..<i]. elem A j 0 < elem A i 0]"
    proof (rule filter_cong[OF refl])
      fix j assume "j \<in> set [0..<i]"
      hence j_lt_i: "j < i" by simp
      hence j_lt: "j < arr_len A - 1" using i_lt by linarith
      show "(elem (butlast A) j 0 < elem (butlast A) i 0)
          = (elem A j 0 < elem A i 0)"
        using elem_butlast[OF j_lt] e_i by simp
    qed
    thus "m_parent (butlast A) 0 i = m_parent A 0 i"
      by (simp add: Let_def)
  qed
  have ancestor: "\<forall>i j. i < arr_len A - 1 \<longrightarrow> j < arr_len A - 1 \<longrightarrow>
                    (m_ancestor (butlast A) 0 i j \<longleftrightarrow> m_ancestor A 0 i j)"
  proof (intro allI impI)
    fix i j assume i_lt: "i < arr_len A - 1" and j_lt: "j < arr_len A - 1"
    show "m_ancestor (butlast A) 0 i j \<longleftrightarrow> m_ancestor A 0 i j"
      using i_lt
    proof (induct i rule: less_induct)
      case (less i)
      show ?case
      proof (cases "m_parent A 0 i")
        case None
        hence par_bl: "m_parent (butlast A) 0 i = None"
          using parent less.prems by simp
        show ?thesis using None par_bl by simp
      next
        case (Some p)
        have p_lt_i: "p < i" using Some by (rule m_parent_lt)
        have p_lt_A: "p < arr_len A - 1" using p_lt_i less.prems by linarith
        have par_bl: "m_parent (butlast A) 0 i = Some p"
          using parent less.prems Some by simp
        have IH_inner: "m_ancestor (butlast A) 0 p j \<longleftrightarrow> m_ancestor A 0 p j"
          using less.hyps[OF p_lt_i p_lt_A] .
        show ?thesis using Some par_bl IH_inner by simp
      qed
    qed
  qed
  show ?case using parent ancestor by blast
next
  case (Suc m)
  hence IH_parent: "\<forall>i. i < arr_len A - 1
                          \<longrightarrow> m_parent (butlast A) m i = m_parent A m i"
    and IH_anc: "\<forall>i j. i < arr_len A - 1 \<longrightarrow> j < arr_len A - 1
                          \<longrightarrow> (m_ancestor (butlast A) m i j
                                \<longleftrightarrow> m_ancestor A m i j)"
    by blast+
  have parent: "\<forall>i. i < arr_len A - 1
                       \<longrightarrow> m_parent (butlast A) (Suc m) i = m_parent A (Suc m) i"
  proof (intro allI impI)
    fix i assume i_lt: "i < arr_len A - 1"
    have e_i: "elem (butlast A) i (Suc m) = elem A i (Suc m)"
      by (rule elem_butlast[OF i_lt])
    have "[j \<leftarrow> [0..<i]. elem (butlast A) j (Suc m) < elem (butlast A) i (Suc m)
                         \<and> m_ancestor (butlast A) m i j]
        = [j \<leftarrow> [0..<i]. elem A j (Suc m) < elem A i (Suc m)
                         \<and> m_ancestor A m i j]"
    proof (rule filter_cong[OF refl])
      fix j assume "j \<in> set [0..<i]"
      hence j_lt_i: "j < i" by simp
      hence j_lt: "j < arr_len A - 1" using i_lt by linarith
      have e_j: "elem (butlast A) j (Suc m) = elem A j (Suc m)"
        by (rule elem_butlast[OF j_lt])
      have anc_eq: "m_ancestor (butlast A) m i j \<longleftrightarrow> m_ancestor A m i j"
        using IH_anc i_lt j_lt by simp
      show "(elem (butlast A) j (Suc m) < elem (butlast A) i (Suc m)
              \<and> m_ancestor (butlast A) m i j)
          = (elem A j (Suc m) < elem A i (Suc m) \<and> m_ancestor A m i j)"
        using e_j e_i anc_eq by simp
    qed
    thus "m_parent (butlast A) (Suc m) i = m_parent A (Suc m) i"
      by (simp add: Let_def)
  qed
  have ancestor: "\<forall>i j. i < arr_len A - 1 \<longrightarrow> j < arr_len A - 1
                          \<longrightarrow> (m_ancestor (butlast A) (Suc m) i j
                                \<longleftrightarrow> m_ancestor A (Suc m) i j)"
  proof (intro allI impI)
    fix i j assume i_lt: "i < arr_len A - 1" and j_lt: "j < arr_len A - 1"
    show "m_ancestor (butlast A) (Suc m) i j
          \<longleftrightarrow> m_ancestor A (Suc m) i j"
      using i_lt
    proof (induct i rule: less_induct)
      case (less i)
      show ?case
      proof (cases "m_parent A (Suc m) i")
        case None
        hence par_bl: "m_parent (butlast A) (Suc m) i = None"
          using parent less.prems by simp
        show ?thesis using None par_bl by simp
      next
        case (Some p)
        have p_lt_i: "p < i" using Some by (rule m_parent_lt)
        have p_lt_A: "p < arr_len A - 1" using p_lt_i less.prems by linarith
        have par_bl: "m_parent (butlast A) (Suc m) i = Some p"
          using parent less.prems Some by simp
        have IH_inner: "m_ancestor (butlast A) (Suc m) p j
                          \<longleftrightarrow> m_ancestor A (Suc m) p j"
          using less.hyps[OF p_lt_i p_lt_A] .
        show ?thesis using Some par_bl IH_inner by simp
      qed
    qed
  qed
  show ?case using parent ancestor by blast
qed

lemma m_parent_butlast:
  assumes "i < arr_len A - 1"
  shows "m_parent (butlast A) m i = m_parent A m i"
  using m_parent_m_ancestor_butlast assms by blast

lemma m_ancestor_butlast_iff:
  assumes "i < arr_len A - 1" "j < arr_len A - 1"
  shows "m_ancestor (butlast A) m i j \<longleftrightarrow> m_ancestor A m i j"
  using m_parent_m_ancestor_butlast assms by blast


text \<open>
  Two lists of equal length agree at any index. For \<open>m \<le> length\<close>
  it is \<open>nth_eq_iff_index_eq\<close>; for \<open>m \<ge> length\<close> both sides
  reduce to \<open>[] ! (m - length _)\<close> by the recursive definition of
  \<open>nth\<close>, giving the same value.
\<close>

lemma nth_same_length_oob:
  assumes "length xs = length ys" "length xs \<le> m"
  shows "xs ! m = ys ! m"
  using assms
proof (induct xs ys arbitrary: m rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons x xs y ys)
  obtain m' where m_eq: "m = Suc m'"
    using Cons.prems by (cases m) auto
  hence "length xs \<le> m'" using Cons.prems by simp
  hence "xs ! m' = ys ! m'" by (rule Cons.hyps)
  thus ?case using m_eq by simp
qed


text \<open>
  Ancestry preservation under \<open>strip_zero_rows\<close>. For a
  non-empty well-formed array \<open>B\<close>, every m-ancestor relation in
  \<open>strip_zero_rows B\<close> also holds in \<open>B\<close>. Proof postponed
  to a separate development (see task ID 28).
\<close>

lemma length_strip_zero_rows:
  "length (strip_zero_rows B) = length B"
  unfolding strip_zero_rows_def by (simp add: Let_def)

definition keep_of :: "array \<Rightarrow> nat" where
  "keep_of A = (LEAST h. h \<le> height A \<and>
                  (\<forall>m. h \<le> m \<and> m < height A
                        \<longrightarrow> (\<forall>c \<in> set A. c ! m = 0)))"

lemma keep_of_le_height: "keep_of A \<le> height A"
proof -
  let ?P = "\<lambda>h. h \<le> height A
              \<and> (\<forall>m. h \<le> m \<and> m < height A \<longrightarrow> (\<forall>c \<in> set A. c ! m = 0))"
  have wit: "?P (height A)" by simp
  hence "(LEAST h. ?P h) \<le> height A" by (rule Least_le)
  thus ?thesis unfolding keep_of_def by simp
qed

lemma keep_of_row_zero:
  assumes "keep_of A \<le> m" "m < height A" "c \<in> set A"
  shows "c ! m = 0"
proof -
  have wit: "(height A \<le> height A)
             \<and> (\<forall>m. height A \<le> m \<and> m < height A
                      \<longrightarrow> (\<forall>c \<in> set A. c ! m = 0))"
    by simp
  hence "(keep_of A \<le> height A)
       \<and> (\<forall>m. keep_of A \<le> m \<and> m < height A
                \<longrightarrow> (\<forall>c \<in> set A. c ! m = 0))"
    unfolding keep_of_def by (rule LeastI)
  thus ?thesis using assms by blast
qed

lemma strip_zero_rows_eq_map_take:
  assumes "A \<noteq> []"
  shows "strip_zero_rows A = map (\<lambda>c. take (keep_of A) c) A"
  using assms unfolding strip_zero_rows_def keep_of_def by (simp add: Let_def)

lemma length_col_arr:
  assumes is_arr: "is_array A" and A_ne: "A \<noteq> []" and i_lt: "i < arr_len A"
  shows "length (A ! i) = height A"
proof -
  have "A ! i \<in> set A" using i_lt by (rule nth_mem)
  moreover from is_arr have "\<forall>c \<in> set A. length c = height A"
    unfolding is_array_def by blast
  ultimately show ?thesis by blast
qed

lemma length_col_strip:
  assumes is_arr: "is_array A" and A_ne: "A \<noteq> []" and i_lt: "i < arr_len A"
  shows "length ((strip_zero_rows A) ! i) = keep_of A"
proof -
  let ?k = "keep_of A"
  let ?H = "height A"
  have strip_eq: "strip_zero_rows A = map (\<lambda>c. take ?k c) A"
    using A_ne by (rule strip_zero_rows_eq_map_take)
  hence col_i: "(strip_zero_rows A) ! i = take ?k (A ! i)"
    using i_lt by simp
  have len_col: "length (A ! i) = ?H"
    using is_arr A_ne i_lt by (rule length_col_arr)
  from col_i have "length ((strip_zero_rows A) ! i) = min ?k (length (A ! i))"
    by simp
  also have "\<dots> = min ?k ?H" using len_col by simp
  also have "\<dots> = ?k" using keep_of_le_height by simp
  finally show ?thesis .
qed

lemma elem_strip_lt_keep:
  assumes A_ne: "A \<noteq> []" and i_lt: "i < arr_len A" and m_lt: "m < keep_of A"
  shows "elem (strip_zero_rows A) i m = elem A i m"
proof -
  have "strip_zero_rows A = map (\<lambda>c. take (keep_of A) c) A"
    using A_ne by (rule strip_zero_rows_eq_map_take)
  hence "(strip_zero_rows A) ! i = take (keep_of A) (A ! i)"
    using i_lt by simp
  hence "((strip_zero_rows A) ! i) ! m = (take (keep_of A) (A ! i)) ! m"
    by simp
  also have "\<dots> = (A ! i) ! m" using m_lt by simp
  finally show ?thesis unfolding elem_def .
qed

lemma elem_strip_lt_iff:
  assumes is_arr: "is_array A"
      and i_lt: "i < arr_len A" and j_lt: "j < arr_len A"
  shows "(elem (strip_zero_rows A) j m < elem (strip_zero_rows A) i m)
       \<longleftrightarrow> (elem A j m < elem A i m)"
proof (cases "A = []")
  case True
  hence "strip_zero_rows A = A" by (simp add: strip_zero_rows_def)
  thus ?thesis by simp
next
  case A_ne: False
  show ?thesis
  proof (cases "m < keep_of A")
    case True
    have e_i: "elem (strip_zero_rows A) i m = elem A i m"
      using A_ne i_lt True by (rule elem_strip_lt_keep)
    have e_j: "elem (strip_zero_rows A) j m = elem A j m"
      using A_ne j_lt True by (rule elem_strip_lt_keep)
    show ?thesis using e_i e_j by simp
  next
    case False
    hence k_le_m: "keep_of A \<le> m" by simp
    have len_strip_i: "length ((strip_zero_rows A) ! i) = keep_of A"
      using is_arr A_ne i_lt by (rule length_col_strip)
    have len_strip_j: "length ((strip_zero_rows A) ! j) = keep_of A"
      using is_arr A_ne j_lt by (rule length_col_strip)
    have strip_eq: "elem (strip_zero_rows A) j m = elem (strip_zero_rows A) i m"
      unfolding elem_def
    proof -
      from len_strip_i len_strip_j
      have eq_len: "length ((strip_zero_rows A) ! j) = length ((strip_zero_rows A) ! i)"
        by simp
      from k_le_m len_strip_j
      have m_ge: "length ((strip_zero_rows A) ! j) \<le> m" by simp
      show "((strip_zero_rows A) ! j) ! m = ((strip_zero_rows A) ! i) ! m"
        using eq_len m_ge by (rule nth_same_length_oob)
    qed
    have orig_eq: "elem A j m = elem A i m"
    proof (cases "m < height A")
      case True
      have ci: "A ! i \<in> set A" using i_lt by (rule nth_mem)
      have cj: "A ! j \<in> set A" using j_lt by (rule nth_mem)
      have zi: "(A ! i) ! m = 0"
        using k_le_m True ci by (rule keep_of_row_zero)
      have zj: "(A ! j) ! m = 0"
        using k_le_m True cj by (rule keep_of_row_zero)
      show ?thesis unfolding elem_def using zi zj by simp
    next
      case False
      hence H_le_m: "height A \<le> m" by simp
      have len_i: "length (A ! i) = height A"
        using is_arr A_ne i_lt by (rule length_col_arr)
      have len_j: "length (A ! j) = height A"
        using is_arr A_ne j_lt by (rule length_col_arr)
      show ?thesis unfolding elem_def
      proof -
        from len_i len_j have eq_len: "length (A ! j) = length (A ! i)" by simp
        from H_le_m len_j have m_ge: "length (A ! j) \<le> m" by simp
        show "(A ! j) ! m = (A ! i) ! m"
          using eq_len m_ge by (rule nth_same_length_oob)
      qed
    qed
    show ?thesis using strip_eq orig_eq by simp
  qed
qed

lemma is_array_butlast:
  assumes "is_array A"
  shows "is_array (butlast A)"
proof (cases "butlast A = []")
  case True
  thus ?thesis by (simp add: is_array_def)
next
  case False
  hence A_ne: "A \<noteq> []" by auto
  let ?H = "height A"
  have all_A: "\<forall>c \<in> set A. length c = ?H"
    using assms unfolding is_array_def by blast
  have hd_eq: "hd (butlast A) = hd A"
    using A_ne False by (metis append_butlast_last_id hd_append2)
  hence H_eq: "height (butlast A) = ?H" using A_ne False by simp
  have all_bl: "\<forall>c \<in> set (butlast A). length c = ?H"
    using all_A by (meson in_set_butlastD)
  show ?thesis unfolding is_array_def
    using all_bl H_eq False by auto
qed

lemma m_parent_m_ancestor_strip:
  assumes is_arr: "is_array A"
  shows "(\<forall>i. i < arr_len A
              \<longrightarrow> m_parent (strip_zero_rows A) m i = m_parent A m i)
       \<and> (\<forall>i j. i < arr_len A \<longrightarrow> j < arr_len A \<longrightarrow>
            (m_ancestor (strip_zero_rows A) m i j \<longleftrightarrow> m_ancestor A m i j))"
proof (induct m)
  case 0
  have parent: "\<forall>i. i < arr_len A
                     \<longrightarrow> m_parent (strip_zero_rows A) 0 i = m_parent A 0 i"
  proof (intro allI impI)
    fix i assume i_lt: "i < arr_len A"
    have "[j \<leftarrow> [0..<i].
              elem (strip_zero_rows A) j 0 < elem (strip_zero_rows A) i 0]
        = [j \<leftarrow> [0..<i]. elem A j 0 < elem A i 0]"
    proof (rule filter_cong[OF refl])
      fix j assume "j \<in> set [0..<i]"
      hence j_lt_i: "j < i" by simp
      hence jA: "j < arr_len A" using i_lt by linarith
      show "(elem (strip_zero_rows A) j 0 < elem (strip_zero_rows A) i 0)
          = (elem A j 0 < elem A i 0)"
        using is_arr i_lt jA by (rule elem_strip_lt_iff)
    qed
    thus "m_parent (strip_zero_rows A) 0 i = m_parent A 0 i"
      by (simp add: Let_def)
  qed
  have ancestor: "\<forall>i j. i < arr_len A \<longrightarrow> j < arr_len A \<longrightarrow>
                    (m_ancestor (strip_zero_rows A) 0 i j \<longleftrightarrow> m_ancestor A 0 i j)"
  proof (intro allI impI)
    fix i j assume i_lt: "i < arr_len A" and j_lt: "j < arr_len A"
    show "m_ancestor (strip_zero_rows A) 0 i j \<longleftrightarrow> m_ancestor A 0 i j"
      using i_lt
    proof (induct i rule: less_induct)
      case (less i)
      show ?case
      proof (cases "m_parent A 0 i")
        case None
        hence par_str: "m_parent (strip_zero_rows A) 0 i = None"
          using parent less.prems by simp
        show ?thesis using None par_str by simp
      next
        case (Some p)
        have p_lt_i: "p < i" using Some by (rule m_parent_lt)
        have p_lt_A: "p < arr_len A" using p_lt_i less.prems by linarith
        have par_str: "m_parent (strip_zero_rows A) 0 i = Some p"
          using parent less.prems Some by simp
        have IH_inner: "m_ancestor (strip_zero_rows A) 0 p j
                          \<longleftrightarrow> m_ancestor A 0 p j"
          using less.hyps[OF p_lt_i p_lt_A] .
        show ?thesis using Some par_str IH_inner by simp
      qed
    qed
  qed
  show ?case using parent ancestor by blast
next
  case (Suc m)
  hence IH_parent:
      "\<forall>i. i < arr_len A
            \<longrightarrow> m_parent (strip_zero_rows A) m i = m_parent A m i"
    and IH_anc:
      "\<forall>i j. i < arr_len A \<longrightarrow> j < arr_len A
              \<longrightarrow> (m_ancestor (strip_zero_rows A) m i j
                    \<longleftrightarrow> m_ancestor A m i j)"
    by blast+
  have parent: "\<forall>i. i < arr_len A
                     \<longrightarrow> m_parent (strip_zero_rows A) (Suc m) i
                          = m_parent A (Suc m) i"
  proof (intro allI impI)
    fix i assume i_lt: "i < arr_len A"
    have "[j \<leftarrow> [0..<i].
              elem (strip_zero_rows A) j (Suc m)
                < elem (strip_zero_rows A) i (Suc m)
              \<and> m_ancestor (strip_zero_rows A) m i j]
        = [j \<leftarrow> [0..<i].
              elem A j (Suc m) < elem A i (Suc m)
              \<and> m_ancestor A m i j]"
    proof (rule filter_cong[OF refl])
      fix j assume "j \<in> set [0..<i]"
      hence j_lt_i: "j < i" by simp
      hence jA: "j < arr_len A" using i_lt by linarith
      have elem_eq: "(elem (strip_zero_rows A) j (Suc m)
                        < elem (strip_zero_rows A) i (Suc m))
                  = (elem A j (Suc m) < elem A i (Suc m))"
        using is_arr i_lt jA by (rule elem_strip_lt_iff)
      have anc_eq: "m_ancestor (strip_zero_rows A) m i j
                      \<longleftrightarrow> m_ancestor A m i j"
        using IH_anc i_lt jA by simp
      show "(elem (strip_zero_rows A) j (Suc m)
              < elem (strip_zero_rows A) i (Suc m)
              \<and> m_ancestor (strip_zero_rows A) m i j)
          = (elem A j (Suc m) < elem A i (Suc m)
              \<and> m_ancestor A m i j)"
        using elem_eq anc_eq by simp
    qed
    thus "m_parent (strip_zero_rows A) (Suc m) i = m_parent A (Suc m) i"
      by (simp add: Let_def)
  qed
  have ancestor: "\<forall>i j. i < arr_len A \<longrightarrow> j < arr_len A
                          \<longrightarrow> (m_ancestor (strip_zero_rows A) (Suc m) i j
                                \<longleftrightarrow> m_ancestor A (Suc m) i j)"
  proof (intro allI impI)
    fix i j assume i_lt: "i < arr_len A" and j_lt: "j < arr_len A"
    show "m_ancestor (strip_zero_rows A) (Suc m) i j
          \<longleftrightarrow> m_ancestor A (Suc m) i j"
      using i_lt
    proof (induct i rule: less_induct)
      case (less i)
      show ?case
      proof (cases "m_parent A (Suc m) i")
        case None
        hence par_str: "m_parent (strip_zero_rows A) (Suc m) i = None"
          using parent less.prems by simp
        show ?thesis using None par_str by simp
      next
        case (Some p)
        have p_lt_i: "p < i" using Some by (rule m_parent_lt)
        have p_lt_A: "p < arr_len A" using p_lt_i less.prems by linarith
        have par_str: "m_parent (strip_zero_rows A) (Suc m) i = Some p"
          using parent less.prems Some by simp
        have IH_inner: "m_ancestor (strip_zero_rows A) (Suc m) p j
                          \<longleftrightarrow> m_ancestor A (Suc m) p j"
          using less.hyps[OF p_lt_i p_lt_A] .
        show ?thesis using Some par_str IH_inner by simp
      qed
    qed
  qed
  show ?case using parent ancestor by blast
qed

lemma m_ancestor_strip_subsume:
  assumes "is_array B" "B \<noteq> []" "i < length B" "j < length B"
          "m_ancestor (strip_zero_rows B) m i j"
  shows "m_ancestor B m i j"
  using m_parent_m_ancestor_strip[OF assms(1)] assms(3-5) by blast


lemma filter_set_subset_aux:
  "x \<in> set (filter P xs) \<Longrightarrow> x \<in> set xs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons a xs) thus ?case by (cases "P a") auto
qed

lemma max_parent_level_lt:
  assumes "max_parent_level A = Some m\<^sub>0"
  shows "m\<^sub>0 < height A"
proof -
  have ne: "A \<noteq> []"
    using assms unfolding max_parent_level_def
    by (auto split: if_splits)
  define P :: "nat \<Rightarrow> bool" where
    P_def: "P = (\<lambda>m. m_parent A m (last_col_idx A) \<noteq> None)"
  define ms where ms_def: "ms = filter P [0..<height A]"
  have mp_form: "max_parent_level A
               = (if ms = [] then None else Some (Max (set ms)))"
    using ne unfolding max_parent_level_def ms_def P_def
    by (simp add: Let_def)
  hence ms_ne: "ms \<noteq> []"
    using assms by (cases "ms = []") auto
  with assms mp_form have m0_eq: "m\<^sub>0 = Max (set ms)" by simp
  have set_fin: "finite (set ms)" by simp
  have set_ne: "set ms \<noteq> {}" using ms_ne by (cases ms) auto
  have "Max (set ms) \<in> set ms"
    using set_fin set_ne by (rule Max_in)
  hence m0_in: "m\<^sub>0 \<in> set ms" using m0_eq by simp
  hence "m\<^sub>0 \<in> set [0..<height A]"
    unfolding ms_def by (rule filter_set_subset_aux)
  thus ?thesis by simp
qed

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


text \<open>
  Step 1: at row \<open>m\<^sub>0\<close>, the bumped column \<open>B\<^sub>1[0]\<close> is strictly
  less than the last column \<open>C\<close>. This row does not ascend
  (\<open>m\<^sub>0 < m\<^sub>0\<close> is false), so the bumped value equals the original
  value of the first column of \<open>B\<^sub>0\<close>, which is the
  \<open>m\<^sub>0\<close>-parent of \<open>C\<close>.
\<close>

text \<open>
  Pointwise formula for \<open>bump_col\<close>: the \<open>m\<close>-th entry of
  \<open>bump_col A d i\<close> is \<open>(A!(s+d))!m + i*delta A m\<close> on
  ascending rows, or \<open>(A!(s+d))!m\<close> otherwise.
\<close>

lemma bump_col_nth_general:
  assumes b0: "b0_start A = Some s"
      and m_lt: "m < length (A ! (s + d))"
  shows "(bump_col A d i) ! m
       = (A ! (s + d)) ! m + (if ascends A d m then i * delta A m else 0)"
  unfolding bump_col_def Let_def using b0 m_lt by simp

text \<open>
  Strict monotonicity of \<open>bump_col A d _\<close> in the multiplier
  at ascending rows (when \<open>delta A k > 0\<close>): \<open>i < i' \<Longrightarrow>
  bump_col A d i ! k < bump_col A d i' ! k\<close>.
\<close>

text \<open>
  At any row \<open>m < m\<^sub>0\<close>, \<open>delta A m > 0\<close>: the chain
  \<open>m_ancestor A m (last) s\<close> (from @{thm m_ancestor_mono})
  forces \<open>elem A s m < elem A (last) m\<close>
  (@{thm m_ancestor_elem_lt}).
\<close>

lemma delta_pos_of_lt_m0:
  assumes b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and m_lt: "m < m\<^sub>0"
  shows "0 < delta A m"
proof -
  have parent: "m_parent A m\<^sub>0 (last_col_idx A) = Some s"
    using b0 mp unfolding b0_start_def by simp
  have m0_anc: "m_ancestor A m\<^sub>0 (last_col_idx A) s"
    using parent by simp
  have m_anc: "m_ancestor A m (last_col_idx A) s"
    using m_ancestor_mono[OF less_imp_le_nat[OF m_lt] m0_anc] .
  have base_lt: "elem A s m < elem A (last_col_idx A) m"
    using m_ancestor_elem_lt[OF m_anc] .
  have delta_eq: "delta A m = elem A (last_col_idx A) m - elem A s m"
    unfolding delta_def using b0 by simp
  show ?thesis using delta_eq base_lt by simp
qed

lemma bump_col_lt_step:
  assumes b0: "b0_start A = Some s"
      and asc: "ascends A d k"
      and delta_pos: "0 < delta A k"
      and i_lt: "i < i'"
      and len_k: "k < length (A ! (s + d))"
  shows "(bump_col A d i) ! k < (bump_col A d i') ! k"
proof -
  have bi: "(bump_col A d i) ! k = (A ! (s + d)) ! k + i * delta A k"
    using bump_col_nth_general[OF b0 len_k] asc by simp
  have bi': "(bump_col A d i') ! k = (A ! (s + d)) ! k + i' * delta A k"
    using bump_col_nth_general[OF b0 len_k] asc by simp
  have "i * delta A k < i' * delta A k"
    using i_lt delta_pos by simp
  thus ?thesis using bi bi' by simp
qed

lemma bump_col_value_lt_m0:
  assumes b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and ne: "A \<noteq> []"
      and len_s: "m\<^sub>0 < length (A ! s)"
  shows "(bump_col A 0 1) ! m\<^sub>0 < (A ! last_col_idx A) ! m\<^sub>0"
proof -
  have parent: "m_parent A m\<^sub>0 (last_col_idx A) = Some s"
    using b0 mp unfolding b0_start_def by simp
  have base_lt: "elem A s m\<^sub>0 < elem A (last_col_idx A) m\<^sub>0"
    using m_parent_elem_lt[OF parent] .
  have not_asc: "\<not> ascends A 0 m\<^sub>0"
    unfolding ascends_def using b0 mp by simp
  have "(bump_col A 0 1) ! m\<^sub>0 = (A ! s) ! m\<^sub>0
                                + (if ascends A 0 m\<^sub>0 then 1 * delta A m\<^sub>0 else 0)"
    unfolding bump_col_def Let_def using b0 len_s by simp
  also have "\<dots> = (A ! s) ! m\<^sub>0" using not_asc by simp
  also have "\<dots> = elem A s m\<^sub>0" unfolding elem_def by simp
  finally have eq_left: "(bump_col A 0 1) ! m\<^sub>0 = elem A s m\<^sub>0" .
  have eq_right: "(A ! last_col_idx A) ! m\<^sub>0 = elem A (last_col_idx A) m\<^sub>0"
    unfolding elem_def by simp
  show ?thesis using eq_left eq_right base_lt by simp
qed


text \<open>
  Step 2: at any row \<open>m < m\<^sub>0\<close>, the bumped column \<open>B\<^sub>1[0]\<close>
  agrees with the last column \<open>C\<close>. The row ascends (since the first
  column of \<open>B\<^sub>0\<close> is itself, hence a non-strict \<open>m\<close>-ancestor),
  so the bumped value equals the original plus the delta to \<open>C\<close>.
\<close>

lemma bump_col_value_eq_below:
  assumes b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some m\<^sub>0"
      and ne: "A \<noteq> []"
      and m_lt: "m < m\<^sub>0"
      and len: "m < length (A ! s)"
  shows "(bump_col A 0 1) ! m = (A ! last_col_idx A) ! m"
proof -
  have parent: "m_parent A m\<^sub>0 (last_col_idx A) = Some s"
    using b0 mp unfolding b0_start_def by simp
  have m0_anc: "m_ancestor A m\<^sub>0 (last_col_idx A) s"
    using parent by simp
  have m_anc: "m_ancestor A m (last_col_idx A) s"
    using m_ancestor_mono[OF less_imp_le_nat[OF m_lt] m0_anc] .
  have base_lt: "elem A s m < elem A (last_col_idx A) m"
    using m_ancestor_elem_lt[OF m_anc] .
  have asc: "ascends A 0 m"
    unfolding ascends_def using b0 mp m_lt
    by (simp add: non_strict_ancestor_def)
  have delta_eq: "delta A m = elem A (last_col_idx A) m - elem A s m"
    unfolding delta_def using b0 by simp
  have "(bump_col A 0 1) ! m = (A ! s) ! m
                              + (if ascends A 0 m then 1 * delta A m else 0)"
    unfolding bump_col_def Let_def using b0 len by simp
  also have "\<dots> = (A ! s) ! m + delta A m" using asc by simp
  also have "\<dots> = elem A s m + (elem A (last_col_idx A) m - elem A s m)"
    using delta_eq unfolding elem_def by simp
  also have "\<dots> = elem A (last_col_idx A) m" using base_lt by simp
  also have "elem A (last_col_idx A) m = (A ! last_col_idx A) ! m"
    unfolding elem_def by simp
  finally show ?thesis .
qed


lemma length_bump_col_eq:
  assumes "b0_start A = Some s"
  shows "length (bump_col A 0 1) = length (A ! s)"
  unfolding bump_col_def Let_def using assms by simp


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


lemma length_Bi_block: "length (Bi_block A i) = length (B0_block A)"
  unfolding Bi_block_def Let_def by simp

lemma Bi_block_nth:
  assumes "d < length (B0_block A)"
  shows "Bi_block A i ! d = bump_col A d i"
  unfolding Bi_block_def Let_def using assms by simp

text \<open>
  When \<open>max_parent_level A = Some 0\<close> (no ascending rows),
  all \<open>Bi_block A i\<close> equal \<open>B0_block A\<close>: bumping
  is the identity at every row.
  Helper purpose: fills the \<open>m_0 = 0\<close> sub-case of
  \<open>lemma_2_5_at_main\<close>'s sorry by reducing all B-blocks to B0.
\<close>

lemma Bi_block_eq_B0_when_m0_zero:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some 0"
  shows "Bi_block A i = B0_block A"
proof -
  have len_eq: "length (Bi_block A i) = length (B0_block A)"
    by (rule length_Bi_block)
  have not_asc: "\<And>d m. \<not> ascends A d m"
    unfolding ascends_def using b0 mp by simp
  have entry_eq: "\<And>d. d < length (B0_block A)
                       \<Longrightarrow> Bi_block A i ! d = Bi_block A 0 ! d"
  proof -
    fix d assume d_lt: "d < length (B0_block A)"
    have bi_d: "Bi_block A i ! d = bump_col A d i"
      using d_lt by (rule Bi_block_nth)
    have b0_d: "Bi_block A 0 ! d = bump_col A d 0"
      using d_lt by (rule Bi_block_nth)
    have len_col: "length (bump_col A d i) = length (A ! (s + d))"
      unfolding bump_col_def Let_def using b0 by simp
    have len_col0: "length (bump_col A d 0) = length (A ! (s + d))"
      unfolding bump_col_def Let_def using b0 by simp
    have pointwise: "\<And>m. m < length (A ! (s + d))
                         \<Longrightarrow> (bump_col A d i) ! m = (bump_col A d 0) ! m"
    proof -
      fix m assume m_lt: "m < length (A ! (s + d))"
      have "(bump_col A d i) ! m = (A ! (s + d)) ! m"
        using bump_col_nth_general[OF b0 m_lt] not_asc by simp
      moreover have "(bump_col A d 0) ! m = (A ! (s + d)) ! m"
        using bump_col_nth_general[OF b0 m_lt] not_asc by simp
      ultimately show "(bump_col A d i) ! m = (bump_col A d 0) ! m"
        by simp
    qed
    have "bump_col A d i = bump_col A d 0"
      using len_col len_col0 pointwise nth_equalityI by metis
    thus "Bi_block A i ! d = Bi_block A 0 ! d" using bi_d b0_d by simp
  qed
  have len_eq_b0: "length (Bi_block A 0) = length (B0_block A)"
    using Bi_block_zero[OF A_ne] by simp
  have "Bi_block A i = Bi_block A 0"
    using nth_equalityI[where xs = "Bi_block A i" and ys = "Bi_block A 0"]
          len_eq len_eq_b0 entry_eq by simp
  also have "\<dots> = B0_block A" using Bi_block_zero[OF A_ne] .
  finally show ?thesis .
qed

lemma Bs_concat_Suc:
  "Bs_concat A (Suc n) = Bs_concat A n @ Bi_block A (Suc n)"
  by (simp add: Bs_concat_def)

text \<open>
  When \<open>max_parent_level A = Some 0\<close>, \<open>Bs_concat A n\<close>
  is the \<open>n+1\<close>-fold concatenation of \<open>B0_block A\<close>.
  Helper purpose: extends @{thm Bi_block_eq_B0_when_m0_zero} to
  the full \<open>Bs_concat\<close> for the m_0 = 0 sub-case of
  \<open>lemma_2_5_at_main\<close>'s sorry.
\<close>

lemma Bs_concat_when_m0_zero:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some 0"
  shows "Bs_concat A n = concat (replicate (Suc n) (B0_block A))"
proof -
  have bi_eq: "\<And>i. Bi_block A i = B0_block A"
    using A_ne b0 mp by (rule Bi_block_eq_B0_when_m0_zero)
  have len: "length (map (Bi_block A) [0..<Suc n])
           = length (replicate (Suc n) (B0_block A))"
    by simp
  have entries: "\<And>i. i < length (map (Bi_block A) [0..<Suc n])
                       \<Longrightarrow> map (Bi_block A) [0..<Suc n] ! i
                            = replicate (Suc n) (B0_block A) ! i"
  proof -
    fix i assume "i < length (map (Bi_block A) [0..<Suc n])"
    hence i_lt: "i < Suc n" by simp
    have l: "map (Bi_block A) [0..<Suc n] ! i = Bi_block A i"
    proof -
      have i_lt_len: "i < length [0..<Suc n]" using i_lt by simp
      have "map (Bi_block A) [0..<Suc n] ! i = Bi_block A ([0..<Suc n] ! i)"
        using i_lt_len by (rule nth_map)
      also have "[0..<Suc n] ! i = i"
        using i_lt nth_upt[where i = 0 and k = i and j = "Suc n"] by simp
      finally show ?thesis .
    qed
    have r: "replicate (Suc n) (B0_block A) ! i = B0_block A"
      using i_lt nth_replicate[where n = "Suc n" and x = "B0_block A" and i = i]
      by simp
    show "map (Bi_block A) [0..<Suc n] ! i
        = replicate (Suc n) (B0_block A) ! i"
      using l r bi_eq by simp
  qed
  have map_eq: "map (Bi_block A) [0..<Suc n]
              = replicate (Suc n) (B0_block A)"
    using len entries by (rule nth_equalityI)
  have step1: "Bs_concat A n = concat (map (Bi_block A) [0..<Suc n])"
    unfolding Bs_concat_def by simp
  have step2: "concat (map (Bi_block A) [0..<Suc n])
             = concat (replicate (Suc n) (B0_block A))"
    using map_eq by simp
  show ?thesis using step1 step2 by simp
qed

text \<open>
  Pre-strip expansion form at \<open>max_parent_level A = Some 0\<close>:
  the pre-strip array is \<open>G_block A\<close> followed by
  \<open>n+1\<close> copies of \<open>B0_block A\<close>.
  Helper purpose: fills the m_0 = 0 sub-case of \<open>lemma_2_5_at_main\<close>'s
  sorry by exposing A[n]'s explicit column structure.
\<close>

lemma pre_strip_expansion_when_m0_zero:
  assumes A_ne: "A \<noteq> []"
      and b0: "b0_start A = Some s"
      and mp: "max_parent_level A = Some 0"
  shows "G_block A @ Bs_concat A n
       = G_block A @ concat (replicate (Suc n) (B0_block A))"
  using Bs_concat_when_m0_zero[OF A_ne b0 mp] by simp

lemma length_Bs_concat:
  "length (Bs_concat A n) = Suc n * length (B0_block A)"
proof (induct n)
  case 0
  show ?case by (simp add: Bs_concat_def length_Bi_block)
next
  case (Suc n)
  show ?case using Bs_concat_Suc Suc length_Bi_block by simp
qed

text \<open>
  Column count of an expansion: \<open>A[n]\<close> has
  \<open>length (G_block A) + Suc n * length (B0_block A)\<close> columns
  (because \<open>strip_zero_rows\<close> preserves column count).
\<close>

lemma arr_len_expansion:
  assumes A_ne: "A \<noteq> []"
  shows "arr_len (A[n]) = length (G_block A) + Suc n * length (B0_block A)"
proof -
  have "A[n] = strip_zero_rows (G_block A @ Bs_concat A n)"
    using A_ne unfolding expansion_def by simp
  hence "arr_len (A[n]) = length (G_block A @ Bs_concat A n)"
    by (simp add: length_strip_zero_rows)
  also have "\<dots> = length (G_block A) + length (Bs_concat A n)"
    by simp
  also have "\<dots> = length (G_block A) + Suc n * length (B0_block A)"
    by (simp add: length_Bs_concat)
  finally show ?thesis .
qed

lemma arr_len_expansion_Suc:
  assumes A_ne: "A \<noteq> []"
  shows "arr_len (A[Suc n]) = arr_len (A[n]) + length (B0_block A)"
  using arr_len_expansion[OF A_ne, of "Suc n"]
        arr_len_expansion[OF A_ne, of n]
  by simp

text \<open>
  At the pre-strip level, the columns of \<open>A[Suc n]\<close>'s underlying
  array agree with those of \<open>A[n]\<close>'s on the shared index range
  (i.e.\ for \<open>i < arr_len (A[n])\<close>). After strip the lengths of
  individual columns may differ but column-indexing is preserved.
\<close>

lemma b0_start_lt_last:
  assumes "b0_start A = Some s"
  shows "s < last_col_idx A"
proof -
  obtain m\<^sub>0 where mp_eq: "max_parent_level A = Some m\<^sub>0"
                and par_eq: "m_parent A m\<^sub>0 (last_col_idx A) = Some s"
    using assms unfolding b0_start_def
    by (cases "max_parent_level A") auto
  show ?thesis using par_eq by (rule m_parent_lt)
qed

lemma l1_pos_of_some:
  assumes A_ne: "A \<noteq> []" and b0: "b0_start A = Some s"
  shows "0 < length (B0_block A)"
proof -
  have s_lt: "s < last_col_idx A" using b0 by (rule b0_start_lt_last)
  have last_lt: "last_col_idx A < length A" using A_ne by (cases A) auto
  have B0_form: "B0_block A = take (last_col_idx A - s) (drop s A)"
    using b0 by (simp add: B0_block_def)
  have len_drop: "length (drop s A) = length A - s"
    by simp
  have "length (B0_block A) = min (last_col_idx A - s) (length A - s)"
    using B0_form by simp
  also have "\<dots> = last_col_idx A - s"
    using s_lt last_lt by simp
  finally show ?thesis using s_lt by simp
qed

lemma pre_strip_expansion_prefix:
  assumes A_ne: "A \<noteq> []" and i_lt: "i < arr_len (expansion A n)"
  shows "(G_block A @ Bs_concat A (Suc n)) ! i = (G_block A @ Bs_concat A n) ! i"
proof -
  have len_eq: "arr_len (expansion A n) = length (G_block A @ Bs_concat A n)"
  proof -
    have "expansion A n = strip_zero_rows (G_block A @ Bs_concat A n)"
      using A_ne unfolding expansion_def by simp
    thus ?thesis by (simp add: length_strip_zero_rows)
  qed
  have i_lt_pre: "i < length (G_block A @ Bs_concat A n)"
    using i_lt len_eq by simp
  have decomp: "G_block A @ Bs_concat A (Suc n)
              = (G_block A @ Bs_concat A n) @ Bi_block A (Suc n)"
    by (simp add: Bs_concat_Suc)
  have step: "((G_block A @ Bs_concat A n) @ Bi_block A (Suc n)) ! i
             = (G_block A @ Bs_concat A n) ! i"
    by (rule nth_append_left[OF i_lt_pre]) (* nth_append_left: n < length xs ⟹ (xs @ ys) ! n = xs ! n *)
  show ?thesis using decomp step by simp
qed

lemma Bs_concat_take_l1:
  assumes ne: "A \<noteq> []"
  shows "take (length (B0_block A)) (Bs_concat A n) = B0_block A"
proof -
  let ?l = "length (B0_block A)"
  have aux: "take ?l (Bs_concat A n) = Bi_block A 0"
  proof (induct n)
    case 0
    have base: "Bs_concat A 0 = Bi_block A 0"
      by (simp add: Bs_concat_def)
    have take_b0i: "take ?l (Bi_block A 0) = Bi_block A 0"
      by (simp add: length_Bi_block)
    show ?case using base take_b0i by simp
  next
    case (Suc n)
    have step: "Bs_concat A (Suc n) = Bs_concat A n @ Bi_block A (Suc n)"
      by (simp add: Bs_concat_def)
    have len_lower: "?l \<le> length (Bs_concat A n)"
      using length_Bs_concat[where n = n and A = A] by simp
    have "take ?l (Bs_concat A (Suc n)) = take ?l (Bs_concat A n)"
      using step len_lower by (simp add: take_append)
    thus ?case using Suc by simp
  qed
  thus ?thesis using Bi_block_zero[OF ne] by simp
qed

lemma Bs_concat_nth_first_B1:
  assumes nge: "1 \<le> n" and bne: "0 < length (B0_block A)"
  shows "Bs_concat A n ! length (B0_block A) = bump_col A 0 1"
  using nge
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  let ?l = "length (B0_block A)"
  have bs_step: "Bs_concat A (Suc n) = Bs_concat A n @ Bi_block A (Suc n)"
    by (simp add: Bs_concat_def)
  show ?case
  proof (cases "n = 0")
    case True
    have bs0: "Bs_concat A 0 = Bi_block A 0"
      by (simp add: Bs_concat_def)
    have len_b0i: "length (Bi_block A 0) = ?l" by (rule length_Bi_block)
    have b1_nth: "Bi_block A 1 ! 0 = bump_col A 0 1"
      using Bi_block_nth[where d = 0 and i = 1] bne by simp
    have "Bs_concat A (Suc n) = Bi_block A 0 @ Bi_block A 1"
      using bs_step bs0 True by simp
    moreover have "(Bi_block A 0 @ Bi_block A 1) ! ?l = Bi_block A 1 ! 0"
      using len_b0i by (simp add: nth_append)
    ultimately show ?thesis using b1_nth by simp
  next
    case False
    have nge': "1 \<le> n" using False by simp
    have IH: "Bs_concat A n ! ?l = bump_col A 0 1"
      using Suc.hyps nge' by simp
    have len_lt: "?l < length (Bs_concat A n)"
      using length_Bs_concat[where n = n and A = A] bne nge' by simp
    show ?thesis using bs_step IH len_lt by (simp add: nth_append)
  qed
qed

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

text \<open>
  Out-of-range nth on equal-length replicates yields the same
  (default) value, regardless of the replicated value.
\<close>

lemma replicate_nth_oob_eq:
  fixes a b :: nat
  assumes "n \<le> m"
  shows "(replicate n a) ! m = (replicate n b) ! m"
  using assms
proof (induct n arbitrary: m)
  case 0 thus ?case by simp
next
  case (Suc n)
  obtain m' where m_eq: "m = Suc m'"
    using Suc.prems by (cases m) auto
  hence "n \<le> m'" using Suc.prems by simp
  hence ih: "(replicate n a) ! m' = (replicate n b) ! m'"
    by (rule Suc.hyps)
  show ?case using m_eq ih by simp
qed

text \<open>
  For \<open>m \<ge> n\<close>, the \<open>m\<close>-parent of column 1 in \<open>seed n\<close>
  is undefined, since the candidate filter compares two values that
  are equal (both out-of-range nth on \<open>replicate n _\<close>).
\<close>

lemma m_parent_seed_top:
  assumes "n \<le> m"
  shows "m_parent (seed n) m 1 = None"
proof -
  have eq: "(seed n) ! 0 ! m = (seed n) ! 1 ! m"
    using assms by (simp add: seed_def replicate_nth_oob_eq)
  hence not_lt: "\<not> elem (seed n) 0 m < elem (seed n) 1 m"
    unfolding elem_def by simp
  show ?thesis
  proof (cases m)
    case 0
    have "[j \<leftarrow> [0..<1]. elem (seed n) j 0 < elem (seed n) 1 0] = []"
      using not_lt 0 by simp
    thus ?thesis using 0 by (simp add: Let_def)
  next
    case (Suc m')
    have "[j \<leftarrow> [0..<1]. elem (seed n) j (Suc m') < elem (seed n) 1 (Suc m')
                          \<and> m_ancestor (seed n) m' 1 j] = []"
      using not_lt Suc by simp
    thus ?thesis using Suc by (simp add: Let_def)
  qed
qed

corollary m_ancestor_seed_top:
  assumes "n \<le> m"
  shows "\<not> m_ancestor (seed n) m 1 0"
  using m_parent_seed_top[OF assms] by simp

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
proof -
  let ?A = "seed (Suc n)"
  let ?f = "\<lambda>m. (replicate (Suc n) 0) ! m
                + (if ascends ?A 0 m then 1 * delta ?A m else 0)"
  have b0: "b0_start ?A = Some 0" using b0_start_seed by simp
  have c_eq: "?A ! (0 + 0) = replicate (Suc n) 0"
    using seed_nth0 by simp
  have len_c: "length (?A ! (0 + 0)) = Suc n"
    using c_eq length_replicate by metis
  let ?lhs = "bump_col ?A 0 1"
  let ?rhs = "replicate n 1 @ [0]"
  have lhs_unfold: "?lhs = map ?f [0..<Suc n]"
    unfolding bump_col_def Let_def
    using b0 c_eq len_c by (simp only: option.case)
  have len_lhs: "length ?lhs = Suc n"
    using lhs_unfold by simp
  have len_rhs: "length ?rhs = Suc n" by simp
  have nth_lhs: "?lhs ! i = ?f i" if i_lt: "i < Suc n" for i
    using lhs_unfold i_lt by (simp only: nth_map_upt) simp
  have z_rep: "(replicate (Suc n) 0) ! i = 0" if "i < Suc n" for i
    using that nth_replicate by metis
  have nth_eq: "?lhs ! i = ?rhs ! i" if i_lt: "i < Suc n" for i
  proof (cases "i < n")
    case True
    have asc: "ascends ?A 0 i" using ascends_seed_succ[OF True] .
    have dlt: "delta ?A i = 1" using delta_seed_succ[where m = i] i_lt by simp
    have z: "(replicate (Suc n) 0) ! i = 0" using z_rep i_lt by simp
    have "?lhs ! i = ?f i" using nth_lhs i_lt by simp
    also have "\<dots> = 0 + 1 * 1" using asc dlt z by simp
    also have "\<dots> = 1" by simp
    finally have lhs_val: "?lhs ! i = 1" .
    have rhs_val: "?rhs ! i = 1"
      using True by (simp add: nth_append)
    show ?thesis using lhs_val rhs_val by metis
  next
    case False
    with i_lt have i_eq: "i = n" by simp
    have nasc: "\<not> ascends ?A 0 n" using not_ascends_seed_succ_top .
    have z: "(replicate (Suc n) 0) ! n = 0"
      using z_rep[of n] by simp
    have "?lhs ! n = ?f n" using nth_lhs[of n] by simp
    also have "\<dots> = 0" using nasc z by simp
    finally have lhs_val: "?lhs ! n = 0" .
    have rhs_val: "?rhs ! n = 0"
      by (simp add: nth_append)
    show ?thesis using lhs_val rhs_val i_eq by metis
  qed
  show ?thesis
  proof (intro nth_equalityI)
    show "length ?lhs = length ?rhs" using len_lhs len_rhs by simp
  next
    fix i assume "i < length ?lhs"
    hence "i < Suc n" using len_lhs by simp
    thus "?lhs ! i = ?rhs ! i" using nth_eq by simp
  qed
qed

text \<open>
  General-\<open>i\<close> version of @{thm bump_col_seed_one}: the bumped
  column of \<open>seed (Suc n)\<close> with multiplier \<open>i\<close> equals
  \<open>replicate n i @ [0]\<close>.
\<close>

lemma bump_col_seed:
  shows "bump_col (seed (Suc n)) 0 i = replicate n i @ [0]"
proof -
  let ?A = "seed (Suc n)"
  let ?f = "\<lambda>m. (replicate (Suc n) 0) ! m
                + (if ascends ?A 0 m then i * delta ?A m else 0)"
  have b0: "b0_start ?A = Some 0" using b0_start_seed by simp
  have c_eq: "?A ! (0 + 0) = replicate (Suc n) 0"
    using seed_nth0 by simp
  have len_c: "length (?A ! (0 + 0)) = Suc n"
    using c_eq length_replicate by metis
  let ?lhs = "bump_col ?A 0 i"
  let ?rhs = "replicate n i @ [0]"
  have lhs_unfold: "?lhs = map ?f [0..<Suc n]"
    unfolding bump_col_def Let_def
    using b0 c_eq len_c by (simp only: option.case)
  have len_lhs: "length ?lhs = Suc n"
    using lhs_unfold by simp
  have len_rhs: "length ?rhs = Suc n" by simp
  have nth_lhs: "?lhs ! m = ?f m" if m_lt: "m < Suc n" for m
    using lhs_unfold m_lt by (simp only: nth_map_upt) simp
  have z_rep: "(replicate (Suc n) 0) ! m = 0" if "m < Suc n" for m
    using that nth_replicate by metis
  have nth_eq: "?lhs ! m = ?rhs ! m" if m_lt: "m < Suc n" for m
  proof (cases "m < n")
    case True
    have asc: "ascends ?A 0 m" using ascends_seed_succ[OF True] .
    have dlt: "delta ?A m = 1" using delta_seed_succ[where m = m] m_lt by simp
    have z: "(replicate (Suc n) 0) ! m = 0" using z_rep m_lt by simp
    have "?lhs ! m = ?f m" using nth_lhs m_lt by simp
    also have "\<dots> = 0 + i * 1" using asc dlt z by simp
    also have "\<dots> = i" by simp
    finally have lhs_val: "?lhs ! m = i" .
    have rhs_val: "?rhs ! m = i"
      using True by (simp add: nth_append)
    show ?thesis using lhs_val rhs_val by metis
  next
    case False
    with m_lt have m_eq: "m = n" by simp
    have nasc: "\<not> ascends ?A 0 n" using not_ascends_seed_succ_top .
    have z: "(replicate (Suc n) 0) ! n = 0"
      using z_rep[of n] by simp
    have "?lhs ! n = ?f n" using nth_lhs[of n] by simp
    also have "\<dots> = 0" using nasc z by simp
    finally have lhs_val: "?lhs ! n = 0" .
    have rhs_val: "?rhs ! n = 0"
      by (simp add: nth_append)
    show ?thesis using lhs_val rhs_val m_eq by metis
  qed
  show ?thesis
  proof (intro nth_equalityI)
    show "length ?lhs = length ?rhs" using len_lhs len_rhs by simp
  next
    fix m assume "m < length ?lhs"
    hence "m < Suc n" using len_lhs by simp
    thus "?lhs ! m = ?rhs ! m" using nth_eq by simp
  qed
qed

lemma B0_block_seed:
  shows "B0_block (seed (Suc n)) = [replicate (Suc n) 0]"
proof -
  have b0: "b0_start (seed (Suc n)) = Some 0" using b0_start_seed by simp
  have len: "length (seed (Suc n)) = 2" by (rule length_seed)
  have last_idx: "last_col_idx (seed (Suc n)) = 1" using len by simp
  have "B0_block (seed (Suc n))
          = take (last_col_idx (seed (Suc n)) - 0) (drop 0 (seed (Suc n)))"
    using b0 by (simp add: B0_block_def)
  also have "\<dots> = take 1 (seed (Suc n))" using last_idx by simp
  also have "\<dots> = [(seed (Suc n)) ! 0]" using len by (simp add: take_Suc_conv_app_nth)
  also have "\<dots> = [replicate (Suc n) 0]" using seed_nth0 by simp
  finally show ?thesis .
qed

lemma length_B0_block_seed:
  shows "length (B0_block (seed (Suc n))) = 1"
  by (simp add: B0_block_seed)

lemma Bi_block_seed:
  shows "Bi_block (seed (Suc n)) i = [replicate n i @ [0]]"
proof -
  have len: "length (B0_block (seed (Suc n))) = 1" by (rule length_B0_block_seed)
  have "Bi_block (seed (Suc n)) i
          = map (\<lambda>d. bump_col (seed (Suc n)) d i) [0..<1]"
    unfolding Bi_block_def Let_def using len by simp
  also have "\<dots> = [bump_col (seed (Suc n)) 0 i]" by simp
  also have "\<dots> = [replicate n i @ [0]]" using bump_col_seed by simp
  finally show ?thesis .
qed

text \<open>
  Closed form of \<open>Bs_concat (seed (Suc n)) k\<close>: it is a list of
  \<open>k+1\<close> bumped columns, one for each \<open>i \<in> [0..k]\<close>.
\<close>

lemma Bs_concat_seed:
  shows "Bs_concat (seed (Suc n)) k = map (\<lambda>i. replicate n i @ [0]) [0..<Suc k]"
proof (induct k)
  case 0
  show ?case
    by (simp add: Bs_concat_def Bi_block_seed)
next
  case (Suc k)
  have step: "Bs_concat (seed (Suc n)) (Suc k)
                = Bs_concat (seed (Suc n)) k @ Bi_block (seed (Suc n)) (Suc k)"
    by (simp add: Bs_concat_def)
  have map_eq: "map (\<lambda>i. replicate n i @ [0]) [0..<Suc k]
                  @ [replicate n (Suc k) @ [0]]
                = map (\<lambda>i. replicate n i @ [0]) [0..<Suc (Suc k)]"
    by simp
  show ?case
    using step Suc.hyps Bi_block_seed[where i = "Suc k"] map_eq by simp
qed

text \<open>
  Strip applied to the closed-form \<open>Bs_concat (seed (Suc n)) k\<close>
  for \<open>k \<ge> 1\<close>: the trailing all-zero row is removed, exposing
  \<open>replicate n i\<close> for each column index \<open>i\<close>.
\<close>

lemma strip_zero_rows_seed_form:
  fixes n k :: nat
  assumes "1 \<le> k"
  shows "strip_zero_rows (map (\<lambda>i. replicate n i @ [0]) [0..<Suc k])
       = map (\<lambda>i. replicate n i) [0..<Suc k]"
proof -
  let ?X = "map (\<lambda>i. replicate n i @ [0]) [0..<Suc k]"
  let ?P = "\<lambda>h. h \<le> Suc n
              \<and> (\<forall>m. h \<le> m \<and> m < Suc n
                  \<longrightarrow> (\<forall>c \<in> set ?X. c ! m = 0))"

  have X_ne: "?X \<noteq> []" by simp
  have X_len: "length ?X = Suc k" by simp
  have upt_decomp: "[0..<Suc k] = 0 # [Suc 0..<Suc k]"
    by (rule upt_conv_Cons) simp
  have X_cons: "?X = (replicate n 0 @ [0])
                     # map (\<lambda>i. replicate n i @ [0]) [Suc 0..<Suc k]"
    by (subst upt_decomp) simp
  have hd_X: "hd ?X = replicate n 0 @ [0]" using X_cons by simp
  have height_X: "height ?X = Suc n"
    using X_ne hd_X by simp

  have set_X: "set ?X = (\<lambda>i. replicate n i @ [0]) ` set [0..<Suc k]"
    by simp

  have one_in: "replicate n (Suc 0) @ [0] \<in> set ?X"
  proof -
    have "Suc 0 < Suc k" using assms by linarith
    hence "Suc 0 \<in> set [0..<Suc k]" by auto
    thus ?thesis by force
  qed

  have P_n: "?P n"
  proof (intro conjI allI impI)
    show "n \<le> Suc n" by simp
  next
    fix m
    assume mb: "n \<le> m \<and> m < Suc n"
    hence m_eq: "m = n" by simp
    show "\<forall>c \<in> set ?X. c ! m = 0"
    proof
      fix c assume c_in: "c \<in> set ?X"
      have "set ?X = (\<lambda>i. replicate n i @ [0]) ` set [0..<Suc k]"
        by simp
      hence "c \<in> (\<lambda>i. replicate n i @ [0]) ` set [0..<Suc k]"
        using c_in by simp
      then obtain i where c_eq: "c = replicate n i @ [0]"
        by blast
      have "c ! m = (replicate n i @ [0]) ! n" using c_eq m_eq by simp
      also have "\<dots> = [0] ! 0" by (simp add: nth_append)
      finally show "c ! m = 0" by simp
    qed
  qed

  have ge_n: "n \<le> h" if Ph: "?P h" for h
  proof (rule ccontr)
    assume "\<not> n \<le> h"
    hence h_lt: "h < n" by simp
    have h_in_range: "h \<le> h \<and> h < Suc n" using h_lt by simp
    have all_zero: "\<forall>c \<in> set ?X. c ! h = 0"
      using Ph h_in_range by blast
    have nth_one: "(replicate n (Suc 0) @ [0]) ! h = Suc 0"
      using h_lt by (simp add: nth_append)
    note c1_eq = all_zero[THEN bspec, OF one_in]
    show False using c1_eq nth_one by simp
  qed

  have least_eq: "(LEAST h. ?P h) = n"
  proof (rule Least_equality)
    show "?P n" by (rule P_n)
  next
    fix h' assume "?P h'"
    thus "n \<le> h'" by (rule ge_n)
  qed

  have take_eq: "take n (replicate n i @ [0]) = replicate n i" for i
    by simp

  have "strip_zero_rows ?X = map (\<lambda>c. take n c) ?X"
    unfolding strip_zero_rows_def Let_def
    using X_ne height_X least_eq by simp
  also have "\<dots> = map ((\<lambda>c. take n c) \<circ> (\<lambda>i. replicate n i @ [0])) [0..<Suc k]"
    by (simp add: map_map)
  also have "\<dots> = map (\<lambda>i. replicate n i) [0..<Suc k]"
    using take_eq by (simp add: o_def)
  finally show ?thesis .
qed

text \<open>
  Strip is the identity on \<open>map (\<lambda>j. replicate n j) [0..<Suc k]\<close>
  for \<open>k \<ge> 1\<close>: rows contain \<open>(0, 1, ..., k)\<close> which is non-zero,
  so no row strips.
\<close>

lemma strip_zero_rows_no_zero_row:
  assumes "1 \<le> k"
  shows "strip_zero_rows (map (\<lambda>j. replicate n j) [0..<Suc k])
       = map (\<lambda>j. replicate n j) [0..<Suc k]"
proof -
  let ?Y = "map (\<lambda>j. replicate n j) [0..<Suc k]"
  let ?P = "\<lambda>h. h \<le> n
              \<and> (\<forall>m. h \<le> m \<and> m < n
                  \<longrightarrow> (\<forall>c \<in> set ?Y. c ! m = 0))"

  have Y_ne: "?Y \<noteq> []" by simp
  have upt_decomp: "[0..<Suc k] = 0 # [Suc 0..<Suc k]"
    by (rule upt_conv_Cons) simp
  have Y_cons: "?Y = replicate n 0
                     # map (\<lambda>j. replicate n j) [Suc 0..<Suc k]"
    by (subst upt_decomp) simp
  have height_Y: "height ?Y = n" using Y_cons by simp

  have P_n: "?P n" by simp

  have ge_n: "n \<le> h" if Ph: "?P h" for h
  proof (cases "n = 0")
    case True thus ?thesis by simp
  next
    case False
    show ?thesis
    proof (rule ccontr)
      assume "\<not> n \<le> h"
      hence h_lt: "h < n" by simp
      have h_in_range: "h \<le> h \<and> h < n" using h_lt by simp
      have all_zero: "\<forall>c \<in> set ?Y. c ! h = 0"
        using Ph h_in_range by blast
      have one_in: "replicate n (Suc 0) \<in> set ?Y"
      proof -
        have "Suc 0 < Suc k" using assms by linarith
        hence "Suc 0 \<in> set [0..<Suc k]" by auto
        thus ?thesis by force
      qed
      have nth_one: "(replicate n (Suc 0)) ! h = Suc 0"
        using h_lt by simp
      note c_eq = all_zero[THEN bspec, OF one_in]
      show False using c_eq nth_one by simp
    qed
  qed

  have least_eq: "(LEAST h. ?P h) = n"
  proof (rule Least_equality)
    show "?P n" by (rule P_n)
  next
    fix h' assume "?P h'"
    thus "n \<le> h'" by (rule ge_n)
  qed

  have take_n: "take n (replicate n j) = replicate n j" for j by simp

  have "strip_zero_rows ?Y = map (\<lambda>c. take n c) ?Y"
    unfolding strip_zero_rows_def Let_def
    using Y_ne height_Y least_eq by simp
  also have "\<dots> = map ((\<lambda>c. take n c) \<circ> (\<lambda>j. replicate n j)) [0..<Suc k]"
    by (simp add: map_map)
  also have "\<dots> = map (\<lambda>j. replicate n j) [0..<Suc k]"
    using take_n by (simp add: o_def)
  finally show ?thesis .
qed

text \<open>
  Closed form of \<open>seed (Suc n) [k]\<close> for \<open>k \<ge> 1\<close>:
  \<open>k+1\<close> columns, each \<open>replicate n j\<close> for \<open>j \<in> [0..k]\<close>.
  (For \<open>k = 0\<close> the form would be \<open>[replicate n 0]\<close> which
  strips to \<open>[[]]\<close>; that case is handled by \<open>seed_expansion_zero\<close>
  below.)
\<close>

lemma seed_expansion_form:
  assumes "1 \<le> k"
  shows "(seed (Suc n))[k] = map (\<lambda>j. replicate n j) [0..<Suc k]"
proof -
  let ?A = "seed (Suc n)"
  have ne: "?A \<noteq> []" by (rule seed_nonempty)
  have b0: "b0_start ?A = Some 0" using b0_start_seed by simp
  have G_eq: "G_block ?A = []" using b0 by (simp add: G_block_def)
  have Bs_eq: "Bs_concat ?A k = map (\<lambda>i. replicate n i @ [0]) [0..<Suc k]"
    by (rule Bs_concat_seed)
  have "(seed (Suc n))[k]
          = strip_zero_rows (G_block ?A @ Bs_concat ?A k)"
    unfolding expansion_def using ne by simp
  also have "\<dots> = strip_zero_rows (map (\<lambda>i. replicate n i @ [0]) [0..<Suc k])"
    using G_eq Bs_eq by simp
  also have "\<dots> = map (\<lambda>j. replicate n j) [0..<Suc k]"
    by (rule strip_zero_rows_seed_form[OF assms])
  finally show ?thesis .
qed

text \<open>
  Strip helper: when \<open>X = [replicate (Suc n) 0, replicate n 1 @ [0]]\<close>,
  the @{const strip_zero_rows} of \<open>X\<close> equals @{term "seed n"}.
\<close>

lemma strip_zero_rows_seed_X:
  fixes n :: nat
  defines "X \<equiv> [replicate (Suc n) (0::nat), replicate n 1 @ [0]]"
  shows "strip_zero_rows X = seed n"
proof -
  have X_ne: "X \<noteq> []" by (simp add: X_def)
  have hX: "height X = Suc n" by (simp add: X_def)
  let ?P = "\<lambda>h. h \<le> Suc n \<and>
              (\<forall>m. h \<le> m \<and> m < Suc n \<longrightarrow> (\<forall>c \<in> set X. c ! m = 0))"
  let ?keep = "Least ?P"

  have wit_n: "?P n"
  proof -
    have a: "\<forall>m. n \<le> m \<and> m < Suc n \<longrightarrow> (\<forall>c \<in> set X. c ! m = 0)"
    proof (intro allI impI)
      fix m assume "n \<le> m \<and> m < Suc n"
      hence m_eq: "m = n" by simp
      have e1: "(replicate (Suc n) (0::nat)) ! n = 0"
        by (rule nth_replicate) simp
      have e2: "(replicate n (1::nat) @ [0]) ! n = 0"
        by (simp add: nth_append)
      show "\<forall>c \<in> set X. c ! m = 0"
        using e1 e2 m_eq by (simp add: X_def)
    qed
    show ?thesis using a by simp
  qed
  have keep_le_n: "?keep \<le> n" using wit_n by (rule Least_le)

  have not_P: "\<not> ?P k" if k_lt: "k < n" for k
  proof
    assume P_k: "?P k"
    have c_in: "(replicate n (1::nat) @ [0]) \<in> set X" by (simp add: X_def)
    have k_le_k: "k \<le> k \<and> k < Suc n" using k_lt by simp
    from P_k k_le_k c_in have z: "(replicate n (1::nat) @ [0]) ! k = 0" by blast
    have len_lt: "k < length (replicate n (1::nat))" using k_lt by simp
    have nz: "(replicate n (1::nat) @ [0]) ! k = 1"
      using len_lt by (simp add: nth_append)
    show False using z nz by simp
  qed

  have keep_ge_n: "n \<le> ?keep"
  proof (rule ccontr)
    assume "\<not> n \<le> ?keep"
    hence "?keep < n" by simp
    moreover have "?P ?keep"
      using wit_n by (rule LeastI)
    ultimately show False using not_P by blast
  qed

  have keep_eq: "?keep = n" using keep_le_n keep_ge_n by simp

  have strip_form: "strip_zero_rows X = map (\<lambda>c. take ?keep c) X"
    using X_ne hX unfolding strip_zero_rows_def by (simp add: Let_def)
  have strip_n: "strip_zero_rows X = map (\<lambda>c. take n c) X"
    using strip_form keep_eq by simp
  have take_a: "take n (replicate (Suc n) (0::nat)) = replicate n 0"
  proof -
    have "take n (replicate (Suc n) (0::nat)) = replicate (min n (Suc n)) 0"
      by (rule take_replicate)
    also have "min n (Suc n) = n" by simp
    finally show ?thesis .
  qed
  have take_b: "take n (replicate n (1::nat) @ [0]) = replicate n 1"
    by simp
  have map_eq: "map (\<lambda>c. take n c) X = [replicate n 0, replicate n 1]"
    using take_a take_b by (simp add: X_def)
  show ?thesis
    using strip_n map_eq by (simp add: seed_def)
qed

lemma seed_Suc_expand_one:
  shows "(seed (Suc n))[1] = seed n"
proof -
  let ?A = "seed (Suc n)"
  have ne: "?A \<noteq> []" by (rule seed_nonempty)
  have len_A: "length ?A = 2" by (rule length_seed)
  have last_idx: "last_col_idx ?A = 1" using len_A by simp
  have b0: "b0_start ?A = Some 0" using b0_start_seed[where n = "Suc n"] by simp

  have G_eq: "G_block ?A = []"
    using b0 by (simp add: G_block_def)
  have B0_eq: "B0_block ?A = [?A ! 0]"
    using b0 last_idx len_A by (simp add: B0_block_def take_Suc_conv_app_nth)
  have B0_len: "length (B0_block ?A) = 1" using B0_eq by simp

  have Bi0: "Bi_block ?A 0 = B0_block ?A"
    by (rule Bi_block_zero[OF ne])

  have bump_eq: "bump_col ?A 0 1 = replicate n 1 @ [0]"
    by (rule bump_col_seed_one)
  have Bi1: "Bi_block ?A 1 = [replicate n 1 @ [0]]"
  proof -
    have "Bi_block ?A 1 = map (\<lambda>d. bump_col ?A d 1) [0..<1]"
      unfolding Bi_block_def Let_def using B0_len by simp
    also have "\<dots> = [bump_col ?A 0 1]" by simp
    finally show ?thesis using bump_eq by simp
  qed

  have Bs_step: "Bs_concat ?A 1 = Bi_block ?A 0 @ Bi_block ?A 1"
    by (simp add: Bs_concat_def)
  have A0: "?A ! 0 = replicate (Suc n) 0" by (rule seed_nth0)

  have X_eq: "G_block ?A @ Bs_concat ?A 1
            = [replicate (Suc n) (0::nat), replicate n 1 @ [0]]"
    using G_eq Bs_step Bi0 Bi1 B0_eq A0 by simp

  show ?thesis
    unfolding expansion_def
    using ne X_eq strip_zero_rows_seed_X[where n = n] by simp
qed

text \<open>
  \<open>seed N [0]\<close> collapses to a single empty column for every \<open>N\<close>.

  Computation: \<open>butlast (seed N) = [replicate N 0]\<close>, a single
  all-zero column.  \<open>strip_zero_rows\<close> strips every all-zero row,
  yielding the single column of zero rows \<open>[[]]\<close>.
\<close>

lemma seed_expansion_zero:
  shows "(seed N)[0] = [[]]"
proof -
  have ne: "seed N \<noteq> []" by (rule seed_nonempty)
  have bl: "butlast (seed N) = [replicate N 0]"
    by (simp add: seed_def)
  let ?X = "[replicate N (0::nat)]"
  have H: "height ?X = N" by simp
  have keep0_cond: "(0::nat) \<le> N \<and>
                    (\<forall>m. 0 \<le> m \<and> m < N \<longrightarrow> (\<forall>c \<in> set ?X. c ! m = 0))"
    by simp
  have least_eq: "(LEAST h. h \<le> N \<and>
                     (\<forall>m. h \<le> m \<and> m < N \<longrightarrow> (\<forall>c \<in> set ?X. c ! m = 0))) = 0"
    by (rule Least_equality, simp_all)
  have strip_eq: "strip_zero_rows ?X = [[]]"
  proof (cases "?X = []")
    case True thus ?thesis by simp
  next
    case False
    have "strip_zero_rows ?X
            = map (\<lambda>c. take 0 c) ?X"
      unfolding strip_zero_rows_def Let_def using False least_eq H by simp
    also have "\<dots> = [[]]" by simp
    finally show ?thesis .
  qed
  have "(seed N)[0] = strip_zero_rows (butlast (seed N))"
    by (rule expansion_zero_eq[OF ne])
  also have "\<dots> = strip_zero_rows ?X" using bl by simp
  also have "\<dots> = [[]]" using strip_eq .
  finally show ?thesis .
qed

text \<open>
  Base case of the structural identity \<open>(seed N [Suc k])[0] = seed N [k]\<close>
  for \<open>k = 0\<close> (with \<open>N \<ge> 1\<close>): \<open>(seed N [1])[0] = seed N [0]\<close>.

  Both sides equal \<open>[[]]\<close>.  Combined with @{thm seed_Suc_expand_one}
  giving \<open>seed (Suc m)[1] = seed m\<close>, this reduces to
  \<open>(seed m)[0] = (seed (Suc m))[0]\<close>, which is immediate from
  @{thm seed_expansion_zero}.
\<close>

text \<open>
  Degenerate base \<open>N = 0\<close>: every expansion of \<open>seed 0\<close> is
  \<open>[[]]\<close>.  Follows from @{thm expansion_no_b0_eq_zero} since
  \<open>b0_start (seed 0) = None\<close> (height 0 leaves no \<open>m\<^sub>0\<close>-parent
  candidates).
\<close>

lemma seed_0_expansion:
  shows "(seed 0)[k] = [[]]"
proof -
  have ne: "seed 0 \<noteq> []" by (rule seed_nonempty)
  have b0: "b0_start (seed 0) = None"
  proof -
    have h: "height (seed 0) = 0" by (simp add: seed_def)
    have "max_parent_level (seed 0) = None"
      unfolding max_parent_level_def using ne h by (simp add: Let_def)
    thus ?thesis by (simp add: b0_start_def)
  qed
  have "(seed 0)[k] = (seed 0)[0]"
    using expansion_no_b0_eq_zero[OF ne b0] .
  also have "\<dots> = [[]]" by (rule seed_expansion_zero)
  finally show ?thesis .
qed

text \<open>
  Companion: \<open>[[]][k] = []\<close>.  The single-empty-column array
  has \<open>b0_start = None\<close>, so its expansion is the strip of its
  \<open>butlast\<close> = \<open>[]\<close>.
\<close>

text \<open>
  \<open>(seed 1)[k] = replicate (Suc k) []\<close>: a uniform closed form
  combining the \<open>k = 0\<close> base (\<open>[[]] = replicate 1 []\<close>) and
  the \<open>k \<ge> 1\<close> case of @{thm seed_expansion_form}
  (\<open>map (\<lambda>j. replicate 0 j) [0..<Suc k] = replicate (Suc k) []\<close>).
\<close>

lemma seed_1_expansion:
  shows "(seed 1)[k] = replicate (Suc k) []"
proof (cases k)
  case 0
  have "(seed 1)[0] = [[]]" by (rule seed_expansion_zero)
  also have "[[]] = replicate 1 []" by simp
  finally show ?thesis using 0 by simp
next
  case (Suc k')
  hence k_ge: "1 \<le> k" by simp
  have form: "(seed (Suc 0))[k] = map (\<lambda>j. replicate 0 j) [0..<Suc k]"
    by (rule seed_expansion_form[OF k_ge])
  have aux: "map (\<lambda>j. replicate 0 j) [0..<n] = replicate n ([] :: nat list)" for n
  proof (induct n)
    case 0 show ?case by simp
  next
    case (Suc n)
    have "map (\<lambda>j. replicate 0 j) [0..<Suc n]
            = map (\<lambda>j. replicate 0 j) [0..<n] @ [replicate 0 n]" by simp
    also have "\<dots> = replicate n [] @ [[]]" using Suc by simp
    also have "\<dots> = replicate (Suc n) []"
      by (simp add: replicate_append_same)
    finally show ?case .
  qed
  show ?thesis using form aux by (simp add: replicate_append_same)
qed

text \<open>
  Expansion of \<open>replicate (Suc k) []\<close>: collapses to
  \<open>replicate k []\<close> regardless of \<open>m\<close> (height-0 array has
  \<open>b0_start = None\<close>, so expansion is determined by
  \<open>butlast\<close>).
\<close>

lemma replicate_empty_expansion:
  shows "(replicate (Suc k) ([] :: nat list))[m] = replicate k []"
proof -
  let ?A = "replicate (Suc k) ([] :: nat list)"
  have ne: "?A \<noteq> []" by simp
  have b0: "b0_start ?A = None"
  proof -
    have h: "height ?A = 0" by simp
    have "max_parent_level ?A = None"
      unfolding max_parent_level_def using ne h by (simp add: Let_def)
    thus ?thesis by (simp add: b0_start_def)
  qed
  have G_eq: "G_block ?A = butlast ?A"
    using b0 by (simp add: G_block_def)
  have bl: "butlast ?A = replicate k []"
  proof -
    have "?A = replicate k ([] :: nat list) @ [[]]"
      by (simp add: replicate_append_same)
    thus ?thesis by simp
  qed
  have Bs_empty: "Bs_concat ?A m = []"
    unfolding Bs_concat_def using b0
    by (simp add: Bi_block_def B0_block_def)
  have "?A[m] = strip_zero_rows (G_block ?A @ Bs_concat ?A m)"
    unfolding expansion_def using ne by simp
  also have "\<dots> = strip_zero_rows (replicate k [])"
    using G_eq bl Bs_empty by simp
  also have "\<dots> = replicate k []"
  proof (cases k)
    case 0
    thus ?thesis by (simp add: strip_zero_rows_def)
  next
    case (Suc k')
    have ne_rk: "replicate k ([] :: nat list) \<noteq> []" using Suc by simp
    have h_rk: "height (replicate k ([] :: nat list)) = 0" by simp
    have least: "(LEAST h. h \<le> 0 \<and>
                  (\<forall>m. h \<le> m \<and> m < 0 \<longrightarrow>
                    (\<forall>c \<in> set (replicate k ([] :: nat list)). c ! m = 0))) = 0"
      by simp
    have "strip_zero_rows (replicate k ([] :: nat list))
            = map (\<lambda>c. take 0 c) (replicate k [])"
      unfolding strip_zero_rows_def Let_def
      using ne_rk h_rk least by simp
    also have "\<dots> = replicate k []" by (induct k) auto
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma empty_col_expansion:
  shows "[[]][k] = []"
proof -
  let ?A = "[[] :: nat list]"
  have ne: "?A \<noteq> []" by simp
  have b0: "b0_start ?A = None"
  proof -
    have h: "height ?A = 0" by simp
    have "max_parent_level ?A = None"
      unfolding max_parent_level_def using ne h by (simp add: Let_def)
    thus ?thesis by (simp add: b0_start_def)
  qed
  have "?A[k] = ?A[0]"
    using expansion_no_b0_eq_zero[OF ne b0] .
  also have "\<dots> = strip_zero_rows (butlast ?A)"
    by (rule expansion_zero_eq[OF ne])
  also have "\<dots> = strip_zero_rows []" by simp
  also have "\<dots> = []" by (simp add: strip_zero_rows_def)
  finally show ?thesis .
qed

lemma seed_expansion_one_zero:
  shows "(seed (Suc m))[1][0] = (seed (Suc m))[0]"
proof -
  have "(seed (Suc m))[1][0] = (seed m)[0]"
    using seed_Suc_expand_one by simp
  also have "\<dots> = [[]]" by (rule seed_expansion_zero)
  also have "\<dots> = (seed (Suc m))[0]" using seed_expansion_zero by simp
  finally show ?thesis .
qed

text \<open>
  Structural identity \<open>(seed (Suc n) [Suc k])[0] = seed (Suc n) [k]\<close>
  for any \<open>k \<ge> 0\<close>.  This is the strip-respecting reading of
  Hunter's \<open>A[0]\<close>-induction step (cf. \<open>bug.md\<close> entry B-1).

  Combined with \<open>bms_le_expand\<close> (in BMS_Lex) this yields the
  expansion chain \<open>seed N [k] \<le>\<^sub>B seed N [k+1]\<close>, hence
  \<open>k \<le> k' \<Longrightarrow> seed N [k] \<le>\<^sub>B seed N [k']\<close>.
\<close>

lemma seed_expansion_succ_zero:
  shows "(seed (Suc n))[Suc k][0] = (seed (Suc n))[k]"
proof (cases k)
  case 0
  thus ?thesis using seed_expansion_one_zero by simp
next
  case (Suc k')
  hence k_ge: "1 \<le> k" by simp
  hence suc_k_ge: "1 \<le> Suc k" by simp
  let ?A = "seed (Suc n)"
  let ?Yk  = "map (\<lambda>j. replicate n j) [0..<Suc k]"
  let ?Ysk = "map (\<lambda>j. replicate n j) [0..<Suc (Suc k)]"
  have A_Suc_k_eq: "?A[Suc k] = ?Ysk"
    by (rule seed_expansion_form[OF suc_k_ge])
  have A_k_eq: "?A[k] = ?Yk"
    by (rule seed_expansion_form[OF k_ge])
  have ne_A_Suc_k: "?A[Suc k] \<noteq> []" using A_Suc_k_eq by simp
  have butlast_eq: "butlast ?Ysk = ?Yk"
  proof -
    have upt_split: "[0..<Suc (Suc k)] = [0..<Suc k] @ [Suc k]" by simp
    have ysk_snoc: "?Ysk = ?Yk @ [replicate n (Suc k)]"
      by (subst upt_split) simp
    have "butlast ?Ysk = butlast (?Yk @ [replicate n (Suc k)])"
      using ysk_snoc by simp
    also have "\<dots> = ?Yk" by (simp add: butlast_append)
    finally show ?thesis .
  qed
  have "?A[Suc k][0] = strip_zero_rows (butlast (?A[Suc k]))"
    by (rule expansion_zero_eq[OF ne_A_Suc_k])
  also have "\<dots> = strip_zero_rows (butlast ?Ysk)" using A_Suc_k_eq by simp
  also have "\<dots> = strip_zero_rows ?Yk" using butlast_eq by simp
  also have "\<dots> = ?Yk" by (rule strip_zero_rows_no_zero_row[OF k_ge])
  also have "\<dots> = ?A[k]" using A_k_eq by simp
  finally show ?thesis .
qed

inductive_set BMS :: "array set" where
  seed_in_BMS:   "seed n \<in> BMS"
| expand_in_BMS: "A \<in> BMS \<Longrightarrow> A[n] \<in> BMS"

inductive bms_le :: "array \<Rightarrow> array \<Rightarrow> bool" (infix "\<le>\<^sub>B" 50) where
  bms_le_refl: "A \<le>\<^sub>B A"
| bms_le_step: "A' \<le>\<^sub>B A[n] \<Longrightarrow> A' \<le>\<^sub>B A"

definition bms_lt :: "array \<Rightarrow> array \<Rightarrow> bool" (infix "<\<^sub>B" 50) where
  "A' <\<^sub>B A \<longleftrightarrow> A' \<le>\<^sub>B A \<and> A' \<noteq> A"

end
