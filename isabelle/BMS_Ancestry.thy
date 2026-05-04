(*
  BMS_Ancestry.thy

  Formalization of Lemma 2.5 of
    Rachel Hunter, "Well-Orderedness of the Bashicu Matrix System"
    (arXiv:2307.04606v3, 2024).

  Lemma 2.5 has five clauses (i)--(v), proved by simultaneous induction
  on \<open>k\<close>. We state each clause as its own lemma and discharge them
  jointly inside one proof.

  Notation: in the lemma below, \<open>A\<close> is a non-empty array, \<open>n\<close> a
  natural number, and from Definition 1.1 we have arrays
  \<open>G, B\<^sub>0, B\<^sub>1, ..., B_n, m\<^sub>0\<close> with
  \<open>A = G + B\<^sub>0 + (C)\<close> and \<open>A[n] = G + B\<^sub>0 + B\<^sub>1 + ... + B_n\<close>
  (zero rows stripped). \<open>l\<^sub>0 = arr_len G\<close>, \<open>l\<^sub>1 = arr_len B\<^sub>0\<close>.
*)

theory BMS_Ancestry
  imports BMS_Lex
begin

section \<open>Auxiliary: positions in \<open>A[n]\<close>\<close>

text \<open>
  We need to refer to the \<open>i\<close>-th column of \<open>G\<close>, of \<open>B_t\<close>
  (for \<open>0 \<le> t \<le> n\<close>) inside both \<open>A\<close> and \<open>A[n]\<close>. Below,
  \<open>idx_G A i\<close>, \<open>idx_B A t i\<close> denote those indices in
  \<open>A[n]\<close>; in \<open>A\<close> itself, \<open>B_t\<close> only exists for \<open>t = 0\<close>.
\<close>

definition idx_G :: "array \<Rightarrow> nat \<Rightarrow> nat" where
  "idx_G A i = i"   \<comment> \<open>columns of \<open>G\<close> sit at the prefix of both
                       \<open>A\<close> and \<open>A[n]\<close>\<close>

definition l0 :: "array \<Rightarrow> nat" where
  "l0 A = arr_len (G_block A)"

definition l1 :: "array \<Rightarrow> nat" where
  "l1 A = arr_len (B0_block A)"


section \<open>Lemma 2.5 (i)--(v)\<close>

text \<open>
  Quote (paper, p.~4--5):
    Let \<open>A\<close> be a non-empty array and \<open>n\<close> a natural number, let
    \<open>G, B\<^sub>0, B\<^sub>1, ..., B_n, m\<^sub>0\<close> be as in Definition 1.1, and
    let \<open>l\<^sub>0, l\<^sub>1\<close> be the lengths of \<open>G, B\<^sub>0\<close>.

    (i)  For all \<open>i < l\<^sub>0\<close>, \<open>j < l\<^sub>1\<close> and \<open>k \<in> \<nat>\<close>, in
         \<open>A[n]\<close>, the \<open>i\<close>-th column in \<open>G\<close> is a \<open>k\<close>-ancestor
         of the \<open>j\<close>-th column in \<open>B\<^sub>0\<close> iff it is a
         \<open>k\<close>-ancestor of the \<open>j\<close>-th column in \<open>B_n\<close>.

    (ii) For all \<open>i, j < l\<^sub>1\<close> and \<open>k \<in> \<nat>\<close>, the \<open>i\<close>-th
         column in \<open>B\<^sub>0\<close> is a \<open>k\<close>-ancestor of the \<open>j\<close>-th
         column in \<open>B\<^sub>0\<close> iff the \<open>i\<close>-th column in \<open>B_n\<close>
         is a \<open>k\<close>-ancestor of the \<open>j\<close>-th column in \<open>B_n\<close>.

    (iii) If \<open>n > 0\<close>, then for all \<open>i < l\<^sub>1\<close> and
         \<open>k < m\<^sub>0\<close>, in \<open>A\<close>, the \<open>i\<close>-th column in \<open>B\<^sub>0\<close>
         is a \<open>k\<close>-ancestor of the last column of \<open>A\<close> iff in
         \<open>A[n]\<close>, the \<open>i\<close>-th column in \<open>B_{n-1}\<close> is a
         \<open>k\<close>-ancestor of the first column in \<open>B_n\<close>.

    (iv) For all \<open>0 < i < l\<^sub>1\<close> and \<open>k \<in> \<nat>\<close>, in \<open>A[n]\<close>,
         the \<open>k\<close>-parent of the \<open>i\<close>-th column in \<open>B_n\<close> is
         either in \<open>B_n\<close> or in \<open>G\<close>.

    (v)  For all \<open>i, j < l\<^sub>1\<close> and \<open>k \<in> \<nat>\<close> and
         \<open>n\<^sub>0 < n\<^sub>1 < n\<close>, in \<open>A[n]\<close>, the \<open>i\<close>-th column
         in \<open>B_{n\<^sub>0}\<close> is a \<open>k\<close>-ancestor of the \<open>j\<close>-th
         column in \<open>B_{n\<^sub>1}\<close> iff it's a \<open>k\<close>-ancestor of
         the \<open>j\<close>-th column in \<open>B_{n\<^sub>1+1}\<close>.

  ``We can prove this by induction on \<open>k\<close>. The proof is relatively
  straightforward, but tedious. The author recommends drawing the
  mentioned ancestry relations in order to see what is happening.''

  We mirror this structure: each of (i)--(v) is a separate \<open>lemma\<close>
  taking \<open>k\<close> as a parameter; the joint induction on \<open>k\<close> is
  the contents of one combined statement, then projected.
\<close>

text \<open>Convenience: index of the \<open>j\<close>-th column of \<open>B_t\<close> inside \<open>A[n]\<close>.\<close>
definition idx_B_in_expansion :: "array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "idx_B_in_expansion A t j = l0 A + t * l1 A + j"

text \<open>Index of the \<open>j\<close>-th column of \<open>B\<^sub>0\<close> inside the original \<open>A\<close>.\<close>
definition idx_B0_in_orig :: "array \<Rightarrow> nat \<Rightarrow> nat" where
  "idx_B0_in_orig A j = l0 A + j"


lemma lemma_2_5_i:
  assumes "A \<in> BMS" "A \<noteq> []" "i < l0 A" "j < l1 A"
  shows "m_ancestor (A[n]) k (idx_G A i) (idx_B_in_expansion A 0 j)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_G A i) (idx_B_in_expansion A n j)"
  sorry

lemma lemma_2_5_ii:
  assumes "A \<in> BMS" "A \<noteq> []" "i < l1 A" "j < l1 A"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A 0 i) (idx_B_in_expansion A 0 j)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n i) (idx_B_in_expansion A n j)"
  sorry

lemma lemma_2_5_iii:
  assumes "A \<in> BMS" "A \<noteq> []" "n > 0"
      and "max_parent_level A = Some m\<^sub>0" "k < m\<^sub>0" "i < l1 A"
  shows "m_ancestor A k (idx_B0_in_orig A i) (last_col_idx A)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A (n - 1) i)
                                  (idx_B_in_expansion A n 0)"
  sorry

lemma lemma_2_5_iv:
  assumes "A \<in> BMS" "A \<noteq> []" "0 < i" "i < l1 A"
  shows "m_parent (A[n]) k (idx_B_in_expansion A n i) = None
       \<or> (\<exists>p. m_parent (A[n]) k (idx_B_in_expansion A n i) = Some p
              \<and> ((\<exists>j < l1 A. p = idx_B_in_expansion A n j)
                 \<or> (\<exists>j < l0 A. p = idx_G A j)))"
  sorry

lemma lemma_2_5_v:
  assumes "A \<in> BMS" "A \<noteq> []" "i < l1 A" "j < l1 A"
      and "n\<^sub>0 < n\<^sub>1" "n\<^sub>1 < n"
  shows "m_ancestor (A[n]) k (idx_B_in_expansion A n\<^sub>0 i)
                                (idx_B_in_expansion A n\<^sub>1 j)
       \<longleftrightarrow> m_ancestor (A[n]) k (idx_B_in_expansion A n\<^sub>0 i)
                                  (idx_B_in_expansion A (n\<^sub>1 + 1) j)"
  sorry

end
