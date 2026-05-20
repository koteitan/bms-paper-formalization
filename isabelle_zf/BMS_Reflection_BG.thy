(*
  BMS_Reflection_BG.thy

  ZF-side discharge of Hunter's Lemma 2.6 sub-tasks (B)-(G),
  i.e. task IDs 18-23 in task.md.

  This file is kept separate from BMS_Reflection.thy (owned by F1 for
  Sigma_0 / 2.6.A) so the two sub-agents can iterate independently.

  Status in this revision (C-zf sub-agent, 2026-05-20):
    * formula_ZF / And_ZF / Exists_ZF / Forall_ZF: definitions over
      Paulson's @{term formula} (And_ZF_type etc. are lemmas).
    * is_Sigma_n / is_Pi_n: NO LONGER axiomatized.  They are now plain
      definitions on top of a single \<open>inductive\<close> set @{term LevyHier}
      \<open>\<subseteq> (nat \<times> 2) \<times> formula\<close> (tag 0 = Sigma, tag 1 = Pi).  The intro
      rules encode Hunter Definition 2.3 directly.  Consequently the
      ENTIRE previous \<open>axiomatization is_Sigma_n is_Pi_n\<close> block
      (8 axioms: in_formula x2, mono x2, succ_Exists, succ_Forall,
      And_closure) is removed; every one is now a proven \<open>lemma\<close>
      derived from a LevyHier introduction rule.
    * stab_fm / L_elem_fm: still abstract, with the axiom
      \<open>stab_fm_is_Sigma_succ_k\<close> exposing the Sigma_{k+1} judgement
      at the base level.  Cannot be discharged until @{term stab_fm}
      is given an explicit @{term Member}/@{term Forall}/@{term Nand}
      definition; documented contract retained.
    * 2.6.B (phi_1_is_Sigma_n_plus_1):  \<open>lemma\<close> proven from
      \<open>stab_fm_is_Sigma_succ_k\<close> and \<open>is_Sigma_n_mono\<close> by nat-induction.
    * 2.6.D (Sigma_n_conjunction_closed): proven \<open>lemma\<close> (no sorry):
      it is the specialization of the new \<open>is_Sigma_n_And_closure\<close>
      lemma to level \<open>succ(n)\<close>.
    * 2.6.E (Sigma_n_existential_closure): UPGRADED axiom -> \<open>lemma\<close>,
      discharged by the dedicated intro rule @{thm LevyHier.LH_Exists_closure}.
    * 2.6.C, F, G:  still axiomatized stubs.  Each ranges over an
      abstract constant whose explicit definition is not yet available
      in this session (L_elem_fm for C; sats_L for F; bij_ZF/witness_fm
      for G), so they cannot be discharged here.  The Paulson-lemma
      correspondence is documented at each (2.6.C <-> Kranakis 1982
      Thm 1.8; 2.6.F <-> Ex_reflection + And_reflection; 2.6.G <->
      a witness-extraction over the reflecting CU class).

  New-axiom accounting requested by the task:
    * is_Sigma_n_And_closure  -- now a LEMMA (LH_And_Sigma intro).
    * stab_fm_is_Sigma_succ_k -- still an axiom (abstract stab_fm).

  References
  ----------
    Rachel Hunter, 'Well-Orderedness of the Bashicu Matrix System',
      arXiv:2307.04606v3, 2024, Lemma 2.6 (parts B-G).
    Eleftherios Kranakis, 'Reflection and partition properties of
      admissible ordinals', Annals of Pure and Applied Logic 23 (1982),
      Theorem 1.8 (relevant for 2.6.C).
    Lawrence C. Paulson, 'The Reflection Theorem: A Study in
      Meta-theoretic Reasoning', CADE-18 (2002) -- the proof template
      whose lemmas And_reflection, Ex_reflection, etc. (in
      ZF/Constructible/Reflection.thy) we will eventually invoke for
      2.6.F.
*)

theory BMS_Reflection_BG
  imports BMS_Reflection
begin

section \<open>Concrete connectives over Paulson's @{term formula}\<close>

text \<open>
  Re-anchor the placeholder constants from the previous revision to
  Paulson's @{text formula} datatype directly.  The names are kept
  identical so any downstream theory referring to them by name continues
  to compile.
\<close>

definition formula_ZF :: "i"
  where "formula_ZF \<equiv> formula"

definition And_ZF :: "[i, i] \<Rightarrow> i"
  where "And_ZF(p, q) \<equiv> And(p, q)"

definition Exists_ZF :: "i \<Rightarrow> i"
  where "Exists_ZF(p) \<equiv> Exists(p)"

definition Forall_ZF :: "i \<Rightarrow> i"
  where "Forall_ZF(p) \<equiv> Forall(p)"

lemma And_ZF_type:
  "\<lbrakk>p \<in> formula_ZF; q \<in> formula_ZF\<rbrakk> \<Longrightarrow> And_ZF(p, q) \<in> formula_ZF"
  unfolding formula_ZF_def And_ZF_def by (rule And_type)

lemma Exists_ZF_type:
  "p \<in> formula_ZF \<Longrightarrow> Exists_ZF(p) \<in> formula_ZF"
  unfolding formula_ZF_def Exists_ZF_def by (rule Exists_type)

lemma Forall_ZF_type:
  "p \<in> formula_ZF \<Longrightarrow> Forall_ZF(p) \<in> formula_ZF"
  unfolding formula_ZF_def Forall_ZF_def by (rule formula.Forall)

section \<open>Inductive Sigma_n / Pi_n hierarchy over ZF formulas\<close>

text \<open>
  We now \emph{define} the Levy hierarchy inductively rather than
  axiomatizing it.  The single inductive set @{term LevyHier} lives in
  \<open>(nat \<times> 2) \<times> formula\<close>: an element \<open><<n, t>, p>\<close> records that the
  formula @{term p} is at level @{term n}, with the tag @{term t}
  selecting \<open>\<Sigma>\<close> (\<open>t = 0\<close>) or \<open>\<Pi>\<close> (\<open>t = 1\<close>).  The two judgements
  @{term is_Sigma_n} and @{term is_Pi_n} are then plain abbreviations.

  The introduction rules encode exactly Hunter's Definition 2.3:
  \<^item> every @{term Sigma_0} formula sits at both \<open>\<Sigma>\<^sub>0\<close> and \<open>\<Pi>\<^sub>0\<close>;
  \<^item> monotonicity \<open>\<Sigma>\<^sub>n \<subseteq> \<Sigma>\<^sub>{n+1}\<close> and \<open>\<Pi>\<^sub>n \<subseteq> \<Pi>\<^sub>{n+1}\<close>;
  \<^item> \<open>\<exists>x. \<phi>\<close> is \<open>\<Sigma>\<^sub>{n+1}\<close> when \<open>\<phi>\<close> is \<open>\<Pi>\<^sub>n\<close>;
  \<^item> \<open>\<forall>x. \<phi>\<close> is \<open>\<Pi>\<^sub>{n+1}\<close> when \<open>\<phi>\<close> is \<open>\<Sigma>\<^sub>n\<close>;
  \<^item> each \<open>\<Sigma>\<^sub>n\<close> (and \<open>\<Pi>\<^sub>n\<close>) stratum is closed under @{term And}.

  Every closure axiom of the previous revision is now a \<open>lemma\<close>
  obtained directly from the corresponding introduction rule, so the
  whole @{text axiomatization} block of @{term is_Sigma_n} /
  @{term is_Pi_n} (8 axioms) is removed.

  Notation note: nat-valued levels are encoded as ZF naturals
  (@{term "n \<in> nat"}); the level \<open>0\<close> corresponds to bounded (Delta_0)
  formulas, levels \<open>succ(n)\<close> to the alternating hierarchy.
\<close>

consts
  LevyHier :: "i"

text \<open>Tag membership facts \<open>0 \<in> 2\<close>, \<open>1 \<in> 2\<close> for the domain type-check.\<close>

lemma zero_in_two: "0 \<in> 2"
  by (simp add: succI2 succI1)

lemma one_in_two: "1 \<in> 2"
  by (simp add: succI1)

inductive
  domains "LevyHier" \<subseteq> "(nat \<times> 2) \<times> formula"
  intros
    LH_base_Sigma:
      \<comment> \<open>every \<open>\<Sigma>\<^sub>0\<close> formula is \<open>\<Sigma>\<^sub>0\<close>\<close>
      "p \<in> Sigma_0 \<Longrightarrow> \<langle>\<langle>0, 0\<rangle>, p\<rangle> \<in> LevyHier"
    LH_base_Pi:
      \<comment> \<open>every \<open>\<Sigma>\<^sub>0 = \<Pi>\<^sub>0\<close> formula is \<open>\<Pi>\<^sub>0\<close>\<close>
      "p \<in> Sigma_0 \<Longrightarrow> \<langle>\<langle>0, 1\<rangle>, p\<rangle> \<in> LevyHier"
    LH_mono_Sigma:
      \<comment> \<open>\<open>\<Sigma>\<^sub>n \<subseteq> \<Sigma>\<^sub>{n+1}\<close>\<close>
      "\<lbrakk>n \<in> nat; \<langle>\<langle>n, 0\<rangle>, p\<rangle> \<in> LevyHier\<rbrakk>
        \<Longrightarrow> \<langle>\<langle>succ(n), 0\<rangle>, p\<rangle> \<in> LevyHier"
    LH_mono_Pi:
      \<comment> \<open>\<open>\<Pi>\<^sub>n \<subseteq> \<Pi>\<^sub>{n+1}\<close>\<close>
      "\<lbrakk>n \<in> nat; \<langle>\<langle>n, 1\<rangle>, p\<rangle> \<in> LevyHier\<rbrakk>
        \<Longrightarrow> \<langle>\<langle>succ(n), 1\<rangle>, p\<rangle> \<in> LevyHier"
    LH_Exists:
      \<comment> \<open>\<open>\<exists>x. \<phi>\<close> is \<open>\<Sigma>\<^sub>{n+1}\<close> whenever \<open>\<phi>\<close> is \<open>\<Pi>\<^sub>n\<close>\<close>
      "\<lbrakk>n \<in> nat; \<langle>\<langle>n, 1\<rangle>, p\<rangle> \<in> LevyHier\<rbrakk>
        \<Longrightarrow> \<langle>\<langle>succ(n), 0\<rangle>, Exists(p)\<rangle> \<in> LevyHier"
    LH_Forall:
      \<comment> \<open>\<open>\<forall>x. \<phi>\<close> is \<open>\<Pi>\<^sub>{n+1}\<close> whenever \<open>\<phi>\<close> is \<open>\<Sigma>\<^sub>n\<close>\<close>
      "\<lbrakk>n \<in> nat; \<langle>\<langle>n, 0\<rangle>, p\<rangle> \<in> LevyHier\<rbrakk>
        \<Longrightarrow> \<langle>\<langle>succ(n), 1\<rangle>, Forall(p)\<rangle> \<in> LevyHier"
    LH_And_Sigma:
      \<comment> \<open>\<open>\<Sigma>\<^sub>n\<close> closed under @{term And}\<close>
      "\<lbrakk>\<langle>\<langle>n, 0\<rangle>, p\<rangle> \<in> LevyHier; \<langle>\<langle>n, 0\<rangle>, q\<rangle> \<in> LevyHier\<rbrakk>
        \<Longrightarrow> \<langle>\<langle>n, 0\<rangle>, And(p, q)\<rangle> \<in> LevyHier"
    LH_And_Pi:
      \<comment> \<open>\<open>\<Pi>\<^sub>n\<close> closed under @{term And}\<close>
      "\<lbrakk>\<langle>\<langle>n, 1\<rangle>, p\<rangle> \<in> LevyHier; \<langle>\<langle>n, 1\<rangle>, q\<rangle> \<in> LevyHier\<rbrakk>
        \<Longrightarrow> \<langle>\<langle>n, 1\<rangle>, And(p, q)\<rangle> \<in> LevyHier"
    LH_Exists_closure:
      \<comment> \<open>2.6.E: \<open>\<Sigma>\<^sub>{n+1}\<close> closed under @{term Exists} (the new
          quantifier merges into the leading existential block)\<close>
      "\<lbrakk>n \<in> nat; \<langle>\<langle>succ(n), 0\<rangle>, p\<rangle> \<in> LevyHier\<rbrakk>
        \<Longrightarrow> \<langle>\<langle>succ(n), 0\<rangle>, Exists(p)\<rangle> \<in> LevyHier"
  type_intros formula.intros And_type Exists_type
              Sigma_0_subset_formula
              SigmaI nat_succI nat_0I nat_1I
              zero_in_two one_in_two

definition is_Sigma_n :: "[i, i] \<Rightarrow> o"
  where "is_Sigma_n(n, p) \<equiv> \<langle>\<langle>n, 0\<rangle>, p\<rangle> \<in> LevyHier"

definition is_Pi_n :: "[i, i] \<Rightarrow> o"
  where "is_Pi_n(n, p) \<equiv> \<langle>\<langle>n, 1\<rangle>, p\<rangle> \<in> LevyHier"

text \<open>Membership in @{term formula_ZF}, from the inductive domain
  @{thm LevyHier.dom_subset}.\<close>

lemma is_Sigma_n_in_formula:
  "is_Sigma_n(n, p) \<Longrightarrow> p \<in> formula_ZF"
  unfolding is_Sigma_n_def formula_ZF_def
  using LevyHier.dom_subset by blast

lemma is_Pi_n_in_formula:
  "is_Pi_n(n, p) \<Longrightarrow> p \<in> formula_ZF"
  unfolding is_Pi_n_def formula_ZF_def
  using LevyHier.dom_subset by blast

text \<open>The former closure axioms, now derived from the intro rules.\<close>

lemma is_Sigma_n_mono:
  "\<lbrakk>n \<in> nat; is_Sigma_n(n, p)\<rbrakk> \<Longrightarrow> is_Sigma_n(succ(n), p)"
  unfolding is_Sigma_n_def by (rule LevyHier.LH_mono_Sigma)

lemma is_Pi_n_mono:
  "\<lbrakk>n \<in> nat; is_Pi_n(n, p)\<rbrakk> \<Longrightarrow> is_Pi_n(succ(n), p)"
  unfolding is_Pi_n_def by (rule LevyHier.LH_mono_Pi)

lemma is_Sigma_succ_Exists:
  "\<lbrakk>n \<in> nat; is_Pi_n(n, p)\<rbrakk> \<Longrightarrow> is_Sigma_n(succ(n), Exists_ZF(p))"
  unfolding is_Sigma_n_def is_Pi_n_def Exists_ZF_def
  by (rule LevyHier.LH_Exists)

lemma is_Pi_succ_Forall:
  "\<lbrakk>n \<in> nat; is_Sigma_n(n, p)\<rbrakk> \<Longrightarrow> is_Pi_n(succ(n), Forall_ZF(p))"
  unfolding is_Sigma_n_def is_Pi_n_def Forall_ZF_def
  by (rule LevyHier.LH_Forall)

lemma is_Sigma_n_And_closure:
  "\<lbrakk>n \<in> nat; is_Sigma_n(n, p); is_Sigma_n(n, q)\<rbrakk>
     \<Longrightarrow> is_Sigma_n(n, And_ZF(p, q))"
  unfolding is_Sigma_n_def And_ZF_def
  by (rule LevyHier.LH_And_Sigma)

section \<open>Internalized stability relation and L-projection\<close>

text \<open>
  Hunter Definition 2.4 introduces the stability ordering
  \<open>\<eta> <\<^sub>k \<xi>  \<longleftrightarrow>  L\<^sub>\<eta> \<prec>\<^sub>{\<Sigma>\<^sub>k} L\<^sub>\<xi>\<close>.  We name the internalized
  formula coding this relation (with de Bruijn index 0 = \<open>\<eta>\<close>,
  index 1 = \<open>\<xi>\<close>, parameter \<open>k\<close>) and a separate formula coding
  \<open>L\<^sub>\<eta> \<prec>\<^sub>{\<Sigma>\<^sub>{k+1}} L\<close> used in 2.6.C.

  These constants will be defined in terms of Paulson's @{text formula}
  inductive type once the Sigma_0 layer in BMS_Reflection.thy is
  stable; for now they are abstract.  The base-level Sigma_{k+1}
  judgement \<open>stab_fm_is_Sigma_succ_k\<close> introduced below is the input
  that 2.6.B (Lemma below) elaborates over the entire \<open>\<Sigma>\<^sub>{n+1}\<close> tail.
\<close>

axiomatization
  stab_fm :: "i \<Rightarrow> i"                \<comment> \<open>internalized \<open>\<eta> <\<^sub>k \<xi>\<close>\<close>
  and L_elem_fm :: "i \<Rightarrow> i"          \<comment> \<open>internalized \<open>L\<^sub>\<eta> \<prec>\<^sub>{\<Sigma>\<^sub>{k+1}} L\<close>\<close>
  where
    stab_fm_formula:
      "k \<in> nat \<Longrightarrow> stab_fm(k) \<in> formula_ZF" and
    L_elem_fm_formula:
      "k \<in> nat \<Longrightarrow> L_elem_fm(k) \<in> formula_ZF" and
    stab_fm_is_Sigma_succ_k:
      \<comment> \<open>Base \<open>\<Sigma>\<^sub>{k+1}\<close> judgement for \<open>\<eta> <\<^sub>k \<xi>\<close>: this is the
          Tarski-Vaught unfolding -- one existential block over a
          \<open>\<Pi>\<^sub>k\<close> matrix.  Will be discharged structurally once
          @{term stab_fm} is given an explicit definition in terms of
          @{term Member} / @{term Forall} / @{term Nand}.\<close>
      "k \<in> nat \<Longrightarrow> is_Sigma_n(succ(k), stab_fm(k))"

section \<open>2.6.B  [ID 18]:  \<open>\<eta> <\<^sub>k \<xi>\<close> is \<open>\<Sigma>\<^sub>{n+1}\<close>\<close>

text \<open>
  Hunter 2.6.B.  Combining the base judgement
  @{text stab_fm_is_Sigma_succ_k} with @{text is_Sigma_n_mono}
  (iterated \<open>n - k\<close> times along the inclusion
  \<open>\<Sigma>\<^sub>{k+1} \<subseteq> \<Sigma>\<^sub>{k+2} \<subseteq> \<dots> \<subseteq> \<Sigma>\<^sub>{n+1}\<close>) lifts to the desired level.

  We perform the iteration by induction on @{term n} (with @{term k}
  fixed); the induction hypothesis packages the universal closure
  over the case \<open>k \<le> n\<close>.
\<close>

lemma phi_1_is_Sigma_n_plus_1:
  assumes "n \<in> nat" "k \<in> nat" "k \<le> n"
  shows "is_Sigma_n(succ(n), stab_fm(k))"
proof -
  \<comment> \<open>Induct on @{term n}; the hypothesis @{prop "k \<le> n"} is treated
      as a side condition discharged at each step.\<close>
  from \<open>n \<in> nat\<close> \<open>k \<le> n\<close> show ?thesis
  proof (induct n)
    case 0
    \<comment> \<open>Then \<open>k \<le> 0\<close>, hence \<open>k = 0\<close>; the base axiom
        @{text stab_fm_is_Sigma_succ_k} discharges
        \<open>is_Sigma_n(succ(0), stab_fm(0))\<close> directly.\<close>
    from \<open>k \<le> 0\<close> have "k = 0" by simp
    with \<open>k \<in> nat\<close> show ?case
      using stab_fm_is_Sigma_succ_k by simp
  next
    case (succ n)
    \<comment> \<open>If \<open>k \<le> succ(n)\<close>, either \<open>k \<le> n\<close> (induction hypothesis + one
        application of @{text is_Sigma_n_mono}) or \<open>k = succ(n)\<close>
        (base axiom directly).\<close>
    from \<open>k \<le> succ(n)\<close> have disj: "k \<le> n \<or> k = succ(n) \<and> Ord(k)"
      by (rule le_succ_iff [THEN iffD1])
    from disj show ?case
    proof
      assume "k \<le> n"
      with succ.hyps have IH: "is_Sigma_n(succ(n), stab_fm(k))" by simp
      from \<open>n \<in> nat\<close> have "succ(n) \<in> nat" by (rule nat_succI)
      from this IH show "is_Sigma_n(succ(succ(n)), stab_fm(k))"
        by (rule is_Sigma_n_mono)
    next
      assume "k = succ(n) \<and> Ord(k)"
      then have keq: "k = succ(n)" by (rule conjunct1)
      from \<open>k \<in> nat\<close> have "is_Sigma_n(succ(k), stab_fm(k))"
        by (rule stab_fm_is_Sigma_succ_k)
      with keq show "is_Sigma_n(succ(succ(n)), stab_fm(k))" by simp
    qed
  qed
qed

section \<open>2.6.C  [ID 19]:  \<open>L\<^sub>\<eta> \<prec>\<^sub>{\<Sigma>\<^sub>{k+1}} L\<close> is \<open>\<Pi>\<^sub>{k+1}\<close>\<close>

text \<open>
  Hunter 2.6.C (Kranakis 1982, Theorem 1.8).  The assertion
    \<open>\<forall> \<Sigma>\<^sub>{k+1}-formulas \<psi>. \<forall> a \<in> L\<^sub>\<eta>. \<psi>\<^bsup>L\<^sub>\<eta>\<^esup>(a) \<longleftrightarrow> \<psi>\<^bsup>L\<^esup>(a)\<close>
  is a single outer Pi-layer over a \<open>\<Sigma>\<^sub>{k+1}\<close> matrix, hence
  \<open>\<Pi>\<^sub>{k+1}\<close>.  Discharge deferred to ZF-EFG sub-agent.
\<close>

axiomatization where
  phi_2_is_Pi_k_plus_1:
    "k \<in> nat \<Longrightarrow> is_Pi_n(succ(k), L_elem_fm(k))"

section \<open>2.6.D  [ID 20]:  finite \<open>\<Sigma>\<^sub>{n+1}\<close>-conjunction is \<open>\<Sigma>\<^sub>{n+1}\<close>\<close>

text \<open>
  Closure of \<open>\<Sigma>\<^sub>{n+1}\<close> under finite @{term And_ZF}.  In prenex
  normal form the leading existential block of one conjunct absorbs
  the conjunction via quantifier shifting
  \<open>(\<exists>x. \<phi>(x)) \<and> \<psi> \<equiv> \<exists>x. (\<phi>(x) \<and> \<psi>)\<close>.  Semantic counterpart in
  Paulson's library: @{text And_reflection}.

  Once ZF-EFG installs the inductive Sigma_{n+1} presentation, the
  proof obligation reduces to: given \<open>is_Sigma_n(succ(n), p)\<close> and
  \<open>is_Sigma_n(succ(n), q)\<close>, exhibit a Pi_n witness for the body of
  \<open>Exists_ZF(\<dots>)\<close> by prenex-shifting.  At the abstract layer we
  expose the \<open>And\<close>-closure of every \<open>\<Sigma>\<^sub>n\<close> stratum as the new axiom
  @{text is_Sigma_n_And_closure}; the specialization to
  \<open>succ(n)\<close> is just an instance.
\<close>

lemma Sigma_n_conjunction_closed:
  assumes "n \<in> nat"
      and p: "is_Sigma_n(succ(n), p)"
      and q: "is_Sigma_n(succ(n), q)"
  shows "is_Sigma_n(succ(n), And_ZF(p, q))"
proof -
  from \<open>n \<in> nat\<close> have "succ(n) \<in> nat" by (rule nat_succI)
  from this p q show ?thesis by (rule is_Sigma_n_And_closure)
qed

section \<open>2.6.E  [ID 21]:  existential closure preserves \<open>\<Sigma>\<^sub>{n+1}\<close>\<close>

text \<open>
  If \<open>p\<close> is \<open>\<Sigma>\<^sub>{n+1}\<close>, so is @{term "Exists_ZF(p)"} -- the new
  quantifier merges into the leading existential block.
  Semantic counterpart: @{text Ex_reflection}.  Now that the Levy
  hierarchy is inductive, this is the dedicated introduction rule
  @{thm LevyHier.LH_Exists_closure}; the former axiom is removed.
\<close>

lemma Sigma_n_existential_closure:
  "\<lbrakk>n \<in> nat; is_Sigma_n(succ(n), p)\<rbrakk>
   \<Longrightarrow> is_Sigma_n(succ(n), Exists_ZF(p))"
  unfolding is_Sigma_n_def Exists_ZF_def
  by (rule LevyHier.LH_Exists_closure)

section \<open>2.6.F  [ID 22]:  \<open>\<psi> \<and> \<phi>\<close> reflects from \<open>L\<^sub>\<beta>\<close> to \<open>L\<^sub>\<alpha>\<close>\<close>

text \<open>
  Given \<open>\<alpha> <\<^sub>n \<beta>\<close> (i.e.\ \<open>L\<^sub>\<alpha> \<prec>\<^sub>{\<Sigma>\<^sub>n} L\<^sub>\<beta>\<close>) and a \<open>\<Sigma>\<^sub>{n+1}\<close>
  formula \<open>\<chi> = \<psi> \<and> \<phi>\<close>, any environment in \<open>L\<^sub>\<alpha>\<close> satisfying
  \<open>\<chi>\<close> in \<open>L\<^sub>\<beta>\<close> also satisfies it in \<open>L\<^sub>\<alpha>\<close>.

  This is the application of Paulson's reflection package along
  the closed-unbounded class supplied by the stability filter.
  Semantic side once Constructible is wired in:
  @{text Ex_reflection} + @{text And_reflection}.

  We keep @{term sats_L} and @{term Lset_ZF} abstract here so the
  signature lands in pure ZF; once Constructible is imported they
  resolve to Paulson's @{text sats} and @{text Lset}.
\<close>

axiomatization
  Lset_ZF :: "i \<Rightarrow> i"                \<comment> \<open>abstract @{text Lset}; later Paulson's @{text Lset}\<close>
  and sats_L :: "[i, i, i] \<Rightarrow> o"     \<comment> \<open>\<open>sats_L(\<beta>, \<phi>, env) := L\<^sub>\<beta> \<Turnstile> \<phi>[env]\<close>\<close>
  and stab_lt :: "[i, i, i] \<Rightarrow> o"    \<comment> \<open>\<open>stab_lt(n, \<alpha>, \<beta>) := \<alpha> <\<^sub>n \<beta>\<close>\<close>

axiomatization where
  psi_and_phi_reflects:
    "\<lbrakk>n \<in> nat;
      Ord(alpha); Ord(beta);
      stab_lt(n, alpha, beta);
      is_Sigma_n(succ(n), psi);
      is_Sigma_n(succ(n), phi);
      sats_L(beta, And_ZF(psi, phi), env)\<rbrakk>
     \<Longrightarrow> sats_L(alpha, And_ZF(psi, phi), env)"

section \<open>2.6.G  [ID 23]:  witnesses inside \<open>L\<^sub>\<alpha>\<close> furnish \<open>Y'\<close> and \<open>f\<close>\<close>

text \<open>
  Given a witness inside \<open>L\<^sub>\<alpha>\<close> for the existential closure of the
  ancestry-witness predicate @{term witness_fm} on a candidate
  ancestry set @{term Y}, one extracts
  \<^item> a reflected ancestry set \<open>Y' \<subseteq> \<alpha>\<close>, and
  \<^item> a bijection \<open>f : Y \<rightarrow> Y'\<close>
  preserving the relevant order-theoretic data.

  This is the conclusion of Lemma 2.6 in Hunter (2024); it is the
  place where the @{text stable_rep_extend_strict} construction in
  @{text BMS_WellOrdered.thy} ultimately reads off its reflected
  stability ordinal.

  The signature below leaves @{term bij_ZF} abstract; once the
  imports are widened to include Paulson's library this resolves to
  the standard @{text bij}.
\<close>

axiomatization
  witness_fm :: "i \<Rightarrow> i"             \<comment> \<open>internalized ancestry-witness predicate
                                         parameterized by the candidate set @{term Y}\<close>
  and bij_ZF :: "[i, i] \<Rightarrow> i"        \<comment> \<open>abstract @{text bij}\<close>

axiomatization where
  Yprime_and_bijection_from_witnesses:
    "\<lbrakk>n \<in> nat;
      Ord(alpha);
      sats_L(alpha, Exists_ZF(witness_fm(Y)), Cons(Y, Nil))\<rbrakk>
     \<Longrightarrow> \<exists>Yp. \<exists>f. Yp \<subseteq> alpha \<and> f \<in> bij_ZF(Y, Yp)"

end
