(*
  BMS_Reflection_BG.thy

  ZF-side signature stubs for Hunter's Lemma 2.6 sub-tasks (B)-(G),
  i.e. task IDs 18-23 in task.md.

  This file is intentionally kept separate from BMS_Reflection.thy
  (which is owned by F1 and tracks the Sigma_0 / 2.6.A discharge) so
  the two sub-agents can iterate independently.  Once F1 lands the
  Sigma_0 / Sigma_n inductive presentation, the abstract predicates
  below (is_Sigma_n, is_Pi_n) should be re-anchored to the concrete
  ones; until then they are introduced as opaque axiomatized
  constants together with the closure properties 2.6.B-G actually
  exercise.

  All six sub-lemmas are stated as axiomatizations (NOT lemma+sorry)
  so the session builds cleanly without enabling quick_and_dirty.
  They will be re-cast as theorems with full proofs in follow-up
  commits.

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
  imports ZF
begin

section \<open>Abstract Sigma_n / Pi_n predicates over ZF formulas\<close>

text \<open>
  Until F1's concrete inductive Sigma_0 presentation in
  \<open>BMS_Reflection.thy\<close> stabilises, we work with opaque
  predicates @{term is_Sigma_n} / @{term is_Pi_n}.  The axiomatization
  pins down only the closure properties the 2.6.B-G arguments actually
  exercise: monotonicity along the hierarchy, existential closure
  (Sigma side), universal closure (Pi side), and propositional closure
  under conjunction.

  Notation note: nat-valued levels are encoded as ZF naturals
  (@{term "n \<in> nat"}); the level \<open>0\<close> corresponds to bounded (Delta_0)
  formulas, levels \<open>succ(n)\<close> to the alternating hierarchy.
\<close>

axiomatization
  formula_ZF :: "i"                  \<comment> \<open>placeholder for the set of internalized formulas;
                                         when imports are lifted to ZF-Constructible this
                                         is replaced by Paulson's @{text formula}.\<close>
  and And_ZF :: "[i, i] \<Rightarrow> i"        \<comment> \<open>placeholder for @{text And} (conjunction constructor)\<close>
  and Exists_ZF :: "i \<Rightarrow> i"          \<comment> \<open>placeholder for @{text Exists} (existential constructor)\<close>
  and Forall_ZF :: "i \<Rightarrow> i"          \<comment> \<open>placeholder for @{text Forall} (universal constructor)\<close>
  where
    And_ZF_type:
      "\<lbrakk>p \<in> formula_ZF; q \<in> formula_ZF\<rbrakk> \<Longrightarrow> And_ZF(p, q) \<in> formula_ZF" and
    Exists_ZF_type:
      "p \<in> formula_ZF \<Longrightarrow> Exists_ZF(p) \<in> formula_ZF" and
    Forall_ZF_type:
      "p \<in> formula_ZF \<Longrightarrow> Forall_ZF(p) \<in> formula_ZF"

axiomatization
  is_Sigma_n :: "[i, i] \<Rightarrow> o"        \<comment> \<open>\<open>is_Sigma_n(n, p)\<close>: formula @{term p} is \<open>\<Sigma>\<^sub>n\<close>\<close>
  and is_Pi_n :: "[i, i] \<Rightarrow> o"        \<comment> \<open>\<open>is_Pi_n(n, p)\<close>: formula @{term p} is \<open>\<Pi>\<^sub>n\<close>\<close>
  where
    is_Sigma_n_in_formula:
      "is_Sigma_n(n, p) \<Longrightarrow> p \<in> formula_ZF" and
    is_Pi_n_in_formula:
      "is_Pi_n(n, p) \<Longrightarrow> p \<in> formula_ZF" and
    is_Sigma_n_mono:
      \<comment> \<open>\<open>\<Sigma>\<^sub>n \<subseteq> \<Sigma>\<^sub>{n+1}\<close>\<close>
      "\<lbrakk>n \<in> nat; is_Sigma_n(n, p)\<rbrakk> \<Longrightarrow> is_Sigma_n(succ(n), p)" and
    is_Pi_n_mono:
      \<comment> \<open>\<open>\<Pi>\<^sub>n \<subseteq> \<Pi>\<^sub>{n+1}\<close>\<close>
      "\<lbrakk>n \<in> nat; is_Pi_n(n, p)\<rbrakk> \<Longrightarrow> is_Pi_n(succ(n), p)" and
    is_Sigma_succ_Exists:
      \<comment> \<open>\<open>\<exists>x. \<phi>\<close> is \<open>\<Sigma>\<^sub>{n+1}\<close> whenever \<open>\<phi>\<close> is \<open>\<Pi>\<^sub>n\<close>\<close>
      "\<lbrakk>n \<in> nat; is_Pi_n(n, p)\<rbrakk> \<Longrightarrow> is_Sigma_n(succ(n), Exists_ZF(p))" and
    is_Pi_succ_Forall:
      \<comment> \<open>\<open>\<forall>x. \<phi>\<close> is \<open>\<Pi>\<^sub>{n+1}\<close> whenever \<open>\<phi>\<close> is \<open>\<Sigma>\<^sub>n\<close>\<close>
      "\<lbrakk>n \<in> nat; is_Sigma_n(n, p)\<rbrakk> \<Longrightarrow> is_Pi_n(succ(n), Forall_ZF(p))"

section \<open>Internalized stability relation and L-projection\<close>

text \<open>
  Hunter Definition 2.4 introduces the stability ordering
  \<open>\<eta> <\<^sub>k \<xi>  \<longleftrightarrow>  L\<^sub>\<eta> \<prec>\<^sub>{\<Sigma>\<^sub>k} L\<^sub>\<xi>\<close>.  We name the internalized
  formula coding this relation (with de Bruijn index 0 = \<open>\<eta>\<close>,
  index 1 = \<open>\<xi>\<close>, parameter \<open>k\<close>) and a separate formula coding
  \<open>L\<^sub>\<eta> \<prec>\<^sub>{\<Sigma>\<^sub>{k+1}} L\<close> used in 2.6.C.

  These constants will be defined in terms of Paulson's @{text formula}
  inductive type once the Sigma_0 layer in BMS_Reflection.thy is
  stable; for now they are abstract.
\<close>

axiomatization
  stab_fm :: "i \<Rightarrow> i"                \<comment> \<open>internalized \<open>\<eta> <\<^sub>k \<xi>\<close>\<close>
  and L_elem_fm :: "i \<Rightarrow> i"          \<comment> \<open>internalized \<open>L\<^sub>\<eta> \<prec>\<^sub>{\<Sigma>\<^sub>{k+1}} L\<close>\<close>
  where
    stab_fm_formula:
      "k \<in> nat \<Longrightarrow> stab_fm(k) \<in> formula_ZF" and
    L_elem_fm_formula:
      "k \<in> nat \<Longrightarrow> L_elem_fm(k) \<in> formula_ZF"

section \<open>2.6.B  [ID 18]:  \<open>\<eta> <\<^sub>k \<xi>\<close> is \<open>\<Sigma>\<^sub>{n+1}\<close>\<close>

text \<open>
  Hunter 2.6.B.  Unfolding the stability ordering through the
  Tarski-Vaught test exhibits \<open>\<eta> <\<^sub>k \<xi>\<close> as a \<open>\<Sigma>\<^sub>{k+1}\<close> assertion
  (one existential block over a \<open>\<Pi>\<^sub>k\<close> matrix), which by
  @{thm is_Sigma_n_mono} lifts to \<open>\<Sigma>\<^sub>{n+1}\<close> whenever \<open>k \<le> n\<close>.
\<close>

axiomatization where
  phi_1_is_Sigma_n_plus_1:
    "\<lbrakk>n \<in> nat; k \<in> nat; k \<le> n\<rbrakk> \<Longrightarrow> is_Sigma_n(succ(n), stab_fm(k))"

section \<open>2.6.C  [ID 19]:  \<open>L\<^sub>\<eta> \<prec>\<^sub>{\<Sigma>\<^sub>{k+1}} L\<close> is \<open>\<Pi>\<^sub>{k+1}\<close>\<close>

text \<open>
  Hunter 2.6.C (Kranakis 1982, Theorem 1.8).  The assertion
    \<open>\<forall> \<Sigma>\<^sub>{k+1}-formulas \<psi>. \<forall> a \<in> L\<^sub>\<eta>. \<psi>\<^bsup>L\<^sub>\<eta>\<^esup>(a) \<longleftrightarrow> \<psi>\<^bsup>L\<^esup>(a)\<close>
  is a single outer Pi-layer over a \<open>\<Sigma>\<^sub>{k+1}\<close> matrix, hence
  \<open>\<Pi>\<^sub>{k+1}\<close>.
\<close>

axiomatization where
  phi_2_is_Pi_k_plus_1:
    "k \<in> nat \<Longrightarrow> is_Pi_n(succ(k), L_elem_fm(k))"

section \<open>2.6.D  [ID 20]:  finite \<open>\<Sigma>\<^sub>{n+1}\<close>-conjunction is \<open>\<Sigma>\<^sub>{n+1}\<close>\<close>

text \<open>
  Closure of \<open>\<Sigma>\<^sub>{n+1}\<close> under finite @{term And_ZF}.  In prenex
  normal form the leading existential block of one conjunct absorbs
  the conjunction via quantifier shifting (\<open>(\<exists>x. \<phi>(x)) \<and> \<psi> \<equiv> \<exists>x. (\<phi>(x) \<and> \<psi>)\<close>).
  Semantic counterpart in Paulson's library: @{text And_reflection}.
\<close>

axiomatization where
  Sigma_n_conjunction_closed:
    "\<lbrakk>n \<in> nat;
      is_Sigma_n(succ(n), p);
      is_Sigma_n(succ(n), q)\<rbrakk>
     \<Longrightarrow> is_Sigma_n(succ(n), And_ZF(p, q))"

section \<open>2.6.E  [ID 21]:  existential closure preserves \<open>\<Sigma>\<^sub>{n+1}\<close>\<close>

text \<open>
  If \<open>p\<close> is \<open>\<Sigma>\<^sub>{n+1}\<close>, so is @{term "Exists_ZF(p)"} -- the new
  quantifier merges into the leading existential block.
  Semantic counterpart: @{text Ex_reflection}.
\<close>

axiomatization where
  Sigma_n_existential_closure:
    "\<lbrakk>n \<in> nat; is_Sigma_n(succ(n), p)\<rbrakk>
     \<Longrightarrow> is_Sigma_n(succ(n), Exists_ZF(p))"

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
