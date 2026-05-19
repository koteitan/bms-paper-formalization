(*
  BMS_Reflection.thy

  ZF-side stub for Hunter's Lemma 2.6 (stability reflection).

  Plan (task IDs 16-24 in task.md):
    16: import Paulson's Constructible library                       <-- this file
    17 (2.6.A): show phi_0(eta, xi) := eta in xi  is Sigma_0          <-- this file
    18 (2.6.B): show phi_1(eta, xi, k) := eta <_k xi  is Sigma_{n+1}
    19 (2.6.C): show phi_2(eta, k) := <L_eta, in> <_{Sigma_{k+1}} <L, in>
                is Pi_{k+1}  (Kranakis 1982, Theorem 1.8)
    20 (2.6.D): finite Sigma_{n+1}-conjunction is Sigma_{n+1}
    21 (2.6.E): existential closure preserves Sigma_{n+1}
    22 (2.6.F): psi /\ phi reflects from L_beta to L_alpha via alpha <_n beta
    23 (2.6.G): witnesses inside L_alpha furnish Y' and the bijection f
    24:        connect to HOL via transfer to discharge the
                axiomatize block in isabelle/BMS_Stability.thy

  Imports
  -------
    The session is ZF-Constructible (see ROOT).  Formula.thy gives:
      - the inductive set "formula" of internalized FOL formulas with
        constructors Member, Equal, Nand, Forall (and derived Neg, And, Or,
        Implies, Iff, Exists);
      - the satisfaction relation  sats(A, p, env);
      - the arity function on formulas;
      - the constructible hierarchy Lset(i) and the predicate L.
    Reflection.thy gives Paulson's Levy reflection theorem packaged via the
    Reflects predicate; Normal.thy gives closed-unbounded classes.

  Hunter's Sigma_n / Pi_n hierarchy on top of "formula"
  ------------------------------------------------------
    We introduce the inductive set Sigma_0 inside Isabelle/ZF, mirroring the
    standard bounded-quantifier (Delta_0 = Sigma_0 = Pi_0) class:

      Sigma_0 = Pi_0 = Delta_0: closure of atomic formulas under
        propositional connectives (here: the primitive Nand) and *bounded*
        quantifiers, encoded as Forall(Implies(Member(0, succ(k)), .)).

    Higher levels are deferred to subsequent task IDs:
      Sigma_{n+1} = exists-closure of Pi_n
      Pi_{n+1}    = forall-closure of Sigma_n

  Status
  ------
    Sigma_0 is introduced as an inductive set, with the introduction rules
    Sigma_0_Member / Sigma_0_Equal / Sigma_0_Nand / Sigma_0_BForall.
    2.6.A (Member is Sigma_0) is discharged outright -- it is essentially the
    introduction rule.  The remaining sub-tasks (IDs 18-23) are deferred to
    follow-up sub-agents and are not stubbed in this file (so the build does
    not depend on quick_and_dirty mode).
*)

theory BMS_Reflection
  imports
    "ZF-Constructible.Formula"
    "ZF-Constructible.Reflection"
begin

section \<open>Bounded (Sigma_0) formulas\<close>

text \<open>
  A formula is \emph{bounded} (Sigma_0 = Pi_0 = Delta_0) iff every quantifier
  inside it is bounded by membership in a free variable.  Paulson's
  @{term formula} type uses @{term Forall} and @{term Nand} as primitive
  constructors and derives the rest, so we phrase the inductive definition
  in those primitive terms.

  The standard convention (Kunen, ``Set Theory'', I.13) is that a quantifier
  is \emph{bounded} when it has the shape @{text "\<forall>x \<in> y. \<phi>"}, i.e. the
  de Bruijn index inside @{term Forall} is governed by a @{term Member}
  guard.
\<close>

consts
  Sigma_0 :: "i"

inductive
  domains "Sigma_0" \<subseteq> "formula"
  intros
    Sigma_0_Member:
      "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> Member(x, y) \<in> Sigma_0"
    Sigma_0_Equal:
      "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> Equal(x, y) \<in> Sigma_0"
    Sigma_0_Nand:
      "\<lbrakk>p \<in> Sigma_0; q \<in> Sigma_0\<rbrakk> \<Longrightarrow> Nand(p, q) \<in> Sigma_0"
    Sigma_0_BForall:
      \<comment> \<open>bounded universal: under @{term Forall}, the body is guarded by a
          @{term Member} atom on de Bruijn index 0.\<close>
      "\<lbrakk>k \<in> nat; p \<in> Sigma_0\<rbrakk>
        \<Longrightarrow> Forall(Implies(Member(0, succ(k)), p)) \<in> Sigma_0"
  type_intros formula.intros Implies_type nat_succI nat_0I nat_1I

abbreviation Pi_0 :: "i"
  where "Pi_0 \<equiv> Sigma_0"

lemma Sigma_0_subset_formula:
  "p \<in> Sigma_0 \<Longrightarrow> p \<in> formula"
  using Sigma_0.dom_subset by blast

section \<open>2.6.A: \<open>\<phi>\<^sub>0(\<eta>,\<xi>) := \<eta> \<in> \<xi>\<close> is \<open>\<Sigma>\<^sub>0\<close>\<close>

text \<open>
  Hunter's \<open>\<phi>\<^sub>0\<close> is the atomic membership predicate.  Under our convention
  (de Bruijn 0 = \<open>\<eta>\<close>, de Bruijn 1 = \<open>\<xi>\<close>) it is internalized as
  @{term "Member(0, 1)"}, and the introduction rule @{thm Sigma_0.Sigma_0_Member}
  discharges the goal directly.
\<close>

lemma phi_0_is_Sigma_0:
  "Member(0, 1) \<in> Sigma_0"
  by (rule Sigma_0.Sigma_0_Member) (rule nat_0I, rule nat_1I)

text \<open>Stronger / more usable form: any membership atom is \<open>\<Sigma>\<^sub>0\<close>.\<close>

lemma Member_in_Sigma_0:
  "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> Member(x, y) \<in> Sigma_0"
  by (rule Sigma_0.Sigma_0_Member)

(*
  Remaining 2.6 sub-tasks (IDs 18-24) are deferred to dedicated sub-agents
  and are NOT introduced here as sorry-stubs (we want the BMS_ZF session to
  build cleanly without quick_and_dirty).
*)

end
