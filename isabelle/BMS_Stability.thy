(*
  BMS_Stability.thy

  Lemma 2.6 of
    Rachel Hunter, "Well-Orderedness of the Bashicu Matrix System"
    (arXiv:2307.04606v3, 2024).

  This lemma is a *stability reflection* property of the constructible
  hierarchy and uses the Kranakis 1982 reflection theorem (Theorem 1.8
  of [4]). Its full proof requires the constructible hierarchy L_alpha,
  the relations <=_{Sigma_n} on Ord, and a formal treatment of Sigma_n
  formulas; these are most cleanly developed in Isabelle/ZF on top of
  Paulson's `Constructible` library.

  In the present HOL development we therefore *axiomatize* the lemma in
  a sufficiently general form for Theorem 2.7 to go through, with a
  clear plan to discharge the axiom from the ZF side later (see
  Isabelle_ZF/BMS_Reflection.thy).
*)

theory BMS_Stability
  imports BMS_Ancestry
begin

section \<open>Abstract ordinal layer\<close>

(*
  Lemma 2.6 talks about ordinals alpha, beta in sigma and the relations
  <, <_k, <_m. We introduce a HOL-side type `ord` together with the
  abstract operations and assumptions used by Theorem 2.7. The actual
  realisation is done in ZF.
*)

typedecl Ord_t

axiomatization
  ord_lt :: "Ord_t \<Rightarrow> Ord_t \<Rightarrow> bool" (infix "<\<^sub>o" 50) and
  stable_lt :: "nat \<Rightarrow> Ord_t \<Rightarrow> Ord_t \<Rightarrow> bool" and
  sigma_bound :: "Ord_t set"
where
  ord_lt_irrefl: "\<not> \<alpha> <\<^sub>o \<alpha>"  and
  ord_lt_trans:  "\<alpha> <\<^sub>o \<beta> \<Longrightarrow> \<beta> <\<^sub>o \<gamma> \<Longrightarrow> \<alpha> <\<^sub>o \<gamma>"  and
  ord_wf:        "wfP (<\<^sub>o)"  and
  seed_stable_pair_exists:
    "\<exists>\<alpha> \<beta>. \<alpha> <\<^sub>o \<beta> \<and> (\<forall>m < n. stable_lt m \<alpha> \<beta>)"


section \<open>Lemma 2.6 (Stability reflection)\<close>

(*
  sigma is the smallest ordinal alpha such that there exists an ordinal
  beta with for-all n in N (alpha <_n beta).

  Lemma 2.6 (paper, p.7):
    For all alpha, beta in sigma and n in N, if omega < alpha <_n beta,
    then for all finite X, Y subset of Ord such that gamma < alpha <=
    delta < beta for all gamma in X and delta in Y, there exists a
    finite Y' subset of Ord and a bijection f : Y -> Y' such that for
    all gamma in X, all delta_0, delta_1 in Y, all k in N and all
    m < n:
      - gamma < f(delta_0) < alpha
      - gamma <_k delta_0  =>  gamma <_k f(delta_0)
      - delta_0 < delta_1  =>  f(delta_0) < f(delta_1)
      - delta_0 <_k delta_1  =>  f(delta_0) <_k f(delta_1)
      - delta_0 <_m delta_1  =>  f(delta_0) <_m alpha.

  Sub-lemmas (the proof structures these as):
    2.6.A  phi_0(eta,xi) := eta in xi  is Sigma_0.
    2.6.B  phi_1(eta,xi,k) := eta <_k xi  is Sigma_{n+1}.
    2.6.C  phi_2(eta,k) := <L_eta, in> <_{Sigma_{k+1}} <L, in>  is
           Pi_{k+1}.   (Kranakis 1982, Theorem 1.8.)
    2.6.D  Finite conjunctions of Sigma_{n+1}-formulas are Sigma_{n+1}.
    2.6.E  Existential closure preserves Sigma_{n+1}.
    2.6.F  psi /\ phi true in L_beta reflects to L_alpha via
           alpha <_n beta.
    2.6.G  Witnesses inside L_alpha furnish Y' and the bijection f.

  We axiomatize the conclusion. The seven sub-lemmas are TODOs in the
  ZF-side development.
*)

axiomatization where
  lemma_2_6:
    "\<lbrakk> \<alpha> \<in> sigma_bound; \<beta> \<in> sigma_bound;
       \<omega>_o <\<^sub>o \<alpha>; stable_lt n \<alpha> \<beta>;
       finite X; finite Y;
       \<forall>\<gamma> \<in> X. \<forall>\<delta> \<in> Y. \<gamma> <\<^sub>o \<alpha> \<and> (\<alpha> = \<delta> \<or> \<alpha> <\<^sub>o \<delta>) \<and> \<delta> <\<^sub>o \<beta> \<rbrakk>
     \<Longrightarrow> \<exists>Y' f. finite Y'
              \<and> bij_betw f Y Y'
              \<and> (\<forall>\<gamma> \<in> X. \<forall>\<delta>\<^sub>0 \<in> Y. \<gamma> <\<^sub>o (f \<delta>\<^sub>0) \<and> (f \<delta>\<^sub>0) <\<^sub>o \<alpha>)
              \<and> (\<forall>\<gamma> \<in> X. \<forall>\<delta>\<^sub>0 \<in> Y. \<forall>k.
                    stable_lt k \<gamma> \<delta>\<^sub>0 \<longrightarrow> stable_lt k \<gamma> (f \<delta>\<^sub>0))
              \<and> (\<forall>\<delta>\<^sub>0 \<in> Y. \<forall>\<delta>\<^sub>1 \<in> Y.
                    \<delta>\<^sub>0 <\<^sub>o \<delta>\<^sub>1 \<longrightarrow> (f \<delta>\<^sub>0) <\<^sub>o (f \<delta>\<^sub>1))
              \<and> (\<forall>\<delta>\<^sub>0 \<in> Y. \<forall>\<delta>\<^sub>1 \<in> Y. \<forall>k.
                    stable_lt k \<delta>\<^sub>0 \<delta>\<^sub>1 \<longrightarrow> stable_lt k (f \<delta>\<^sub>0) (f \<delta>\<^sub>1))
              \<and> (\<forall>\<delta>\<^sub>0 \<in> Y. \<forall>\<delta>\<^sub>1 \<in> Y. \<forall>m < n.
                    stable_lt m \<delta>\<^sub>0 \<delta>\<^sub>1 \<longrightarrow> stable_lt m (f \<delta>\<^sub>0) \<alpha>)"

(* omega_o is the abstract omega; placeholder constant for now. *)

axiomatization \<omega>_o :: Ord_t

end
