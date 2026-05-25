theory ValueCheck_expand
  imports BMS_Defs
begin

text \<open>
  Machine-checked witnesses (by eval) settling two methodological questions:

  (1) yaBMS (the external C tool used by verify/*.py) computes the SAME expansion
      as the Isabelle/Hunter definition `G_block A @ Bs_concat A n` (pre-strip).
      So the yaBMS-based probes measure the correct expansion (an earlier agent
      claim "yaBMS != Hunter" was wrong).
  (2) The probe's b0_start / max_parent_level agree with Isabelle on the
      loc_R1 counterexample, which is REAL in Isabelle semantics: b0_start(A[1])=8
      is mid-block (l0=4, l1=3 by last-s, block-starts {4,7}). BUT that A[1] has
      l1(A[1]) = 9-8 = 1, i.e. DOM is vacuous there — OUTSIDE the design regime
      (the joint-induction location lemma needs the guard l1(A[n]) >= 2, not l1(A) >= 2).

  Acx = (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,1); yaBMS Acx[1] =
        (0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,0)(8,1)(9,2)  (no strip).
  (Note: `l1` is not code-executable, so it is not asserted here by eval.)
\<close>

definition Acx :: array where
  "Acx = [[0,0],[1,1],[2,2],[3,1],[4,0],[5,1],[6,2],[7,1]]"

lemma vc_prestrip_eq_yaBMS:
  "G_block Acx @ Bs_concat Acx 1
     = [[0,0],[1,1],[2,2],[3,1],[4,0],[5,1],[6,2],[7,0],[8,1],[9,2]]"
  by eval

lemma vc_b0_Acx: "b0_start Acx = Some 4" by eval

lemma vc_b0_exp_midblock:
  "b0_start (G_block Acx @ Bs_concat Acx 1) = Some 8" by eval

lemma vc_mpl_exp:
  "max_parent_level (G_block Acx @ Bs_concat Acx 1) = Some 1" by eval

end
