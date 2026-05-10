(*
  BMS_Reflection.thy

  ZF-side stub for Hunter's Lemma 2.6 (stability reflection).

  Plan (task IDs Z3-Z10 in task.md):
    Z3 (2.6.A): show phi_0(eta, xi) := eta in xi  is Sigma_0
    Z4 (2.6.B): show phi_1(eta, xi, k) := eta <_k xi  is Sigma_{n+1}
    Z5 (2.6.C): show phi_2(eta, k) := <L_eta, in> <_{Sigma_{k+1}} <L, in>
                is Pi_{k+1} (Kranakis 1982, Theorem 1.8)
    Z6 (2.6.D): finite Sigma_{n+1}-conjunction is Sigma_{n+1}
    Z7 (2.6.E): existential closure preserves Sigma_{n+1}
    Z8 (2.6.F): psi /\ phi reflects from L_beta to L_alpha via alpha <_n beta
    Z9 (2.6.G): witnesses inside L_alpha furnish Y' and the bijection f
    Z10:        connect to HOL via transfer to discharge the
                axiomatize block in isabelle/BMS_Stability.thy

  Required imports (TBD):
    ZF                                         — base theory
    Constructible                              — Paulson's L hierarchy
    Reflection                                 — Levy's reflection theorem
*)

theory BMS_Reflection
  imports ZF
begin

(* TODO: Z3-Z10 *)

end
