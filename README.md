[English](README.md) | [Japanese](README-ja.md)

# BMS Well-Orderedness Formal Verification

**Version:** v0.1.4

A formal verification project of the well-orderedness proof of the **Bashicu Matrix System (BMS)** using the proof assistant **Isabelle/HOL**.

## Background

The Bashicu Matrix System is a recursive system of ordinal notations with a very large order type, originally created by the user **BashicuHyudora** of the Japanese Googology Wiki.

This project formalizes and machine-verifies the proof from:

- **Paper**: Rachel Hunter, *Well-Orderedness of the Bashicu Matrix System*, October 15, 2024.
  - arXiv: [2307.04606v3](https://arxiv.org/abs/2307.04606)

## Why Isabelle/HOL

Hunter's proof critically uses two ingredients that are challenging in most proof assistants:

1. **Gödel's constructible hierarchy `L_α`**.
2. **Σ_n-elementary substructure / stability reflection** (Kranakis 1982).

Lawrence Paulson has formalized **Gödel's Constructible Universe** in `Isabelle/ZF`, including `Constructible.thy` and the L hierarchy. This makes Isabelle the most pragmatic choice for the deepest lemma of the paper (Lemma 2.6).

The combinatorial parts of the proof (Lemmas 2.1–2.5) live more naturally in **Isabelle/HOL**, where automation tools (`auto`, `simp`, `blast`, `sledgehammer`) are extremely effective.

## Proof Structure

```
Theorem 2.7  BMS is well-ordered
│
├── 2.7.a  Define o(A) as the minimum α such that some stable
│          representation of A maps into α
├── 2.7.b  o is defined and order-preserving on the seed set
│          X_0 = {((0,…,0),(1,…,1))_n : n ∈ ℕ}
├── 2.7.c  Inductive step: build f_{n+1} from f_n using Lemma 2.6
├── 2.7.d  f_{n+1} is a stable representation of A[n+1] (uses Lemma 2.5)
├── 2.7.e  Closure under expansion ⇒ o defined on all of BMS
├── 2.7.f  An order-preserving o : BMS → Ord ⇒ no infinite descent
│
├── Lemma 2.6  Stability reflection
│   For α, β ∈ σ with ω < α <_n β, finite X ⊆ Ord below α and
│   finite Y ⊆ Ord with X < α ≤ Y < β, there exists a finite
│   Y' ⊆ Ord and a bijection f : Y → Y' preserving <, <_k, <_m
│   for k ∈ ℕ, m < n.
│   ├── 2.6.A  φ_0(η,ξ) ≡ η ∈ ξ  is Σ_0 (hence Σ_{n+1})
│   ├── 2.6.B  φ_1(η,ξ,k) ≡ η <_k ξ  is Σ_{n+1}
│   ├── 2.6.C  φ_2(η,k) ≡ ⟨L_η,∈⟩ ≺_{Σ_{k+1}} ⟨L,∈⟩  is Π_{k+1}
│   │          └── Kranakis 1982, Theorem 1.8
│   ├── 2.6.D  Finite conjunction of Σ_{n+1} formulas is Σ_{n+1}
│   ├── 2.6.E  Existential closure of a Σ_{n+1} formula is Σ_{n+1}
│   ├── 2.6.F  ψ ∧ φ true in L_β reflects to L_α via α <_n β
│   └── 2.6.G  Witnesses in L_α yield Y' and bijection f
│
├── Lemma 2.5  Five ancestry-preservation properties (proved by
│              simultaneous induction on k)
│   ├── 2.5 (i)    G→B_0 k-ancestry ⇔ G→B_n k-ancestry
│   ├── 2.5 (ii)   k-ancestry within B_0 ⇔ within B_n
│   ├── 2.5 (iii)  (n>0, k<m_0) i-th col in B_0 is k-ancestor of
│   │              last col of A ⇔ i-th col in B_{n-1} is k-ancestor
│   │              of first col in B_n
│   ├── 2.5 (iv)   k-parent of i-th col in B_n (i>0) lies in B_n or G
│   └── 2.5 (v)    k-ancestry from B_{n_0} to B_{n_1} ⇔ to B_{n_1+1}
│
└── Lemma 2.3  BMS is totally ordered
    │           (Order coincides with lexicographic order — Cor 2.4)
    │
    ├── Lemma 2.1  For all A ∈ BMS and n ∈ ℕ, A[n] <_lex A
    │              (columns also compared lexicographically)
    │
    └── Corollary 2.2  A' < A  ⇒  A' <_lex A
```

### Definitions used

- **Array** (Definition 1.1): an element of `(ℕ^n)^m`, i.e. a sequence of equal-length columns of natural numbers.
- **m-parent / m-ancestor**: structural relations between columns based on row-wise inequalities.
- **Ascending element**: an element of a column whose row "ascends" via the m-ancestor structure.
- **Expansion `A[n]`**: the rewrite step that defines the dynamics of BMS, of the form `A[n] = G + B_0 + B_1 + … + B_n`.
- **BMS**: the ⊆-minimal partial order containing the closure of the seeds `((0,…,0),(1,…,1))` under expansion at each `n ∈ ℕ`, with `A[n] ≤ A`.

## Repository Layout (planned)

```
bms-paper/
├── README.md / README-ja.md
├── isabelle/
│   ├── ROOT                        # session definition
│   ├── BMS_Defs.thy                # Definition 1.1, expansion
│   ├── BMS_Lex.thy                 # Lemma 2.1, Cor 2.2, Lemma 2.3, Cor 2.4
│   ├── BMS_Ancestry.thy            # Lemma 2.5
│   ├── BMS_Stability.thy           # Lemma 2.6 (axiomatized first)
│   └── BMS_WellOrdered.thy         # Theorem 2.7
└── isabelle_zf/
    └── BMS_Reflection.thy          # discharge of Lemma 2.6 (planned)
```

## Build / Reproduce

To be added once the first theory file is written.

```
isabelle build -d . BMS
```

## License

The original paper is © Rachel Hunter, distributed via arXiv. Formalization code in this repository will be released under a permissive open-source license (TBD).

## References

1. Rachel Hunter. *Well-Orderedness of the Bashicu Matrix System.* 2024. [arXiv:2307.04606](https://arxiv.org/abs/2307.04606)
2. BashicuHyudora. *Summary of big numbers in BASIC language* (Japanese). Googology Wiki.
3. Evangelos Kranakis. *Reflection and partition properties of admissible ordinals.* Annals of Mathematical Logic 22.3 (1982), 213–242.
4. Lawrence C. Paulson. *The Reflection Theorem* and *The Constructible Universe* in *Isabelle/ZF*. Archive of Formal Proofs.
