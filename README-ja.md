[English](README.md) | [Japanese](README-ja.md)

# BMS 整礎性 形式検証

**バージョン:** v0.1.25

巨大数論で知られる **バシク行列システム (Bashicu Matrix System, BMS)** の整礎性証明を、証明支援系 **Isabelle/HOL** で形式検証するプロジェクトです。

## 背景

バシク行列システムは、日本語版 Googology Wiki のユーザー **BashicuHyudora** 氏により考案された、非常に大きな順序型を持つ順序数表記の再帰的体系です。

本プロジェクトでは次の論文の証明を機械的に検証します:

- **対象論文**: Rachel Hunter, *Well-Orderedness of the Bashicu Matrix System*, 2024年10月15日
  - arXiv: [2307.04606v3](https://arxiv.org/abs/2307.04606)

## なぜ Isabelle/HOL か

Hunter 氏の証明は、ほとんどの証明支援系で扱いにくい以下の二つの道具を本質的に使用します:

1. **ゲーデルの構成可能階層 `L_α`**
2. **Σ_n-初等部分構造 / 安定反映原理** (Kranakis 1982)

Lawrence Paulson が **Isabelle/ZF** 上で `Constructible.thy` を含むゲーデル構成可能宇宙を完全形式化しており、論文中で最深部に位置する **Lemma 2.6** の検証に直接利用できます。これは他の証明支援系には存在しない決定的な優位点です。

一方、組合せ論的な部分 (Lemma 2.1〜2.5) は **Isabelle/HOL** との相性が良く、`auto`, `simp`, `blast`, `sledgehammer` などの強力な自動化機構の恩恵を受けられます。

## 証明の構造

```
Theorem 2.7  BMS は整礎
│
├── 2.7.a  o(A) を「A の安定表現が値域として収まる最小の α」として定義
├── 2.7.b  種集合 X_0 = {((0,…,0),(1,…,1))_n : n ∈ ℕ} 上で
│          o が定義され順序保存的であること
├── 2.7.c  帰納段: f_n から Lemma 2.6 を用いて f_{n+1} を構成
├── 2.7.d  f_{n+1} が A[n+1] の安定表現であること (Lemma 2.5 を使用)
├── 2.7.e  展開の閉包性により o が全 BMS 上で定義される
├── 2.7.f  順序保存写像 o : BMS → Ord の存在 ⇒ 無限降下列が不存在
│
├── Lemma 2.6  安定反映 (stability reflection)
│   α, β ∈ σ かつ ω < α <_n β, 有限 X ⊆ Ord (X は α 未満),
│   有限 Y ⊆ Ord (X < α ≤ Y < β) に対し、
│   有限 Y' ⊆ Ord と全単射 f : Y → Y' が存在し
│   <, <_k, <_m (k ∈ ℕ, m < n) を保存する。
│   ├── 2.6.A  φ_0(η,ξ) ≡ η ∈ ξ は Σ_0 (したがって Σ_{n+1})
│   ├── 2.6.B  φ_1(η,ξ,k) ≡ η <_k ξ は Σ_{n+1}
│   ├── 2.6.C  φ_2(η,k) ≡ ⟨L_η,∈⟩ ≺_{Σ_{k+1}} ⟨L,∈⟩ は Π_{k+1}
│   │          └── Kranakis 1982, Theorem 1.8 に依拠
│   ├── 2.6.D  有限個の Σ_{n+1} 論理式の連言は Σ_{n+1}
│   ├── 2.6.E  Σ_{n+1} 論理式の存在閉包は Σ_{n+1}
│   ├── 2.6.F  ψ ∧ φ が L_β で真 ⇒ α <_n β により L_α で真
│   └── 2.6.G  L_α 内の証拠から Y' と全単射 f を構成
│
├── Lemma 2.5  祖先関係保存に関する5つの性質
│              (k に関する同時帰納法で証明)
│   ├── 2.5 (i)    G→B_0 の k-祖先 ⇔ G→B_n の k-祖先
│   ├── 2.5 (ii)   B_0 内の k-祖先 ⇔ B_n 内の k-祖先
│   ├── 2.5 (iii)  (n>0, k<m_0) B_0 の i 列が末列の k-祖先
│   │              ⇔ B_{n-1} の i 列が B_n の最初の列の k-祖先
│   ├── 2.5 (iv)   B_n の i 列 (i>0) の k-親は B_n か G に存在
│   └── 2.5 (v)    B_{n_0} から B_{n_1} の k-祖先 ⇔ B_{n_1+1} の k-祖先
│
└── Lemma 2.3  BMS は全順序
    │           (順序は辞書式順序と一致 — Corollary 2.4)
    │
    ├── Lemma 2.1  全ての A ∈ BMS, n ∈ ℕ に対し A[n] <_lex A
    │              (列も辞書式に比較)
    │
    └── Corollary 2.2  A' < A  ⇒  A' <_lex A
```

### 使用される定義

- **配列 (array)** (Definition 1.1): `(ℕ^n)^m` の元、すなわち長さの揃った自然数列 (列, column) の列。
- **m-親 (m-parent) / m-祖先 (m-ancestor)**: 列の m 番目の要素の不等式に基づく構造的関係。
- **上昇要素 (ascending element)**: m-祖先構造において行が「上昇」する列の要素。
- **展開 `A[n]`**: BMS の動力学を定める書換えステップ。`A[n] = G + B_0 + B_1 + … + B_n` の形をとる。
- **BMS**: 種 `((0,…,0),(1,…,1))` を各 `n ∈ ℕ` での展開で閉じた集合の中で、`A[n] ≤ A` を満たす ⊆-極小な半順序。

## リポジトリ構成 (計画)

```
bms-paper/
├── README.md / README-ja.md
├── isabelle/
│   ├── ROOT                        # session 定義
│   ├── BMS_Defs.thy                # Definition 1.1, 展開
│   ├── BMS_Lex.thy                 # Lemma 2.1, Cor 2.2, Lemma 2.3, Cor 2.4
│   ├── BMS_Ancestry.thy            # Lemma 2.5
│   ├── BMS_Stability.thy           # Lemma 2.6 (まずは axiomatize)
│   └── BMS_WellOrdered.thy         # Theorem 2.7
└── isabelle_zf/
    └── BMS_Reflection.thy          # Lemma 2.6 の解消 (予定)
```

## ビルド / 再現

最初の理論ファイル作成後に追記します。

```
isabelle build -d . BMS
```

## ライセンス

元論文の著作権は Rachel Hunter 氏に帰属し、arXiv で配布されています。本リポジトリ内の形式化コードは寛容なオープンソースライセンス (TBD) で公開予定です。

## 参考文献

1. Rachel Hunter. *Well-Orderedness of the Bashicu Matrix System.* 2024. [arXiv:2307.04606](https://arxiv.org/abs/2307.04606)
2. BashicuHyudora. *BASIC言語による巨大数のまとめ*. Googology Wiki.
3. Evangelos Kranakis. *Reflection and partition properties of admissible ordinals.* Annals of Mathematical Logic 22.3 (1982), 213–242.
4. Lawrence C. Paulson. *The Reflection Theorem* および *The Constructible Universe* (Isabelle/ZF). Archive of Formal Proofs.
