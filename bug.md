# Hunter 論文 (arXiv:2307.04606v3) の正誤

Hunter, *Well-Orderedness of the Bashicu Matrix System* (October 15, 2024) を
Isabelle/HOL で形式化する過程で発見した、論文側の不整合・ゆるさ・誤植を蓄積する。

各項目で
- **Where**: 論文の該当箇所 (page / lemma / paragraph)
- **Issue**: 何が問題か (literal な誤り / 暗黙の仮定 / 表記ゆれ / 誤植)
- **Impact**: 形式化への影響
- **Workaround**: Isabelle 側でどう扱うか

## B-1. Lemma 2.3 proof: "A[0] = A without the last column" が strip と矛盾

**Where**: p.4, Lemma 2.3 proof 冒頭
> "For every non-empty A ∈ BMS, A[0] is simply A without the last column,
>  as it is equal to G + B_0, and thus A = A[0] + (C)."

**Issue**: Definition 1.1 の expansion は "with all rows of zeroes at the bottom removed" を含むため、
`A[0] = strip(G + B_0) = strip(butlast A)` であって `butlast A` そのものとは限らない。
具体例: `A = seed n` (n ≥ 1) では `butlast(seed n) = [replicate n 0]` が全行ゼロのため
strip で `[[]]` (0 行 1 列) に縮む。`A[0] + (C)` の列高さ (= 0) が (C) の高さ (= n) と
合わないため、`A = A[0] + (C)` は array としても成立しない。

**Impact**:
Lemma 2.3 の論証で使われている induction step "A = A[0] + (C)" は seed を含めた
non-empty BMS array で literal には成立しない。

**Workaround**:
Hunter の論証の正しい解釈は「A[n] は A[n+1] から [0] を何回か適用して得られる」
(構造的同一性 `A[n] = (A[n+1])[0]^k`)。これは strip 込みでも成立する。
実証: `seed 2 = [[0,0],[1,1]]` で
- `(seed 2)[2] = [[0],[1],[2]]` (strip で 1 行除去後)
- `(seed 2)[2][0] = [[0],[1]] = seed 1 = (seed 2)[1]` ✓

Isabelle 側では `seed_lex_implies_le_B` を直接の "A = A[0] + (C)" 経由ではなく、
`expansion_chain_le_B: k ≤ k' ⟹ A[k] ≤_B A[k']` を経由して証明する必要がある。

