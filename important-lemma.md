# Hunter Lemma 2.5 — 5 clause の正式記述

ブログ記号 ($\boldsymbol{S}$, $X$, $Y$, $S_{xy}$, $t$, $r$, $\Delta_y$, $A_{xy}$, $\boldsymbol{B}^{(a)}$ 等) を使用。

## 補助記号

### 行列・展開

- $\boldsymbol{S}$: BMS 行列 ($X$ 列 × $Y$ 行)
- $S_{xy}$: 列 $x$、 行 $y$ の値
- $\boldsymbol{S}[n]$: 展開 ($a = 0, 1, \ldots, n$ について $\boldsymbol{B}^{(a)}$ を生成して結合し、 strip 適用)

### 各種 index

- $r := P_t(X-1)$ (bad root)
- $l := X - 1 - r$ (悪部分の列数)
- $\text{idx}_G(i) := i$ (良部分の $i$ 番目列 → $\boldsymbol{S}[n]$ における列 index)
- $\text{idx}_B(a, j) := r + a \cdot l + j$ ($\boldsymbol{B}^{(a)}$ の $j$ 番目列 → $\boldsymbol{S}[n]$ における列 index)
- $\text{idx}_{B_0\text{-orig}}(i) := r + i$ (元 $\boldsymbol{S}$ における悪部分の $i$ 番目列)

### Parent / Ancestor (再掲)

- $P_y(\boldsymbol{S}, x)$: 列 $x$ の 行 $y$ における親 (定義はブログ参照)
- $\text{Anc}_y(\boldsymbol{S}, x, j) := \exists a \geq 1.\ j = (P_y(\boldsymbol{S}, \cdot))^a (x)$

## clause (i) — $G$ への祖先関係は block index に依らない

$$
\forall i, j.\ (i < r \land j < l) \implies
\Bigl[ \text{Anc}_k(\boldsymbol{S}[n],\ \text{idx}_B(0, j),\ \text{idx}_G(i))
\iff
\text{Anc}_k(\boldsymbol{S}[n],\ \text{idx}_B(n, j),\ \text{idx}_G(i)) \Bigr]
$$

## clause (ii) — $\boldsymbol{B}$ 内部の祖先関係は block index に依らない

$$
\forall i, j.\ (i < l \land j < l) \implies
\Bigl[ \text{Anc}_k(\boldsymbol{S}[n],\ \text{idx}_B(0, j),\ \text{idx}_B(0, i))
\iff
\text{Anc}_k(\boldsymbol{S}[n],\ \text{idx}_B(n, j),\ \text{idx}_B(n, i)) \Bigr]
$$

## clause (iii) — 元 $\boldsymbol{S}$ と展開後 $\boldsymbol{S}[n]$ の祖先関係対応

$$
\forall i.\ (n > 0 \land t\text{ は定義済} \land k < t \land i < l) \implies
$$
$$
\Bigl[ \text{Anc}_k(\boldsymbol{S},\ X - 1,\ \text{idx}_{B_0\text{-orig}}(i))
\iff
\text{Anc}_k(\boldsymbol{S}[n],\ \text{idx}_B(n, 0),\ \text{idx}_B(n - 1, i)) \Bigr]
$$

## clause (iv) — 最上位 block $\boldsymbol{B}^{(n)}$ の parent は中間 block に居ない

$$
\forall i.\ (0 < i < l) \implies
\Bigl[\ P_k(\boldsymbol{S}[n],\ \text{idx}_B(n, i)) = \text{None}
$$
$$
\lor\ \exists p.\ P_k(\boldsymbol{S}[n],\ \text{idx}_B(n, i)) = p
$$
$$
\land\ \bigl(\ \exists j < l.\ p = \text{idx}_B(n, j)
\lor\ \exists j < r.\ p = \text{idx}_G(j) \bigr) \Bigr]
$$

## clause (v) — block index の上方 shift で祖先関係が不変

$$
\forall i, j, n_0, n_1.\ (i < l \land j < l \land n_0 < n_1 < n) \implies
$$
$$
\Bigl[ \text{Anc}_k(\boldsymbol{S}[n],\ \text{idx}_B(n_1, j),\ \text{idx}_B(n_0, i))
\iff
\text{Anc}_k(\boldsymbol{S}[n],\ \text{idx}_B(n_1 + 1, j),\ \text{idx}_B(n_0, i)) \Bigr]
$$

## clause 間の依存関係 (Hunter の同時帰納順)

Hunter の証明は $k$ に関する帰納 (IH: 全 $k' < k$ で `lemma_2_5_at` 成立) で、 各 $k$ で以下の順:

$$
\text{(ii)}_k \to \text{(iii)}_k \to \text{(iv)}_k \to \text{(i)}_k \to \text{(v)}_k
$$

各 sub-case は同 $k$ の先行 clause と IH at $k' < k$ を使う。 5 つを **同時に** 証明する。

## clause (i)-(v) の依存関係 matrix

行 = 「この clause を 行 $k$ で証明する」、 列 = 「同 $k$ で使う他 clause」。 `✓` = 依存あり、 `-` = なし。 **IH (= 全 clause at $k' < k$)** は全行で使う (列省略)。

|         | (i) | (ii) | (iii) | (iv) | (v) | IH at $k' < k$ |
|---------|:---:|:---:|:---:|:---:|:---:|:---:|
| **(i)**   | - | ✓  | ✓ | ✓ | - | ✓ |
| **(ii)**  | - | -  | - | - | - | ✓ |
| **(iii)** | - | ✓  | - | - | - | ✓ |
| **(iv)**  | - | ✓  | ✓ | - | - | ✓ |
| **(v)**   | ✓ | ✓  | ✓ | ✓ | - | ✓ |

### 重要点

- **線形順序 (循環なし)**: 本実装では (ii) → (iii) → (iv) → (i) → (v) の linear 順で組み立て、 joint lemma 不使用。 (iv) step lemma の signature には (v) at k なし
- **(ii) が最も独立**: 同 k で他 clause 不要、 IH のみで attempt 可能。 ただし IH 内で (iv) at $k' < k$ を使うので「真に独立」 ではない
- **(i) は (ii)(iii)(iv) に依存**: 同 k で 3 clause を要する。 単独証明は困難 (我々の attempt で確認済)
- **(iv) の (v) 非依存は未検証**: Hunter は (iv) at k で (v) at k を暗黙利用と読める論証をするが、 本実装は (v) なしで (iv) を proof する方針。 (iv) step lemma は現在 sorry、 attempt 時に独自戦略 (例: n=0 case は trivially) が要求される。 n=0 case は 2026-05-17 で proven (block 0 のみで positions trivial 分割)

### Hunter のオリジナル順序 vs 我々の実装順序

| 順序 | (1) | (2) | (3) | (4) | (5) |
|---|---|---|---|---|---|
| Hunter (paper) | (ii) | (iii) | (iv) | (i) | (v) |
| Isabelle (本実装) | (ii) | (iii) | (iv) | (i) | (v) |

両者同じ linear 順。 過去に検討した (iv)+(v) joint 案は不採用。

### 詳細

#### (i) at $k$
- IH + **(ii) at $k$** + **(iii) at $k$** + **(iv) at $k$**
- 内容: G への祖先関係が block index に依らない
- 依存 3 つ: (ii) で B 内 chain、 (iii) で chain の翻訳、 (iv) で chain の中間 block escape 排除

#### (ii) at $k$
- IH のみ使用 (= 全 clause at $k' < k$)
- 内容: B 内部の祖先関係が block index に依らない
- 直接攻撃: m_ancestor を IH 経由で walking、 bumping の uniform shift を利用

#### (iii) at $k$
- IH + **(ii) at $k$**
- 内容: 元 array と展開後の祖先関係対応
- (ii) を使う理由: 元 $S$ の `last_col → B_0[i]` 連鎖を $S[n]$ の `B_n[0] → B_{n-1}[i]` 連鎖に翻訳する際、 (ii) の block-invariance を介して

#### (iv) at $k$
- IH + **(ii) at $k$** + **(iii) at $k$** (本実装 signature; (v) at k は不要としている)
- 内容: 最上位 block の parent は中間 block に居ない
- Hunter は (v) at k を暗黙利用しているように読めるが、 本実装では (v) 非依存で discharge する方針 (戦略未確定、 現在 sorry)
- ✅ n=0 case proven inline (block 0 が唯一の B-block、 positions trivial 分割)

#### (v) at $k$
- IH + **(i) at $k$** + **(ii) at $k$** + **(iii) at $k$** + **(iv) at $k$** (linear、 (iv) 完了後)
- 内容: block index の上方 shift で祖先関係が不変
- (iv) を使う理由: shift 先の parent が中間 block に escape しないことを (iv) で保証

