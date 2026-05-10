# タスクリスト

> **メモ**: 完了履歴はこのファイルに書かないこと。各 commit 自体が履歴であり、
> 重複させると古くなって誤情報になる。
> **メモ**: 番号 (ID) は一度付けたら変更しない。新規追加は末尾に追加し、
> 完了・削除しても他の ID は再採番しない。

現在 `sorry`: **4** (`lex_implies_le_B`, `lemma_2_5_at_main` Some s, `o_on_seed`, `stable_rep_extend_strict`)。

## タスク

| ID | Lemma | タスク | 状態 | 見込み |
|---:|---|---|---|:---:|
|  1 | Cor 2.4 backward | `expansion_succ_zero_eq` 系 (制限版) の正しい命題化: empirical に成立する `A` の class を整理 | 未着手 | 不明 |
|  2 | Cor 2.4 backward | `expansion_chain_le_B`: `k ≤ k' ⟹ A[k] ≤_B A[k']` を 1 から導出 | 1 待ち | 30m |
|  3 | Cor 2.4 backward | cross-branch totality: `B ∈ BMS, X ≤_B B, Y ≤_B B ⟹ X ≤_B Y ∨ Y ≤_B X` を double induction で構築 | 2 待ち | 数h |
|  4 | Cor 2.4 backward | `lex_implies_le_B` 本体 (3 + `bms_pair_below_seed` で確定) | 3 待ち | 30m |
|  5 | Lemma 2.5 | 補助補題群整備 (m_parent / m_ancestor が strip / bumping / k-祖先と相互作用する性質) | 未着手 | 不明 |
|  6 | Lemma 2.5 | `lemma_2_5_at_inductive_step`: IH at `k' < k` から各 clause を順に 5 個の helper として独立化 | 5 待ち | 数h+ |
|  7 | Lemma 2.5 | `lemma_2_5_at_main_some` 本体: `nat_less_induct` で 6 を組み立て | 6 待ち | 1h |
|  8 | Lemma 2.5 | 既存 `lemma_2_5_i` 〜 `lemma_2_5_v` projection が新証明と互換に動作することを確認 | 7 待ち | 30m |
|  9 | Theorem 2.7 / `o_on_seed` | `Ord_t` の axiom 拡張: 任意の `n` に対し `stable_lt n α β` を満たす `α <_o β` の存在 | 公理化判断要 | 1h+ |
| 10 | Theorem 2.7 / `o_on_seed` | seed n の 2 列に対し `f 0 = α, f 1 = β` で `stable_rep` を構築 | 9 待ち | 1h |
| 11 | Theorem 2.7 / `o_on_seed` | `m_ancestor (seed n) m 1 0` の `m ≥ n` ケース補強 (m_parent_seed 系拡張) | 未着手 | 1h |
| 12 | Theorem 2.7 / `stable_rep_extend_strict` | `g` の構成定義: G_block には `f` の対応値、B_i (i ≥ 1) には Lemma 2.6 で反射した値 | 5-8 待ち | 数h |
| 13 | Theorem 2.7 / `stable_rep_extend_strict` | その `g` が `stable_rep` を満たすことの証明 (Lemma 2.5 を本質的に使用) | 12 待ち | 1日 |
| 14 | Theorem 2.7 / `stable_rep_extend_strict` | `β` の構成と `g i <_o β` の検証 | 13 待ち | 半日 |
| 15 | Lemma 2.6 / Phase 3 ZF | `isabelle_zf/` ディレクトリ・`ROOT` 雛形 | 未着手 | 30m |
| 16 | Lemma 2.6 / Phase 3 ZF | Paulson `Constructible` ライブラリ import | 15 待ち | 1日 |
| 17 | Lemma 2.6 / Phase 3 ZF | 2.6.A: `φ_0(η,ξ) := η ∈ ξ` が Σ_0 | 16 待ち | 1日 |
| 18 | Lemma 2.6 / Phase 3 ZF | 2.6.B: `φ_1(η,ξ,k) := η <_k ξ` が Σ_{n+1} | 17 待ち | 1日 |
| 19 | Lemma 2.6 / Phase 3 ZF | 2.6.C: `φ_2(η,k) := L_η ≺_{Σ_{k+1}} L` が Π_{k+1} (Kranakis 1982 経由) | 18 待ち | 数日 |
| 20 | Lemma 2.6 / Phase 3 ZF | 2.6.D: 有限 Σ_{n+1} 連言の Σ_{n+1} 性 | 19 待ち | 1日 |
| 21 | Lemma 2.6 / Phase 3 ZF | 2.6.E: Σ_{n+1} 存在閉包 | 20 待ち | 1日 |
| 22 | Lemma 2.6 / Phase 3 ZF | 2.6.F: ψ ∧ φ の `L_β` から `L_α` への反射 | 21 待ち | 1日 |
| 23 | Lemma 2.6 / Phase 3 ZF | 2.6.G: `L_α` 内の証拠から `Y'` と全単射 `f` を構成 | 22 待ち | 1日 |
| 24 | Lemma 2.6 / Phase 3 ZF | HOL 側の `axiomatize lemma_2_6` を ZF 側からの transfer に置換 | 23 待ち | 半日 |
