# タスクリスト

> **メモ**: 完了したタスクは行を残し、状態欄に ✅ を入れる。
> 各 commit が一次履歴であり、本ファイルは概観用。
> **メモ**: 番号 (ID) は一度付けたら変更しない。新規追加は末尾に追加し、
> 完了・削除しても他の ID は再採番しない。
> **メモ**: 表は **怪しさ (truth が破れるリスク) の高い順** に並べる。
> 行内容を変更しても並べ替え順序は維持する。

現在 `sorry`: **3** (`seed_descendants_total`, `lemma_2_5_at_main` Some s, `stable_rep_extend_strict`)。

公理一覧 (BMS_Stability.thy / BMS_WellOrdered.thy):
- `ord_lt_irrefl`, `ord_lt_trans`, `ord_wf`: `<_o` の基本性質
- `sigma_pair_exists`: `∃α β ∈ sigma_bound. ω_o <_o α <_o β ∧ ∀m. stable_lt m α β` — Hunter の σ-pair 存在条件
- `lemma_2_6`: Hunter Lemma 2.6 そのまま (ZF 側で discharge 予定)
- `o_of_def`: `A ∈ BMS ⟹ ∃f. stable_rep A f ∧ (∀i. f i <_o o_of A) ∧ (β-minimality)` — BMS に制限済み (v0.1.28)

`stable_rep_extend_strict` は `A ≠ []` を仮定として持つ (`o_of [] = bottom` で `β <_o o_of []` が偽になるため、v0.1.25)。

## タスク (怪しさ高 → 低)

| ID | Lemma | タスク | 怪しさ要因 | 状態 | 見込み |
|---:|---|---|---|---|:---:|
|  3 | Cor 2.4 backward | `seed_descendants_total` 一般 N: `A ≤_B seed N ∧ A' ≤_B seed N ⟹ A ≤_B A' ∨ A' ≤_B A` (Hunter Lemma 2.3 closure 議論). N=0 base ✅ | Hunter の論証は (α)(β)(γ) を使うが (α) は strip と矛盾 (bug.md B-1)。strip-faithful な再構成が必要で、Hunter の loose な議論をそのまま写せない | 一般 N 残 | 数h–数日 |
| 14 | Theorem 2.7 / `stable_rep_extend_strict` | `β` の構成と `g i <_o β` の検証 | `β` の存在は Hunter handwave。`f` の最大値 (= `f(last col)`) を `β` に取れるか具体 indexing が論文未明示 | 13 待ち | 半日 |
| 13 | Theorem 2.7 / `stable_rep_extend_strict` | `g` が `stable_rep` を満たす証明 (Lemma 2.5 を本質的に使用) | Lemma 2.5 (i)-(v) の convention が Hunter の使い方と完全一致するか要検証。我々の `m_ancestor A m i j` の (j 早い側, i 後) と Hunter の (i 早い, j 後) で reverse が必要 | 12 待ち | 1日 |
| 12 | Theorem 2.7 / `stable_rep_extend_strict` | `g` の構成定義: G_block には `f` の対応値、B_i (i ≥ 1) には Lemma 2.6 の Y' 反射値 | indexing (B_n と B_{n+1} の対応) と Lemma 2.6 への X, Y の渡し方が Hunter で省略気味 | 5-8 待ち | 数h |
| 19 | Lemma 2.6 / Phase 3 ZF | 2.6.C: `φ_2(η,k) := L_η ≺_{Σ_{k+1}} L` が Π_{k+1} (Kranakis 1982 Theorem 1.8) | 外部依存 (Kranakis 論文の前提と命題が Paulson の `Constructible` 内で言明可能か未確認) | 18 待ち | 数日 |
|  5 | Lemma 2.5 | 補助補題群整備 (m_parent / m_ancestor が strip / bumping / k-祖先と相互作用する性質) | Hunter は "tedious but straightforward" と書くが、補題リストを論文に書かない。手作業で発見・列挙する必要 | 未着手 | 不明 |
|  6 | Lemma 2.5 | `lemma_2_5_at_inductive_step`: IH at `k' < k` から 5 clause を順に独立化 | (iv) と (v) が同一 k で相互依存 (BMS_Ancestry.thy のコメント参照)。Hunter の順序 (ii)→(iii)→(iv)→(i)→(v) を我々は (iv,v 同時)→(i,ii,iii) に変更したが、それで証明が通るかは未確認 | 5 待ち | 数h+ |
|  7 | Lemma 2.5 | `lemma_2_5_at_main_some` 本体: `nat_less_induct` で 6 を組み立て | 6 が完成すれば直接的だが、誘導の cong 関係に subtle なミスマッチが出やすい | 6 待ち | 1h |
| 22 | Lemma 2.6 / Phase 3 ZF | 2.6.F: ψ ∧ φ の `L_β` から `L_α` への反射 | Paulson の reflection theorem を ψ∧φ の具体形に当てはめる必要。論文では暗黙 | 21 待ち | 1日 |
| 23 | Lemma 2.6 / Phase 3 ZF | 2.6.G: `L_α` 内の証拠から `Y'` と全単射 `f` を構成 | 反射した formula の witness 抽出を全単射として整理する箇所、bijection を Isabelle で具体化する手間あり | 22 待ち | 1日 |
| 20 | Lemma 2.6 / Phase 3 ZF | 2.6.D: 有限 Σ_{n+1} 連言の Σ_{n+1} 性 | Σ_n hierarchy の closure は Paulson 内で確立済みだが、Σ_{n+1} 形式の boilerplate が要る | 19 待ち | 1日 |
| 21 | Lemma 2.6 / Phase 3 ZF | 2.6.E: Σ_{n+1} 存在閉包 | 同上 (20 と同質) | 20 待ち | 1日 |
| 18 | Lemma 2.6 / Phase 3 ZF | 2.6.B: `φ_1(η,ξ,k) := η <_k ξ` が Σ_{n+1} | 17 上の組合せ。Hunter は構造的に書くが Isabelle/ZF での Σ_n 階層内符号化に手間 | 17 待ち | 1日 |
|  8 | Lemma 2.5 | 既存 `lemma_2_5_i` 〜 `lemma_2_5_v` projection が新証明と互換に動作することを確認 | 7 完成後の sanity check。怪しさ低 | 7 待ち | 30m |
| 17 | Lemma 2.6 / Phase 3 ZF | 2.6.A: `φ_0(η,ξ) := η ∈ ξ` が Σ_0 | 標準事実、Paulson 内に既存の可能性 | 16 待ち | 1日 |
| 16 | Lemma 2.6 / Phase 3 ZF | Paulson `Constructible` ライブラリ import | 怪しさ低 (作業量のみ) | 15 待ち | 1日 |
| 24 | Lemma 2.6 / Phase 3 ZF | HOL 側の `axiomatize lemma_2_6` を ZF 側からの transfer に置換 | 23 完成後の機械的 transfer | 23 待ち | 半日 |
|  1 | Cor 2.4 backward | `seed_expansion_succ_zero`: `(seed (Suc n)[Suc k])[0] = seed (Suc n)[k]` (Hunter p.4 "A[0] = butlast A" の strip-faithful 版; bug.md B-1) | — | ✅ | — |
|  2 | Cor 2.4 backward | `seed_chain_le_B_expansion`: `k ≤ k' ⟹ seed (Suc n)[k] ≤_B seed (Suc n)[k']` (1 から導出) | — | ✅ | — |
|  4 | Cor 2.4 backward | `seed_lex_implies_le_B` (3 + Cor 2.2 + arr_lex_irrefl/trans で導出); `lex_implies_le_B` (`bms_pair_below_seed` + 3 経由で導出済み) | — | ✅ | — |
|  9 | Theorem 2.7 / `o_on_seed` | `Ord_t` の axiom 拡張: `sigma_pair_exists` (Hunter σ-pair 存在) | — | ✅ | — |
| 10 | Theorem 2.7 / `o_on_seed` | seed n の 2 列に対し `f 0 = α, f 1 = β` で `stable_rep` を構築 | — | ✅ | — |
| 11 | Theorem 2.7 / `o_on_seed` | `m_ancestor (seed n) m 1 0` の `m ≥ n` ケース補強 | — | ✅ | — |
| 15 | Lemma 2.6 / Phase 3 ZF | `isabelle_zf/` ディレクトリ・`ROOT` 雛形 | — | ✅ | — |
| 25 | Soundness audit | `sigma_pair_exists` を Hunter の σ-pair 条件に強化 (v0.1.27) | — | ✅ | — |
| 26 | Soundness audit | `o_of_def` 公理を `A ∈ BMS` に制限 (v0.1.28) | — | ✅ | — |
