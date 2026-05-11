# タスクリスト

> **メモ**: 完了したタスクは行を残し、状態欄に ✅ を入れる。
> 各 commit が一次履歴であり、本ファイルは概観用。
> **メモ**: 番号 (ID) は一度付けたら変更しない。新規追加は末尾に追加し、
> 完了・削除しても他の ID は再採番しない。

現在 `sorry`: **3** (`seed_lex_implies_le_B`, `lemma_2_5_at_main` Some s, `stable_rep_extend_strict`)。

公理一覧 (BMS_Stability.thy / BMS_WellOrdered.thy):
- `ord_lt_irrefl`, `ord_lt_trans`, `ord_wf`: `<_o` の基本性質
- `sigma_pair_exists`: `∃α β ∈ sigma_bound. ω_o <_o α <_o β ∧ ∀m. stable_lt m α β` — Hunter の σ-pair 存在条件
- `lemma_2_6`: Hunter Lemma 2.6 そのまま (ZF 側で discharge 予定)
- `o_of_def`: `A ∈ BMS ⟹ ∃f. stable_rep A f ∧ (∀i. f i <_o o_of A) ∧ (β-minimality)` — BMS に制限済み (v0.1.28)

`stable_rep_extend_strict` は `A ≠ []` を仮定として持つ (`o_of [] = bottom` で `β <_o o_of []` が偽になるため、v0.1.25)。

## タスク

| ID | Lemma | タスク | 状態 | 見込み |
|---:|---|---|---|:---:|
|  1 | Cor 2.4 backward | `seed_expansion_succ_zero`: `(seed (Suc n)[Suc k])[0] = seed (Suc n)[k]` (Hunter p.4 "A[0] = butlast A" の strip-faithful 版; bug.md B-1) | ✅ | — |
|  2 | Cor 2.4 backward | `seed_chain_le_B_expansion`: `k ≤ k' ⟹ seed (Suc n)[k] ≤_B seed (Suc n)[k']` (1 から導出) | ✅ | — |
|  3 | Cor 2.4 backward | `seed_lex_implies_le_B`: `A ≤_B seed N, A' ≤_B seed N, A <_lex A' ⟹ A ≤_B A'` (seed の展開木内部での cross-branch totality; Hunter (γ) `A[n] < A' ≤ A[n+1] ⟹ A[n] ≤_B A'[0]` 経由) | 2 完了, 詰めはまだ | 数h |
|  4 | Cor 2.4 backward | `lex_implies_le_B` (`bms_pair_below_seed` + 3 で `seed N` に落とす形で導出済み) | ✅ | — |
|  5 | Lemma 2.5 | 補助補題群整備 (m_parent / m_ancestor が strip / bumping / k-祖先と相互作用する性質) | 未着手 | 不明 |
|  6 | Lemma 2.5 | `lemma_2_5_at_inductive_step`: IH at `k' < k` から各 clause を順に 5 個の helper として独立化 | 5 待ち | 数h+ |
|  7 | Lemma 2.5 | `lemma_2_5_at_main_some` 本体: `nat_less_induct` で 6 を組み立て | 6 待ち | 1h |
|  8 | Lemma 2.5 | 既存 `lemma_2_5_i` 〜 `lemma_2_5_v` projection が新証明と互換に動作することを確認 | 7 待ち | 30m |
|  9 | Theorem 2.7 / `o_on_seed` | `Ord_t` の axiom 拡張: `sigma_pair_exists`: ∃α β ∈ sigma_bound. ω_o<_o α<_o β ∧ ∀m. stable_lt m α β (Hunter σ-pair 存在) | ✅ | — |
| 10 | Theorem 2.7 / `o_on_seed` | seed n の 2 列に対し `f 0 = α, f 1 = β` で `stable_rep` を構築 | ✅ | — |
| 11 | Theorem 2.7 / `o_on_seed` | `m_ancestor (seed n) m 1 0` の `m ≥ n` ケース補強 (m_parent_seed 系拡張) | ✅ | — |
| 12 | Theorem 2.7 / `stable_rep_extend_strict` | `g` の構成定義: G_block には `f` の対応値、B_i (i ≥ 1) には Lemma 2.6 で反射した値 | 5-8 待ち | 数h |
| 13 | Theorem 2.7 / `stable_rep_extend_strict` | その `g` が `stable_rep` を満たすことの証明 (Lemma 2.5 を本質的に使用) | 12 待ち | 1日 |
| 14 | Theorem 2.7 / `stable_rep_extend_strict` | `β` の構成と `g i <_o β` の検証 | 13 待ち | 半日 |
| 15 | Lemma 2.6 / Phase 3 ZF | `isabelle_zf/` ディレクトリ・`ROOT` 雛形 (空セッション build OK) | ✅ | — |
| 16 | Lemma 2.6 / Phase 3 ZF | Paulson `Constructible` ライブラリ import | 15 待ち | 1日 |
| 17 | Lemma 2.6 / Phase 3 ZF | 2.6.A: `φ_0(η,ξ) := η ∈ ξ` が Σ_0 | 16 待ち | 1日 |
| 18 | Lemma 2.6 / Phase 3 ZF | 2.6.B: `φ_1(η,ξ,k) := η <_k ξ` が Σ_{n+1} | 17 待ち | 1日 |
| 19 | Lemma 2.6 / Phase 3 ZF | 2.6.C: `φ_2(η,k) := L_η ≺_{Σ_{k+1}} L` が Π_{k+1} (Kranakis 1982 経由) | 18 待ち | 数日 |
| 20 | Lemma 2.6 / Phase 3 ZF | 2.6.D: 有限 Σ_{n+1} 連言の Σ_{n+1} 性 | 19 待ち | 1日 |
| 21 | Lemma 2.6 / Phase 3 ZF | 2.6.E: Σ_{n+1} 存在閉包 | 20 待ち | 1日 |
| 22 | Lemma 2.6 / Phase 3 ZF | 2.6.F: ψ ∧ φ の `L_β` から `L_α` への反射 | 21 待ち | 1日 |
| 23 | Lemma 2.6 / Phase 3 ZF | 2.6.G: `L_α` 内の証拠から `Y'` と全単射 `f` を構成 | 22 待ち | 1日 |
| 24 | Lemma 2.6 / Phase 3 ZF | HOL 側の `axiomatize lemma_2_6` を ZF 側からの transfer に置換 | 23 待ち | 半日 |
| 25 | Soundness audit | `sigma_pair_exists` を Hunter の σ-pair 条件 (sigma_bound 内 / ω_o<_o α / ∀m.stable_lt m α β) に強化 (v0.1.27) | ✅ | — |
| 26 | Soundness audit | `o_of_def` 公理を `A ∈ BMS` に制限 (v0.1.28 — m_ancestor 不整合配列で stable_rep が存在しない可能性に対処) | ✅ | — |
