# Lemma 2.5 同時帰納 — 実装設計 (2026-05-25, verify-first 設計フェーズ)

CORE-A(elem_lt domination)+ CORE-B(gateway)を一括で閉じる Hunter (i)-(v) 同時帰納の設計。
playbook (`reference_simultaneous_induction_playbook.md`) の step(a)(b)を具体化。
**まだ .thy に skeleton を入れない**(過去の premature-skeleton revert を回避)。設計確定 → 実装の順。

> **2026-05-25 更新(续29)**: domination transfer の両ブランチが proven building block になった —
> R1=`dom_transfer_R1`(DOM(A)+bump)、 R2=`dom_transfer_R2`(ancestry+`m_ancestor_elem_lt`)。
> 両者とも **domination は ancestry の下流**。 ∴ CORE-A も CORE-B も「**ancestry clause (i)-(v)
> の前方伝播**」 という単一目標に収束。 残るは ⑥ assembly = ancestry を BMS.induct で回す同時帰納
> (= Hunter 原論文の (i)-(v) k-induction)。 domination/elem_lt はそこから自動。

## 1. 複合不変量 (step a: joint-IH の形)

domination を Lemma 2.5 の 5 clause と束ねた複合述語を **`induct A rule: BMS.induct`(展開帰納)** で証明する。

```
bms_2_5_joint A ≡
  (∀ n k. lemma_2_5_i_clause   A n k
        ∧ lemma_2_5_ii_clause  A n k
        ∧ lemma_2_5_iii_clause A n k
        ∧ lemma_2_5_iv_clause  A n k
        ∧ lemma_2_5_v_clause   A n k)
  ∧ DOM A
where
  DOM A ≡ ∀ s t m j. b0_start A = Some s ⟶ max_parent_level A = Some t
                   ⟶ m < t ⟶ 0 < j ⟶ j < l1 A
                   ⟶ elem A s m < elem A (s+j) m            (= elem_lt_below_t)
```

`theorem: A ∈ BMS ⟹ bms_2_5_joint A`、 `proof (induct A rule: BMS.induct)`。
- 既存の `lemma_2_5_at_main` は固定 A の k/n 帰納で 5 clause を組むが、 **(ii) だけ standalone(elem_lt 経由)で DOM が IH に無い**のが病巣。 DOM を不変量に入れ、 展開帰納の IH で predecessor の DOM を使えるようにするのが本設計の要。

## 2. 帰納構造 (step b: 各 step が IH で閉じるか)

### seed case (A = seed N)
- `l1 (seed N) ≤ 1` ゆえ **DOM は vacuous**(interior 列 0<j<l1 が無い)。
- 5 clause の seed case は既存(`lemma_2_5_at_n_zero` 等)を流用。

### expand case (A ↦ A[n'], predecessor = A, IH = bms_2_5_joint A)
DOM(A[n']) を示す。 b0_start(A[n']) の位置で **l1 A による case-split**(正しい検証は `verify/probe_location_3way.py`; 旧 `probe_location_predictor.py` は mid-block 破棄バグで信用不可):

- **DOM(A[n']) が非 vacuous なのは `l1(A[n'])≥2 ∧ mpl(A[n'])≥1` のときのみ**(これが位置を使う設計領域)。
- ⚠️ **「l1 A≥2 ⟹ block-start」 は偽だった**(私の coverage-gap/bucket バグ artifact、3回訂正、続24)。 確定版 `verify/probe_location_correct.py`(深い BFS, MECE, 正しい guard): 設計領域で位置は **2-way: R1(block-start `=l0A+c·l1A`)∨ R2(in-G' `<l0A`)**、 **mid-block(R3)は起きない**(R3=0; これだけが robust な前進)。 clean な l1 discriminator は無い。
- 共通: A[n'] の B-region 列 = bump 公式 `elem (A[n']) (idx_B c x) m = (A!(s_A+x))!m + (ascends A x m ? c·delta A m : 0)`。
- **CASE R1(b0_start(A[n']) = block-start)**: B0' interior は bump コピー → DOM(A[n']) ⟸ DOM(A)[IH]+bump(续9 transfer 720/0)。 比較的 clean。
- **CASE R2(b0_start(A[n']) in-G')** — ✅ **解決(`dom_transfer_R2`, 续29)**: 「G'-tail = A の G 列間 domination(M1 proxy)」 という見方は **誤り**だった(M1 は global 再index/strip を無視、 续27 の 54viol は probe artifact)。 **A[n]-direct に見れば R2 target は `elem_lt_below_t` を A[n]∈BMS で instantiate したものそのもの**で、 G'-tail/B-region の case-split は無い(B0'(A[n]) は連続 index）。 必要不変量 = **ancestry conjunct `ANC(A[n])`**(s'=b0_start(A[n]) が A[n] 内で s'+j の m-祖先、 = `b0_col_ancestor_below_t` の A[n] 結論 = 同時帰納が運ぶ ancestry)。 ANC があれば domination は `m_ancestor_elem_lt` で free。 genuine-seed/A[n]-direct で 0 viol 検証(`verify/probe_R2_anc_at_AEn.py`)。

- **CASE l1 A = 1(特殊・thin)** — `verify/probe_l1eq1_case.py` で構造判明(DOM(A[n']) 0 viol):
  - A の B0 単一列 → **DOM(A)[IH] は vacuous**。 B-region は同一列の bump コピー(`(A!s)!m + c·delta`)で block-index c に単調。
  - **R1 sub-case(b0_start(A[n']) block-start、 888/888)**: A[n'] の B0' interior は **全て B-region の bump コピー** → DOM = **bump の c-単調性**(bump 公式 + delta≥0)で直接証明。 DOM(A) 不要。 **clean**。
  - **R2 sub-case(b0_start(A[n']) in-G')** — ✅ **解決(续29)**: 上の CASE R2 と同一。 「G 列間 domination が唯一の残 gap」 は M1 proxy 由来の誤認で、 A[n]-direct では ancestry invariant `ANC(A[n])` から `m_ancestor_elem_lt` で従う(`dom_transfer_R2`)。 残作業ではない。

### 5 clause の expand step
- 既存の `lemma_2_5_{i,ii,iii,iv,v}_clause_step` を joint-IH(= bms_2_5_joint A + 同 k の他 clause)を仮定する形に保つ。
- CORE-B(gateway)の leaf(iii_single_step / clause_iv / clause_i 4本 / v_iff)は within-block monotonicity 経由で DOM に帰着 → DOM が IH/不変量に入ったことで閉じる見込み。 [要検証: 各 leaf が DOM から出るか]

## 3. 必要な補題(実装時に証明)
- ✅ `dom_transfer_R1`: R1 block-start のとき domination ⟸ DOM(A)[IH] + bump(off''>0 は DOM+単調、 off''=0 は DPOS strictness)。 proven(955fbca)、 eval 111321/0。
- ✅ `dom_transfer_R2` / `dom_transfer_R2_via_BMS`: R2 in-G' のとき domination ⟸ ancestry `ANC(A[n])` + `m_ancestor_elem_lt`。 proven(续29）、 genuine-seed 30936/0。
- `loc`: 設計領域(`l1(A[n'])≥2 ∧ mpl(A[n'])≥1`)で位置は 2-way R1∨R2(mid-block R3=0、 genuine-seed `probe_location_genuine.py` で 0)。 **無条件 block-start は偽**。 R1/R2 exhaustive split が必要(closed form なし)。
- `mpl_relation`: t'=mpl(A[n']) と tA の関係(t-1/t/t+1、 t'=t-1 は pure R1)。 IH を正しい level で使うため。
- **⭐ 真の load-bearing target = ancestry clause (i)-(v) の前方伝播**。 R1/R2 とも domination は ancestry の下流(m_ancestor_elem_lt)ゆえ、 ⑥ assembly では DOM/elem_lt でなく **ancestry 不変量が expansion で伝播することを BMS.induct で回す**(Hunter 原論文の同時 k-induction)。

## 4. リスク / 注意
- `loc_R1` 等は経験則 → §10 false-confidence 回避のため strip-correct + eval で再確認してから証明に使う([[feedback-strip-before-bms-verify]])。
- 実装は段階的に(まず CASE l1≥2 の DOM step、 次に 5 clause、 最後に l1=1)。 各段階で isbman build green を保ち、 **net-new sorry を増やさない**(閉じられない部分は単一の明示 sorry に留め、 skeleton 化しない)。
- premature skeleton(1→多 sorry)は過去 revert 済([[project-lemma-2-5-ii-iii-attack-state]] 续4)。 段階ごとに net-positive を確認。
