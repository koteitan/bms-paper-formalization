# Lemma 2.5 同時帰納 — 実装設計 (2026-05-25, verify-first 設計フェーズ)

CORE-A(elem_lt domination)+ CORE-B(gateway)を一括で閉じる Hunter (i)-(v) 同時帰納の設計。
playbook (`reference_simultaneous_induction_playbook.md`) の step(a)(b)を具体化。
**まだ .thy に skeleton を入れない**(過去の premature-skeleton revert を回避)。設計確定 → 実装の順。

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

- **CASE l1 A ≥ 2(主ケース)**:
  - **DOM(A[n']) が非 vacuous なのは mpl(A[n'])≥1 のときのみ**(mpl=0 なら m<0 で vacuous、 位置不要)。
  - **mpl(A[n'])≥1 のとき** b0_start(A[n']) は **必ず block-start** R1: `= l0 A + c·l1 A`。 [要補題化: `loc_R1`、 **mpl(A[n'])≥1 guard 必須**; 2160/2160 検証]
  - ⚠️ 無条件 `loc_R1`(guard なし)は **偽**: mpl(A[n'])=0 で mid-block(R3)が起きる(反例 `A=(0)(1)(2)(1)(0)(1)(2)(1)`, b0(A[1])=8 mid-block)。
  - A[n'] の B0' block の interior 列 = bump 公式 `elem (A[n']) (idx_B c x) m = (A!(s_A+x))!m + (ascends A x m ? c·delta A m : 0)` で A の列に対応。
  - DOM(A[n']) ⟸ **DOM(A)[IH, 非 vacuous]** + bump 非負 + delta 構造(续9 で内部 transfer 720/0 検証済)。
  - → IH で閉じる(同レベル循環は展開方向に開く)。

- **CASE l1 A = 1(特殊・thin)** — `verify/probe_l1eq1_case.py` で構造判明(DOM(A[n']) 0 viol):
  - A の B0 単一列 → **DOM(A)[IH] は vacuous**。 B-region は同一列の bump コピー(`(A!s)!m + c·delta`)で block-index c に単調。
  - **R1 sub-case(b0_start(A[n']) block-start、 888/888)**: A[n'] の B0' interior は **全て B-region の bump コピー** → DOM = **bump の c-単調性**(bump 公式 + delta≥0)で直接証明。 DOM(A) 不要。 **clean**。
  - **R2 sub-case(b0_start(A[n']) in-G'、 l1=1 では多数 1515)**: interior = **G'-tail(verbatim A の G 列)+ B-region コピー**。 B-region は単調。 **G'-tail = A の G 列間 domination**(b0_start(A[n']) が後続 G 列を level<t' で dominate)が要 → DOM(A)(B0 domination)では覆われない。 **唯一の残設計 gap**。 見込み: clause (i)(G への ancestry)/ G-region の ancestry 保存(M1 `elem_orig_eq_AEn_G` で G'-tail は verbatim A)に帰着 → joint IH の clause から出る可能性。 要追加設計検証。

### 5 clause の expand step
- 既存の `lemma_2_5_{i,ii,iii,iv,v}_clause_step` を joint-IH(= bms_2_5_joint A + 同 k の他 clause)を仮定する形に保つ。
- CORE-B(gateway)の leaf(iii_single_step / clause_iv / clause_i 4本 / v_iff)は within-block monotonicity 経由で DOM に帰着 → DOM が IH/不変量に入ったことで閉じる見込み。 [要検証: 各 leaf が DOM から出るか]

## 3. 必要な補題(実装時に証明)
- `loc_R1`(**guarded**): `A∈BMS ⟹ l1 A ≥ 2 ⟹ mpl(A[n'])≥1 ⟹ b0_start(A[n']) = Some(l0 A + c·l1 A)`(block-start)。 guard 付きは 2160/2160 検証、 無条件は偽(mpl=0 で mid-block)。 構造証明要(おそらく clause(iv)/gateway から)。
- `dom_transfer_R1`: R1 block-start のとき DOM(A[n']) ⟸ DOM(A) + bump。 续9 で 720/0。
- `mpl_relation`: t'=mpl(A[n']) と tA の関係(t-1/t/t+1、 t'=t-1 は pure R1)。 IH を正しい level で使うため。
- l1 A=1 case の handle(設計 gap)。

## 4. リスク / 注意
- `loc_R1` 等は経験則 → §10 false-confidence 回避のため strip-correct + eval で再確認してから証明に使う([[feedback-strip-before-bms-verify]])。
- 実装は段階的に(まず CASE l1≥2 の DOM step、 次に 5 clause、 最後に l1=1)。 各段階で isbman build green を保ち、 **net-new sorry を増やさない**(閉じられない部分は単一の明示 sorry に留め、 skeleton 化しない)。
- premature skeleton(1→多 sorry)は過去 revert 済([[project-lemma-2-5-ii-iii-attack-state]] 续4)。 段階ごとに net-positive を確認。
