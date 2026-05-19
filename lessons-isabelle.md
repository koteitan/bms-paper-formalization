# Isabelle/HOL 形式証明 教訓

直近 (2026-05-17 〜 2026-05-19) の Lemma 2.5 攻略で得た知見。

## 1. ビルド検証 — 「exit 0」 は嘘になる

### 問題

`setsid timeout --kill-after=10s N isabelle build -d . BMS > log 2>&1; echo "exit=$?"` で `exit=0` を見ても、 実際の build は失敗していたケースが複数あった。

- 親 bash が `setsid` で detach すると即終了 (exit 0)
- 子の `isabelle build` (= java process) は別 session で継続
- `polyml` が orphan として 99% CPU で残り、 build は実は進んでいる
- 親の exit code を build 結果と誤認すると、 broken な code が commit される

### 教訓

- `isabelle build` の **完走判定は log の "Finished BMS"** で行う (exit code は信用しない)
- `Failed`、 `*** Failed to`、 `Errors:` が出れば build 失敗
- `-v` を必ず付ける。 出力なしの 30 分待ちは無駄

### 推奨コマンド

```bash
setsid timeout --kill-after=10s 3600 isabelle build -v -d . BMS > /tmp/build.log 2>&1
# その後、 log を tail で監視:
tail -F /tmp/build.log | grep -E "(Finished|Failed|FAILED|\*\*\*|theory.*100%)"
```

## 2. `-v` 出力で slow tactic を特定する

### 形式

```
BMS: command "by" running for 56.055s (line 3549 of theory "BMS.BMS_Ancestry")
```

5 秒以上更新されない `by` は調査対象。 20 秒超えたら確実に書き直す。

### よくある slow tactic

- `metis [lemma1 lemma2 lemma3 lemma4 lemma5 lemma6 lemma7]` — 多 lemma の resolution 探索が指数爆発
- `by auto` で大きい goal — 不要な unfolding を試して時間を食う
- `by (simp add: foo_def bar_def)` — 複数 def の組合せ展開

### 対策

- metis は 1-2 lemma に絞るか、 `define`/`obtain`/手動 derivation に置換
- auto より blast/force/explicit
- 簡単な式変形は `by (rule lemma)` で直接

## 3. 再帰関数 (m_ancestor) の auto-unfolding 罠

### 背景

`m_ancestor A k i j` は再帰関数で、 内部的に `m_parent` を呼んで chain を辿る:
```
m_ancestor A k i j = (case m_parent A k i of
                       None ⇒ False
                     | Some p ⇒ p = j ∨ m_ancestor A k p j)
```

Isabelle はこの定義式を `m_ancestor.simps` という名前で **simp set に自動登録** する。

### 問題

`m_ancestor A k i j` を含む goal に対して `by simp` や `by auto` を呼ぶと、 simp が `m_ancestor.simps` を発動して上記 case statement に展開する。 展開後、 別の場所で書いた `m_ancestor A k i j` (まだ展開されていない) との照合が外れ、 自動証明が閉じなくなる。

具体的に: filter predicate に `m_ancestor A k (s+j) j'` を含むと、 simp 後 goal は:
```
filter (λj'. ... ∧ (case m_parent A k (s+j) of None ⇒ False | Some p ⇒ p = j' ∨ m_ancestor A k p j'))
       [0..<s+j] = []
```
となり、 仮定 `m_ancestor A k (s+j) p` (展開前) と filter 内の case expression (展開後) が syntactic に違うので matching に失敗。

### 解決策

3 通り。

**(a) 明示 unfold lemma を使う**

`m_anc_via_parent_some: m_parent A m i = Some p ⟹ m_ancestor A m i j ⟷ p = j ∨ m_ancestor A m p j` を `using` で渡す。 これは `m_parent` が分かっている前提なので unfolding が制御できる。

**(b) filter membership 経由で抽出**

`r = last (filter ?P [0..<y])` で `cands_y_ne` (= filter ≠ []) が分かっていれば:
```isabelle
have "r ∈ set (filter ?P [0..<y])" using last_in_set[OF cands_y_ne] by simp
hence "?P r" by simp  (* これは filter membership の定義 *)
```
`?P r` の中に欲しい `m_ancestor A k y r` が conjunct として入っているので、 そこから取り出せる。 simp で再展開されない。

**(c) どうしても simp 必要なら抑止**

```isabelle
by (auto simp del: m_ancestor.simps)
```
で `m_ancestor` 自動展開を切る。 ただし他 tactic は使えない。

## 4. ライブラリ lemma の signature を名前から推測しない

### 失敗例

`sorted (filter P xs)` を示したくて `by (simp add: sorted_filter)` と書いた。 名前から「sorted preserved under filter」 と直感したが、 実際の `sorted_filter` は別物:

```isabelle
lemma sorted_filter:
  "sorted (map f xs) \<Longrightarrow> sorted (map f (filter P xs))"
```

`map f` が必須で、 単純な `sorted (filter ...)` には適用できない。 結果 simp が閉じず build 失敗。

### 正しい lemma

求めていたのは **`sorted_wrt_filter`** (= 別ファイル `List.thy` line 5896):

```isabelle
lemma sorted_wrt_filter:
  "sorted_wrt R xs \<Longrightarrow> sorted_wrt R (filter P xs)"
```

`sorted xs = sorted_wrt (\<le>) xs` なので、 `sorted_wrt_filter` を instantiate すれば `sorted xs ⟹ sorted (filter P xs)` が得られる:

```isabelle
have sorted_cands: "sorted (filter ?P [0..<n])"
  by (rule sorted_wrt_filter[OF sorted_upt])
```
ここで `sorted_upt: sorted [0..<n]` も library 既存。

### 教訓

似た名前の lemma が複数あるとき、 名前で判断せず必ず source で signature を確認:
```bash
grep -n "^lemma sorted_" /opt/Isabelle2025-2/src/HOL/List.thy
```
で候補一覧を見て、 conclusion 形が一致するものを選ぶ。

## 5. text ブロック内の `@{thm}` は parse 時に解決される

### 背景

Isabelle の `text \<open>...\<close>` ブロックは latex/html 生成用のドキュメンテーション。 中に `@{thm foo}` と書くと、 「lemma foo の statement をここに展開して表示」 という指示。

### 問題

`@{thm foo}` は **theory 読み込み時 (parse 時) に解決される**。 もし foo の定義 (= `lemma foo: ...`) が text ブロックより後にあると、 parse 時には未定義なので:
```
*** Undefined fact: "foo"
```
で build が失敗する。 ファイル内の順序が重要。

### 失敗例

```isabelle
text \<open>
  Maximality sub-lemma for case 2 of @{thm bms_chain_level_lift_A}:  -- line 3374
  ...
\<close>

lemma bms_max_elem_above_q1: ...  -- 補助 lemma (line 3381)

...

lemma bms_chain_level_lift_A: ...  -- 本体 (line 3500)
```

text が line 3374、 `bms_chain_level_lift_A` の定義が line 3500。 text を parse する時点で本体未定義。

### 解決策

(a) text 内の `@{thm}` を **plain text の名前** に置換:
```isabelle
text \<open>
  Maximality sub-lemma for case 2 of \<open>bms_chain_level_lift_A\<close> (defined below):
  ...
\<close>
```
`\<open>...\<close>` で囲むと verbatim 表示 (latex の \texttt{} 相当)、 解決不要。

(b) lemma を先に定義してから text を書く (ファイル順を入れ替え)。

教訓: 後方参照を `@{thm}` で書かない。 forward reference に気付かず latex 生成だけ通って build 通らなかった、 の罠。

## 6. List 操作の頑健 pattern

### 「x ∈ set xs ⟹ xs ≠ []」 が auto で閉じない

filter predicate に m_ancestor 等の case statement が含まれると auto が混乱。

```isabelle
(* NG *)
have cands_ne: "?cands ≠ []" using p_in_cands by auto

(* OK: 数値不等式に落とす *)
have cands_ne: "?cands ≠ []"
  using length_pos_if_in_set[OF p_in_cands] by simp
```

### 「∀x ∈ set xs. x ≤ last xs」 が metis で 40 秒以上

sorted list の最大が last、 という標準事実。 metis に多 lemma 渡すと爆発。

```isabelle
(* OK: 明示 nth-mono *)
have all_le_last: "∀y ∈ set ?cands. y ≤ last ?cands"
proof
  fix y assume y_in: "y ∈ set ?cands"
  have ex_k: "∃k<length ?cands. ?cands ! k = y"
    using y_in unfolding in_set_conv_nth by blast
  obtain k where k_lt: "k < length ?cands" and yk_eq: "?cands ! k = y"
    using ex_k by blast
  have len_pos: "0 < length ?cands" using cands_ne by simp
  have k_le: "k ≤ length ?cands - 1" using k_lt by linarith
  have last_lt: "length ?cands - 1 < length ?cands" using len_pos by simp
  have "?cands ! k ≤ ?cands ! (length ?cands - 1)"
    using sorted_cands k_le last_lt by (simp add: sorted_iff_nth_mono)
  moreover have "last ?cands = ?cands ! (length ?cands - 1)"
    using cands_ne by (simp add: last_conv_nth)
  ultimately show "y ≤ last ?cands" using yk_eq by simp
qed
```

## 7. 経験的検証 (empirical verification)

### workflow

形式証明開始前に **データで命題真偽を verify**:
1. yaBMS C tool (`tmp/yaBMS/c/bms`) で BMS 展開
2. Python BFS で seed (= Hunter `seed n`) から expand
3. 命題を Python に書き、 全 BMS でテスト
4. 違反 0 → 証明試行、 違反あり → 命題改訂

### 実例

- `at_zero_when_t_pos`: 328 BMS、 0 違反 → 証明試行 → 成功
- `bms_not_ascend_propagates_to_chain_ancestor`: 151 BMS で 2 違反 → broken と判定 → 削除
- Hunter clause (ii) 全体: 441 BMS、 0 違反 → 健全と確認

### Hunter BMS vs Bashicu BMS の罠

`seed n = [(0,...,0), (1,...,1)]` の closure (Hunter) と、 yaBMS 内部の Bashicu 標準形は **違う集合**。
- seed list に非-Hunter BMS (例: `(0,0,0,0)(1,0,1,1)(2,1,2,1)`) を入れると、 yaBMS BFS で巨大数値 (`17439,...`) や負値が出る
- これらは Hunter clause の仮定外なので「違反」 と誤判定する
- verify script は **必ず Hunter `seed n` から始める**

### 教訓

- 「広く取れば違反多発」 ≠ 「命題が偽」
- 真の検証には domain 制限 (Hunter `seed n` closure 等) が必要

## 8. ファイル分割の必要性 (未実施)

BMS_Ancestry.thy は ~5500 行で monolithic。 1 行変えると全 elaboration が ~18 秒 (slow tactic 修正後)。 試行錯誤コストを下げるには:

- 安定部分 (Round 1 helpers 等) を別 .thy file に分離
- session 化 (`isabelle build -b BMS_Stable`) で heap キャッシュ再利用
- 開発中の lemma は最小 file で書き、 安定したら merge

## 9. 補題分割で proof を BMS-free 部分と BMS 部分に分ける

### 目的

主定理を 1 つの長い proof で書くと、 BMS 固有の仮定 (`A ∈ BMS`、 `b0_start A = Some s` 等) と純粋な list/nat 計算 (`m_parent` の定義から導く下界等) が混ざる。 これを分離すると:

- BMS-free 部分は standard library lemma だけで済む (= simp/auto が動きやすい)
- BMS 部分は構造的な仮定だけ扱う (= 流れが見える)
- 各々 < 100 行 で書け、 build 失敗時の修正範囲が小さい

### 具体例: (H) `bms_all_b0_ascend_row0_when_t_pos` の分割

(H) 全部を 1 proof で書くと:
- m_parent の filter 計算 (=「sorted filter の last は s 以上」)
- BMS 構造から (\*) を呼び出し
- less_induct
- ascends の reflexivity case

が混ざって ~120 行。

これを **m_parent 計算部分だけ** 切り出した:
```isabelle
lemma m_parent_row0_b0_when_row0_lt:
  fixes A :: array and s j :: nat  -- A は array、 BMS と仮定しない
  assumes j_pos: "0 < j"
      and row0_lt: "elem A s 0 < elem A (s + j) 0"
  shows "∃p. m_parent A 0 (s + j) = Some p ∧ s ≤ p ∧ p < s + j"
```
- 仮定: `0 < j` (純粋 nat) + `elem A s 0 < elem A (s + j) 0` (純粋 array 値の不等式)
- 結論: m_parent の存在と range
- 証明: standard list lemma (sorted_wrt_filter, in_set_conv_nth, last_conv_nth, sorted_iff_nth_mono) のみ
- **BMS の仮定なし** ので、 純粋な calculation として独立に検証できる

主補題 (H) はこの helper を 1 行で呼ぶ:
```isabelle
obtain p where mp_eq: "m_parent A 0 (s + j) = Some p"
           and p_ge: "s ≤ p" and p_lt: "p < s + j"
  using m_parent_row0_b0_when_row0_lt[OF j_pos row0_lt] by blast
```

### 利点

- BMS 関係 lemma が変更されても、 helper は影響を受けない (BMS を仮定しないため)
- helper の proof が壊れた場合、 BMS 仮定無関係の standard list 計算だけ見れば良い
- 主補題側は flow (less_induct, ascends 展開) に集中できる

## 10. 経験的に偽な sorry は補題ごと削除する

### 問題の構造

「補題 X を sorry で置いて、 他の証明から `using X` で参照する」 と、 X が偽でも他の証明が「通った」 ように見える。 sorry の数だけ見ると 1 個でも、 実質的に **その 1 sorry が全体を支配** している。

### 具体例

`bms_not_ascend_propagates_to_chain_ancestor` (line 3778 旧版):
```isabelle
lemma bms_not_ascend_propagates_to_chain_ancestor:
  assumes not_asc_j: "¬ ascends A j (Suc k)"
      and chain_AEn: "m_ancestor (A[n]) k (idx_B 0 j) (idx_B 0 x)"
  shows "¬ ascends A x (Suc k)"
  sorry
```
これを使って `lemma_2_5_ii_clause_step_v2` の case B 部分を「証明」 していた。

ところが yaBMS BFS で `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` をテストすると **j=2, k=0, x ∈ {0, 1} で違反**。 つまりこの sorry は「証明できない命題」 を仮定していて、 case B の証明全体が成立しない。

### 対処

(a) sorry の補題を **削除**する
(b) 使用箇所 (line 4494 等) に `sorry` を inline で書く
(c) その sorry のコメントに「経験的反例: ...」 と書く

### 効果

- 削除前: sorry 1 個に「at 第○行に有効な broken lemma」 が隠れる
- 削除後: 使用箇所の sorry が見えて、 reader に「ここで Hunter case B のロジックが破綻」 と分かる
- sorry の総数は同じだが、 質的に異なる (誤誘導しない)

## 11. 補題の signature 設計時、 transitively 要る仮定を見落とすな

### 失敗例

`m_anc_zero_idx_B_in_block_shift_when_t_pos_all_asc` (case-A 本体補題) を最初に書いたとき、 必要な assumption を:
```
A_BMS, A_ne, b0, mp, t_pos, all_asc, a_le: a ≤ n, b_le: b ≤ n, i_lt, j_lt, i_lt_j
```
で済むと判断した。 ところが proof 中で `elem_AEn_lt_block_invariant_when_both_ascend` を呼ぶと、 その helper の side condition `0 < keep_of (G_block A @ Bs_concat A n)` が必要で、 これを示すには `keep_of_pre_strip_pos_of_t_pos_and_n_pos` を呼ぶしかなく、 その lemma は **`n_pos: 0 < n`** を要求する。

### 結果

proof を書き始めてから「n_pos が要る」 と気付き、 helper の signature 自体を書き換える羽目になった。 wrapper 側 (`at_zero_when_t_pos`) も `n_pos` を渡すよう修正、 連鎖的な変更。

### 教訓

新 helper の signature を決める時:
1. 主使用する内部 lemma の signature を全部書き出す
2. 各 lemma の side condition (= keep_of、 length 関係、 n_pos 等) を辿る
3. **transitively** 要る assumption を最初から helper の signature に入れる

特に `keep_of_pre_strip_*` 系は `n_pos` を要求する。 これに気付かないと後で大改修。

## 12. tactic 探索の指針 (経験則)

頑健度 順 (簡単な goal から複雑へ):
1. `by simp` (= 一発書き換え)
2. `by (rule lemma)` (= 結論側適用)
3. `using ... by simp/blast` (= 仮定明示)
4. `unfolding foo_def by ...` (= 部分展開)
5. `proof - ... show ?thesis by ... qed` (= 中間 step 明示)
6. `by (metis lemma1 lemma2)` (= 2 lemma までなら速い)
7. `by force/fastforce` (= auto より強力、 ただし慎重に)

`metis [a b c d e]` のように 5 個以上は避ける。 失敗時 timeout を待つ価値より、 explicit derive する方が速い。
