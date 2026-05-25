# 経験的検証(probe)の落とし穴と対策

本プロジェクトで **plausible だが偽の命題を「検証済」と誤認** して大きな手戻りを繰り返した
(consec / linchpin / gmin / UNIFIED / T2 / elem_lt(m=t) / 位置補題 ×3)。
それらの根本原因と対策のチェックリスト。**probe で universal な主張を「真」と確信する前に必ず通す**。

## 大原則

> **「violation 0」は「探索範囲で反例なし」であって「真」ではない**(§10 false-confidence)。
> probe は **反証(screening)** には強いが、**universal 命題の確証** には弱い。
> confident な構造的主張は **probe でなく Isabelle `value`/`eval` か証明** で確定する。

## 罠 → 対策(実害つき)

1. **未 strip で計算** → b0_start/mpl/l1 が別配列の値になり偽陰性。
   - 実害: `consec`/`linchpin` を「数千件 0 viol」と誤検証 → 偽命題上に (ii) を構築、1367 行 revert。
   - 対策: **必ず `strip` してから** b0_start/max_parent_level/l1 を計算(row-0 不変量でも s/l1 は変わる)。

2. **bucket が非 MECE / 「その他」 を黙って捨てる** → 反例がカウント前に消える。
   - 実害: 位置 probe を R1/R2 の 2 bucket にし mid-block(R3)を `else: continue` で破棄 →「l1≥2⟹block-start」 誤認。
   - 対策: bucket は **MECE**、想定外ケースは **捨てず必ず数えて表示**。「その他=0」 を主張に使うなら、そのケースを明示的に出力して 0 を確認。

3. **BFS が浅い / seed が hand-picked** → coverage gap、深い反例を見落とす。
   - 実害: 位置 `probe_location_3way`(depth7)が depth~10 の反例(`(0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,1)`)を見落とし「R2/R3=0」誤認。
   - 対策: **BFS を深く(depth 10+)**、反例が出そうな構造(staircase 等)の seed も入れる。 重要主張は深さを変えて再走し安定を確認。

4. **guard が設計の実条件とずれる** → 設計非該当の反例で命題を偽と誤判定 / 逆も。
   - 実害: loc 補題を `mpl(A[n])≥1` だけで guard → l1(A[n])=1(DOM vacuous=設計非該当)の反例で振り回された。 正しくは `l1(A[n])≥2 ∧ mpl(A[n])≥1`。
   - 対策: guard は **設計が実際に使う条件に正確に**(predecessor の l1 か expansion の l1 か、 等を取り違えない)。

5. **非 genuine BMS を混入** → 偽の反例 / 偽の確証。
   - 実害: `(0,0,0)(1,2,0)(1,1,1)` 等の多列「seed」 は非 BMS。 yaBMS で truncation の展開が当該列を生成しないものは BMS でない。
   - 対策: BFS の **根は真の seed(`(0,..)(1,..)` 2 列形)のみ**。 反例候補は genuine BMS provenance(seed からの展開鎖)を確認。

6. **yaBMS = Bashicu 標準形、 Hunter と別再帰の可能性** → 別集合を測る。
   - 注: 反例 `(0,0)(1,1)(2,2)(3,1)(4,0)(5,1)(6,2)(7,1)` では yaBMS の A[1] と faithful 展開が一致したので、 expansion 演算は一致の見込み。 ただし memory `reference_bms_database_and_yabms` は Bashicu-vs-Hunter 差を警告。
   - 対策: **definitive な主張は Isabelle `eval`/`value` で**。 `expansion` の `strip_zero_rows` は `LEAST` で code-gen 不可だが **pre-strip(`G_block A @ Bs_concat A n`)は eval 可能**、 b0_start/max_parent_level/m_parent も Max/filter 形で eval 可能。 yaBMS と eval を突き合わせる。

7. **狙い撃ち反証 > 網羅 BFS**。
   - 対策: chain 解析等で **反例候補を構造的に推論して狙い撃ち** probe する方が、 網羅 BFS より強く偽を暴ける(UNIFIED の反例はこれで発見)。

8. **proven 補題が sorry'd 補題に依存していないか監査**。
   - 実害: 偽の sorry(T2 / consec_guarded)を proven 補題が引用 = silent unsoundness。
   - 対策: sorried 補題を sorry-free 補題が引用していたら、 その sorried 補題が **真か**(strip+eval)を確認。 偽なら restate/削除 + consumer rework。

## pre-flight チェックリスト(probe 結果を信じる前に)

- [ ] strip してから b0/mpl/l1 を計算したか
- [ ] bucket は MECE で「その他」 を数えているか(捨てていないか)
- [ ] BFS は十分深いか、 深さを変えて安定か
- [ ] guard は証明/設計が使う実条件と一致するか
- [ ] 根は genuine seed のみか、 反例は BMS provenance ありか
- [ ] universal 主張なら Isabelle eval / 証明で裏取りしたか(probe 単独で確信しない)
