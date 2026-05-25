# 大規模同時帰納証明の playbook

有名な同時/相互帰納証明から蒸留した技法と、Hunter Lemma 2.5 (i)-(v) 同時帰納への適用指針。
本プロジェクトの CORE-A(elem_lt domination)/ CORE-B(gateway)を一括で閉じる
multi-session reconstruction に着手する際の指針。

## 共通の病理

ほぼ全ての失敗は **「帰納仮説 (IH) が弱すぎる」** に集約される。素朴な命題 P を induction しても、
step で P(より小)を仮定しても構成子(application / 次レベル / 展開)が P を保たず P(現在)が出ない。
本プロジェクトで見た **level-k 循環**(domination@k ⟺ ascends@k が同レベルで相互依存)はこの典型。
解決の本質は **「構成子で閉じる、より強い不変量」を見つけて束ねる** こと。

## 有名例 → 各々が教える技法

| 証明 | 鍵 | 技法 |
|---|---|---|
| **Tait (1967) / Girard (1972)** 強正規化 (SN) の reducibility | SN 直接帰納は application で詰む → 型に関する帰納で *閉じる* logical relation(reducibility / candidats de réductibilité)を証明 | **IH-strengthening(最重要)**: 弱い目標でなく閉じる強い不変量を証明 |
| **Tait–Martin-Löf** Church-Rosser(合流性) | 1-step reduction は diamond を持たない → **parallel reduction** を導入すると diamond 直接成立 | **補助概念の導入**: step が綺麗に回る中間概念を作る |
| **Gentzen** cut elimination / 無矛盾性 | cut-rank × proof-height の辞書式 + ε₀ 超限帰納 | **正しい整礎測度の設計** |
| **相互再帰型の type safety**(式/文) | 相互依存命題を 1 連言で一括証明(mutual induction) | **single combined goal** |
| **Boyer–Moore / ACL2** "induction loading" | 式を一般化して初めて帰納が閉じる(強い定理の方が易しい) | **一般化 + accumulator**(Isabelle の `arbitrary:`) |
| **Buchholz / Bashicu・Hunter 系** 順序数表記の整礎性 | clause 群を level に関する同時帰納、各 clause が他 clause の lower-level を使う | 本プロジェクトの系統そのもの |

## 蒸留チェックリスト

1. **強い不変量を束ねる**: 証明対象を連言 `P(k) ≡ (i)@k ∧ … ∧ (v)@k ∧ domination@k` にし、
   **1 回の帰納**で回す(各 step は `∀k'<k. P(k')` を使える)。
2. **正しい測度**: 何で induction するか。level 単独で循環するなら **展開構造を測度に組み込む**
   (predecessor の不変量を IH に。bump 等で持ち上げ、同レベル循環を展開方向に開く)。
   level × 展開の入れ子/辞書式。
3. **補助概念**(ascends / 集合 I / bump 公式 / gateway)で step を綺麗に。
4. **一般化を先に**: index(列/block/offset)を `arbitrary:` で外出し、IH を universal に。
5. **各 step を独立 lemma 化**(joint IH を仮定)、最後に induction wrapper で組む。

## 検証ファースト(premature skeleton 回避)

`.thy` に skeleton を入れる前に:
- (a) 複合述語の **statement だけ**書き、各 clause step が要求する joint-IH の形を洗う。
- (b)「展開 × level」測度で各 step が predecessor-IH + 補助公式で閉じるかを
  **紙 + eval-faithful probe で先に確認**(`verify/probe_*.py`、必ず strip してから
  b0_start/mpl/l1 を計算)。Isabelle `value`/`eval` で小例照合。
- 経験則の「0 violations」は coverage-gap で偽陽性になり得る(§10 false-confidence)。
  反例候補を構造的に推論して狙い撃ちする方が網羅 BFS より強い。
- 段階実装し、各段階で build green を保ち **net-new sorry を増やさない**
  (閉じられない部分は単一の明示 sorry に留め、skeleton 化しない)。

## 本プロジェクトでの教訓(実害から)

- **偽命題の上に証明を組まない**: `consec`/`linchpin`/`gmin`/`UNIFIED`/`T2` は
  un-stripped probe の「0 viol」で真と誤認され、偽と判明して大量 revert / 削除になった。
  依拠する補題は strip-correct + Isabelle `eval` で真偽確認してから使う。
- **論文の文面 vs 構成**: 公理/補題は「論文の bundling した文面」でなく
  「Hunter の構成が実際に与える内容」に合わせる方が正しい(例: lemma_2_6 の
  `f δ₀ < α` を `∀γ∈X` 束縛から取り出す分割は構成に忠実で、X=∅ でも有効)。
- **probe の bucket 網羅性を疑え**: 分類 probe で「想定外ケース」を黙って捨てる
  (`else: continue`)と、その反例がカウント前に消えて false-confidence になる。
  実例: 位置 probe を R1/R2 の 2 bucket にし mid-block(R3)を破棄 →「l1≥2⟹100% block-start」
  と誤認(無条件では偽; 正しくは `mpl(A[n])≥1` guard 付きで真)。bucket は MECE に、
  「その他」は捨てず必ず数えて表示する。
- **guard の特定**: 経験則が「ほぼ真・一部反例」のとき、反例の共通条件(ここでは
  `mpl(A[n])=0` = domination vacuous)を見つけて guard 化すれば、設計が使う領域で真の
  補題になることが多い。反例を捨てず分析する。

詳細な対応する Isabelle 補題・進捗は `important-lemma.md` の進捗ツリー、
`doc/joint_induction_design.md` の実装設計を参照。
