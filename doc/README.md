# doc/ — 再利用可能なリファレンス集

このディレクトリは、本プロジェクト(BMS well-orderedness の Isabelle 形式化)で
得られた **再利用可能性の高い知見・技法・設計** を蓄積する場所。
タスク固有の進捗は `task.md` / commit / コードに、論文抽出は `tmp/`(gitignored)に置き、
ここには「後で何度も参照する一般的・構造的な知見」を貯める。

## 収録

- `simultaneous_induction_playbook.md` — 大規模同時帰納証明のコツ(有名証明から蒸留)+
  Hunter Lemma 2.5 (i)-(v) 同時帰納の設計指針。
- `joint_induction_design.md` — Lemma 2.5 同時帰納の具体実装設計(複合不変量・
  展開帰納の case-split・必要補題)。verify-first 設計フェーズの成果。
