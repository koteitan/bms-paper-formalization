# BMS paper project — local rules

## Isabelle build / kill rule

**常に `isbman` を使う**（`isbman` skill / `~/bin/isbman`）。 素の `isabelle build` と `pkill -f poly|isabelle` は使わない。

- ビルド: `isabelle build <args>` の代わりに **`isbman build <args>`**（例 `isbman build -d . -v BMS`）。 引数は同じ、 foreground でストリームし、 開始時に **BUILD ID** を表示する:
  ```
  isbman: build 04f31d started in /home/koteitan/bms-paper
  isbman: stop it with  ->  isbman kill 04f31d
  ```
- kill: ハング/タイムアウト時は **`isbman kill <ID>`**（どのディレクトリ・別シェルからでも）。 ID を控え忘れたら `isbman ps` で確認。 他に `isbman kill --all`、 引数なし `isbman kill`（カレントディレクトリ発のビルドを kill）。
- 一覧: **`isbman ps`** — 全ビルドを ID/起動ディレクトリ/経過/引数付きでグローバル表示。
- timeout 既定 1800s、 変更は `ISBMAN_TIMEOUT=<秒> isbman build ...`。

### なぜ isbman か
- **ID ベースの reaping（知識不要）**: ビルドの全プロセス(JVM/bash_process/detach した `poly`/naproche…)は `ISBMAN_ID` を environ に継承する。 `kill`/`ps` はその ID 完全一致で `/proc/<pid>/environ` を走査して対象だけ kill するので、 git/worktree/cwd の知識なしに、 別ディレクトリからでも正確に殺せる。 状態ファイル不要（プロセス環境自体がレジストリ）。 `poly` は別セッションに detach するためグループ kill だけでは届かない → environ 一致が真の同定軸。 他 OS ユーザのプロセスは読めないので巻き込まない。
- **heap 隔離（内部都合・意識不要）**: `USER_HOME` をディレクトリ毎に切替えて `ISABELLE_HEAPS` を専用化、 SQLite ロック競合を回避。 HOL は配布 heaps から read、 ZF 等は初回コピー seed で再ビルドなし。

### 旧ルール(廃止)
- ~~`pkill -9 -u "$USER" -f polyml; pkill ... -f isabelle`~~ … ユーザー全体を巻き込み並列ビルドを誤爆するので **使わない**。 `isbman kill <ID>` / `--all` に統一。
- `isbman build`/`isbman kill` 後は孤児が自動 reap されるので `ps -ef | grep poly` の手動確認は不要（確認は `isbman ps`）。

詳細は `~/.claude/skills/isbman/{SKILL.md,README.md}`。
