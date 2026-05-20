# BMS paper project — local rules

## Isabelle build / kill rule

**常に `isbman` を使う**（`isbman` skill / `~/bin/isbman`）。 素の `isabelle build` と `pkill -f poly|isabelle` は使わない。

- ビルド: `isabelle build <args>` の代わりに **`isbman build <args>`**（例 `isbman build -d . -v BMS`）。 引数は同じ、 foreground でストリームする。
- kill: ハング/タイムアウト時は **`isbman kill`**（worktree 内ならどこからでも）。 その worktree の Isabelle プロセスだけを reap する（detach した `poly` セッション含む）。
- 確認: **`isbman ps`**（この worktree）/ `isbman ps --all`（全 worktree）。
- timeout 既定 1800s、 変更は `ISBMAN_TIMEOUT=<秒> isbman build ...`。

### なぜ isbman か（並列安全性）
- **heap 隔離**: `USER_HOME` を worktree 毎に切替え → `ISABELLE_HEAPS` が cascade して `<session>.db` を専用化、 SQLite ロック競合が起きない。 HOL は配布 `ISABELLE_HEAPS_SYSTEM` から read、 ZF 等は共有 heaps を初回コピー seed するので再ビルド地獄なし。
- **正確な reaping**: ビルドの全プロセス(JVM/`poly`/naproche…)は worktree の `USER_HOME` を environ に継承する。 isbman はその `USER_HOME` 完全一致で `/proc/<pid>/environ` を走査して kill するので、 他 worktree のビルドには絶対に触れない。 `poly` は別セッションに detach するためプロセスグループ kill だけでは不足 → environ 一致が真の同定軸。

### 旧ルール(廃止)
- ~~`pkill -9 -u "$USER" -f polyml; pkill -9 -u "$USER" -f isabelle`~~ … ユーザー全体を巻き込み並列ビルドを誤爆するので **使わない**。 `isbman kill` に統一。
- `isbman build`/`isbman kill` 後は孤児が自動 reap されるので `ps -ef | grep poly` の手動確認は不要（確認したいときは `isbman ps`）。

詳細は `~/.claude/skills/isbman/{SKILL.md,README.md}`。
