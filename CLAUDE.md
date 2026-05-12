# BMS paper project — local rules

## Isabelle build / kill rule

- `isabelle build` で長時間の proof elaboration がタイムアウトすると、 親プロセスは死んでも子の `polyml` プロセスが孤児化して 100% CPU で残ることがある。
- 28 コアマシンでも、 孤児が 3 つ累積すれば 24 スレッドを占有して GUI が止まる。
- 対策:
  - `timeout` には `--kill-after=10s` を付けて SIGKILL escalation する
  - `kill` / `pkill` を実行した後は **必ず** `ps -ef | grep -iE "poly|isabelle" | grep -v grep` で孤児確認
  - 孤児があれば `pkill -9 -u "$USER" -f polyml; pkill -9 -u "$USER" -f isabelle` で一掃
  - 最も堅実: `setsid timeout --kill-after=10s 900 isabelle build ...` でプロセスグループ化し、 失敗時 `kill -9 -- -$pid` でグループ全体を kill
- `.claude/settings.json` に PostToolUse hook を入れてあり、 `kill` / `pkill` 系コマンドの後に自動で REMINDER が出る。
