# Preoscript command benchmark corpus

This corpus keeps semantic goldens separate from performance measurement.
`scripts/preo-bench.sh golden` hard-fails changes to generated declaration
names and canonical types, `preoExt` row order, the rendered report, exact
surface diagnostics, or whole-command rollback. The diagnostics and rollback
file uses `#guard_msgs` and then successfully reuses each failed declaration
name in the same environment.

`scripts/preo-bench.sh profile` performs two warmups followed by five serialized
`lean -j1 --profile` runs under `/usr/bin/time -lp`. It never clears caches and
does not enable `trace.profiler`. Persistent wall/user MAD above 8% is reported
as infrastructure noise after a nine-run retry. Import-only controls separate
module cost from fields/custom fields at 1/8/32, typed derives at 0/1/4/16, and
future/certificate, protocol/session, native protocol, budget, export, report,
all-command, and rollback-negative fixtures. Same-name reuse remains in the
separate unconditional golden rather than contaminating rejection timing.

The committed baseline is commit `ab4c767`. Recreate it without altering the
checkout with:

```text
scripts/preo-bench.sh baseline ab4c767
```

The runner creates a detached temporary worktree, copies only this benchmark
corpus into it, warms normal Lake caches, profiles serially, and removes the
worktree. `compare` applies the documented relative-plus-absolute thresholds;
exact goldens remain unconditional hard gates.

Regression thresholds require both their relative and absolute arms: wall
warns above 12% and 250 ms and fails above 20% and 500 ms; user time and each
cumulative Lean phase warn above 10% and 50 ms and fail above 20% and 100 ms;
RSS warns above 5% and 64 MiB and fails above 10% and 128 MiB. The rollback
negative path fails above 25% and 100 ms. Typed N=16 per-item user/elaboration
cost may not exceed N=4 by both 25% and 10 ms/item; RSS growth may not exceed
4 MiB/item. Scaling subtracts the typed-N=0 import/command control before
dividing by the item count.
