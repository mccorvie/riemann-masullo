# Role: progress tracker

Keep the public progress map linked from the README current. Run this role in a Claude
session with access to the repository, the built Mathlib packages, GitHub issues through
`gh`, and the Artifact tool for the existing map. Read [`AGENTS.md`](../AGENTS.md).

## Build the map

Use a dedicated worktree of `origin/main`. Run this setup once from the main checkout.

```sh
tracker=../riemann-masullo-wt/progress-tracker
git fetch -q origin main &&
  git worktree add --detach "$tracker" origin/main &&
  mkdir -p "$tracker/.lake" &&
  ln -s "$PWD/.lake/packages" "$tracker/.lake/packages"
```

Refresh on startup and then every 20 minutes, on a timer, while running. Do not refresh on
every merge: main moves every few minutes. Issue claims and closures can change even when the
commit stays the same. Start each refresh in the main checkout.

```sh
tracker=../riemann-masullo-wt/progress-tracker
git -C "$tracker" fetch -q origin main &&
  git -C "$tracker" checkout -q --detach origin/main &&
  python3 "$tracker/scripts/progress/build.py" --out "$PWD/.agent/progress/index.html"
```

The generator builds the library in the tracker worktree, reads the live issues, and checks
the totals. The output path keeps the page beside its existing `history.jsonl`.

## Sync the issues after every refresh

After each refresh, so about every 20 minutes, run the issue sync from the main checkout:

```sh
scripts/sync_issues.sh
```

It opens a proof issue for each `sorry` that has none, closes the issues whose `sorry` is gone,
and unblocks section issues whose prerequisites are stated. It works in a worktree of its own
(`../riemann-masullo-wt/sync`), so it does not disturb your tracker worktree or anyone's
checkout, and it takes a few minutes because it builds the library first.

Many changes at once are normal: a section's statements arrive sixty at a time. The script
checks each change against the text of the files before it makes any, and that check, not the
number of changes, is what stops it.

- Only one sync runs at a time. If it prints that another sync is running, skip this run; do
  not wait for it or start a second one.
- It stops without changing anything if the checkout moves under it. Run it again after the
  next refresh.
- If it says that changes **disagree with the text of the files**, or that it would close more
  than half of the open issues, **do not pass `--force`**. Send the integrator the lines it
  printed; the integrator decides.
- If it says that main does not build, report that to the integrator and the merger at once.

The integrator and the merger also sync after merging statements. If a discrepancy between the
map and the issues persists across two refreshes after a sync, report it to the integrator with
the commit and issue numbers.

## Publish the map

On a successful refresh, publish the generated `.agent/progress/index.html` from the main
checkout verbatim. Update the existing artifact by passing the progress map link as the
Artifact tool's `url`. On first use in a session, read the artifact with the tool before
updating it. Confirm that the published map shows the commit and theorem counts printed
by the generator. [Progress map](https://claude.ai/artifact/CtQyX8qfYAF822bgHJHHE3)

If generation fails, keep the last publication in place and use the generator's error to
diagnose the next run. If the session cannot update the existing artifact, tell the owner
which commit was generated and where its HTML is. Refer changes to the generator or its
template under `scripts/progress/` to the integrator.
