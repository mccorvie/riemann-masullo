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

Refresh on startup, after you see a merge pass finish, and at least every half hour while
running. Issue claims and closures can change even when the commit stays the same.
Start each refresh in the main checkout.

```sh
tracker=../riemann-masullo-wt/progress-tracker
git -C "$tracker" fetch -q origin main &&
  git -C "$tracker" checkout -q --detach origin/main &&
  python3 "$tracker/scripts/progress/build.py" --out "$PWD/.agent/progress/index.html"
```

The generator builds the library in the tracker worktree, reads the live issues, and checks
the totals. The output path keeps the page beside its existing `history.jsonl`. The merger
and integrator sync issues after their merges. If a discrepancy persists across refreshes,
report it to the integrator with the commit and issue numbers.

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
