# Writing AGENTS.md

How to change [`AGENTS.md`](../AGENTS.md) so that agents follow it. Use the same style for the role
prompts in this directory.

## Why it matters

- Every agent reads the whole file on every run, so every line costs tokens on every task.
- Long, discursive context files do not make agents more successful. A 2026 study across several
  agents and models found that repository context files gave no gain in task success and raised
  cost by over 20%. Its authors advise human-written files that state only minimal
  requirements ([Gloaguen et al., arXiv:2602.11988](https://arxiv.org/abs/2602.11988)).
- Effective files lead with goals and commands, show code instead of describing it, and state
  explicit boundaries (GitHub's analysis of over 2,500 `agents.md` files).

## The shape of a rule

```markdown
- **<Goal, as an imperative sentence.>**
  - <What to do, as an imperative: a command, a path, a name to use.>
  - <At most four such bullets.>
  - *Why:* <one or two sentences: the consequence, with one number and an issue link.>
```

- **Start with the goal**: what the rule protects ("Prevent cascading rebuilds"), not the
  mechanism ("A new import in a low file rebuilds everything above it").
- **One action per bullet**, as an imperative: "Keep new helpers `private`", not "helpers should
  generally be kept private where possible".
- **Name the exact thing**: the command, path, flag or lemma name an agent would type.
- **Keep the *Why:* line short.** It lets an agent handle a case the rule did not foresee. Put the
  measurements and the history in the linked issue, not here.
- Omit the *Why:* line when the rule is self-evident ("Keep diffs small").

## What belongs in AGENTS.md

- **Only what an agent would get wrong without it.** For each line, ask: would removing it cause
  a mistake? If not, cut it.
- **Rules every role needs.** Role-specific instructions go in the role prompt.
- **No generic advice** ("write clean code", "be careful"): agents already try.
- **No patterns that are being phased out**, except as a "never" rule: describing them steers
  agents toward them.
- **No history** ("this rule was added after…") beyond an issue link.

## Changing the file

- **Add a rule when a mistake recurs**, with an issue that shows it. Link the issue from the
  *Why:* line.
- **Merge rather than append.** Put a new point into the existing rule with the same goal. For
  example, "No `import all`" and "a new import rebuilds everything above it" are one rule:
  prevent cascading rebuilds.
- **Shorten a rule once a check enforces it.** When CI or `scripts/lint.sh` catches the mistake,
  say so in one line ("`scripts/lint.sh` checks this") and drop the explanation.
- **Remove rules that no longer apply.**
- **Keep the file under about 250 lines.** If it grows past that, look for rules to merge, move
  to a role prompt, or delete.
- **Keep these headings unchanged**; other files refer to them by name:
  - "Rules for Lean code" (the Layout table, `prompts/digester.md`),
  - "False statements and gaps" (`prompts/prover.md`, `prompts/digester.md`),
  - "Building and checking" (`prompts/prover.md`),
  - "Using existing Lean" (`scripts/agent.sh`).
- AGENTS.md is integrator territory: change it through a pull request.
