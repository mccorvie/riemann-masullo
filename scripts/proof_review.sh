#!/usr/bin/env bash
# Print the reasons to read a proof PR. An empty result means ordinary proof text.
# Both queue scripts pass the base and head commits they inspected.
set -euo pipefail
base=$1
sha=$2
diff=$(git diff "$base...$sha")
added=$(grep -E '^\+[^+]' <<<"$diff" || true)
newfiles=$(git diff --diff-filter=A --name-only "$base...$sha")

# Added lines that make a pull request worth reading before it is merged.
# Importing Mathlib or this library, and silencing a linter, are routine and are not flagged.
eyes='^\+[[:space:]]*(#|@\[|open Lean|attribute|macro|syntax|notation|elab|initialize|unsafe|instance|def |abbrev |structure|class |inductive|axiom|opaque|noncomputable)|run_|by_elab|simproc|Lean\.|Elab|Meta\.|IO\.|extern|implemented_by|native'
# Commands that change what later declarations mean or that run code, wherever they stand on the
# line and whatever modifiers precede them: a `variable [Fact False]` makes everything after it
# vacuous, `private def` and `local notation` hide behind their modifier, a second command can
# follow a proof on the same line, and `admit` is `sorry` under another name.
eyes="$eyes"'|^\+[[:space:]]*((private|protected|local|scoped|public|noncomputable|nonrec)[[:space:]]+)+(def|abbrev|instance|structure|class|inductive|notation|macro|syntax|elab|infix|infixl|infixr|prefix|postfix)\b|\b(variable|universe|admit|initialize|macro|macro_rules|syntax|elab|elab_rules|notation|axiom|opaque|unsafe|mutual|export|namespace)\b'
routine='^\+[[:space:]]*((public )?import (Mathlib|RiemannMasullo)\.[A-Za-z0-9_.]+[[:space:]]*$|set_option linter\.[A-Za-z0-9_.]+ (true|false) in[[:space:]]*$)'
# Flag citations and new public declarations for a reader to distinguish a proved lemma
# from a paper definition or an admitted paper theorem.
decl='[[:space:]]*(@\[[^]]*\][[:space:]]*)*((public|protected|noncomputable|nonrec|scoped|local)[[:space:]]+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive)[[:space:]]+'
declared() {  # names declared on those diff lines of stdin that start with the sign $1
  grep -E "^[$1]$decl" | sed -E "s/^[$1]$decl//; s/[[:space:]:({[].*//" | sort -u
}
why=""
grep -qw sorry <<<"$added" && why="adds a sorry"
[ -z "$newfiles" ] || why="${why:+$why, }new file"
rest=$(grep -vE "$routine" <<<"$added" || true)
grep -qE "$eyes|^\+[[:space:]]*(import|set_option) " <<<"$rest" && why="${why:+$why, }not plain proof text"
grep -qE '^\+.*Paper:' <<<"$added" && why="${why:+$why, }cites the paper"
# A name that is also on a removed line is an existing declaration whose first line was
# rewritten to hold the proof, not a new one.
lib=$(git diff "$base...$sha" -- RiemannMasullo ':(exclude)RiemannMasullo/ForMathlib') || exit 1
newdecl=$(comm -23 <(declared + <<<"$lib") <(declared - <<<"$lib") | paste -sd' ')
[ -z "$newdecl" ] || why="${why:+$why, }new public declaration: $newdecl"
printf '%s\n' "$why"
