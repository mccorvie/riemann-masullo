# Writing for the proof companion

A reader should be able to reconstruct a repair from the note, Masullo's paper, and the sources it cites. We write for a mathematician who knows the relevant background and is new to this part of the paper. Reading the proof should require no knowledge of Lean.

## The claim and its place in the paper

Start the heading with the paper's item type and number, including the part when the note covers one. Follow it with a short title, as in `Theorem 5.2.1.1(3). Embedding a finite theta stage`. The same heading appears in the table of contents.

Give the printed page and state the claim in terms a reader of the paper will recognize. Explain which step needs repair before introducing the construction that replaces it. Discuss downstream uses where the reader has enough information to understand them. For a false claim, give a counterexample or point to one. For a missing justification, name the inference that needs to be proved. Check the cited passage against the PDF and link the erratum or issue.

Give the repaired statement before the proof, with its hypotheses, quantifiers, and conclusion. Use the paper's notation where it agrees with the formalization. Explain any difference that affects the statement, such as a stricter cutoff, a weaker conclusion, or a different topology. When the statement changes, point to the first relevant downstream use and say whether the repaired form suffices there.

## The proof

- Explain each construction by saying what it has to achieve. Introduce notation where it is first needed and keep it consistent. Give a one-line definition or a precise reference for objects specific to the paper. Use a displayed formula when it exposes a calculation or a dependence that would be harder to follow in prose.
- Work through the inferences that are specific to the repair. If a map is defined on representatives, explain why it descends. If continuity matters, give the topology and the argument for continuity. If an estimate must be uniform, say what the constant may depend on and show where uniformity comes from.
- Compress routine calculations when a reader can reproduce them. For a substantial result used as an input, cite the specific statement and explain which of its hypotheses apply. Keep any unproved input visible where the proof uses it.
- Use examples when they explain a choice in the proof or test the scope of the statement. Say what the example illustrates. Give the argument for the full claim at the point where it is needed.

## Correspondence with Lean

Link the main Lean declaration at a fixed repository revision. Add links for intermediate declarations when they help a reader check a substantive inference. Present the same mathematical argument at the level of detail appropriate for prose. If the note uses a different argument for one step, identify it so the reader can tell which argument the linked code checks.

Check the declaration's statement and run `#print axioms` at the cited revision before describing the result as fully proved in Lean. If the declaration depends on a `sorry`, identify the open mathematical input by name. If the result establishes an equivalence with a conjecture, state the equivalence and say which original question remains open. Attribute borrowed arguments where they enter the proof.

## Review

Ask someone who did not write the note to read the rendered version with the paper and cited mathematical sources before looking at the Lean code. Can they state exactly what is proved, explain why the replacement works, and reproduce a decisive inference from what is written? If they have to ask the author how a step works, revise that step in the text.

Then compare the statement and the decisive steps with the linked Lean declarations, including hypotheses and any open dependencies. Record in the pull request which inference the reader checked. A reader can do both passes if they know enough of the mathematics and Lean.
