# Proof companion

The companion collects proofs and repairs from the Lean formalization of
Masullo's *The Music of the Primes*. Each note explains one result and links
the Lean declarations that check the argument.

## Build the PDF

From this directory, run the following with `latexmk` and pdfLaTeX installed.

```sh
latexmk -pdf -halt-on-error -outdir=build main.tex
```

The PDF is `build/main.pdf`.

## Add or revise a note

Keep each note in its own file under `notes/`. Name the file after the paper
item and give it a short descriptive suffix, as in
`notes/5-2-1-1-3-theta-embedding.tex`. Start the `\section` heading with the
paper's item type and number, followed by a short title. Keep the note's
text, equations, and citations together, and prefix LaTeX labels with the
filename stem so they are unique across the document.

Add an `\input{notes/<filename-stem>}` line to `notes.tex` in paper order.
`main.tex` holds the shared preamble and reads `introduction.tex` and
the note list. For an existing note, edit its file directly. Keep shared
formatting changes in their own pull requests so each mathematical note
can be reviewed on its own.

Build and read the PDF before submitting, and use the [writing guide](WRITING.md)
to check the argument and its links to Lean.
