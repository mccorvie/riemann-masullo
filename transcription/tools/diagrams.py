#!/usr/bin/env python3
"""Compile every ```latex diagram block of the transcription with pdflatex + tikz-cd.

Usage (from the repository root; needs a TeX installation with tikz-cd):

    python3 transcription/tools/diagrams.py            # report blocks that do not compile
    python3 transcription/tools/diagrams.py --keep DIR # also keep the PDFs in DIR

Exit status 1 if any block fails. A block that compiles is not thereby correct:
compare the rendered diagram with the page image (scripts/paper.sh --png N).
"""
import pathlib, re, shutil, subprocess, sys, tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1] / 'chapters'
MARK = re.compile(r'^## PDF page (\d+)[ \t]*$', re.M)
BLOCK = re.compile(r'```latex\n(.*?)```', re.S)
PRE = ('\\documentclass{article}\n\\usepackage{amsmath,amssymb,mathrsfs,tikz-cd}\n\\usetikzlibrary{decorations.markings}\n'
       '\\pagestyle{empty}\n\\begin{document}\n$$\n')
POST = '\n$$\n\\end{document}\n'


def blocks():
    for f in sorted(ROOT.glob('*.md')):
        if f.name == 'README.md':
            continue
        parts = MARK.split(f.read_text(encoding='utf-8'))
        for i in range(1, len(parts), 2):
            for k, m in enumerate(BLOCK.finditer(parts[i + 1])):
                yield int(parts[i]), k, m.group(1)


def main():
    if not shutil.which('pdflatex'):
        sys.exit('pdflatex not found')
    keep = pathlib.Path(sys.argv[sys.argv.index('--keep') + 1]) if '--keep' in sys.argv else None
    if keep:
        keep.mkdir(parents=True, exist_ok=True)
    failed, total = [], 0
    with tempfile.TemporaryDirectory() as tmp:
        for page, k, body in blocks():
            total += 1
            name = f'p{page:03d}_{k}'
            tex = pathlib.Path(tmp, name + '.tex')
            tex.write_text(PRE + body.strip() + POST, encoding='utf-8')
            r = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', tex.name],
                               cwd=tmp, capture_output=True, text=True)
            if r.returncode:
                err = next((l for l in r.stdout.splitlines() if l.startswith('!')), '?')
                failed.append(f'p. {page}, block {k + 1}: {err}')
            elif keep:
                shutil.copy(pathlib.Path(tmp, name + '.pdf'), keep)
    print(f'diagram blocks: {total}, not compiling: {len(failed)}')
    for line in failed:
        print('  ' + line)
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
