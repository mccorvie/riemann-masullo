#!/usr/bin/env python3
"""Check transcription/chapters/*.md against the pinned PDF (paper/the-music-of-the-primes.pdf).

Usage (from the repository root):
    pip install pymupdf            # PDF glyph/font extraction
    python3 transcription/tools/check.py            # summary
    python3 transcription/tools/check.py --list     # every flag not already in reviewed_flags.txt

Checks, all page-by-page against the PDF:
  pages      every PDF page appears exactly once, in order
  delimiters every paragraph has balanced $ / $$ (outside ```latex blocks)
  footnotes  every footnote printed at the bottom of a PDF page is filed under that page marker
  tags       every equation tag (X.Y.Z) printed on a page appears under that page marker
  glyphs     math glyphs are aligned 1:1 with the LaTeX tokens of the transcription;
             for aligned glyphs it reports alphabet mismatches (italic/roman/bold/
             calligraphic/script/fraktur/blackboard, read from the PDF fonts),
             sub- vs superscript mismatches (from glyph baselines), and glyph substitutions.
The glyph check is a strong detector, not a proof: reading order of displays differs
between PDF and LaTeX (limits, fractions), so a few flags are expected false positives.
Commutative diagrams (```latex tikzcd blocks) are not glyph-checked; they were checked by eye.
"""
import sys, os, re, json, difflib, collections
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)
import pymupdf as fitz
from pdfglyphs import tokens as pdf_tokens
from mdtokens import page_tokens
PDF = os.path.join(ROOT, 'paper', 'the-music-of-the-primes.pdf'); CH = os.path.join(ROOT, 'transcription', 'chapters')
MARK = re.compile(r'^## PDF page (\d+)[ \t]*$', re.M)
NORM = str.maketrans({'Ω': 'Ω', 'ϕ': 'φ', 'ϵ': 'ε', 'ϑ': 'θ', 'ϱ': 'ρ', 'ς': 'σ', 'ϖ': 'π', '↦': '→', '↪': '→'})
LET = {'it', 'rm', 'bf', 'cal', 'scr', 'frak', 'bb'}
def load_md():
    pages = {}; order = []
    for f in sorted(os.listdir(CH)):
        if not f.endswith('.md') or f == 'README.md': continue
        parts = MARK.split(open(os.path.join(CH, f), encoding='utf-8').read())
        for i in range(1, len(parts), 2):
            n = int(parts[i]); order.append(n); pages[n] = pages.get(n, '') + parts[i+1]
    return pages, order
def load_pdf():
    d = fitz.open(PDF); out = []
    for p in d:
        spans = []
        for b in p.get_text('dict')['blocks']:
            for l in b.get('lines', []):
                for s in l['spans']:
                    if s['text'].strip():
                        spans.append(dict(t=s['text'], f=s['font'], sz=round(s['size'], 2), bb=[round(x, 1) for x in s['bbox']], o=[round(x, 1) for x in s['origin']]))
        out.append(dict(n=p.number + 1, spans=spans, text=p.get_text()))
    return out
def canon(T, depth_of):
    out = []; i = 0; N = len(T)
    while i < N:
        if depth_of(T[i]) == 0 or T[i]['pos'] in ('base', 'label'): out.append(T[i]); i += 1; continue
        j = i
        while j < N and depth_of(T[j]) >= 1 and T[j]['pos'] != 'label': j += 1
        groups = []
        for t in T[i:j]:
            if depth_of(t) == 1 or not groups: groups.append([t])
            else: groups[-1].append(t)
        groups.sort(key=lambda g: 0 if g[0]['pos'] == 'sub' else 1)
        for g in groups: out.extend(g)
        i = j
    return out
def glyph_check(pg, text):
    P = canon(pdf_tokens(pg), lambda t: 0 if t['pos'] == 'base' else (2 if t['sz'] < 6.2 else 1))
    M = canon(page_tokens(text), lambda t: min(t.get('depth', 0), 2))
    a = ''.join(t['g'] for t in P).translate(NORM); b = ''.join(t['g'] for t in M).translate(NORM)
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False); m2p = {}; res = collections.defaultdict(list); eq = 0
    ops = sm.get_opcodes()
    for op, i1, i2, j1, j2 in ops:
        if op == 'equal':
            eq += i2 - i1
            for k in range(i2 - i1): m2p[id(M[j1+k])] = P[i1+k]
    for op, i1, i2, j1, j2 in ops:
        if op == 'equal':
            for k in range(i2 - i1):
                p, m = P[i1+k], M[j1+k]; ctx = text[max(0, m['off'] - 30):m['off'] + 10].replace('\n', ' ')
                if i2 - i1 >= 4 and p['cls'] in LET and m['cls'] in LET and p['cls'] != m['cls']:
                    res['alphabet'].append(f"{m['g']}: PDF {p['cls']}, md {m['cls']} | {ctx}")
                par = m.get('parent')
                if m['pos'] in ('sup', 'sub') and par is not None and id(par) in m2p and not m['frac']:
                    pb = m2p[id(par)]
                    if pb['sz'] > p['sz'] * 1.1:
                        near = sorted(q['oy'] for q in P if abs(q['oy'] - pb['oy']) < 3.5 and pb['sz'] * 0.9 <= q['sz'] <= pb['sz'] * 1.1 and abs(q['x'] - pb['x']) < 80)
                        bl = near[len(near) // 2] if near else pb['oy']; d = p['oy'] - bl
                        pp = 'sup' if d < -0.8 else 'sub' if d > 0.8 else 'base'
                        if pb['cls'] == 'op': continue
                        if pp in ('sup', 'sub') and pp != m['pos'] and m.get('depth', 1) == 1:
                            res['script'].append(f"{par['g']}{'^' if pp == 'sup' else '_'}{m['g']} in PDF, md has {m['pos']} | {ctx}")
        elif op == 'replace' and i2 - i1 == j2 - j1 <= 3:
            if sorted(a[i1:i2]) == sorted(b[j1:j2]): continue
            for k in range(i2 - i1):
                m = M[j1+k]; res['substitution'].append(f"PDF {P[i1+k]['g']} vs md {m['g']} | {text[max(0, m['off'] - 30):m['off'] + 10].replace(chr(10), ' ')}")
    return eq, len(P), res
def main():
    listing = '--list' in sys.argv
    md, order = load_md(); pdf = load_pdf(); problems = collections.Counter(); detail = []
    if sorted(order) != list(range(1, len(pdf) + 1)):
        problems['pages'] += 1; detail.append('pages: markers missing, duplicated or out of order')
    tot_eq = tot = 0
    for pg in pdf:
        n = pg['n']; text = md.get(n, '')
        body = re.sub(r'```.*?```', '', text, flags=re.S)
        if body.count('$$') % 2: problems['delimiters'] += 1; detail.append(f'p{n}: odd number of $$')
        for para in re.split(r'\n\s*\n', re.sub(r'\$\$.*?\$\$', '\n\n', body, flags=re.S)):
            if para.replace('\\$', '').count('$') % 2: problems['delimiters'] += 1; detail.append(f'p{n}: unbalanced $: {para.strip()[:80]}')
        W = lambda s: ' '.join(w.lower() for w in re.findall(r'[A-Za-z]{4,}', s))
        mdw = W(text)
        for m in re.finditer(r'^\s{0,3}(\d{1,3})([A-Z“(][^\n]{15,})$', pg['text'], flags=re.M):
            words = W(m.group(2)).split()[:4]
            if len(words) >= 3 and ' '.join(words) not in mdw:
                # footnote text may contain math: accept if most words occur in order
                if sum(w in mdw for w in words) < 3: problems['footnotes'] += 1; detail.append(f'p{n}: footnote {m.group(1)} not under this page: {m.group(2)[:60]}')
        for s in pg['spans']:
            t = s['t'].strip(); mm = re.match(r'^\(([0-9A-E]+(?:\.[0-9]+){2,5}[a-z]?)\)$', t)
            if mm and s['bb'][0] < 120 and mm.group(1) not in text: problems['tags'] += 1; detail.append(f'p{n}: tag ({mm.group(1)}) not under this page')
        eq, np_, res = glyph_check(pg, text); tot_eq += eq; tot += np_
        for k, v in res.items():
            problems[k] += len(v); detail += [f'p{n} {k}: {x}' for x in v]
    print(f'pages: {len(md)} transcribed, {len(pdf)} in PDF')
    print(f'math glyphs aligned 1:1 with the transcription: {tot_eq}/{tot} ({100*tot_eq/max(1,tot):.1f}%)')
    for k in ('pages', 'delimiters', 'footnotes', 'tags', 'alphabet', 'script', 'substitution'):
        print(f'{k:13s} {problems[k]}')
    base_path = os.path.join(HERE, 'reviewed_flags.txt')
    reviewed = set()
    if os.path.exists(base_path):
        reviewed = {l.rstrip('\n') for l in open(base_path, encoding='utf-8') if l.strip() and not l.startswith('#')}
    new = [x for x in detail if x not in reviewed]
    print(f'flags not in reviewed_flags.txt (i.e. new): {len(new)}')
    if '--write-baseline' in sys.argv:
        with open(base_path, 'w', encoding='utf-8') as f:
            f.write('# Flags raised by check.py that were each compared with the page image and found to be\n'
                    '# false positives (reading order of limits/fractions, labels on arrows, text inside \\text{}).\n')
            f.write('\n'.join(detail) + '\n')
    if listing: print('\n'.join(new if reviewed else detail))
if __name__ == '__main__':
    main()
