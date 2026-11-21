"""PDF side: math glyph tokens per page with alphabet class and script position."""
import re
CMEX = {'P':'∑','X':'∑','Q':'∏','Y':'∏','`':'∐','a':'∐','R':'∫','Z':'∫','N':'⊗','O':'⊗','L':'⊕','M':'⊕','S':'⋃','[':'⋃','T':'⋂','\\':'⋂','J':'⊙','K':'⊙'}
SYM = {'⊗':'⊗','⊕':'⊕','⊔':'∐','×':'×','∈':'∈','⊂':'⊂','⊃':'⊃','≤':'≤','≥':'≥','→':'→','←':'←','↦':'↦','∞':'∞','∂':'∂','⋆':'⋆','ℓ':'ℓ','=':'=','<':'<','>':'>','+':'+','−':'−','∩':'∩','∪':'∪','⊆':'⊆','≃':'≃','∼':'∼','≅':'≅','⇒':'⇒','↪':'↪','∀':'∀','∃':'∃','∅':'∅','⊥':'⊥','∇':'∇','♯':'♯','♭':'♭'}
def fclass(f):
    if f.startswith('CMMI'): return 'it'
    if f.startswith('CMBX'): return 'bf'
    if f.startswith('CMR'): return 'rm'
    if f.startswith('EUSM'): return 'cal'
    if f.startswith('rsfs'): return 'scr'
    if f.startswith('EUFM'): return 'frak'
    if f.startswith('MSBM'): return 'bb'
    if f.startswith('CMSY'): return 'sy'
    if f.startswith('CMEX'): return 'ex'
    return None
def tokens(page):
    out = []
    for si, s in enumerate(page['spans']):
        c = fclass(s['f'])
        if c is None: continue
        x0, y0, x1, y1 = s['bb']; t = s['t']; n = max(1, len(t))
        w = (x1 - x0) / n
        for k, ch in enumerate(t):
            if ch == ' ': continue
            if c == 'ex':
                if ch not in CMEX: continue
                g, cls = CMEX[ch], 'op'
            elif c == 'sy':
                if ch.isascii() and ch.isalpha() and ch.isupper(): g, cls = ch, 'cal'
                elif ch in SYM: g, cls = SYM[ch], 'sym'
                else: continue
            else:
                if ch == '∆': ch = 'Δ'
                if ch.isalnum() or ch in 'µ∂ℓ⋆':
                    g, cls = ch, c
                    if ch == 'µ': g = 'μ'
                    if ch in '∂ℓ⋆': cls = 'sym'
                    if ch == '∆': g = 'Δ'
                elif ch in SYM: g, cls = SYM[ch], 'sym'
                else: continue
            out.append(dict(g=g, cls=cls, sz=s['sz'], x=x0 + k*w, w=w, y0=y0, y1=y1, oy=s['o'][1], span=si))
    # script position relative to nearest preceding larger token on the same visual neighbourhood
    for i, t in enumerate(out):
        t['pos'] = 'base'
        for j in range(i-1, max(-1, i-12), -1):
            b = out[j]
            if b['sz'] > t['sz'] * 1.15 and abs(b['x'] - t['x']) < 60:
                tc = (t['y0'] + t['y1']) / 2; bc = (b['y0'] + b['y1']) / 2
                if b['cls'] == 'op':   # limits / scripts of big operators
                    t['pos'] = 'sup' if tc < bc - 2 else 'sub' if tc > bc + 2 else 'base'
                else:
                    d = t['oy'] - b['oy']
                    t['pos'] = 'sup' if d < -1.0 else 'sub' if d > 1.0 else 'base'
                break
            if b['sz'] <= t['sz'] * 1.15 and b['sz'] >= t['sz'] / 1.15 and abs(b['oy'] - t['oy']) < 0.6:
                t['pos'] = b.get('pos', 'base'); break
    return out
