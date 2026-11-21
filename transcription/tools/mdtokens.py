"""Markdown side: tokens from math segments with alphabet class, script position, offsets."""
import re
GREEK = {'alpha':'α','beta':'β','gamma':'γ','delta':'δ','epsilon':'ϵ','varepsilon':'ε','zeta':'ζ','eta':'η','theta':'θ','vartheta':'ϑ','iota':'ι','kappa':'κ','lambda':'λ','mu':'μ','nu':'ν','xi':'ξ','pi':'π','varpi':'ϖ','rho':'ρ','varrho':'ϱ','sigma':'σ','varsigma':'ς','tau':'τ','upsilon':'υ','phi':'ϕ','varphi':'φ','chi':'χ','psi':'ψ','omega':'ω'}
GREEKU = {'Gamma':'Γ','Delta':'Δ','Theta':'Θ','Lambda':'Λ','Xi':'Ξ','Pi':'Π','Sigma':'Σ','Upsilon':'Υ','Phi':'Φ','Psi':'Ψ','Omega':'Ω'}
OPS = {'sum':'∑','prod':'∏','coprod':'∐','bigsqcup':'∐','amalg':'∐','sqcup':'∐','int':'∫','iint':'∫','oint':'∫','bigotimes':'⊗','otimes':'⊗','bigoplus':'⊕','oplus':'⊕','bigcup':'⋃','bigcap':'⋂','bigodot':'⊙','odot':'⊙'}
BIGOPS = {'sum','prod','coprod','bigsqcup','int','iint','oint','bigotimes','bigoplus','bigcup','bigcap','bigodot'}
SYMS = {'times':'×','in':'∈','subset':'⊂','supset':'⊃','le':'≤','leq':'≤','ge':'≥','geq':'≥','to':'→','rightarrow':'→','longrightarrow':'→','leftarrow':'←','longleftarrow':'←','mapsto':'↦','infty':'∞','partial':'∂','star':'⋆','ell':'ℓ','cap':'∩','cup':'∪','subseteq':'⊆','simeq':'≃','sim':'∼','cong':'≅','Rightarrow':'⇒','hookrightarrow':'↪','forall':'∀','exists':'∃','emptyset':'∅','varnothing':'∅','perp':'⊥','nabla':'∇','sharp':'♯','flat':'♭'}
FUNCS = {'log','exp','sin','cos','tan','max','min','sup','inf','lim','ker','det','deg','dim','arg','gcd','hom','Hom','Re','Im','liminf','limsup','sinh','cosh','tanh','lcm','Pr','mod','bmod','pmod'}
FUNCTXT = {'liminf':'liminf','limsup':'limsup','Re':'Re','Im':'Im','bmod':'mod','pmod':'mod'}
ALPHA = {'mathcal':'cal','mathscr':'scr','mathfrak':'frak','mathbb':'bb','mathbf':'bf','boldsymbol':'bf','bm':'bf','mathrm':'rm','operatorname':'rm','mathit':'it','mathsf':'rm','mathup':'rm','rm':'rm','bf':'bf','cal':'cal','mathnormal':'it'}
TEXT = {'text','textrm','textit','textbf','mbox','textsf','texttt','emph','textup','hbox','tag','label','hspace','vspace','mathrlap','mathllap','phantom','hphantom','vphantom','operatornamewithlimits','begin','end'}
ACC = {'hat','widehat','bar','overline','tilde','widetilde','check','underline','vec','dot','ddot','breve','acute','grave','mathring','widecheck'}
LABELARG = {'xrightarrow','xleftarrow','xRightarrow','xLeftarrow','xhookrightarrow','xmapsto','overset','underset','stackrel','overbrace','underbrace','xlongrightarrow'}
SKIP0 = {'left','right','big','Big','bigg','Bigg','bigl','bigr','Bigl','Bigr','biggl','biggr','quad','qquad','displaystyle','textstyle','scriptstyle','scriptscriptstyle','limits','nolimits','middle','lvert','rvert','lVert','rVert','vert','Vert','langle','rangle','cdot','cdots','ldots','dots','circ','prime','colon','mid','setminus','backslash','lbrace','rbrace','lfloor','rfloor','lceil','rceil','square','Box','blacksquare','neq','ne','not','notin','pm','mp','div','ast','bullet','wedge','vee','land','lor','neg','lnot','approx','equiv','propto','parallel','downarrow','uparrow','Downarrow','Uparrow','nearrow','searrow','swarrow','nwarrow','Leftarrow','Leftrightarrow','leftrightarrow','iff','implies','twoheadrightarrow','rightrightarrows','leftrightarrows','dashrightarrow','rightsquigarrow','longmapsto','Longrightarrow','emptyset','triangle','top','bot','vdash','dagger','ddagger','aleph','hbar','imath','jmath','wp','Re','Im','angle','cdotp','ldotp','vdots','ddots','smallsetminus','unlhd','lhd','rhd','unrhd','trianglelefteq','triangleleft','boxtimes','oslash','ominus','uplus','sqcap','wr','diamond','natural','clubsuit','lessdot','ll','gg','prec','succ','preceq','succeq','sqsubset','sqsubseteq','models','asymp','doteq','frown','smile','bowtie','Join','iota','nexists','complement','ltimes','rtimes','leqslant','geqslant','lesssim','gtrsim','nmid','varprojlim','varinjlim','projlim','injlim','colim','mathstrut','strut','allowbreak','nobreak','relax','limits','!',',',';',':',' ','{','}','|','#','&','%','$','_','^'}
class Tok(dict): pass
def tokenize(text, base_offset=0):
    """Tokenize a LaTeX math string. Returns list of tokens: g, cls, pos (base/sup/sub), op_off (offset of controlling ^/_ or None), alpha_cmd (offset,name,group span) and acc flags."""
    toks = []; i = 0; n = len(text)
    def group_end(j):
        # j at '{' -> index after matching '}'
        depth = 0
        while j < n:
            c = text[j]
            if c == '\\': j += 2; continue
            if c == '{': depth += 1
            elif c == '}':
                depth -= 1
                if depth == 0: return j + 1
            j += 1
        return n
    def arg_span(j):
        while j < n and text[j] == ' ': j += 1
        if j < n and text[j] == '{': return j, group_end(j)
        if j < n and text[j] == '\\':
            m = re.match(r'\\([A-Za-z]+|.)', text[j:]); return j, j + len(m.group(0))
        return j, min(n, j + 1)
    def walk(a, b, ctx):
        nonlocal toks
        j = a
        while j < b:
            c = text[j]
            if c == '\\':
                m = re.match(r'\\([A-Za-z]+|.)', text[j:b]); name = m.group(1); k = j + len(m.group(0))
                if name in ALPHA:
                    s, e = arg_span(k)
                    walk(s + (1 if text[s:s+1] == '{' else 0), e - (1 if text[s:s+1] == '{' else 0), dict(ctx, cls=ALPHA[name], alpha=(j, name, s, e)))
                    j = e; continue
                if name in TEXT:
                    if name in ('begin', 'end'):
                        s, e = arg_span(k); j = e
                        if name == 'begin' and text[s:e] in ('{array}',):
                            s2, e2 = arg_span(j); j = e2  # column spec
                        continue
                    if name in ('hspace', 'vspace', 'tag', 'label', 'phantom', 'hphantom', 'vphantom'):
                        s, e = arg_span(k); j = e; continue
                    s, e = arg_span(k); j = e; continue   # text content: rendered in text font, not compared
                if name in ACC:
                    s, e = arg_span(k)
                    walk(s + (1 if text[s:s+1] == '{' else 0), e - (1 if text[s:s+1] == '{' else 0), dict(ctx, acc=ctx.get('acc', ()) + (name,)))
                    j = e; continue
                if name in LABELARG:
                    # optional [..] and {..} args are labels: mark as 'label' position
                    while k < b and text[k] in ' ': k += 1
                    if k < b and text[k] == '[':
                        e = text.find(']', k); walk(k + 1, e, dict(ctx, pos='label', op=None)); k = e + 1
                    s, e = arg_span(k); walk(s + 1 if text[s:s+1] == '{' else s, e - 1 if text[s:s+1] == '{' else e, dict(ctx, pos='label', op=None))
                    if name in ('overset', 'underset', 'stackrel'):
                        s2, e2 = arg_span(e); walk(s2 + 1 if text[s2:s2+1] == '{' else s2, e2 - 1 if text[s2:s2+1] == '{' else e2, ctx); e = e2
                    j = e; continue
                if name in ('frac', 'dfrac', 'tfrac', 'cfrac', 'binom', 'tbinom', 'dbinom'):
                    s1, e1 = arg_span(k); walk(s1 + 1, e1 - 1, dict(ctx, frac=True)); s2, e2 = arg_span(e1); walk(s2 + 1, e2 - 1, dict(ctx, frac=True)); j = e2; continue
                if name in ('sqrt',):
                    j = k; continue
                if name in GREEK: toks.append(Tok(g=GREEK[name], cls='it', off=j, end=k, **_c(ctx))); j = k; continue
                if name in GREEKU: toks.append(Tok(g=GREEKU[name], cls='rm' if ctx['cls'] in ('it', 'rm') else ctx['cls'], off=j, end=k, **_c(ctx))); j = k; continue
                if name in OPS:
                    toks.append(Tok(g=OPS[name], cls='op' if name in BIGOPS else 'sym', off=j, end=k, name=name, **_c(ctx))); j = k; continue
                if name in SYMS: toks.append(Tok(g=SYMS[name], cls='sym', off=j, end=k, **_c(ctx))); j = k; continue
                if name in FUNCS:
                    w = FUNCTXT.get(name, name)
                    for q, ch in enumerate(w): toks.append(Tok(g=ch, cls='rm', off=j, end=k, func=True, **_c(ctx)))
                    j = k; continue
                j = k; continue
            if c in '^_':
                k = j + 1
                s, e = arg_span(k)
                cm = re.match(r'\\([A-Za-z]+)$', text[s:e])
                if cm and (cm.group(1) in ALPHA or cm.group(1) in ACC or cm.group(1) in ('text', 'operatorname')):
                    s2, e2 = arg_span(e); e = e2
                    inner = (s, e)
                    pos = 'sup' if c == '^' else 'sub'
                    parent = toks[-1] if toks else None; start = len(toks)
                    walk(inner[0], inner[1], dict(ctx, pos=pos, op=j, depth=ctx.get('depth', 0) + 1))
                    for t in toks[start:]:
                        if t.get('parent') is None: t['parent'] = parent
                    j = e; continue
                inner = (s + 1, e - 1) if text[s:s+1] == '{' else (s, e)
                pos = 'sup' if c == '^' else 'sub'
                parent = toks[-1] if toks else None
                start = len(toks)
                walk(inner[0], inner[1], dict(ctx, pos=pos, op=j, depth=ctx.get('depth', 0) + 1))
                for t in toks[start:]:
                    if t.get('parent') is None: t['parent'] = parent
                j = e; continue
            if c == '{':
                e = group_end(j); walk(j + 1, e - 1, ctx); j = e; continue
            if c.isalnum():
                cls = ctx['cls'] if (c.isalpha() or ctx['cls'] in ('bf', 'bb')) else 'rm'
                if c.isdigit() and ctx['cls'] == 'it': cls = 'rm'
                toks.append(Tok(g=c, cls=cls, off=j, end=j + 1, **_c(ctx))); j += 1; continue
            if c in '=<>+-':
                toks.append(Tok(g={'-': '−'}.get(c, c), cls='sym', off=j, end=j + 1, **_c(ctx))); j += 1; continue
            j += 1
    def _c(ctx):
        return dict(pos=ctx.get('pos', 'base'), op=ctx.get('op'), alpha=ctx.get('alpha'), acc=ctx.get('acc', ()), frac=ctx.get('frac', False), depth=ctx.get('depth', 0))
    walk(0, n, dict(cls='it', pos='base', op=None))
    for t in toks:
        t['off'] += base_offset; t['end'] += base_offset
        if t['op'] is not None: t['op'] += base_offset
        if t['alpha']: a = t['alpha']; t['alpha'] = (a[0] + base_offset, a[1], a[2] + base_offset, a[3] + base_offset)
    return toks
def page_tokens(page_text):
    """Math tokens of a page with absolute offsets. Skips fenced code (tikzcd) for now."""
    toks = []
    masked = re.sub(r'```.*?```', lambda m: ' ' * len(m.group(0)), page_text, flags=re.S)
    for m in re.finditer(r'\$\$(.*?)\$\$|(?<![\\$])\$([^$]+?)\$', masked, flags=re.S):
        g = 1 if m.group(1) is not None else 2
        toks += tokenize(m.group(g), m.start(g))
    return toks
