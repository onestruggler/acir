"""Figures of the paper as words, and the derivations of its appendices as chains."""
import re, os, sys, json
import figparse

HERE = os.path.dirname(os.path.abspath(__file__))
# The paper's arXiv source (main.tex, the appendices, figures/*.pdf).
SRC = os.environ.get('BLAKE_SRC', os.path.join(HERE, 'src'))
FIG = os.path.join(SRC, 'figures')
CACHE = os.path.join(HERE, 'figures.json')

_cache = {}
try:
    for k, v in json.load(open(CACHE, encoding='utf-8')).items():
        _cache[k] = (v[0], [(e[0], e[1], tuple(e[2]) if e[1] == 'box' else
                             ((tuple(e[2]) if e[1] == 'scalar' else
                               ({int(a): b for a, b in e[2].items()} if e[1] == 'perm' else tuple(e[2])))))
                            for e in v[1]])
except FileNotFoundError:
    pass

def _fix(ev):
    x, kind, data = ev
    if kind == 'box': return (x, kind, (data[0], tuple(data[1]), data[2]))
    if kind == 'ctrl': return (x, kind, (list(data[0]), list(data[1])))
    return ev

def events(name):
    if name not in _cache:
        n, ev = figparse.parse(os.path.join(FIG, name + '.pdf'))
        _cache[name] = (n, ev)
        save()
    n, ev = _cache[name]
    return n, [_fix(e) for e in ev]

def save():
    json.dump(_cache, open(CACHE, 'w', encoding='utf-8', newline='\n'), ensure_ascii=False, indent=0,
              sort_keys=True)

TEXCACHE = os.path.join(HERE, 'derivations.json')
def derivations(texfile):
    """label -> list of tokens: ('fig', name) and ('eq', [labels]) / ('eq', []) for '='."""
    try:
        d = json.load(open(TEXCACHE, encoding='utf-8'))
    except FileNotFoundError:
        d = {}
    if texfile in d:
        return {k: [tuple(t) for t in v] for k, v in d[texfile].items()}
    s = open(os.path.join(SRC, texfile), encoding='utf-8').read()
    out = {}
    for m in re.finditer(r'\\begin\{derivation\}\\label\{([^}]*)\}(.*?)\\end\{derivation\}', s, re.S):
        out[m.group(1)] = tokens(m.group(2))
    d[texfile] = out
    json.dump(d, open(TEXCACHE, 'w', encoding='utf-8', newline='\n'), ensure_ascii=False, indent=0,
              sort_keys=True)
    return out

def tokens(body):
    toks = []
    pat = re.compile(r'\\tikzfig\{([^}]*)\}|\\eqeqref\{([^}]*)\}|\\eqdeuxeqref\{([^}]*)\}\{([^}]*)\}'
                     r'|\\eqtroiseqref\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}|(?<![\\a-zA-Z])=')
    for m in pat.finditer(body):
        if m.group(1): toks.append(('fig', m.group(1)))
        elif m.group(2): toks.append(('eq', [m.group(2)]))
        elif m.group(3): toks.append(('eq', [m.group(3), m.group(4)]))
        elif m.group(5): toks.append(('eq', [m.group(5), m.group(6), m.group(7)]))
        else: toks.append(('eq', []))
    return toks

def chain(toks):
    """[(fig0), (labels, fig1), ...] from tokens."""
    figs = [t[1] for t in toks if t[0] == 'fig']
    steps = []
    labs = None
    first = None
    for t in toks:
        if t[0] == 'fig':
            if first is None: first = t[1]
            else: steps.append((labs or [], t[1])); labs = None
        else:
            labs = t[1]
    return first, steps

def swaps_of_perm(perm, n):
    """Adjacent transpositions (time order) realising perm: wire i on the left ends on perm[i]."""
    pos = list(range(n))            # pos[w] = current position of the line that started at w
    full = {i: perm.get(i, i) for i in range(n)}
    out = []
    # bubble: repeatedly swap adjacent positions whose lines are out of order w.r.t. targets
    line_at = list(range(n))        # line_at[p] = original wire of the line at position p
    changed = True
    while changed:
        changed = False
        for p in range(n - 1):
            a, b = line_at[p], line_at[p + 1]
            if full[a] > full[b]:
                line_at[p], line_at[p + 1] = b, a; out.append(p); changed = True
    assert all(full[line_at[p]] == p for p in range(n))
    return out
