"""Tidy a generated Agda module: drop the names of `using` lists, and the
private helpers, that the module does not use."""
import re

TOK = re.compile(r"[^\s(){};.@\"]+")


def _parts(name):
    # The name parts of an operator such as _∷_ or -[1+_].
    if '_' in name:
        return [p for p in name.split('_') if p]
    return [name]


def prune_imports(src):
    def fix(m):
        line = m.group(0)
        if ' public' in line:
            return line
        names = [n.strip() for n in m.group(2).split(';') if n.strip()]
        rest = src[:m.start()] + src[m.end():]
        toks = set(TOK.findall(rest))
        toks |= {t.strip('_') for t in toks}  # sections such as (_xor b)
        kept = [n for n in names if n in toks or all(p in toks for p in _parts(n))]
        if not kept:
            return ''
        return m.group(1) + '(' + ' ; '.join(kept) + ')'
    return re.sub(r'^(open import [^\n]*?using )\(([^)]*)\)', fix, src, flags=re.M).replace('\n\n\n', '\n\n')


def prune_helpers(src, names):
    """Drop each one-line helper `x = ...` (and its signature line, which
    may declare several helpers) whose name is otherwise unused."""
    lines = src.split('\n')
    toks = TOK.findall(src)
    unused = {x for x in names if toks.count(x) <= 2}
    out = []
    for l in lines:
        m = re.match(r'^(\s*)(\S+) = ', l)
        if m and m.group(2) in unused:
            continue
        m = re.match(r'^(\s*)((?:\S+ )+): (.*)$', l)
        if m:
            decl = [x for x in m.group(2).split() if x not in unused]
            if not decl:
                continue
            if len(decl) != len(m.group(2).split()):
                l = m.group(1) + ' '.join(decl) + ' : ' + m.group(3)
        out.append(l)
    return '\n'.join(out)


def tidy(src, helpers=()):
    while True:
        new = prune_helpers(src, helpers)
        if new == src:
            break
        src = new
    return prune_imports(src)
