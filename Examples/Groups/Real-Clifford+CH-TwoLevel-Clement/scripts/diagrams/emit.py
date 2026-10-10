"""Emit Agda derivation modules (generic Engine) from checked derivations."""
import itertools, re

def fin(i):
    t = 'zero'
    for _ in range(i):
        t = '(suc %s)' % t
    return t

def ltp(i, j):
    t = 's≤s z≤n'
    for _ in range(i):
        t = 's≤s (%s)' % t
    return t

def letter(g):
    if g[0] == 'Z':
        return 'z%d' % g[1]
    if g[0] == 'X':
        return 'x%d%d' % (g[1], g[2])
    return 'h%d%d' % (g[1], g[2])

def alist(xs):
    return '(' + ' ∷ '.join(letter(g) for g in xs) + (' ∷ [])' if xs else '[])')

LOCAL = re.compile(r'^(a1|a2|a3|c1|c2|c3|c4|c5|d1|d2)-(\d+)$')

def agda_name(name, derived_names):
    """Map a library name to an Agda Eqn expression."""
    if name.startswith('(sym⁼ '):
        return '(sym⁼ %s)' % agda_name(name[len('(sym⁼ '):-1], derived_names)
    m = LOCAL.match(name)
    if m:
        ax, ds = m.group(1), [int(c) for c in m.group(2)]
        if ax == 'a1':
            return '(ʟa1 f%d)' % ds[0]
        if ax in ('a2', 'a3', 'c1', 'd1', 'd2'):
            a, b = ds
            return '(ʟ%s f%d f%d lt%d%d)' % (ax, a, b, a, b)
        a, b, c = ds
        return '(ʟ%s f%d f%d f%d lt%d%d lt%d%d)' % (ax, a, b, c, a, b, b, c)
    if name in derived_names:
        return 'δ' + name
    return name   # hypotheses and their rot⁼ forms, verbatim

def steps_text(steps, goal, indent, derived_names):
    parts = []
    for st in steps:
        if st[0] == 'perm':
            parts.append('perm %s' % alist(st[1]))
        else:
            parts.append('rw %d %s' % (st[1], agda_name(st[2], derived_names)))
    parts.append('perm %s' % alist(goal))
    return ('\n' + indent + '∷ ').join(parts) + '\n' + indent + '∷ []'

def letters_block(m, used):
    out = []
    out.append('f%s : Fin %d' % (' f'.join(str(i) for i in range(m)), m))
    for i in range(m):
        out.append('f%d = %s' % (i, fin(i)))
    out.append('')
    for i, j in itertools.combinations(range(m), 2):
        out.append('lt%d%d : f%d < f%d' % (i, j, i, j))
        out.append('lt%d%d = %s' % (i, j, ltp(i, j)))
    out.append('')
    for g in sorted(used):
        nm = letter(g)
        out.append('%s : Gen %d' % (nm, m))
        if g[0] == 'Z':
            out.append('%s = Z-gen f%d' % (nm, g[1]))
        elif g[0] == 'X':
            out.append('%s = X-gen f%d f%d lt%d%d' % (nm, g[1], g[2], g[1], g[2]))
        else:
            out.append('%s = H-gen f%d f%d lt%d%d' % (nm, g[1], g[2], g[1], g[2]))
    return out

def collect(derivs):
    used = set()
    for name, l, r, steps in derivs:
        used |= set(l) | set(r)
        for st in steps:
            used |= set(st[1]) if st[0] == 'perm' else set(st[3])
    return used

def section(modname, hyps, derivs, exports, indent='  '):
    """hyps: list of (agda-name, lhs-listname, rhs-listname); derivs from Chain;
    exports: list of (agda-name, derived-name) to expose as ≈ proofs."""
    out = []
    out.append('module %s %s where' % (modname, ' '.join(
        '(%sh : ⟪ %s ⟫ ≈ ⟪ %s ⟫)' % (h, l, r) for h, l, r in hyps)))
    out.append('')
    out.append(indent + 'private')
    ind2 = indent + '  '
    for h, l, r in hyps:
        out.append(ind2 + '%s : Eqn' % h)
        out.append(ind2 + '%s = eqn %s %s %sh' % (h, l, r, h))
    names = set()
    for name, l, r, steps in derivs:
        out.append('')
        out.append(ind2 + 'δ%s : Eqn' % name)
        out.append(ind2 + 'δ%s = derive %s %s' % (name, alist(l), alist(r)))
        out.append(ind2 + '  ( ' + steps_text(steps, r, ind2 + '  ', names | {name}))
        out.append(ind2 + '  ) refl')
        names.add(name)
    for nm, dn, ln, rn in exports:
        out.append('')
        out.append(indent + '%s : ⟪ %s ⟫ ≈ ⟪ %s ⟫' % (nm, ln, rn))
        out.append(indent + '%s = prf δ%s' % (nm, dn))
    return out
