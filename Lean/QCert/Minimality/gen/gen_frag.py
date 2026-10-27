"""Generate `<Fragment>/Derivations.lean` from the derivations the search found (a cache file)."""
import ast, sys
from leangen import Gen, fmt_list, lean_steps

def ident(name):
    s = (name.replace('lem:', '').replace('-dec-eq', 'dec').replace('-unfolding', '').replace('-', '_')
         .replace('~', '_').replace(':', '_'))
    return 'd' + s

def word(letters, lname):
    return '[' + ', '.join('(.%s, %d)' % (lname[g], o) for (g, o) in letters) + ']'

def generate(cfg):
    CACHE = ast.literal_eval(open(cfg['cache'], encoding='utf-8').read())
    res = {k: v[1] for k, v in CACHE.items()}
    g = Gen(cfg['syms'], cfg['scalar'], ident)
    lname = cfg['lname']

    def doc(name):
        if '~' in name:
            base, w = name.rsplit('~', 1)
            what = {'i': 'Both sides of %s inverted, letter by letter.',
                    'm': '%s upside down (conjugated by the swap).',
                    'r': '%s with the order of its three wires reversed.'}[w]
            return what % ('`' + ident(base) + '`')
        if name.startswith('R3:'):
            return 'Reversing three wires carries a gate to its mirror image.'
        return cfg['doc'](name)

    def used_lemmas(name):
        return [e[1] for e in res[name][3] if e[0] == 'lem']

    tops = [k for k in res if k.startswith('dec') or k.startswith('DE')]
    needed = set()
    for nm in tops:
        stack = [nm]
        while stack:
            x = stack.pop()
            for y in used_lemmas(x):
                if y not in needed: needed.add(y); stack.append(y)
    order, seen = [], set()
    def visit(x):
        if x in seen: return
        seen.add(x)
        for y in used_lemmas(x): visit(y)
        order.append(x)
    for x in sorted(needed): visit(x)

    out = [cfg['header']]
    out.append('''/-- The theory of %s. -/
abbrev Th : CRel Gate := Padded (pres.Base fun _ => True)

theorem hsc : ∀ c c' : Gate 0, c = c' := by intro c c'; cases c; cases c'; rfl

/-- Letters of words written out: a gate and the wire it starts on. -/
inductive Lt
  | %s

/-- The generator of `n`-wire circuits for a letter (the scalar for a
letter that does not fit). -/
def Lt.gen : (n : ℕ) → Lt → ℕ → Gen Gate n
%s
  | n + 1, g, o + 1 => .up (Lt.gen n g o)
  | _, _, _ => .gate0 %s

/-- A word written in time order (the first letter applied first). -/
def tw (n : ℕ) (l : List (Lt × ℕ)) : Circuit Gate n :=
  FreeMonoid.ofList (l.reverse.map fun x => x.1.gen n x.2)
''' % (cfg['figure'], ' | '.join(cfg['letters']), '\n'.join(cfg['gen_clauses']), cfg['scalar_ctor']))
    for nm in order:
        n, l, r, eqs, steps = res[nm]
        out.append('''/-- %s -/
def %s : DEqn Th %d where
  lhs := tw %d %s
  rhs := tw %d %s
  proof := %s
''' % (doc(nm), ident(nm), n, n, word(l, lname), n, word(r, lname), g.proof(eqs, steps, 4)))

    out.append('''/-- %s: the decoding of every relation of %s is derivable from %s. -/
theorem rel_derivable : ∀ {k : ℕ} {w v : Circuit %s.Gate k},
    %s.Rel k w v → Derivable (Lift Th k) (D.map k w) (D.map k v)''' % (
        cfg['appG'], cfg['srcname'], cfg['figure'], cfg['src'], cfg['src']))
    for c in cfg['rels']:
        n, l, r, eqs, steps = res['dec' + c]
        out.append('  | _, _, _, .%s =>\n    %s' % (c, g.proof(eqs, steps, 6)))
    out.append(cfg['de'](g, res))
    out.append('\nend %s\n' % cfg['ns'])
    open(cfg['out'], 'w', encoding='utf-8', newline='\n').write('\n'.join(out))
    print('written', cfg['out'], len(order), 'lemmas')
