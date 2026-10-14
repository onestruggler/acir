"""Generate a development's TopPad.agda: its rules on their own wires, the
padded forms, and SameRules (FamilyRules for a PROP) for
Circuit.TopPad.Equivalence (Circuit.Prop.TopPad).

The rules are read off the development's `data _REL,_===_` declaration;
toppad_configs.py says, per development, which module to read, what to
import, how its relation is named and lifted, and what to add by hand
(a schema, private words, lemmas for ⇓-same-by).  A rule set with powers
whose exponent is not a numeral is `stuck`: its padded and ⇓'d rules go
through Circuit.TopPad.Closed's ⇓-same.

usage, from the root of the library:
  python3 Circuit/TopPad/gen/gen_toppad.py CONFIG-NAME
  python3 Circuit/TopPad/gen/gen_toppad.py all"""
import re, sys

WIDTH = {'n': 0, '(₁₊ n)': 1, '(₂₊ n)': 2, '(₃₊ n)': 3, '(₄₊ n)': 4}


def rule_block(src, rel):
    """The constructor declarations of `data _REL,_===_`, as (name, text)."""
    L = src.split('\n')
    start = next(i for i, l in enumerate(L) if re.match(r'\s*data _' + re.escape(rel) + r',_===_ ', l))
    base_ind = len(L[start]) - len(L[start].lstrip())
    decls, cur = [], None
    for l in L[start + 1:]:
        if l.strip() == '':
            continue
        ind = len(l) - len(l.lstrip())
        if ind <= base_ind and not l.lstrip().startswith('--'):
            break
        if l.lstrip().startswith('--'):
            continue
        m = re.match(r'\s*(\S+)\s+:\s*(.*)$', l)
        if m and (cur is None or ind <= cur[2]):
            cur = [m.group(1), m.group(2), ind]
            decls.append(cur)
        else:
            cur[1] += ' ' + l.strip()
    return [(d[0], ' '.join(d[1].split())) for d in decls]


def parse(name, text, rel):
    m = re.match(r'^(.*?)\s*(\(₁₊ n\)|\(₂₊ n\)|\(₃₊ n\)|\(₄₊ n\)|n)\s+' + re.escape(rel) + r',\s*(.*)$', text)
    if not m:
        return None
    params, width, eqn = m.group(1).strip(), m.group(2), m.group(3)
    l, r = eqn.split(' === ')
    p = params.replace('∀', ' ').replace('→', ' ')
    p = re.sub(r'\{[^}]*\}', ' ', p)
    names = []
    for grp in re.findall(r'\.?\(([^)]*)\)|(\S+)', p):
        if grp[0]:
            names += grp[0].split(':')[0].split()
        elif grp[1]:
            names.append(grp[1])
    base_params = re.sub(r'\{n\}\s*', '', params).strip()
    if base_params.replace('∀', '').replace('→', '').strip() == '':
        base_params = ''
    return dict(name=name, params=base_params, args=names, width=width, k=WIDTH[width], l=l, r=r)


def wrap_side(side, pad, width=78):
    """A side of an equation over lines, broken before • where needed."""
    parts = side.split(' • ')
    lines, cur = [], parts[0]
    for q in parts[1:]:
        if len(pad) + len(cur) + 3 + len(q) + 4 > width:
            lines.append(cur + ' •')
            cur = q
        else:
            cur += ' • ' + q
    lines.append(cur)
    return [pad + x for x in lines]


def eqline(prefix, l, r, ind):
    """A typed equation, wrapped before === when it is long."""
    one = f"{prefix} {l} === {r}"
    if len(one) <= 78:
        return [one]
    pad = ' ' * ind
    if len(prefix) + len(l) + 6 <= 78 and len(pad) + len(r) <= 78:
        return [f"{prefix} {l} ===", pad + r]
    L = wrap_side(l, pad)
    L[-1] += ' ==='
    return [prefix] + L + wrap_side(r, pad)


def app(f, args):
    return f if not args else '(' + f + ' ' + ' '.join(args) + ')'


def generate(cfg):
    src = open(cfg['src'], encoding='utf-8').read().replace('\r\n', '\n')
    rules, schemas = [], []
    for name, text in rule_block(src, cfg['rel']):
        r = parse(name, text, cfg['rel'])
        if r and name not in cfg.get('skip', []):
            rules.append(r)
        else:
            schemas.append(name)
    B = cfg.get('suffix', 'ᴮ')
    W = cfg.get('wrap', lambda s: s)
    rel = cfg['rel']
    out = [cfg['header']]
    out.append('------------------------------------------------------------------------')
    out.append('-- The rules on their own wires, padded by Top-Pad')
    out.append('')
    for d in cfg.get('pre-defs', []):
        out.append(d)
    out.append('infix 4 _Base,_===_')
    out.append('data _Base,_===_ : (n : ℕ) → WRel (Gen n) where')
    for r in rules:
        ps = (r['params'] + ' ') if r['params'] else ''
        out += eqline(f"  {r['name']}{B} : {ps}{r['k']} Base,", r['l'], r['r'], 8)
    for s in cfg.get('extra-base', []):
        out.append('  ' + s)
    out.append('')
    SB = f"(⇓-same-by {cfg['same-by']})" if cfg.get('same-by') else '⇓-same'
    prop = cfg.get('prop')
    if prop:
        out.append(f"module P  = Circuit.Prop.TopPad {cfg['gate']} {prop}")
        out.append(f"module E  = P.Lift≅Top-Pad-Prop {cfg['srel']} _Base,_===_")
        out.append("module TP = E.TP")
        base = lambda x: f"TP.srel (E.sbase {x})"
        EE = 'E.E'
    else:
        out.append(f"module TP = Circuit.TopPad.Top-Pad {cfg['gate']} _Base,_===_")
        out.append(f"module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad {cfg['gate']} {cfg['srel']} _Base,_===_")
        base = lambda x: f"TP.srel {x}"
        EE = 'E'
    out.append('')
    out.append('open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)')
    out.append('')
    if cfg.get('stuck'):
        out.append('-- Each rule on the bottom wires of every wider circuit: one wire wider')
        out.append('-- its words are the same words, up to the powers ⇓ does not compute')
        out.append('-- through (⇓-same).')
    else:
        out.append('-- Each rule on the bottom wires of every wider circuit: its words are')
        out.append('-- closed, so one wire wider they are the same words.')
    for r in rules:
        ps = (r['params'] + ' ') if r['params'] else ''
        a = (' '.join(r['args']) + ' ') if r['args'] else ''
        out.append('')
        out += eqline(f"{r['name']}↓ : {ps}{r['width']} TRel,", r['l'], r['r'], 6)
        out.append(f"{r['name']}↓ {{0}}    {a}= {base(app(r['name'] + B, r['args']))}")
        if cfg.get('stuck'):
            out.append(f"{r['name']}↓ {{₁₊ n}} {a}= {EE}.cong↓≡ {SB} {SB} {app(r['name'] + '↓', r['args'])}")
        else:
            out.append(f"{r['name']}↓ {{₁₊ n}} {a}= TP.cong↓ {app(r['name'] + '↓', r['args'])}")
    for s in cfg.get('extra-defs', []):
        out.append(s)
    out.append('')
    out.append('------------------------------------------------------------------------')
    out.append('-- The two have the same rules')
    out.append('')
    if prop:
        out.append('fam : E.FamilyRules')
        out.append('fam = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }')
    else:
        out.append('same : E.SameRules')
        out.append('same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }')
    out.append('  where')
    relnwv = (f"{cfg['rel-prefix']} n w v" if cfg.get('rel-prefix')
              else f"n {cfg['rel-op']}, w === v")
    out.append(f"  pad : {relnwv} → n ⊢ᵀ w ≈ v")
    for r in rules:
        out.append(f"  pad {W(app(r['name'], r['args']))} = PB.axiom {app(r['name'] + '↓', r['args'])}")
    out += ['  ' + s for s in cfg.get('extra-pad', [])]
    out.append('')
    out.append('  unpad : n Base, w === v → n ⊢ᴸ w ≈ v')
    def lift(x):
        return cfg['lift'].format(x) if '{}' in cfg['lift'] else f"{cfg['lift']} {x}"
    for r in rules:
        out.append(f"  unpad {app(r['name'] + B, r['args'])} = PB.axiom ({lift(W(app(r['name'], r['args'])))})")
    out += ['  ' + s for s in cfg.get('extra-unpad', [])]
    out.append('')
    out.append(f"  srel-⇓ : {relnwv} → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓")
    for r in rules:
        dflt = (f"{EE}.axiom≡ {SB} {SB} ({lift(W(app(r['name'], r['args'])))})" if cfg.get('stuck')
                else f"PB.axiom ({lift(W(app(r['name'], r['args'])))})")
        rhs = cfg.get('srel-⇓', {}).get(r['name']) or dflt
        out.append(f"  srel-⇓ {W(app(r['name'], r['args']))} = {rhs}")
    out += ['  ' + s for s in cfg.get('extra-srel-⇓', [])]
    out.append('')
    out.append('------------------------------------------------------------------------')
    out.append('-- So the congruences coincide, and the identity is a group isomorphism')
    out.append('')
    if prop:
        out.append('same : E.E.SameRules')
        out.append('same = E.same fam')
        out.append('')
    out.append(f'open {EE}.Equivalent same public using (lr⇒tp ; tp⇒lr)')
    if cfg.get('grouplike'):
        out.append(f"open {EE}.Equivalent.Iso same {cfg['grouplike']} public using (glᵀ ; lr≅tp)")
    text = '\n'.join(out) + '\n'
    open(cfg['out'], 'w', encoding='utf-8', newline='\n').write(text)
    print(cfg['out'], len(rules), 'rules;', 'not generated:', schemas)


def header(title, module, imports, params='', note='', prop=False, pre=None,
           options='--cubical-compatible --safe'):
    import textwrap
    NL = chr(10)
    if pre is None:
        pre = ('open import Data.Nat using (ℕ ; 2+)' + NL +
               'open import Data.Nat.Primality using (Prime)' + NL + NL) if params else ''
    post = '' if params else 'open import Data.Nat using (ℕ)' + NL
    lifted = "Circuit.Prop's Lift-To-Prop" if prop else "Circuit.Base's Lift-Relation"
    inst = ("Circuit.Prop.TopPad, which has the swap rules already:"
            if prop else "Circuit.TopPad.Equivalence, as Symmetric.TopPad is:")
    rec = 'FamilyRules' if prop else 'SameRules'
    para = lambda t: NL.join('-- ' + x for x in textwrap.wrap(t, 69, break_on_hyphens=False))
    first = para(f"{title}: the rules on their own wires, padded by Circuit.TopPad, "
                 f"give the same congruence as Syntactics' rules at every width, "
                 f"lifted by {lifted}")
    second = para(f"An instance of {inst} each rule that Syntactics states at every "
                  f"width is here stated on its own wires only (its name with ᴮ), its "
                  f"padded form is that rule with idle wires on top (↓), and {rec} "
                  f"says, rule by rule, that the two relations have the same rules."
                  + (' ' + note if note else ''))
    return f'''------------------------------------------------------------------------
-- Presentations of groups
--
{first}
--
{second}
------------------------------------------------------------------------

{{-# OPTIONS {options} #-}}

{pre}module {module}{params} where

{post}open import Notations
open import Word.Base

import Circuit.TopPad
{'import Circuit.Prop.TopPad' if prop else 'import Circuit.TopPad.Equivalence'}
import Presentation.Base as PB

{imports}

private
  variable
    n : ℕ
    w v : Circuit n
'''


if __name__ == '__main__':
    sys.path.insert(0, __file__.rsplit('/', 1)[0] if '/' in __file__ else '.')
    import toppad_configs
    names = list(toppad_configs.CONFIGS) if sys.argv[1] == 'all' else sys.argv[1:]
    for name in names:
        generate(toppad_configs.CONFIGS[name])
