"""The writer of the Lean modules `Axioms`, `Lemmas` and `Rules1`-`Rules5`
from the derivations of `lemmas.py` and `rules.py`."""
from engine import BASE, DB, IDX, mirror, shifted
from supp import frame_size


def lt(a):
    if a[0] == 'w': return 'Lt.om'
    return {'H': 'Lt.H', 'S': 'Lt.S', 'Z': 'Lt.CZ'}[a[0]] + f' {a[1]}'

def wrap_items(items, indent, width=92, first=0):
    out = []; line = ''
    for it in items:
        cand = it if not line else line + ', ' + it
        if len(cand) + (first if not out else indent) > width and line:
            out.append(line + ',')
            line = it
        else:
            line = cand
    out.append(line)
    return ('\n' + ' ' * indent).join(out)

def lst(word, indent=4):
    return '[' + wrap_items([lt(a) for a in word], indent + 1) + ']'

def steps_lean(st, indent=4):
    items = []
    for s in st:
        if s[0] == 'mv':
            items.append(f'Step.mv {s[1]} {s[2]}')
        else:
            _, e, pos, sh, rev = s
            items.append(f'Step.rw {e} {pos} {sh} {"true" if rev else "false"}')
    return '[' + wrap_items(items, indent + 1) + ']'

def localize(st):
    used = sorted({s[1] for s in st if s[0] == 'rw'})
    remap = {g: i for i, g in enumerate(used)}
    out = []
    for s in st:
        if s[0] == 'rw':
            out.append(('rw', remap[s[1]], s[2], s[3], s[4]))
        else:
            out.append(s)
    return used, out

def dbterm(used):
    t = 'db_ok_nil'
    for g in reversed(used):
        t = f'db_ok_cons h{DB[g][0]} ({t})' if t != 'db_ok_nil' else f'db_ok_cons h{DB[g][0]} db_ok_nil'
    return t

def mirror_step(s, K):
    if s[0] == 'mv':
        return s
    _, e, pos, sh, rev = s
    nm, k, l, r = DB[e]
    ml = mirror(shifted(l, sh), K); mr = mirror(shifted(r, sh), K)
    for e2, (nm2, k2, l2, r2) in enumerate(DB):
        if k2 != k: continue
        for s2 in range(0, K - k2 + 1):
            L2, R2 = shifted(l2, s2), shifted(r2, s2)
            if L2 == ml and R2 == mr:
                return ('rw', e2, pos, s2, rev)
            if L2 == mr and R2 == ml:
                return ('rw', e2, pos, s2, not rev)
    raise ValueError(('no mirror', nm, sh, K))

HEAD = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

{doc}
-/
{imports}
namespace QCert.SelingerClifford

set_option maxRecDepth 8000

'''

def gen_axioms():
    s = HEAD.format(doc='''# Clifford circuits (Selinger): the relations as equations of letters

The relations C1–C15 of Figure 8 as equations between words of letters
(time order, our wire numbering), each holding on every number of wires at
least its own (`Holds.of_rel`).''', imports='import QCert.SelingerClifford.Rewrite\n')
    for nm, k, l, r in BASE:
        if not nm.startswith('C'): continue
        s += f'/-- {nm} of Figure 8. -/\n'
        s += f'def e{nm} : Eqn :=\n  ⟨{k}, {lst(l, 6)},\n    {lst(r, 4)}⟩\n\n'
        s += f'theorem h{nm} : Holds e{nm}.k e{nm}.l e{nm}.r :=\n'
        s += f'  Holds.of_rel Rel.{nm} _ _ rfl rfl (by decide) (by decide)\n\n'
    s += 'end QCert.SelingerClifford\n'
    return s

LEMDOC = {
 'L4': '(4) of Lemma 1.1: `SHSH = HSSS·ω`.', 'L5': '(5) of Lemma 1.1: `HSHS = SSSH·ω`.',
 'L6': '(6) of Lemma 1.1: `HSSSH = SHS·ω⁻¹`.', 'L7': '(7) of Lemma 1.1: `SHSSHS = HSSH·ω²`.',
 'L8': '(8) of Lemma 1.1: `HSSHSS = SSHSSH·ω⁴`.', 'L9': '(9) of Lemma 1.1: `SSSHSSH = HSSHS·ω⁻²`.',
 'L10': '(10) of Lemma 1.1: `SSSHSSS = HSH·ω⁻¹`.',
 'L14': '(14) of Lemma 1.2.', 'L15': '(15) of Lemma 1.2.', 'L16': '(16) of Lemma 1.2.',
 'L17': '(17) of Lemma 1.2.', 'L18': '(18) of Lemma 1.2.', 'L20': '(20) of Lemma 1.3.',
 'L21': '(21) of Lemma 1.3.',
}

def gen_lemmas(lemd):
    s = HEAD.format(doc='''# Clifford circuits (Selinger): the lemmas of the supplement

Equations (4)–(10), (14)–(18), (20) and (21) of Lemmas 1.1–1.3 of the
supplement to Selinger's paper, as equations between words of letters in time
order (an equation's `·ω^k` is moved to the side where `k ≥ 0`), with their
"upside-down" versions (`M…`).  Each is derived from the relations of
Figure 8 and the lemmas before it by a checked derivation, found by a search
guided by the steps of the supplement's proof.''',
                    imports='import QCert.SelingerClifford.Axioms\n')
    order = ['L4','L5','L6','L7','L8','L9','L10','L14','M14','L15','M15','L16','M16',
             'L17','M17','L18','M18','L20','M20','L21','M21']
    for nm in order:
        e = DB[IDX[nm]]
        k, l, r = e[1], e[2], e[3]
        doc = LEMDOC.get(nm) or ('The upside-down version of ' + LEMDOC['L' + nm[1:]])
        s += f'/-- {doc} -/\n'
        s += f'def e{nm} : Eqn :=\n  ⟨{k}, {lst(l, 6)},\n    {lst(r, 4)}⟩\n\n'
        der = None
        if nm in lemd:
            K, st = lemd[nm]
            der = st
        elif nm.startswith('M') and ('L' + nm[1:]) in lemd:
            K, st = lemd['L' + nm[1:]]
            der = [mirror_step(x, K) for x in st]
        if der is None:
            s += f'theorem h{nm} : Holds e{nm}.k e{nm}.l e{nm}.r := by\n  sorry\n\n'
        else:
            used, loc = localize(der)
            s += f'theorem h{nm} : Holds e{nm}.k e{nm}.l e{nm}.r :=\n'
            s += f'  Holds.of_derives ({dbterm(used)})\n'
            s += f'    (steps := {steps_lean(loc, 4)})\n'
            s += f'    (by decide +kernel)\n\n'
    s += 'end QCert.SelingerClifford\n'
    return s

def box_expr(tok, k):
    """Lean expression (List Lt) for one supplement token in frame k."""
    name, args = tok
    if name == 'H': return f'[Lt.H {k-1-args[0]}]'
    if name == 'S': return f'[Lt.S {k-1-args[0]}]'
    if name == 'X': return f'bX {k-1-args[0]}'
    if name == 'ZZ': return f'[Lt.CZ {k-2-min(args)}]'
    if name in 'ACE':
        return f'b{name} {args[0]} {k-1-args[1]}'
    if name in 'BD':
        return f'b{name} {args[0]} {k-2-args[1]}'
    raise ValueError(tok)

def word_expr(toks, ph, k):
    # merge consecutive single letters into one list
    parts = []
    cur = []
    for t in toks:
        e = box_expr(t, k)
        if e.startswith('['):
            cur.append(e[1:-1])
        else:
            if cur: parts.append('[' + ', '.join(cur) + ']'); cur = []
            parts.append(e)
    for _ in range(ph % 8):
        cur.append('Lt.om')
    if cur: parts.append('[' + ', '.join(cur) + ']')
    if not parts: return '[]'
    return ' ++ '.join(parts)

def gen_rules(derivs, eqs, part, names, imports):
    s = HEAD.format(doc=f'''# Clifford circuits (Selinger): rewrite rules, part {part}

Equations {names[0]}–{names[-1]} of the supplement to Selinger's paper (the rewrite
rules of Figures 3–7 of the paper), as equations between words of letters in
time order, in our wire numbering (the supplement numbers wires from the
top).  Each is derived from the relations of Figure 8 and the lemmas of the
supplement by a checked derivation, translated from the supplement's own
proof step by step.''', imports=imports)
    for nm in names:
        eq = [e for e in eqs if e['name'] == nm][0]
        k0 = frame_size(eq)
        k = max(k0, 1)
        (lt_, lp), (rt, rp) = eq['stmt']
        L = word_expr(lt_, lp, k)
        R = word_expr(rt, rp, k)
        K, st = derivs[nm]
        assert K == k0
        used, loc = localize(st)
        tname = 'rule_' + nm.replace('.', '_')
        stmt_l = ' '.join(f'{t[0]} {" ".join(map(str, t[1]))}' for t in lt_)
        stmt_r = ' '.join(f'{t[0]} {" ".join(map(str, t[1]))}' for t in rt)
        s += f'/-- Equation {nm} (supplement: `[{stmt_l}]·ω^{lp} = [{stmt_r}]·ω^{rp}`). -/\n'
        s += f'theorem {tname} :\n    Holds {k} ({L})\n      ({R}) :=\n'
        s += f'  Holds.of_derives ({dbterm(used)})\n'
        s += f'    (steps := {steps_lean(loc, 4)})\n'
        s += f'    (by decide +kernel)\n\n'
    s += 'end QCert.SelingerClifford\n'
    return s

def gen_all(lemd, derivs, eqs):
    """{file name: text} of the generated modules."""
    out = {'Axioms.lean': gen_axioms(), 'Lemmas.lean': gen_lemmas(lemd)}
    names = [e['name'] for e in eqs]
    chunks = [names[0:20], names[20:40], names[40:60], names[60:80], names[80:]]
    imports = 'import QCert.SelingerClifford.Lemmas\nimport QCert.SelingerClifford.Boxes\n'
    for i, ch in enumerate(chunks):
        out[f'Rules{i + 1}.lean'] = gen_rules(derivs, eqs, i + 1, ch, imports)
    return out
