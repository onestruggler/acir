# The window library of the five-wire derivations, and their light layout.
#
# emit5.py writes every window step of a derivation as its own
# evaluation, `lwᵢ c4 xs ys tt tt Eq.refl` (literal) or `pwᵢ …` (placed).
# Agda does not share evaluations, and the derivations repeat windows:
# about 70 000 window steps over some 2 000 distinct windows.  This pass
# collects each distinct window, up to orientation, as one lemma of a
# module of its own (Five/Wins/WL*.agda for the literal windows, which
# need only Five.Lits and so can serve the R modules, Five/Wins/WP*.agda
# for the placed ones, which need Five.Resps and so the R modules).
#
# The windows need Lemma 5.1 and with it the whole development below
# four wires (Place, Swaps, ThreeQubit, Clifford+CS-3qubit: 78 MB of
# interfaces, half a minute and 2 GB of heap to load).  So the
# derivations do not import them: their lemmas take the windows as an
# argument, a record of them (Five/WinSig.agda: `WsL` for the literal
# ones, `Ws` for all, `lit` the literal part; each holds chunk records of
# at most CHUNK windows, see write_records), in place of completeness on
# four wires, and a window step is the accessor `wᵏ c4`, or `wᵏ (lit c4)`
# in a D module.  Five/WinInstL.agda and WinInst.agda build
# the records from the library, given completeness on four wires, and the
# modules that use the derivations (Resps, TransportAx, CalcAx, F6Ax)
# apply their lemmas to `wsL c4` and `ws c4`.
#
#   python winlib5.py <Five directory>
#   python winlib5.py --records <Five directory>   (only the record modules)

import io, os, re, sys

NL = '\n'
MOD = 'Examples.Groups.Clifford+CS.Five'
LST = r'(\([^()]*\)|\[\])'
STEP = re.compile(r'\(([lp])w([0-4]) c4 ' + LST + ' ' + LST + r' tt tt Eq\.refl\)')
SIG = re.compile(r'^(\S+) : Complete 4 → ', re.M)
COMPLETE = 'open import Examples.Groups.Clifford+CS.Completeness using (Complete)\n'
CONSUMERS = ['Resps', 'TransportAx', 'CalcAx', 'F6Ax']

# A module of the library holds windows up to this many letters in all.
BUDGET = 1200

BANNER = '''------------------------------------------------------------------------
-- Presentations of groups
--
-- {title}
--
{body}
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

'''


def letters(lst):
    return 0 if lst == '[]' else lst.count('∷')


def modules(root):
    d = os.path.join(root, 'D')
    names = sorted(f for f in os.listdir(d) if f.endswith('.agda'))
    # R modules first (they come first in the dependency order), then D.
    return [os.path.join(d, f) for f in sorted(names, key=lambda f: (f[0] != 'R', f))]


def banner(title, body):
    return BANNER.format(title=title, body=NL.join('-- ' + l if l else '--' for l in body.split(NL)))


def lib_header(mod, kind):
    tables = (f'open import {MOD}.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)' if kind == 'l'
              else f'open import {MOD}.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)')
    what = 'literal' if kind == 'l' else 'placed'
    return banner(f'Windows of the five-wire derivations ({what})',
                  'Each distinct window of the derivations of Five.D, evaluated once\n'
                  '(Five.Win).  Written by `scratchpad/five/winlib5.py`.') + f'''module {MOD}.Wins.{mod} where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import {MOD}.Chain
{tables}
'''


# A record holds at most this many fields.  Agda stores, with each
# projection of a record, a clause binding every field, so a record of n
# fields costs n² in time and memory: WinSig as one record of 1 300
# fields and one of 700 exhausted a 4 GB heap.  So the windows are kept
# in chunk records of at most CHUNK fields, the records WsL and Ws hold
# the chunks, and each window is a function of the same name into its
# chunk, which the derivations use as they would a projection.
CHUNK = 100


def write_records(root, lits, placed, e2s, modof):
    """WinSig (the records and the accessors), WinInstL and WinInst.
    lits, placed: (name, lhs, rhs) of the literal and placed windows;
    e2s: (name, lhs, rhs) of the two-wire equations of Five.D.TR; modof:
    the library module of each window."""
    def chunks(xs):
        return [xs[i:i + CHUNK] for i in range(0, len(xs), CHUNK)]
    lch, pch = chunks(lits), chunks(placed)

    sig = [banner('The windows of the five-wire derivations, as records',
                  'The derivations of Five.D take their windows as an argument (see\n'
                  '`scratchpad/five/winlib5.py`): `WsL` holds the literal windows and\n'
                  'the two-wire equations of Five.D.TR, `Ws` the literal ones (`lit`)\n'
                  'and the placed ones.  Each window is a function of the record, of\n'
                  'its own name; the records themselves hold chunks of at most\n'
                  f'{CHUNK} windows (`WsL01`, …, `Ws01`, …), since a record costs the\n'
                  'square of its number of fields.  Five.WinInstL and Five.WinInst\n'
                  'build them.'),
           f'module {MOD}.WinSig where', '',
           'open import Data.List using (List ; [] ; _∷_)',
           'open import Word.Base using (ε ; _•_)', '',
           'open import Examples.Groups.Clifford+CS.Syntactics using (_⊢_≈_ ; iI ; S ; K ; CS ; _↑)',
           f'open import {MOD}.Chain', '']

    def chunk_record(rec, ch):
        out = [f'record {rec} : Set where', '  no-eta-equality', '  field']
        out += [f'    {n} : ⟪ {a} ⟫ʷ ≈ ⟪ {b} ⟫ʷ' for n, a, b in ch]
        return out + ['']

    for ci, ch in enumerate(lch, 1):
        sig += chunk_record(f'WsL{ci:02d}', ch)
    for ci, ch in enumerate(pch, 1):
        sig += chunk_record(f'Ws{ci:02d}', ch)

    sig += ['record WsL : Set where', '  no-eta-equality', '  field']
    sig += [f'    l{ci:02d} : WsL{ci:02d}' for ci in range(1, len(lch) + 1)]
    # The two-wire equations of the transports (Five.D.TR).
    sig += [f'    {e} : 2 ⊢ {l} ≈ {r}' for e, l, r in e2s]
    sig += ['', 'record Ws : Set where', '  no-eta-equality', '  field', '    lit : WsL']
    sig += [f'    p{ci:02d} : Ws{ci:02d}' for ci in range(1, len(pch) + 1)]
    sig += ['', f'open WsL public using ({" ; ".join(e for e, _, _ in e2s)})' if e2s else '',
            'open Ws public using (lit)', '']

    sig += ['-- The windows.', '']
    for rec, sub, pre, chs in (('WsL', 'WsL', 'l', lch), ('Ws', 'Ws', 'p', pch)):
        for ci, ch in enumerate(chs, 1):
            for n, a, b in ch:
                sig += [f'{n} : {rec} → ⟪ {a} ⟫ʷ ≈ ⟪ {b} ⟫ʷ',
                        f'{n} c = {sub}{ci:02d}.{n} ({rec}.{pre}{ci:02d} c)', '']
    io.open(os.path.join(root, 'WinSig.agda'), 'w', encoding='utf-8', newline=NL).write(NL.join(sig))

    def inst(modname, title, recname, fn, chs, pre, extra_imports, head_fields=(), tail_fields=()):
        mods = sorted({modof[n] for ch in chs for n, _, _ in ch})
        out = [banner(title, 'Written by `scratchpad/five/winlib5.py`.'),
               f'module {MOD}.{modname} where', '',
               'open import Examples.Groups.Clifford+CS.Completeness using (Complete)',
               f'open import {MOD}.WinSig using ({recname} ; '
               + ' ; '.join(f'{recname}{ci:02d}' for ci in range(1, len(chs) + 1)) + ')'] + extra_imports
        for m in mods:
            out.append(f'import {MOD}.Wins.{m} as {m}')
        out.append('')
        for ci, ch in enumerate(chs, 1):
            out += [f'{fn}{ci:02d} : Complete 4 → {recname}{ci:02d}', f'{fn}{ci:02d} c4 = record']
            for k, (n, _, _) in enumerate(ch):
                out.append(('  { ' if k == 0 else '  ; ') + f'{n} = {modof[n]}.{n} c4')
            out += ['  }', '']
        out += [f'{fn} : Complete 4 → {recname}', f'{fn} c4 = record']
        fields = list(head_fields) + [f'{pre}{ci:02d} = {fn}{ci:02d} c4' for ci in range(1, len(chs) + 1)] \
            + list(tail_fields)
        for k, fld in enumerate(fields):
            out.append(('  { ' if k == 0 else '  ; ') + fld)
        out += ['  }', '']
        io.open(os.path.join(root, modname + '.agda'), 'w', encoding='utf-8', newline=NL).write(NL.join(out))

    e2imp = ['open import Relation.Binary.PropositionalEquality as Eq using ()',
             'open import Word.Base using (ε ; _•_)',
             'open import Examples.Groups.Clifford+CS.Syntactics using (iI ; S ; K ; CS ; _↑)',
             'open import Examples.Groups.Clifford+CS.Completeness using (complete₂)',
             'open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)'] if e2s else []
    e2f = [f'{e} = Below.by-sem₀ 2 complete₂ ({l}) ({r}) Eq.refl' for e, l, r in e2s]
    inst('WinInstL', 'The literal windows of the five-wire derivations, as a record',
         'WsL', 'wsL', lch, 'l', e2imp, tail_fields=e2f)
    inst('WinInst', 'The windows of the five-wire derivations, as a record',
         'Ws', 'ws', pch, 'p', [f'open import {MOD}.WinInstL using (wsL)'], head_fields=['lit = wsL c4'])


WINDEF = re.compile(r'^(w[lp]\d{4}) : Complete 4 → ⟪ (.*) ⟫ʷ ≈ ⟪ (.*) ⟫ʷ$', re.M)
E2DEF = re.compile(r'^    (e2-\d+) : 2 ⊢ (.*) ≈ (.*)$', re.M)


def records_from_library(root):
    """Rewrite the record modules from the library Wins/*.agda and the
    two-wire equations of the current WinSig, leaving the derivations."""
    wd = os.path.join(root, 'Wins')
    lits, placed, modof = [], [], {}
    for f in sorted(os.listdir(wd)):
        if not f.endswith('.agda'): continue
        mod = f[:-5]
        for n, a, b in WINDEF.findall(io.open(os.path.join(wd, f), encoding='utf-8').read()):
            modof[n] = mod
            (lits if n.startswith('wl') else placed).append((n, a, b))
    lits.sort(); placed.sort()
    e2s = E2DEF.findall(io.open(os.path.join(root, 'WinSig.agda'), encoding='utf-8').read())
    write_records(root, lits, placed, e2s, modof)
    return len(lits), len(placed), len(e2s)


def main(root, e2s=()):
    files = modules(root)
    texts = {f: io.open(f, encoding='utf-8').read() for f in files}

    # The distinct windows, in order of first use.
    wins = {}          # key -> name
    order = {'l': [], 'p': []}
    for f in files:
        for m in STEP.finditer(texts[f]):
            kind, i, xs, ys = m.groups()
            a, b = sorted((xs, ys))
            key = (kind, i, a, b)
            if key not in wins:
                name = f'w{kind}{len(order[kind]) + 1:04d}'
                wins[key] = name
                order[kind].append(key)

    # ------------------------------------------------------------ the library
    wd = os.path.join(root, 'Wins')
    os.makedirs(wd, exist_ok=True)
    for f in os.listdir(wd):
        if f.endswith('.agda'): os.remove(os.path.join(wd, f))
    modof = {}
    libs = []
    for kind, prefix in (('l', 'WL'), ('p', 'WP')):
        groups, cur, size = [], [], 0
        for key in order[kind]:
            n = letters(key[2]) + letters(key[3])
            if cur and size + n > BUDGET:
                groups.append(cur); cur, size = [], 0
            cur.append(key); size += n
        if cur: groups.append(cur)
        for gi, group in enumerate(groups, 1):
            mod = f'{prefix}{gi:02d}'
            out = [lib_header(mod, kind)]
            for key in group:
                _, i, a, b = key
                name = wins[key]
                modof[name] = mod
                out.append(f'{name} : Complete 4 → ⟪ {a} ⟫ʷ ≈ ⟪ {b} ⟫ʷ')
                out.append(f'{name} c4 = {kind}w{i} c4 {a} {b} tt tt Eq.refl')
                out.append('')
            libs.append((mod, len(group)))
            io.open(os.path.join(wd, mod + '.agda'), 'w', encoding='utf-8', newline=NL).write(NL.join(out))

    # ------------------------------------------------------------ the records
    write_records(root,
                  [(wins[k], k[2], k[3]) for k in order['l']],
                  [(wins[k], k[2], k[3]) for k in order['p']],
                  e2s, modof)

    # ------------------------------------------------------------ the derivations
    rnames = set()
    for f in files:
        if os.path.basename(f).startswith('R'):
            rnames |= set(SIG.findall(texts[f]))
    rref = re.compile(r'\b(' + '|'.join(re.escape(n) for n in sorted(rnames, key=len, reverse=True)) + r') c4\b') \
        if rnames else None

    for f in files:
        s = texts[f]
        isR = os.path.basename(f).startswith('R')
        arg = 'c4' if isR else '(lit c4)'
        used = set()

        def rep(m):
            kind, i, xs, ys = m.groups()
            a, b = sorted((xs, ys))
            name = wins[(kind, i, a, b)]
            used.add(name)
            ref = f'{name} {arg}' if kind == 'l' else f'{name} c4'
            return f'({ref})' if (xs, ys) == (a, b) else f'(sym ({ref}))'

        s = STEP.sub(rep, s)
        if not isR and rref:
            s = rref.sub(lambda m: f'{m.group(1)} (lit c4)', s)
        s = SIG.sub(lambda m: f'{m.group(1)} : {"WsL" if isR else "Ws"} → ', s)
        s = re.sub(r'open import ' + re.escape(MOD) + r'\.Lits using \([^)]*\)\n', '', s)
        s = re.sub(r'open import ' + re.escape(MOD) + r'\.Resps using \([^)]*\)\n', '', s)
        names = (['WsL'] if isR else ['Ws', 'lit']) + sorted(used)
        s = s.replace(COMPLETE, f'open import {MOD}.WinSig using ({" ; ".join(names)})\n', 1)
        io.open(f, 'w', encoding='utf-8', newline=NL).write(s)

    # ------------------------------------------------------------ their users
    lemref = re.compile(r'\b(lem-[^\s()]+) c4\b')
    # TransportAx's parts (transport5.agda_module) are consumers too.
    tdir = os.path.join(root, 'TransportAx')
    parts = sorted('TransportAx/' + f[:-5] for f in os.listdir(tdir) if f.startswith('A') and f.endswith('.agda')) \
        if os.path.isdir(tdir) else []
    for c in CONSUMERS + parts:
        p = os.path.join(root, c + '.agda')
        s = io.open(p, encoding='utf-8').read()
        uses_l, uses_d = [False], [False]

        def rep2(m):
            if m.group(1) in rnames:
                uses_l[0] = True
                return f'{m.group(1)} (wsL c4)'
            uses_d[0] = True
            return f'{m.group(1)} (ws c4)'

        s = lemref.sub(rep2, s)
        imp = (f'open import {MOD}.WinInstL using (wsL)\n' if uses_l[0] else '') + \
              (f'open import {MOD}.WinInst using (ws)\n' if uses_d[0] else '')
        anchor = 'open import Examples.Groups.Clifford+CS.Completeness using (Complete)\n'
        assert anchor in s, c
        s = s.replace(anchor, anchor + imp, 1)
        io.open(p, 'w', encoding='utf-8', newline=NL).write(s)

    return libs, len(wins)


if __name__ == '__main__':
    if sys.argv[1] == '--records':
        print('literal, placed, two-wire:', records_from_library(sys.argv[2]))
    else:
        libs, n = main(sys.argv[1])
        print(n, 'distinct windows in', len(libs), 'modules:', ' '.join(f'{m}({k})' for m, k in libs))
