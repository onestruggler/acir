#!/usr/bin/env python3
"""Write the A16 tower's levels as certificates (Presentation/Certificate),
under NaturalP/FourWire/Classical/A16/:

    L<k>/Base.agda      the kit (as emit16.py), and the norm decision
    L<k>/Cert<i>.agda   the derivation, as data, in blocks
    L<k>.agda           the supplied equations, the targets (one per
                        table entry), `ok : certify cert ts ≡ true` by
                        one evaluation, and the table read off them

A level checked this way loads no interfaces but its kit, its data, the
level below and the extras it cites, where the chunked derivations of
emit16.py loaded every earlier chunk for each chunk.

    python3 -B emitcert16.py [k ...]      (default: every level)
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import tower4 as T
import pipe16 as P16
from emit_gamma4 import AG
from emit16 import HEADER, MOD, ROOT, fin, lst, ax_eqn

BLOCK = 250           # facts per definition
PER_MODULE = 4000     # facts per data module


def emit_base(tag, lev):
    k = lev.k
    K = f'{tag}.L{k}'
    D = ROOT / tag / f'L{k}'
    D.mkdir(parents=True, exist_ok=True)
    letters, below = lev.letters, lev.below
    lower = below.letters if below else []
    nX, nB = len(letters), len(lower)
    base = [HEADER.format(title=f'The four-wire classical tower, level {k}: the kit.'),
            f'module {MOD}.{K}.Base where\n',
            'open import Data.Fin.Base using (Fin)',
            'open import Data.List.Base using (List ; map)',
            'open import Data.Vec.Base using (_∷_ ; [] ; lookup)',
            'open import Relation.Binary.PropositionalEquality using (_≡_)',
            'open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)',
            'import Presentation.Base as PB',
            f'open import {MOD}.Pure',
            f'import {MOD}.EqP as EqP', '',
            f'ιX : Fin {nX} → L',
            f'ιX = lookup ({lst(AG[g] for g in letters)})', '']
    if below:
        base += [f'ιB : Fin {nB} → L',
                 f'ιB = lookup ({lst(AG[g] for g in lower)})', '',
                 f'import {MOD}.{tag}.L{below.k} as Below', '',
                 f'open import {MOD}.LevelKit ιX ιB Below.complete public',
                 'open EqP.Norm ιB Below.complete public using (normOK ; normOK-sound)']
    else:
        base += ['ιB : Fin 0 → L', 'ιB ()', '',
                 'private',
                 '  F0 : Word (Fin 0) → Word L',
                 '  F0 = (λ b → [ ιB b ]ʷ) ʷ', '',
                 '  zero′ : ∀ l → F0 l ≈ ε',
                 '  zero′ [ () ]ʷ',
                 '  zero′ ε       = PB.refl',
                 '  zero′ (u • v) = PB.trans (PB.cong (zero′ u) (zero′ v)) PB.left-unit', '',
                 '  lower : ∀ (l m : Word (Fin 0)) → sp (F0 l) ≡ sp (F0 m) → F0 l ≈ F0 m',
                 '  lower l m _ = PB.trans (zero′ l) (PB.sym (zero′ m))', '',
                 f'open import {MOD}.LevelKit ιX ιB lower public',
                 'open EqP.Norm ιB lower public using (normOK ; normOK-sound)']
    (D / 'Base.agda').write_text('\n'.join(base) + '\n', encoding='utf-8')


def emit_level(tag, lev):
    k = lev.k
    K = f'{tag}.L{k}'
    D = ROOT / tag / f'L{k}'
    for old in D.glob('Facts*.agda'):
        old.unlink()
    for old in D.glob('Cert*.agda'):
        old.unlink()
    emit_base(tag, lev)
    tc, letters, below = lev.tc, lev.letters, lev.below
    lower = below.letters if below else []
    nX, nB, ck = len(letters), len(lower), len(lev.live)
    roots = [f for (_, _, f) in lev.table.values()]
    cl = sorted(P16.closure(tc, roots))
    num = {f: i for i, f in enumerate(cl)}
    nax = len(tc.axioms)

    def src(kind, key):
        if kind == 'ax':
            return f'ax {key}'
        if kind == 'inv':
            return f'ax {nax + key}'
        if kind == 'fact':
            return f'fact {num[key]}'
        raise ValueError(kind)

    def factc(f):
        fact = tc.facts[f]
        st = fact.steps
        if len(st) == 1 and st[0][1][0] == 'norm':
            lab, nf = st[0][1][1]
            return (f'norm ({lst(fin(lower.index(x)) for x in lab)}) '
                    f'({lst(fin(lower.index(x)) for x in nf)})')
        steps = lst(f'st {p} ({src(kk, key)}) {"true" if fw else "false"}' for p, (kk, key), fw in st)
        return (f'steps ({lst(AG[letters[y]] for y in fact.lhs)}) '
                f'({lst(AG[letters[y]] for y in fact.rhs)}) ({steps})')

    facts = [factc(f) for f in cl]
    blocks = [facts[i:i + BLOCK] for i in range(0, len(facts), BLOCK)]
    per = PER_MODULE // BLOCK
    mods = [list(range(i, min(i + per, len(blocks)))) for i in range(0, len(blocks), per)]
    cert_head = ['open import Data.Bool.Base using (true ; false)',
                 'open import Data.Fin using (#_)',
                 'open import Data.Fin.Base using (Fin)',
                 'open import Data.List.Base using (List ; [] ; _∷_)',
                 f'open import {MOD}.Gamma using (L ; _Γ_ ; eqL ; eqL-sound ; {" ; ".join(AG)})',
                 'open import Presentation.Certificate _Γ_ eqL eqL-sound using (FactC ; norm ; steps ; st ; fact ; ax)', '']
    for mi, bs in enumerate(mods):
        out = [HEADER.format(title=f'The four-wire classical tower, level {k}: its derivation as data, part {mi}.'),
               f'module {MOD}.{K}.Cert{mi} where\n'] + cert_head
        for b in bs:
            out.append(f'b{b} : List (FactC (Fin {nB}))')
            out.append(f'b{b} =')
            for x in blocks[b]:
                out.append(f'  {x} ∷')
            out.append('  []\n')
        (D / f'Cert{mi}.agda').write_text('\n'.join(out) + '\n', encoding='utf-8')

    # the level: supplied equations, targets, the check, the table
    used = sorted({a.name for a in tc.axioms if a.name[0] == 'e'}, key=lambda n: int(n[1:]))
    out = [HEADER.format(title=f'The four-wire classical tower, level {k}: its table, checked as a certificate, '
                               f'and completeness.'),
           f'module {MOD}.{K} where\n',
           'open import Data.Bool.Base using (Bool ; true ; false)',
           'open import Data.Fin.Base using (Fin)',
           'open import Data.Fin using (#_)',
           'open import Data.List.Base using (List ; [] ; _∷_ ; _++_)',
           'open import Data.Maybe.Base using (Maybe ; just ; nothing)',
           'open import Data.Nat.Base using (ℕ ; zero ; suc)',
           'open import Data.Product.Base using (_×_ ; _,_)',
           'open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup)',
           'open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)',
           'open import Word.Base using (Word ; [_]ʷ ; _ʷ)',
           f'open import {MOD}.Pure',
           'open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound ; eqF)',
           f'open import {MOD}.{K}.Base',
           'import Presentation.Certificate _Γ_ eqL eqL-sound as C']
    out += [f'open import {MOD}.{K}.Cert{mi}' for mi in range(len(mods))]
    out += [f'open import {MOD}.Extras.{u.upper()} using ({u})' for u in used]
    out.append('')
    axl = [ax_eqn(a.name) for a in tc.axioms] + [f'inv⁼ {AG[letters[y]]}' for y in range(nX)]
    out += ['axL : List Eqn', 'axL =']
    out += [f'  ({e}) ∷' for e in axl]
    out += ['  []\n',
            'nth : List Eqn → ℕ → Maybe Eqn',
            'nth []       _       = nothing',
            'nth (e ∷ es) zero    = just e',
            'nth (e ∷ es) (suc i) = nth es i\n',
            'open C.Checker ιB normOK normOK-sound (nth axL)\n',
            f'cert : List (C.FactC (Fin {nB}))',
            'cert = ' + ' ++ ('.join(f'b{b}' for b in range(len(blocks))) + ' ++ []' + ')' * (len(blocks) - 1) + '\n']
    ents = []
    for c in range(ck):
        for y in range(nX):
            lab, d, f = lev.table[(c, y)]
            fact = tc.facts[f]
            ents.append(f'({num[f]} , ({lst(AG[letters[x]] for x in fact.lhs)}) , '
                        f'({lst(AG[letters[x]] for x in fact.rhs)}))')
    out += ['ts : List Target', 'ts =']
    out += [f'  {e} ∷' for e in ents]
    out += ['  []\n',
            'ok : certify cert ts ≡ true',
            'ok = refl\n',
            'proofs : AllEq ts',
            'proofs = certify-sound cert ts ok\n']
    out.append(f'repL : Vec (List (Fin {nX})) {ck}')
    out.append('repL =')
    for c in range(ck):
        out.append(f'  ({lst(fin(letters.index(x)) for x in lev.reps[c])}) ∷')
    out.append('  []\n')
    out.append(f'tab : Vec (Vec (List (Fin {nB}) × Fin {ck}) {nX}) {ck}')
    out.append('tab =')
    for c in range(ck):
        row = []
        for y in range(nX):
            lab, d, f = lev.table[(c, y)]
            row.append(f'(({lst(fin(lower.index(x)) for x in lab)}) , {fin(d)})')
        out.append('  (' + ' ∷ '.join(row) + ' ∷ []) ∷')
    out.append('  []\n')
    out.append(f'factT : Vec (Vec Eqn {nX}) {ck}')
    out.append('factT =')
    for c in range(ck):
        out.append('  (' + ' ∷ '.join(f'target ts proofs {c * nX + y}' for y in range(nX)) + ' ∷ []) ∷')
    out.append('  []\n')
    kind = lev.kind
    if kind[0] == 'point':
        p = kind[1]
        out.append(f'open import {MOD}.Stab (# {p}) using (ψ ; fixes ; ψ-mul ; eqV)\n')
        out.append('ψ-letter : ∀ b g → ψ (mul (spL (ιB b)) g) ≡ ψ g')
        out.append(f'ψ-letter b = ψ-mul (ιB b) (allFin-sound {nB} (λ b → fixes (ιB b)) refl b)\n')
        inv = lambda g: ['true' if g[x] == p else 'false' for x in range(16)]
        out.append(f'cosets : List (Vec Bool 16 × Fin {ck})')
        out.append('cosets =')
        for c in range(ck):
            out.append(f'  (({lst(inv(lev.repsp[c]))}) , {fin(c)}) ∷')
        out.append('  []\n')
        out.append('open Table repL tab factT ψ ψ-letter eqV cosets (# 0) refl')
    elif kind[0] == 'pair':
        p, q = kind[1], kind[2]
        out.append(f'open import {MOD}.Stab (# 0) using (eqV)')
        out.append(f'open import {MOD}.StabPair (# {p}) (# {q}) using (ψ ; keeps ; ψ-mul)\n')
        out.append('ψ-letter : ∀ b g → ψ (mul (spL (ιB b)) g) ≡ ψ g')
        out.append(f'ψ-letter b = ψ-mul (ιB b) (allFin-sound {nB} (λ b → keeps (ιB b)) refl b)\n')
        inv = lambda g: ['true' if g[x] in (p, q) else 'false' for x in range(16)]
        out.append(f'cosets : List (Vec Bool 16 × Fin {ck})')
        out.append('cosets =')
        for c in range(ck):
            out.append(f'  (({lst(inv(lev.repsp[c]))}) , {fin(c)}) ∷')
        out.append('  []\n')
        out.append('open Table repL tab factT ψ ψ-letter eqV cosets (# 0) refl')
    elif kind[0] == 'colour':
        col = kind[1]
        out.append(f'open import {MOD}.StabCol (lookup ({lst(fin(c) for c in col)})) using (ψ ; keeps ; ψ-mul ; eqC)\n')
        out.append('ψ-letter : ∀ b g → ψ (mul (spL (ιB b)) g) ≡ ψ g')
        out.append(f'ψ-letter b = ψ-mul (ιB b) (allFin-sound {nB} (λ b → keeps (ιB b)) refl b)\n')
        out.append(f'cosets : List (Vec (Fin 16) 16 × Fin {ck})')
        out.append('cosets =')
        for c in range(ck):
            out.append(f'  (({lst(fin(col[lev.repsp[c][x]]) for x in range(16))}) , {fin(c)}) ∷')
        out.append('  []\n')
        out.append('open Table repL tab factT ψ ψ-letter eqC cosets (# 0) refl')
    else:
        out.append('eqP : P → P → Bool')
        out.append('eqP u v = allFin 16 (λ i → eqF (lookup u i) (lookup v i))\n')
        out.append(f'cosets : List (P × Fin {ck})')
        out.append('cosets =')
        for c in range(ck):
            out.append(f'  (({lst(fin(x) for x in lev.repsp[c])}) , {fin(c)}) ∷')
        out.append('  []\n')
        out.append('open Table repL tab factT (λ g → g) (λ ()) eqP cosets (# 0) refl')
    out.append('open Checked refl refl using () renaming (complete to complete′)\n')
    out.append('-- A plain definition, for the level above (see emit16.py).')
    out.append(f'complete : ∀ (l m : Word (Fin {nX})) → sp (((λ x → [ ιX x ]ʷ) ʷ) l) ≡ sp (((λ x → [ ιX x ]ʷ) ʷ) m) →')
    out.append('           ((λ x → [ ιX x ]ʷ) ʷ) l ≈ ((λ x → [ ιX x ]ʷ) ʷ) m')
    out.append('complete = complete′')
    (ROOT / tag / f'L{k}.agda').write_text('\n'.join(out) + '\n', encoding='utf-8')
    print(f'{tag} level {k}: {len(cl)} facts in {len(blocks)} blocks, {len(mods)} data modules, {ck} cosets',
          flush=True)


def main():
    which = {int(a) for a in sys.argv[1:]}
    rels = P16.named_relators([('a', HERE / 'aff4extra.txt'), ('e', HERE / 'tower16extra.txt')])
    levels = P16.build(P16.a16_spec(), rels)
    for lev in levels:
        if not which or lev.k in which:
            emit_level('A16', lev)


if __name__ == '__main__':
    main()
