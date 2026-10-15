# Writes the Agda assembly of Lemma 8.8's K-free facts at n = 4
# (Four/Facts/*.agda): the decoded letters as blocks (Bridges), the
# canonical class facts (Classes), every instance as a transport of its
# class fact (I*), and the record `Facts` of Lemma88.KFree at m = 0.
# Run after emit.py, whose INDEX.txt names the modules of the lemmas.
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
from emit import mname, lemname, ROOT
import facts4 as F4

NL = chr(10)
INDEX = {}
for line in open(os.path.join(ROOT, 'D', 'INDEX.txt'), encoding='utf-8'):
    if line.strip():
        mod, n, name = line.rstrip(NL).split(' ', 2)
        INDEX[name] = mod

FIELD = {'p-inv': 'p-inv', "p'-inv": 'p′-inv', 'p-ord': 'p-ord', 'sq': 'sq', 'l-inv': 'l-inv',
         'h-inv': 'h-inv', 'conj2': 'conj₂', 'p-adj': 'p-adj', 'conj-up': 'conj-up',
         'conj-dn': 'conj-dn', 'braid': 'braid', 'far-pl+': 'far-pl⁺', 'far-pl-': 'far-pl⁻',
         'far-ll': 'far-ll'}
FAM = {'p': 'dPP₁', "p'": 'dPP₁′', 'l': 'lo₁', 'h': 'hi₁'}
KN = {'p': 'p', "p'": 'p′', 'l': 'l', 'h': 'h'}
SWS = ['s₀', 's₁', 's₂']; WIS = ['w₀', 'w₁', 'w₂', 'w₃']

def lst(letters): return '(' + ' ∷ '.join(mname(g) for g in letters) + ' ∷ [])' if letters else '[]'
def bools(bits): return ' '.join('true' if b else 'false' for b in bits)
def blk(b): return f'blk (xb {bools(b[0])}) {lst(b[1])}'
def op(o): return f'rel {SWS[o[1]]}' if o[0] == 'rel' else f'col {WIS[o[1]]}'
def ops(os_): return '(' + ' ∷ '.join(op(o) for o in os_) + ' ∷ [])' if os_ else '[]'
def blist(names): return '(' + ' ∷ '.join(names) + ' ∷ [])' if names else '[]'

def bname(a, kind): return f'B-{KN[kind]}-{a}'
def brname(a, kind): return f'br-{KN[kind]}-{a}'
def cname(k): return f'C-{F4.kname(k)}'

def imports_of(names):
    by = {}
    for n in names: by.setdefault(INDEX[n], set()).add(lemname(n))
    return NL.join(f'open import Examples.Groups.Clifford+CS.Four.D.{m} using ({" ; ".join(sorted(ns))})'
                   for m, ns in sorted(by.items()))

def header(mod, doc, extra=''):
    return f'''------------------------------------------------------------------------
-- Presentations of groups
--
{doc}
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

module Examples.Groups.Clifford+CS.Four.Facts.{mod} where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; s≤s ; z≤n)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.TransportTables
open import Examples.Groups.Clifford+CS.Four.Transport
{extra}'''

def write(mod, text):
    os.makedirs(os.path.join(ROOT, 'Facts'), exist_ok=True)
    open(os.path.join(ROOT, 'Facts', mod + '.agda'), 'w', encoding='utf-8', newline=NL).write(text)

# ------------------------------------------------------------ Bridges
def bridges():
    out = []
    out.append('''------------------------------------------------------------------------
-- Generic lemmas

-- The orientation and the placement respect the congruence.
mc-cong : ∀ b (L : Layout 4) {g g′ : Circuit 4} → g ≈ g′ → mc b L g ≈ mc b L g′
mc-cong false L e = back _ (back _ (front _ e))
mc-cong true  L e = back _ (back _ (front _ (back _ (front _ e))))

-- An X letter passes a line of X letters.
pass-X : ∀ v ws → ⟪ xL v ∷ map xL ws ⟫ʷ ≈ ⟪ map xL ws ++ xL v ∷ [] ⟫ʷ
pass-X v []       = refl
pass-X v (w ∷ ws) = begin
  ⟪ xL v ⟫ • ⟪ xL w ∷ map xL ws ⟫ʷ            ≈⟨ back _ (∷≈ (xL w) (map xL ws)) ⟩
  ⟪ xL v ⟫ • (⟪ xL w ⟫ • ⟪ map xL ws ⟫ʷ)      ≈⟨ sym assoc ⟩
  (⟪ xL v ⟫ • ⟪ xL w ⟫) • ⟪ map xL ws ⟫ʷ      ≈⟨ front _ (xc v w) ⟩
  (⟪ xL w ⟫ • ⟪ xL v ⟫) • ⟪ map xL ws ⟫ʷ      ≈⟨ assoc ⟩
  ⟪ xL w ⟫ • (⟪ xL v ⟫ • ⟪ map xL ws ⟫ʷ)      ≈⟨ back _ (sym (∷≈ (xL v) (map xL ws))) ⟩
  ⟪ xL w ⟫ • ⟪ xL v ∷ map xL ws ⟫ʷ            ≈⟨ back _ (pass-X v ws) ⟩
  ⟪ xL w ⟫ • ⟪ map xL ws ++ xL v ∷ [] ⟫ʷ      ≈⟨ sym (∷≈ (xL w) (map xL ws ++ xL v ∷ [])) ⟩
  ⟪ xL w ∷ map xL ws ++ xL v ∷ [] ⟫ʷ          ∎

-- A word between two copies of a line of X letters is its frame.
negs-F : ∀ ws w → ⟪ map xL ws ⟫ʷ • w • ⟪ map xL ws ⟫ʷ ≈ F⟪ map col ws ⟫ w
negs-F []       w = trans left-unit right-unit
negs-F (v ∷ ws) w = begin
  ⟪ xL v ∷ map xL ws ⟫ʷ • w • ⟪ xL v ∷ map xL ws ⟫ʷ
    ≈⟨ cong (∷≈ (xL v) (map xL ws)) (back w (trans (pass-X v ws) (++≈ (map xL ws) (xL v ∷ [])))) ⟩
  (A • B) • w • (B • A)            ≈⟨ assoc ⟩
  A • B • w • (B • A)              ≈⟨ back A (back B (sym assoc)) ⟩
  A • B • (w • B) • A              ≈⟨ back A (sym assoc) ⟩
  A • (B • (w • B)) • A            ≈⟨ back A (front A (negs-F ws w)) ⟩
  A • F⟪ map col ws ⟫ w • A        ∎
  where
  A = ⟪ xL v ⟫
  B = ⟪ map xL ws ⟫ʷ

-- The decoding's rotation in the spelling of the derivations.
G-rot-≈ : G-rot 1 ≈ ⟪ ''' + lst(F4.RMID) + ''' ⟫ʷ
G-rot-≈ = trans (by-assoc Eq.refl) lem-bridge-G-rot

------------------------------------------------------------------------
-- The decoded letters as blocks
''')
    for a in range(15):
        for kind in ('p', "p'", 'l', 'h'):
            b = F4.decoded(a, kind)
            out.append(f'{bname(a, kind)} : Blk')
            out.append(f'{bname(a, kind)} = {blk(b)}')
            out.append('')
    for a in range(15):
        for kind in ('p', "p'", 'l', 'h'):
            t, x = F4.layout(4, a)
            beta = x[t] ^ F4.FLIP[kind]
            ws = [w for w in range(4) if w != t and x[w] == 0]
            rels = [('rel', j) for j in range(t - 1, -1, -1)] + ([('col', 0)] if beta else [])
            frame = [('col', w) for w in ws] + rels
            assert frame == F4.frame(a, kind)
            mid = F4.MID[kind]; gb = 'G-pp-≈' if kind in ('p', "p'") else 'G-rot-≈'
            wl = '(' + ' ∷ '.join(WIS[w] for w in ws) + ' ∷ [])' if ws else '[]'
            out.append(f'{brname(a, kind)} : {FAM[kind]} {a} ≈ ⟪ flatB {bname(a, kind)} ⟫ʷ')
            out.append(f'{brname(a, kind)} =')
            out.append(f'  trans (mc-cong {"true" if beta else "false"} (layout□ {a}) {gb})')
            out.append(f'  (trans (by-assoc Eq.refl)')
            out.append(f'  (trans (negs-F {wl} (F⟪ {ops(rels)} ⟫ ⟪ {lst(mid)} ⟫ʷ))')
            out.append(f'         (F-blocks {ops(frame)} (blk (xb false false false false) {lst(mid)} ∷ []) tt)))')
            out.append('')
    extra = ('open import Examples.Groups.Clifford+CS.MultiControlled using (Layout ; mc ; G-pp ; G-rot)' + NL +
             'open import Examples.Groups.Clifford+CS.Decoding 0 using (layout□ ; dPP₁ ; dPP₁′ ; lo₁ ; hi₁)' + NL +
             'open import Examples.Groups.Clifford+CS.Four.Bridge using (G-pp-≈)' + NL +
             imports_of(['bridge G-rot']) + NL)
    doc = ('''-- The decoded consecutive letters at four wires as gadget blocks
--
-- A decoded letter is its gadget (the phase gadget or the rotation)
-- conjugated by the X letters of its white controls, the swaps that
-- bring its target to wire 0 and, for its orientation, X on the
-- target: so it is the canonical block carried by that frame
-- (`F-blocks`).  Generated by scratchpad/four/factsgen.py.''')
    write('Bridges', header('Bridges', doc, extra) + NL + NL.join(out) + NL)

# ------------------------------------------------------------ Classes
def classes(plan_out, facts):
    out = []; keys = set()
    for (inst, ops_, sw, fn, kl, kr) in plan_out:
        for k in list(kl) + list(kr): keys.add(k)
    for k in sorted(keys):
        out.append(f'{cname(k)} : Blk'); out.append(f'{cname(k)} = {blk(F4.cblock(k))}'); out.append('')
    cls = {}
    for i, (fn, built) in enumerate(facts.items()):
        cls[fn] = f'cls-{i}'
    seen = set()
    for (inst, ops_, sw, fn, kl, kr) in plan_out:
        if fn in seen: continue
        seen.add(fn)
        out.append(f'-- {fn}')
        out.append(f'{cls[fn]} : ⟪ flat {blist([cname(k) for k in kl])} ⟫ʷ ≈ ⟪ flat {blist([cname(k) for k in kr])} ⟫ʷ')
        out.append(f'{cls[fn]} = {lemname(facts[fn])}')
        out.append('')
    out.append('''------------------------------------------------------------------------
-- Respelling the middle words of a word of blocks

data Resp : List Blk → List Blk → Set where
  []ʳ  : Resp [] []
  same : ∀ {k ls rs} → Resp ls rs → Resp (k ∷ ls) (k ∷ rs)
  re   : ∀ {b m m′ ls rs} → ⟪ m ⟫ʷ ≈ ⟪ m′ ⟫ʷ → Resp ls rs → Resp (blk b m ∷ ls) (blk b m′ ∷ rs)

block-≈ : ∀ b {m m′} → ⟪ m ⟫ʷ ≈ ⟪ m′ ⟫ʷ → ⟪ flatB (blk b m) ⟫ʷ ≈ ⟪ flatB (blk b m′) ⟫ʷ
block-≈ b {m} {m′} e =
  trans (++≈ (Xs b) (m ++ Xs b))
  (trans (back _ (trans (++≈ m (Xs b)) (trans (front _ e) (sym (++≈ m′ (Xs b))))))
         (sym (++≈ (Xs b) (m′ ++ Xs b))))

resp : ∀ {ls rs} → Resp ls rs → ⟪ flat ls ⟫ʷ ≈ ⟪ flat rs ⟫ʷ
resp []ʳ = refl
resp (same {k} {ls} {rs} r) =
  trans (++≈ (flatB k) (flat ls)) (trans (back _ (resp r)) (sym (++≈ (flatB k) (flat rs))))
resp (re {b} {m} {m′} {ls} {rs} e r) =
  trans (++≈ (flatB (blk b m)) (flat ls))
  (trans (cong (block-≈ b e) (resp r)) (sym (++≈ (flatB (blk b m′)) (flat rs))))
''')
    extra = imports_of(list(facts.values())) + NL
    doc = ('''-- The canonical class facts of Lemma 8.8 at four wires
--
-- Every instance of the facts is carried by a transport (Four.Transport)
-- to one of these, up to the spelling of its gadgets' middle words
-- (`Resp`).  Generated by scratchpad/four/factsgen.py.''')
    write('Classes', header('Classes', doc, extra) + NL + NL.join(out) + NL)
    return cls

# ------------------------------------------------------------ instances
def side_word(a, side):
    if not side: return 'ε'
    return ' • '.join(f'{FAM[k]} {a + o}' for o, k in side)

def side_bridge(a, side):
    if not side: return 'refl'
    names = [(brname(a + o, k), bname(a + o, k)) for o, k in side]
    def go(i):
        br, b = names[i]
        if i == len(names) - 1: return br
        rest = blist([n for _, n in names[i + 1:]])
        return f'(trans (cong {br} {go(i + 1)}) (sym (++≈ (flatB {b}) (flat {rest}))))'
    return go(0)

def resp_term(Lt, Lc):
    parts = []
    for bt, bc in zip(Lt, Lc):
        assert bt[0] == bc[0]
        if tuple(bt[1]) == tuple(bc[1]): parts.append('same (')
        else:
            n = F4.respell(bt[1]); RESP_USED.add(n)
            parts.append(f're {lemname(n)} (')
    return ''.join(parts) + '[]ʳ' + ')' * len(parts)

RESP_USED = set()

def instance(entry, cls):
    (inst, ops_, sw, fn, kl, kr) = entry
    name, a, b, l, r = inst
    nm = f'i-{FIELD[name]}-{a}' + (f'-{b}' if name == 'far-ll' else '')
    Lb = blist([bname(a + o, k) for o, k in l]); Rb = blist([bname(a + o, k) for o, k in r])
    Lt = F4.TF(ops_, F4.blocks(a, l)); Rt = F4.TF(ops_, F4.blocks(a, r))
    Lc = [F4.cblock(k) for k in kl]; Rc = [F4.cblock(k) for k in kr]
    LC = blist([cname(k) for k in kl]); RC = blist([cname(k) for k in kr])
    G, GI = ops(ops_), ops(list(reversed(ops_)))
    if not sw:
        e = (f'trans (resp {{TF {G} {Lb}}} {{{LC}}} ({resp_term(Lt, Lc)}))' + NL +
             f'      (trans {cls[fn]} (sym (resp {{TF {G} {Rb}}} {{{RC}}} ({resp_term(Rt, Rc)}))))')
    else:
        e = (f'trans (resp {{TF {G} {Lb}}} {{{RC}}} ({resp_term(Lt, Rc)}))' + NL +
             f'      (trans (sym {cls[fn]}) (sym (resp {{TF {G} {Rb}}} {{{LC}}} ({resp_term(Rt, Lc)}))))')
    lines = [f'{nm} : {side_word(a, l)} ≈ {side_word(a, r)}',
             f'{nm} = trans {side_bridge(a, l)}',
             f'  (trans (transport {GI} (TF {G} {Lb}) (TF {G} {Rb}) tt tt e)',
             f'         (sym {side_bridge(a, r)}))',
             f'  where',
             f'  e : ⟪ flat (TF {G} {Lb}) ⟫ʷ ≈ ⟪ flat (TF {G} {Rb}) ⟫ʷ',
             f'  e = {e}',
             '']
    return nm, NL.join(lines)

def sucs(k, inner): return '(suc ' * k + inner + ')' * k
def sles(k, inner): return '(s≤s ' * k + inner + ')' * k

TYPES = {
    'p-inv': ('suc i < 16', 'dPP₁ i • dPP₁′ i ≈ ε', 1),
    "p'-inv": ('suc i < 16', 'dPP₁′ i • dPP₁ i ≈ ε', 1),
    'p-ord': ('suc i < 16', 'dPP₁ i ^ 4 ≈ ε', 1),
    'sq': ('suc i < 16', 'dPP₁ i • dPP₁ i ≈ lo₁ i • lo₁ i', 1),
    'l-inv': ('suc i < 16', 'lo₁ i • hi₁ i ≈ ε', 1),
    'h-inv': ('suc i < 16', 'hi₁ i • lo₁ i ≈ ε', 1),
    'conj2': ('suc i < 16', 'dPP₁ i • lo₁ i ≈ lo₁ i • dPP₁′ i', 1),
    'p-adj': ('suc (suc i) < 16', 'dPP₁ i • dPP₁ (suc i) ≈ dPP₁ (suc i) • dPP₁ i', 2),
    'conj-up': ('suc (suc i) < 16', 'dPP₁ (suc i) • lo₁ i ≈ lo₁ i • dPP₁ i • dPP₁ (suc i)', 2),
    'conj-dn': ('suc (suc i) < 16', 'dPP₁′ i • dPP₁′ (suc i) • lo₁ (suc i) ≈ lo₁ (suc i) • dPP₁′ i', 2),
    'braid': ('suc (suc i) < 16', 'lo₁ i • lo₁ (suc i) • lo₁ i ≈ lo₁ (suc i) • lo₁ i • lo₁ (suc i)', 2),
    'far-pl+': ('suc (suc (suc i)) < 16', 'dPP₁ i • lo₁ (suc (suc i)) ≈ lo₁ (suc (suc i)) • dPP₁ i', 3),
    'far-pl-': ('suc (suc (suc i)) < 16', 'dPP₁ (suc (suc i)) • lo₁ i ≈ lo₁ i • dPP₁ (suc (suc i))', 3),
}

def dispatcher(field, insts):
    bound, ty, d = TYPES[field]
    f = 'd-' + FIELD[field]
    top = 16 - d                                     # valid i: 0 .. top - 1
    lines = [f'{f} : ∀ i → {bound} → {ty}']
    for a in range(top):
        lines.append(f'{f} {a} _ = {insts[a]}')
    lines.append(f'{f} {sucs(top, "k")} {sles(16, "()")}')
    return NL.join(lines) + NL

def dispatcher_ll(insts):
    f = 'd-far-ll'
    lines = []
    for j in range(2, 15):
        g = f'{f}-{j}'
        lines.append(f'{g} : ∀ i → suc (suc i) ≤ {j} → lo₁ i • lo₁ {j} ≈ lo₁ {j} • lo₁ i')
        for a in range(j - 1): lines.append(f'{g} {a} _ = {insts[(a, j)]}')
        lines.append(f'{g} {sucs(j - 1, "k")} {sles(j, "()")}')
        lines.append('')
    lines.append(f'{f} : ∀ i j → suc j < 16 → suc (suc i) ≤ j → lo₁ i • lo₁ j ≈ lo₁ j • lo₁ i')
    lines.append(f'{f} i 0 _ ()')
    lines.append(f'{f} i 1 _ (s≤s ())')
    for j in range(2, 15): lines.append(f'{f} i {j} _ c = {f}-{j} i c')
    lines.append(f'{f} i {sucs(15, "k")} {sles(16, "()")} _')
    return NL.join(lines) + NL

GROUPS = [('I1', ['p-inv', "p'-inv", 'p-ord', 'sq', 'l-inv', 'h-inv', 'conj2']),
          ('I2', ['p-adj', 'conj-up', 'conj-dn', 'braid']),
          ('I3', ['far-pl+', 'far-pl-']),
          ('I4', ['far-ll'])]

def instances(plan_out, cls):
    for mod, fields in GROUPS:
        out = []; RESP_USED.clear()
        for field in fields:
            insts = {}
            for entry in plan_out:
                inst = entry[0]
                if inst[0] != field: continue
                nm, text = instance(entry, cls)
                out.append(text)
                insts[inst[1] if field != 'far-ll' else (inst[1], inst[2])] = nm
            out.append(dispatcher(field, insts) if field != 'far-ll' else dispatcher_ll(insts))
        extra = ('open import Examples.Groups.Clifford+CS.Decoding 0 using (dPP₁ ; dPP₁′ ; lo₁ ; hi₁)' + NL +
                 'open import Examples.Groups.Clifford+CS.Four.Facts.Bridges' + NL +
                 'open import Examples.Groups.Clifford+CS.Four.Facts.Classes' + NL +
                 imports_of(sorted(RESP_USED)) + NL)
        doc = (f'''-- Lemma 8.8's K-free facts at four wires: {", ".join(FIELD[f] for f in fields)}
--
-- Each instance is its decoded letters as blocks (Bridges), carried by
-- a transport to a canonical class fact (Classes).  Generated by
-- scratchpad/four/factsgen.py.''')
        write(mod, header(mod, doc, extra) + NL + NL.join(out))

def main():
    out, facts, resp = F4.make_all()
    bridges()
    cls = classes(out, facts)
    instances(out, cls)
    print('written', len(out), 'instances')

if __name__ == '__main__':
    main()
