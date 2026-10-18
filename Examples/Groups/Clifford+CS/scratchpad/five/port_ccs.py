# Port v-office's five-wire derivations into a checkout of branch
# clifford-cs, so that its five-wire theory gets λ(ck-tct) as a theorem:
#   FiveV/   v-office's Five tree (Chain, Lines, Letters, Lits, Resps, Win,
#            F2, F1Low, TR2, Transport, Weakening, D/*), module names
#            Five.* -> FiveV.*, over FiveV.Rules = Syntactics and AX only
#            (v-office's Five.Rules without the control schema, which the
#            derivations do not use) -- so the proof cannot use λ-ck-tct;
#   Five/CKTDerived.agda   the embedding of FiveV.Rules' theory into
#            Five.Rules' (old ↦ old, ax ↦ ax) and `ck-tct`, the instance
#            Five.TransportAx.Base.Inst (srel ck-tct) that Five.MissingInst
#            now takes from the rule λ-ck-tct.
#   python3 port_ccs.py SRC_CLIFFORD_CS_DIR DEST_CLIFFORD_CS_DIR
import sys, os, io, re, shutil
SRC = sys.argv[1]      # v-office's Examples/Groups/Clifford+CS
DST = sys.argv[2]      # clifford-cs's Examples/Groups/Clifford+CS
NL = '\n'
TOP = ['Rules', 'Weakening', 'Chain', 'Lines', 'Letters', 'Lits', 'Resps', 'Win', 'F2', 'F1Low', 'TR2', 'Transport',
       'WinSig', 'WinInst', 'WinInstL']


def ren(s):
    return s.replace('Examples.Groups.Clifford+CS.Five.', 'Examples.Groups.Clifford+CS.FiveV.')


os.makedirs(os.path.join(DST, 'FiveV', 'D'), exist_ok=True)
for m in TOP:
    s = io.open(os.path.join(SRC, 'Five', m + '.agda'), encoding='utf-8').read()
    s = ren(s)
    if m == 'Rules':
        s = re.sub(r'\n  -- The control schema, k \+ 1 controls on the top wires\.\n(  ctl-[^\n]*\n)+', '\n', s)
        s = s.replace('open import Examples.Groups.Clifford+CS.Lambda using (λ¹ᵏ)\n', '')
        s = s.replace('-- The rules on five wires and more', '-- The rules on five wires and more: Syntactics and AX (v-office)')
        assert 'ctl-' not in s, 'schema left in Rules'
    assert 'ctl-' not in s or m == 'Weakening', (m, 'uses the schema')
    io.open(os.path.join(DST, 'FiveV', m + '.agda'), 'w', encoding='utf-8', newline=NL).write(s)
n = 0
os.makedirs(os.path.join(DST, 'FiveV', 'Wins'), exist_ok=True)
for f in sorted(os.listdir(os.path.join(SRC, 'Five', 'Wins'))):
    s = io.open(os.path.join(SRC, 'Five', 'Wins', f), encoding='utf-8').read()
    io.open(os.path.join(DST, 'FiveV', 'Wins', f), 'w', encoding='utf-8', newline=NL).write(ren(s))
for f in sorted(os.listdir(os.path.join(SRC, 'Five', 'D'))):
    if not (f.endswith('.agda') or f == 'INDEX.txt'):
        continue
    s = io.open(os.path.join(SRC, 'Five', 'D', f), encoding='utf-8').read()
    assert 'ctl-' not in s, f
    io.open(os.path.join(DST, 'FiveV', 'D', f), 'w', encoding='utf-8', newline=NL).write(ren(s))
    n += 1

# where F1-ck-tct@0 is
mod = None
for line in io.open(os.path.join(SRC, 'Five', 'D', 'INDEX.txt'), encoding='utf-8'):
    p = line.split()
    if len(p) >= 3 and ' '.join(p[2:]) == 'F1-ck-tct@0':
        mod = p[0]
assert mod

bridge = f'''------------------------------------------------------------------------
-- Presentations of groups
--
-- λ(ck-tct) derived on five wires
--
-- Branch v-office's derivation of the controlled ck-tct (its
-- scratchpad/joint/ckt2.py: the joint paper's Proposition three, by
-- de-borrowing over transported two-wire equations, of the rule as
-- Syntactics states it) lives in FiveV/, over FiveV.Rules — the rules of
-- Syntactics and AX, nothing else — so it does not use the rule
-- λ-ck-tct.  Its theory embeds in Five.Rules' (`emb`), and so the
-- instance of Five.TransportAx.Base that Five.MissingInst takes from
-- λ-ck-tct is a theorem given completeness on four wires
-- (`ck-tct-derived`).
-- Written by v-office's scratchpad/five/port_ccs.py.
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

module Examples.Groups.Clifford+CS.Five.CKTDerived where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (Word)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Rules
open import Examples.Groups.Clifford+CS.Five.Chain using (_≈_ ; trans ; by-assoc)
open import Examples.Groups.Clifford+CS.Five.TransportAx.Base using (Inst)
import Examples.Groups.Clifford+CS.FiveV.Rules as V
import Examples.Groups.Clifford+CS.FiveV.D.{mod} as VD
open import Examples.Groups.Clifford+CS.FiveV.WinInst using (ws)

private
  variable
    n : ℕ
    w v : Word (Gen n)

-- FiveV's theory is a part of this one.
emb-rel : n V.XRel, w === v → n XRel, w === v
emb-rel (V.old r) = old r
emb-rel V.ax      = ax

emb-ax : n V.XVRel, w === v → n XVRel, w === v
emb-ax (V.srelₓ r)     = srelₓ (emb-rel r)
emb-ax (V.cong↑ₓ a)    = cong↑ₓ (emb-ax a)
emb-ax (V.comm₁ₓ h g)  = comm₁ₓ h g
emb-ax (V.comm₂ₓ h g)  = comm₂ₓ h g
emb-ax (V.ω↑=ωₓ h)     = ω↑=ωₓ h

emb : n V.⊢ₓ w ≈ v → n ⊢ₓ w ≈ v
emb PB.refl          = PB.refl
emb (PB.sym e)       = PB.sym (emb e)
emb (PB.trans e e′)  = PB.trans (emb e) (emb e′)
emb (PB.cong e e′)   = PB.cong (emb e) (emb e′)
emb PB.assoc         = PB.assoc
emb PB.left-unit     = PB.left-unit
emb PB.right-unit    = PB.right-unit
emb (PB.axiom a)     = PB.axiom (emb-ax a)

-- λ(ck-tct), in the form Five.MissingInst gives it.
ck-tct-derived : Complete 4 → Inst (srel ck-tct)
ck-tct-derived c4 = trans (by-assoc Eq.refl) (trans (emb (VD.lem-F1-ck-tctat0 (ws c4))) (by-assoc Eq.refl))
'''
io.open(os.path.join(DST, 'Five', 'CKTDerived.agda'), 'w', encoding='utf-8', newline=NL).write(bridge)
print(f'FiveV: {len(TOP)} modules and {n} files of D/; F1-ck-tct@0 in {mod}; Five/CKTDerived.agda written')
