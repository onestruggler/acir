# Writes Wide/Weaken.agda: for each small width k, an equation of the
# five-wire theory (Five.Rules, any width) between k-wire circuits holds
# with r idle wires on top (`wk k`), and so placed by any network
# (`placed k`); and a closed equation on k wires decided by its matrices
# given completeness there (`closed k`).  The widths are concrete because
# `top (w ↓ᵏ r)` and `w ↓ᵏ suc r` have the same type only when k is.
#   python3 gen_weaken.py
import os
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(os.path.dirname(HERE)), 'Wide', 'Weaken.agda')
NL = '\n'
SUB = '₀₁₂₃₄₅₆₇₈₉'
K = 8

head = '''------------------------------------------------------------------------
-- Presentations of groups
--
-- Closed equations on a few wires, widened and placed
--
-- For each small width k: an equation of Five.Rules' theory between
-- circuits on k wires holds with r idle wires on top (`wkᵏ`, from
-- Five.Weakening's one wire at a time: `top (w ↓ᵏ r)` is `w ↓ᵏ suc r`),
-- so it holds placed by any network (`placedᵏ`); and an equation of
-- closed circuits on k wires with the same matrix holds given
-- completeness on k wires (`closedᵏ`).  The widths are numerals because
-- the two sides of `top (w ↓ᵏ r) ≡ w ↓ᵏ suc r` have one type only when k
-- is one.  Written by scratchpad/wide/gen_weaken.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Wide.Weaken where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (_↧ ; top)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Same ; same-sem)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_ ; embed)
open import Examples.Groups.Clifford+CS.Five.Weakening using (top-congₓ)
'''


def gens(k):
    out = ['gate₀ h']
    if k >= 1:
        out.append('gate₁ h')
    if k >= 2:
        out.append('gate₂ h')
    return out


body = []
for k in range(K):
    s = SUB[k]
    body.append('')
    body.append('-' * 72)
    body.append(f'-- {k} wire{"s" if k != 1 else ""}')
    body.append('')
    body.append('private')
    body.append(f'  tg{s} : ∀ r (g : Gen {k}) → (g ↧ᵏ r) ↧ ≡ g ↧ᵏ suc r')
    for g in gens(k):
        body.append(f'  tg{s} r ({g}) = Eq.refl')
    if k >= 1:
        body.append(f'  tg{s} r (g ↥) = Eq.cong _↥ (tg{SUB[k - 1]} r g)')
    body.append('')
    body.append(f'  zg{s} : (g : Gen {k}) → g ↧ᵏ 0 ≡ g')
    for g in gens(k):
        body.append(f'  zg{s} ({g}) = Eq.refl')
    if k >= 1:
        body.append(f'  zg{s} (g ↥) = Eq.cong _↥ (zg{SUB[k - 1]} g)')
    body.append('')
    body.append(f'  tw{s} : ∀ r (w : Circuit {k}) → top (w ↓ᵏ r) ≡ w ↓ᵏ suc r')
    body.append(f'  tw{s} r [ g ]ʷ  = Eq.cong [_]ʷ (tg{s} r g)')
    body.append(f'  tw{s} r ε       = Eq.refl')
    body.append(f'  tw{s} r (u • v) = Eq.cong₂ _•_ (tw{s} r u) (tw{s} r v)')
    body.append('')
    body.append(f'  zw{s} : (w : Circuit {k}) → w ↓ᵏ 0 ≡ w')
    body.append(f'  zw{s} [ g ]ʷ  = Eq.cong [_]ʷ (zg{s} g)')
    body.append(f'  zw{s} ε       = Eq.refl')
    body.append(f'  zw{s} (u • v) = Eq.cong₂ _•_ (zw{s} u) (zw{s} v)')
    body.append('')
    body.append(f'wk{s} : ∀ r {{u v : Circuit {k}}} → {k} ⊢ₓ u ≈ v → ({k} +ℕ r) ⊢ₓ u ↓ᵏ r ≈ v ↓ᵏ r')
    body.append(f'wk{s} zero    {{u}} {{v}} e = Eq.subst₂ ({k} ⊢ₓ_≈_) (Eq.sym (zw{s} u)) (Eq.sym (zw{s} v)) e')
    body.append(f'wk{s} (suc r) {{u}} {{v}} e = Eq.subst₂ (_ ⊢ₓ_≈_) (tw{s} r u) (tw{s} r v) (top-congₓ (wk{s} r e))')
    body.append('')
    body.append(f'placed{s} : ∀ r (τ : Word (S.Gen ({k} +ℕ r))) {{u v : Circuit {k}}} → {k} ⊢ₓ u ≈ v →')
    body.append(f'          ({k} +ℕ r) ⊢ₓ pl τ (u ↓ᵏ r) ≈ pl τ (v ↓ᵏ r)')
    body.append(f'placed{s} r τ e = PB.cong PB.refl (PB.cong (wk{s} r e) PB.refl)')
    body.append('')
    body.append(f'closed{s} : Complete {k} → (u v : Circuit {k}) → Same u v → {k} ⊢ₓ u ≈ v')
    body.append(f'closed{s} c u v e = embed (c (same-sem u v e))')

with open(OUT, 'w', encoding='utf-8', newline=NL) as f:
    f.write(head + NL.join(body) + NL)
print('Wide/Weaken.agda written')
