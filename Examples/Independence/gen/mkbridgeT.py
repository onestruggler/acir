"""Write Examples/Independence/Clifford+T/Bridge.agda: the reading of
CliffT₂'s matrices in 𝔻[ω] (from Clifford/Bridge.agda's head), and the
comparison with Bian and Selinger's 4 × 4 matrices, the gates entry by
entry."""
import re

import os
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..') + os.sep
cb = open(base + 'Clifford/Bridge.agda', encoding='utf-8').read()

# The generic part of Clifford.Bridge: digits, Φ and its laws, ⟪_⟫.
i = cb.index('------------------------------------------------------------------------\n-- Digits and bits')
j = cb.index('private\n  scale-1')
generic = cb[i:j]

# exact and its helpers (unscale, cancel, φ-^), from the tail.
k = cb.index('private\n  φ-^')
exact_part = cb[k:]

GENS = [('gate₀ ⌈ ω-gate ⌉', 'C.W'),
        ('gate₁ ⌈ H-gate ⌉', 'C.H0'),
        ('gate₁ ⌈ T-gate ⌉', 'C.T0'),
        ('gate₂ ⌈ CX-gate ⌉', 'C.H0 • C.CZ • C.H0'),
        ('gate₂ swap', 'C.Swap'),
        ('gate₀ ⌈ ω-gate ⌉ ↥', 'C.W'),
        ('gate₁ ⌈ H-gate ⌉ ↥', 'C.H1'),
        ('gate₁ ⌈ T-gate ⌉ ↥', 'C.T1'),
        ('(gate₀ ⌈ ω-gate ⌉ ↥) ↥', 'C.W')]

FIN4 = ['zero', 'suc zero', 'suc (suc zero)', 'suc (suc (suc zero))']


def fin(s):
    return s if s == 'zero' else '(' + s + ')'


head = '''------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffT₂'s matrices against the sources' on one and two qubits
--
-- Bian and Selinger's presentation of 2-qubit Clifford+T operators
-- (Examples.Groups.Clifford+T-2qubit) reads its words over W, H0, H1,
-- S0, S1, T0, T1 and CZ as 4 × 4 matrices over 𝔻[ω], in operator
-- order, through Greylyn's two-level generators; Greylyn's presentation
-- of U₂(ℤ[1/√2, i]) (Examples.Groups.Clifford+T-2qubit-TwoLevel at
-- n = 2) reads two-level words as 2 × 2 ones.  Both are complete.  The
-- decodings Dʷ (two wires: their qubit k on wire k, S as T², CZ as
-- H CNOT H on wire 0) and Dʷ₁ (one wire: ω on |1⟩ as T, on |0⟩ as
-- X T X) read their words letter for letter: every gate matrix is
-- symmetric, so reading a word in diagram order rather than operator
-- order transposes its matrix.  So bridge₂ and bridge₁ say that their
-- matrix of a word is the matrix (Real-Clifford.Semantics.Matrix's mat,
-- wire 0 the most significant bit, as their qubit 0 is) of the
-- transpose of its decoding's reading (1/√2)^h φ(M) in 𝔻[ω] (⟪_⟫, as in
-- Clifford.Bridge): their generators are compared entry by entry, by
-- evaluation on the transparent products of two-level matrices (gm),
-- and a product is a product on both sides.  The encodings ℰʷ and ℰ₁ʷ
-- send CliffT₂'s circuits to their words; Completeness reads their
-- matrices through the decoding, by Lemma 19.  Equal matrices of
-- CliffT₂ give equal readings (exact).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+T.Bridge where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥)
import Data.Empty.Irrelevant as Irr
open import Data.Fin.Base as Fin using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; s≤s ; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; RingD ; AdjointD ; isCommutativeRing-D ; adj-D ; √½ ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics as TLS
open import Examples.Groups.Real-Clifford.Presentation.DOmega using (√½-sq)
import Examples.Groups.Real-Clifford.Semantics.Interpretation as QInterp
import Examples.Groups.Real-Clifford.Semantics.Laws as QLaws
import Examples.Groups.Real-Clifford.Semantics.Matrix as QMatrix
import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra as MatrixAlgebra
open import Examples.Groups.Clifford+T-2qubit.Generator using (module Clifford+T)
import Examples.Groups.Clifford+T-2qubit.Presentation as BS

open import Examples.Independence.Clifford+T.Syntactics
import Examples.Independence.Clifford+T.Semantics as Sem
import Examples.Independence.Semantics.Qubit as O
open O using (module ZΩ ; √2)
open import Examples.Independence.Clifford.Ring using (φ ; φ-+ ; φ-* ; φ-0 ; φ-1 ; √½-√2)

module QI where
  open QLaws {A = D} {{RingD}} isCommutativeRing-D public
  open QInterp {A = D} {{RingD}} isCommutativeRing-D √½ √½-sq public
module QM = QMatrix {A = D} {{RingD}} {{AdjointD}} isCommutativeRing-D adj-D
module MA = MatrixAlgebra {A = D} {{RingD}} {{AdjointD}} isCommutativeRing-D adj-D
module C = Clifford+T

open QI.AR using (_+_ ; _*_ ; 1# ; 0# ; +-identityʳ ; *-identityˡ ; *-identityʳ ;
                  zeroˡ ; zeroʳ ; *-assoc ; *-comm)

private
  variable
    k n : ℕ

'''

mid = '''
private
  scale-1 : (M : QI.Op n) → QI.scale 1# M QI.≐ M
  scale-1 M x y = *-identityˡ (M x y)

  ^-swap : (a b : ℕ) → (√½ QI.^ a) * (√½ QI.^ b) ≡ √½ QI.^ (b +ℕ a)
  ^-swap a b = Eq.trans (*-comm _ _) (Eq.sym (QI.^-+ √½ b a))

-- The reading of a composite is the product of the readings, the
-- second gate's on the left.
⟪∙⟫ : (s t : O.Sc n) → ⟪ s O.∙ t ⟫ QI.≐ (⟪ t ⟫ QI.⊙ ⟪ s ⟫)
⟪∙⟫ (hs , Ms) (ht , Mt) = QI.≐-sym
  (QI.≐-trans (QI.scale-⊙ (√½ QI.^ ht) (√½ QI.^ hs) (Φ (O.ix Mt)) (Φ (O.ix Ms)))
  (QI.≐-trans (λ x y → Eq.cong (λ c → c * (Φ (O.ix Mt) QI.⊙ Φ (O.ix Ms)) x y) (^-swap ht hs))
  (QI.scale-cong (QI.≐-sym (QI.≐-trans (Φ-cong (O.ix-mul Mt Ms)) (Φ-⊙ (O.ix Mt) (O.ix Ms)))))))

⟪ε⟫ : ⟪ O.εs {n} ⟫ QI.≐ QI.Idₒ
⟪ε⟫ = QI.≐-trans (scale-1 _) (QI.≐-trans (Φ-cong O.ix-id) Φ-δ)

------------------------------------------------------------------------
-- Transposes

_ᵀ : QI.Op n → QI.Op n
(M ᵀ) x y = M y x

ᵀ-cong : {M N : QI.Op n} → M QI.≐ N → (M ᵀ) QI.≐ (N ᵀ)
ᵀ-cong e x y = e y x

ᵀ-⊙ : (M N : QI.Op n) → ((M QI.⊙ N) ᵀ) QI.≐ ((N ᵀ) QI.⊙ (M ᵀ))
ᵀ-⊙ M N x y = QI.Σ-cong (λ z → *-comm (M y z) (N z x))

private
  δb-sym : (x y : QI.Bits n) → QI.δb x y ≡ QI.δb y x
  δb-sym []          []          = refl
  δb-sym (true ∷ x)  (true ∷ y)  = δb-sym x y
  δb-sym (false ∷ x) (false ∷ y) = δb-sym x y
  δb-sym (true ∷ x)  (false ∷ y) = refl
  δb-sym (false ∷ x) (true ∷ y)  = refl

ᵀ-Id : ((QI.Idₒ {n}) ᵀ) QI.≐ QI.Idₒ
ᵀ-Id x y = δb-sym y x

------------------------------------------------------------------------
-- The matrix of a two-level word

-- The product of its generators' matrices: transparent, where ⟦_⟧ᵐ acts
-- through the opaque actV.
gm : {m : ℕ} → Word (TL.Gen m) → Matrix m m D
gm [ g ]ʷ  = TLS.gmat g
gm ε       = TLS.⟦ ε ⟧ᵐ
gm (u • v) = gm u ·*· gm v

⟦⟧≡gm : {m : ℕ} (u : Word (TL.Gen m)) → TLS.⟦ u ⟧ᵐ ≡ gm u
⟦⟧≡gm [ g ]ʷ  = TLS.⟦g⟧ᵐ≡ g
⟦⟧≡gm ε       = refl
⟦⟧≡gm (u • v) = Eq.trans (TLS.⟦•⟧ᵐ u v) (Eq.cong₂ _·*·_ (⟦⟧≡gm u) (⟦⟧≡gm v))

------------------------------------------------------------------------
-- Two wires: the encoding, and their words decoded

ℰ : Gen 2 → Word C.Generator
%s

-- A circuit: its gates encoded, in the same order.
ℰʷ : Circuit 2 → Word C.Generator
ℰʷ [ g ]ʷ  = ℰ g
ℰʷ ε       = ε
ℰʷ (w • v) = ℰʷ w • ℰʷ v

-- Their qubit k on wire k, S as T², CZ as H CNOT H on wire 0.
D₀ : C.Generator → Circuit 2
D₀ C.W-gen  = ω
D₀ C.H0-gen = H
D₀ C.H1-gen = H ↑
D₀ C.S0-gen = S
D₀ C.S1-gen = S ↑
D₀ C.T0-gen = T
D₀ C.T1-gen = T ↑
D₀ C.CZ-gen = H • CX • H

-- A word of theirs, letter for letter.
Dʷ : Word C.Generator → Circuit 2
Dʷ [ g ]ʷ  = D₀ g
Dʷ ε       = ε
Dʷ (w • v) = Dʷ w • Dʷ v

-- Their generators, entry by entry.
opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  entries₂ : (x : C.Generator) (r c : Fin 4) →
             MA.ent (gm (BS.tl x)) r c ≡ MA.ent (QM.mat (⟪ Sem.⟦ D₀ x ⟧ ⟫ ᵀ)) r c
%s

-- Their matrix of any word is the transpose of CliffT₂'s matrix of its
-- decoding, read in 𝔻[ω].
bridge₂ : (u : Word C.Generator) → proj₁ BS.⟦ u ⟧ ≡ QM.mat (⟪ Sem.⟦ Dʷ u ⟧ ⟫ ᵀ)
bridge₂ [ x ]ʷ  = Eq.trans (⟦⟧≡gm (BS.tl x)) (MA.mat-ext (entries₂ x))
bridge₂ ε       = Eq.sym (Eq.trans (QM.mat-≐ {n = 2} (QI.≐-trans (ᵀ-cong ⟪ε⟫) ᵀ-Id)) (QM.mat-Id {n = 2}))
bridge₂ (u • v) =
  Eq.trans (TLS.⟦•⟧ᵐ ((BS.tl ʷ) u) ((BS.tl ʷ) v))
  (Eq.trans (Eq.cong₂ _·*·_ (bridge₂ u) (bridge₂ v))
  (Eq.trans (Eq.sym (QM.mat-⊙ (⟪ Sem.⟦ Dʷ u ⟧ ⟫ ᵀ) (⟪ Sem.⟦ Dʷ v ⟧ ⟫ ᵀ)))
  (QM.mat-≐ (QI.≐-trans (QI.≐-sym (ᵀ-⊙ ⟪ Sem.⟦ Dʷ v ⟧ ⟫ ⟪ Sem.⟦ Dʷ u ⟧ ⟫))
                        (ᵀ-cong (QI.≐-sym (⟪∙⟫ Sem.⟦ Dʷ u ⟧ Sem.⟦ Dʷ v ⟧)))))))

------------------------------------------------------------------------
-- One wire: Greylyn's two-level generators on two indices

-- 1 < 1 is empty (for the refutations below).
lt11 : Fin._<_ (Fin.suc (Fin.zero {0})) (Fin.suc (Fin.zero {0})) → ⊥
lt11 (s≤s ())

01< : Fin._<_ (Fin.zero {1}) (Fin.suc (Fin.zero {0}))
01< = s≤s z≤n

ℰ₁ : Gen 1 → Word (TL.Gen 2)
ℰ₁ (gate₀ ⌈ ω-gate ⌉)    = TL.ω zero • TL.ω (suc zero)
ℰ₁ (gate₁ ⌈ H-gate ⌉)    = TL.H zero (suc zero) 01<
ℰ₁ (gate₁ ⌈ T-gate ⌉)    = TL.ω (suc zero)
ℰ₁ (gate₀ ⌈ ω-gate ⌉ ↥)  = TL.ω zero • TL.ω (suc zero)

ℰ₁ʷ : Circuit 1 → Word (TL.Gen 2)
ℰ₁ʷ [ g ]ʷ  = ℰ₁ g
ℰ₁ʷ ε       = ε
ℰ₁ʷ (w • v) = ℰ₁ʷ w • ℰ₁ʷ v

-- ω on |1⟩ is T, ω on |0⟩ is X T X; X and H are themselves.
D₁ : TL.Gen 2 → Circuit 1
D₁ (TL.X-gen _ _ _)      = X
D₁ (TL.K-gen _ _ _)      = H
D₁ (TL.i-gen zero)       = X • T • X
D₁ (TL.i-gen (suc zero)) = T

Dʷ₁ : Word (TL.Gen 2) → Circuit 1
Dʷ₁ [ g ]ʷ  = D₁ g
Dʷ₁ ε       = ε
Dʷ₁ (w • v) = Dʷ₁ w • Dʷ₁ v

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  entries₁ : (y : TL.Gen 2) (r c : Fin 2) →
             MA.ent (TLS.gmat y) r c ≡ MA.ent (QM.mat (⟪ Sem.⟦ D₁ y ⟧ ⟫ ᵀ)) r c
%s

bridge₁ : (u : Word (TL.Gen 2)) → TLS.⟦ u ⟧ᵐ ≡ QM.mat (⟪ Sem.⟦ Dʷ₁ u ⟧ ⟫ ᵀ)
bridge₁ [ y ]ʷ  = Eq.trans (TLS.⟦g⟧ᵐ≡ y) (MA.mat-ext (entries₁ y))
bridge₁ ε       = Eq.sym (Eq.trans (QM.mat-≐ {n = 1} (QI.≐-trans (ᵀ-cong ⟪ε⟫) ᵀ-Id)) (QM.mat-Id {n = 1}))
bridge₁ (u • v) =
  Eq.trans (TLS.⟦•⟧ᵐ u v)
  (Eq.trans (Eq.cong₂ _·*·_ (bridge₁ u) (bridge₁ v))
  (Eq.trans (Eq.sym (QM.mat-⊙ (⟪ Sem.⟦ Dʷ₁ u ⟧ ⟫ ᵀ) (⟪ Sem.⟦ Dʷ₁ v ⟧ ⟫ ᵀ)))
  (QM.mat-≐ (QI.≐-trans (QI.≐-sym (ᵀ-⊙ ⟪ Sem.⟦ Dʷ₁ v ⟧ ⟫ ⟪ Sem.⟦ Dʷ₁ u ⟧ ⟫))
                        (ᵀ-cong (QI.≐-sym (⟪∙⟫ Sem.⟦ Dʷ₁ u ⟧ Sem.⟦ Dʷ₁ v ⟧)))))))

------------------------------------------------------------------------
-- Equal matrices, equal readings

'''

enc = '\n'.join('ℰ (%s) = %s' % (g, e) for g, e in GENS)
SRC = ['C.W-gen', 'C.H0-gen', 'C.H1-gen', 'C.S0-gen', 'C.S1-gen', 'C.T0-gen', 'C.T1-gen', 'C.CZ-gen']
clauses2 = []
for x in SRC:
    for r in FIN4:
        for c in FIN4:
            clauses2.append('  entries₂ %s %s %s = refl' % (x, fin(r), fin(c)))
FIN2 = ['zero', 'suc zero']
clauses1 = []
for y in ['TL.X-gen zero (suc zero) _', 'TL.K-gen zero (suc zero) _',
          'TL.i-gen zero', 'TL.i-gen (suc zero)']:
    for r in FIN2:
        for c in FIN2:
            clauses1.append('  entries₁ (%s) %s %s = refl' % (y, fin(r), fin(c)))
# The other index pairs are not a < b.
for k in ['X', 'K']:
    clauses1.append('  entries₁ (TL.%s-gen zero zero ()) _ _' % k)
    clauses1.append('  entries₁ (TL.%s-gen (suc zero) zero ()) _ _' % k)
    clauses1.append('  entries₁ (TL.%s-gen (suc zero) (suc zero) p) _ _ = Irr.⊥-elim (lt11 p)' % k)

out = head + generic + mid % (enc, '\n'.join(clauses2), '\n'.join(clauses1)) + exact_part
out = out.replace('open O.Circuits Sem.val using (module Exact)',
                  'open O.Circuits Sem.val using (module Exact)')
open(base + 'Clifford+T/Bridge.agda', 'w', encoding='utf-8').write(out)
print('ok', len(clauses2), len(clauses1))
