------------------------------------------------------------------------
-- Presentations of groups
--
-- The Pauli-word calculus inside the Pauli presentation Γ-H ⊕^ n.
--
-- Qubit.Presentation's `conj` returns a word over the Pauli generators,
-- obtained by delogging a Pauli vector with vecToWord.  Reading such a
-- word back — stripping the ε's that vecToWord leaves for the zero
-- exponents, and the trailing image of the identity vector — is the
-- Pauli-side twin of Selinger.PauliVec, and is what the extension
-- presentation needs in order to simplify a conjugate.
--
-- Everything here lives in Γ-H ⊕^ n; nothing mentions gates except
-- through `conj`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.PauliSide where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; zero)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^'_ ; wmap ; WRel)

import Presentation.Base as PB
open import Presentation.Construct.Base using (_⋄_⋄_ ; _⊕^_)

import Examples.Groups.Cyclic.Syntactics as CyS

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥)

open import Examples.Groups.Pauli.Presentation p-2 p-prime using (Γ-H)
open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pI ; pX ; pZ ; pIₙ)
import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; conj ; genToVec ; vecToWord ; shift-gen ; shiftPauli)

open import Examples.Groups.Clifford.Qubit.Selinger.Translation
  using (X-gen ; Z-gen ; pIw-ε)
open import Examples.Groups.Clifford.Qubit.Selinger.PauliVec
  using (genToVec-X ; genToVec-Z)

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- One qubit's worth of Pauli data, as a Pauli word
--
-- Vq is the wire-0 factor of vecToWord; X-gen and Z-gen match its two
-- clauses on the nose.

Vq : Pauli1 → Word (PauliGen (₁₊ m))
Vq (a , b) = [ X-gen ]ʷ ^' toℕ a • [ Z-gen ]ʷ ^' toℕ b

Vq-X : PB._≈_ (Γ-H ⊕^ (₁₊ m)) (Vq pX) [ X-gen {m} ]ʷ
Vq-X = PB.right-unit

Vq-Z : PB._≈_ (Γ-H ⊕^ (₁₊ m)) (Vq pZ) [ Z-gen {m} ]ʷ
Vq-Z = PB.left-unit

Vq-I : PB._≈_ (Γ-H ⊕^ (₁₊ m)) (Vq pI) ε
Vq-I = PB.left-unit

------------------------------------------------------------------------
-- Shifting a Pauli word up one qubit
--
-- At one qubit and above shift-gen is inj₂, which is exactly the right
-- embedding of the n-fold direct product; below that there is nothing to
-- shift, PauliGen 0 being empty.

pauli-shift-ax : {u v : Word (PauliGen m)} →
                 (Γ-H ⊕^ m) u v →
                 (Γ-H ⊕^ (₁₊ m)) (shiftPauli u) (shiftPauli v)
pauli-shift-ax {zero} ()
pauli-shift-ax {₁₊ k} x = _⋄_⋄_.right x

pauli-shift : {u v : Word (PauliGen m)} →
              PB._≈_ (Γ-H ⊕^ m) u v →
              PB._≈_ (Γ-H ⊕^ (₁₊ m)) (shiftPauli u) (shiftPauli v)
pauli-shift PB.refl          = PB.refl
pauli-shift (PB.sym h)       = PB.sym (pauli-shift h)
pauli-shift (PB.trans h h₁)  = PB.trans (pauli-shift h) (pauli-shift h₁)
pauli-shift (PB.cong h h₁)   = PB.cong (pauli-shift h) (pauli-shift h₁)
pauli-shift PB.assoc         = PB.assoc
pauli-shift PB.left-unit     = PB.left-unit
pauli-shift PB.right-unit    = PB.right-unit
pauli-shift (PB.axiom x)     = PB.axiom (pauli-shift-ax x)

------------------------------------------------------------------------
-- Reading a vector off qubit by qubit

V-cons : (q : Pauli1) (ps : Pauli m) →
         PB._≈_ (Γ-H ⊕^ (₁₊ m)) (vecToWord (q ∷ ps))
                                (Vq q • shiftPauli (vecToWord ps))
V-cons {zero} q []       = PB.sym PB.right-unit
V-cons {₁₊ k} q (x ∷ xs) = PB.refl

-- The identity vector delogs to a nest of ε's.
V-pI : PB._≈_ (Γ-H ⊕^ m) (vecToWord (pIₙ {m})) ε
V-pI {zero}    = PB.refl
V-pI {₁₊ zero} = PB.left-unit
V-pI {₂₊ k}   =
  PB.trans (PB.cong PB.left-unit (pIw-ε (Γ-H ⊕^ (₂₊ k)) (₁₊ k) inj₂))
           PB.left-unit

-- A basis vector on wire 0 …
V-basis : (q : Pauli1) →
          PB._≈_ (Γ-H ⊕^ (₁₊ m)) (vecToWord (q ∷ pIₙ {m})) (Vq q)
V-basis {m} q =
  PB.trans (V-cons q (pIₙ {m}))
           (PB.trans (PB.cong PB.refl (pauli-shift (V-pI {m}))) PB.right-unit)

-- … and a vector supported on the bottom two wires.
V-basis₂ : (q q' : Pauli1) →
           PB._≈_ (Γ-H ⊕^ (₂₊ m)) (vecToWord (q ∷ q' ∷ pIₙ {m}))
                                  (Vq {₁₊ m} q • shiftPauli (Vq {m} q'))
V-basis₂ {m} q q' =
  PB.trans (V-cons q (q' ∷ pIₙ {m}))
           (PB.cong PB.refl (pauli-shift (V-basis {m} q')))

------------------------------------------------------------------------
-- The order relations of the Pauli generators
--
-- Γ-H = Cₚ ⋄ Cₚ ⋄ CommRel, so the X- and Z-generators of wire 0 are the
-- left and right cyclic factors; at two qubits and above one more `left`
-- selects wire 0 out of the n-fold product.

X-order : PB._≈_ (Γ-H ⊕^ (₁₊ m)) ([ X-gen {m} ]ʷ • [ X-gen {m} ]ʷ) ε
X-order {zero}  = PB.axiom (_⋄_⋄_.left CyS.order)
X-order {₁₊ k} = PB.axiom (_⋄_⋄_.left (_⋄_⋄_.left CyS.order))

Z-order : PB._≈_ (Γ-H ⊕^ (₁₊ m)) ([ Z-gen {m} ]ʷ • [ Z-gen {m} ]ʷ) ε
Z-order {zero}  = PB.axiom (_⋄_⋄_.right CyS.order)
Z-order {₁₊ k} = PB.axiom (_⋄_⋄_.left (_⋄_⋄_.right CyS.order))

------------------------------------------------------------------------
-- The conjugates that the extension presentation needs

-- H sends Z to X on wire 0.
conj-H-Z : PB._≈_ (Γ-H ⊕^ (₁₊ m))
                  (conj (gate₁ H-gate) (Z-gen {m})) [ X-gen {m} ]ʷ
conj-H-Z {m} =
  PB.trans (PB.refl' _ (Eq.cong (λ □ → vecToWord (actg (gate₁ H-gate) □))
                                (genToVec-Z {m})))
           (PB.trans (V-basis {m} pX) (Vq-X {m}))

-- CZ: X₀ ↦ X₀ Z₁, Z₀ ↦ Z₀, X₁ ↦ Z₀ X₁, Z₁ ↦ Z₁.
conj-CZ-X : PB._≈_ (Γ-H ⊕^ (₂₊ m))
                   (conj (gate₂ CZ-gate) (X-gen {₁₊ m}))
                   ([ X-gen {₁₊ m} ]ʷ • [ inj₂ (Z-gen {m}) ]ʷ)
conj-CZ-X {m} =
  PB.trans (PB.refl' _ (Eq.cong (λ □ → vecToWord (actg (gate₂ CZ-gate) □))
                                (genToVec-X {₁₊ m})))
           (PB.trans (V-basis₂ {m} pX pZ)
                     (PB.cong (Vq-X {₁₊ m}) (pauli-shift (Vq-Z {m}))))

conj-CZ-Z : PB._≈_ (Γ-H ⊕^ (₂₊ m))
                   (conj (gate₂ CZ-gate) (Z-gen {₁₊ m})) [ Z-gen {₁₊ m} ]ʷ
conj-CZ-Z {m} =
  PB.trans (PB.refl' _ (Eq.cong (λ □ → vecToWord (actg (gate₂ CZ-gate) □))
                                (genToVec-Z {₁₊ m})))
           (PB.trans (V-basis₂ {m} pZ pI)
                     (PB.trans (PB.cong (Vq-Z {₁₊ m}) (pauli-shift (Vq-I {m})))
                               PB.right-unit))

conj-CZ-X↑ : PB._≈_ (Γ-H ⊕^ (₂₊ m))
                    (conj (gate₂ CZ-gate) (inj₂ (X-gen {m})))
                    ([ Z-gen {₁₊ m} ]ʷ • [ inj₂ (X-gen {m}) ]ʷ)
conj-CZ-X↑ {m} =
  PB.trans (PB.refl' _
             (Eq.cong (λ □ → vecToWord (actg (gate₂ CZ-gate) (pI ∷ □)))
                      (genToVec-X {m})))
           (PB.trans (V-basis₂ {m} pZ pX)
                     (PB.cong (Vq-Z {₁₊ m}) (pauli-shift (Vq-X {m}))))

conj-CZ-Z↑ : PB._≈_ (Γ-H ⊕^ (₂₊ m))
                    (conj (gate₂ CZ-gate) (inj₂ (Z-gen {m})))
                    [ inj₂ (Z-gen {m}) ]ʷ
conj-CZ-Z↑ {m} =
  PB.trans (PB.refl' _
             (Eq.cong (λ □ → vecToWord (actg (gate₂ CZ-gate) (pI ∷ □)))
                      (genToVec-Z {m})))
           (PB.trans (V-basis₂ {m} pI pZ)
                     (PB.trans (PB.cong (Vq-I {₁₊ m}) (pauli-shift (Vq-Z {m})))
                               PB.left-unit))

-- Conjugating by a shifted gate is the shift of the conjugate: a gate
-- moved up one wire leaves the new wire-0 slot alone.
conj-shift : (x : Gen (₁₊ k)) (y : PauliGen (₁₊ k)) →
             PB._≈_ (Γ-H ⊕^ (₂₊ k))
                    (conj (x ↥) (inj₂ y)) (shiftPauli (conj x y))
conj-shift {k} x y =
  PB.trans (V-cons pI (actg x (genToVec y)))
           (PB.trans (PB.cong (Vq-I {₁₊ k}) PB.refl) PB.left-unit)

------------------------------------------------------------------------
-- The two products C8 and C9 need
--
-- CZ X₀ CZ = X₀ Z₁ and CZ Z₁ CZ = Z₁, so the Z₁'s square away; likewise
-- the Z₀'s in C9.

c8-pauli : PB._≈_ (Γ-H ⊕^ (₂₊ m))
                  (conj (gate₂ CZ-gate) (X-gen {₁₊ m})
                     • conj (gate₂ CZ-gate) (inj₂ (Z-gen {m})))
                  [ X-gen {₁₊ m} ]ʷ
c8-pauli {m} =
  PB.trans (PB.cong conj-CZ-X conj-CZ-Z↑)
           (PB.trans PB.assoc
                     (PB.trans (PB.cong PB.refl (pauli-shift (Z-order {m})))
                               PB.right-unit))

c9-pauli : PB._≈_ (Γ-H ⊕^ (₂₊ m))
                  (conj (gate₂ CZ-gate) (Z-gen {₁₊ m})
                     • conj (gate₂ CZ-gate) (inj₂ (X-gen {m})))
                  [ inj₂ (X-gen {m}) ]ʷ
c9-pauli {m} =
  PB.trans (PB.cong conj-CZ-Z conj-CZ-X↑)
           (PB.trans (PB.sym PB.assoc)
                     (PB.trans (PB.cong (Z-order {₁₊ m}) PB.refl) PB.left-unit))
