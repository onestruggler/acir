------------------------------------------------------------------------
-- Presentations of groups
--
-- Translating Pauli vectors into Figure-8 gate words.
--
-- Qubit.Presentation records a Pauli element twice over: as a vector
-- (Pauli n, the semantic form the symplectic action actg acts on) and as
-- a word over the Pauli generators (the syntactic form conj returns).
-- Qubit.Selinger.Translation sends the latter to gate words with Pw.
-- This module is the calculus of the composite
--
--     Pauli n  --vecToWord-->  Word (PauliGen n)  --Pw-->  Word (Gen n),
--
-- inside Selinger's Figure 8 modulo the global scalar.  Everything is
-- one lemma: a vector is read off qubit by qubit (Pw-cons), so a basis
-- vector becomes a single X or Z on its wire and the identity vector
-- becomes ε.
--
-- Also here: the view `pview` splitting a Pauli generator into
-- "X on wire 0", "Z on wire 0" and "something above wire 0", used to
-- drive the induction in Qubit.Selinger.Conjugation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.PauliVec where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; zero)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^'_ ; _ʷ ; wmap)

import Presentation.Base as PB

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥ ; _↑)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z ; _CRel,_===_ ; lemma-cong↑)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; Z₀ ; genToVec ; vecToWord)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pI ; pX ; pZ ; pIₙ)
import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg)

open import Examples.Groups.Clifford.Qubit.Selinger.Translation
  using (pauliGen→word ; Pw ; Pw-↑ ; X-gen ; Z-gen)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- One qubit's worth of Pauli data, as a gate word
--
-- The exponent vector (a , b) on a single wire becomes Xᵃ Zᵇ there; this
-- is the image under Pw of the corresponding factor of vecToWord.

Pq : Pauli1 → Word (Gen (₁₊ n))
Pq (a , b) = X ^' toℕ a • Z ^' toℕ b

-- The three basis values, with their ε's stripped.

Pq-X : PB._≈_ ((₁₊ n) CRel,_===_) (Pq pX) X
Pq-X = PB.right-unit

Pq-Z : PB._≈_ ((₁₊ n) CRel,_===_) (Pq pZ) Z
Pq-Z = PB.left-unit

Pq-I : PB._≈_ ((₁₊ n) CRel,_===_) (Pq pI) ε
Pq-I = PB.left-unit

-- The one non-basis value that occurs: S sends X to XZ.

Pq-XZ : PB._≈_ ((₁₊ n) CRel,_===_) (Pq (₁ , ₁)) (X • Z)
Pq-XZ = PB.refl

------------------------------------------------------------------------
-- Reading a vector off qubit by qubit

-- Pw commutes with left-associated powers.
Pw-^' : (w : Word (PauliGen n)) (k : ℕ) → Pw (w ^' k) ≡ Pw w ^' k
Pw-^' w zero      = Eq.refl
Pw-^' w (₁₊ zero) = Eq.refl
Pw-^' w (₂₊ k)    = Eq.cong (_• Pw w) (Pw-^' w (₁₊ k))

-- The head of a vector becomes a word on wire 0 and the tail is shifted
-- up.  At one qubit vecToWord has no tail at all, whence the right-unit.
Pw-cons : (q : Pauli1) (ps : Pauli m) →
          PB._≈_ ((₁₊ m) CRel,_===_)
                 (Pw (vecToWord (q ∷ ps))) (Pq q • (Pw (vecToWord ps) ↑))
Pw-cons {zero} (a , b) [] =
  PB.trans (PB.refl' _ (Eq.cong₂ _•_ (Pw-^' [ inj₁ tt ]ʷ (toℕ a))
                                     (Pw-^' [ inj₂ tt ]ʷ (toℕ b))))
           (PB.sym PB.right-unit)
Pw-cons {₁₊ k} (a , b) (x ∷ xs) =
  PB.refl' _ (Eq.cong₂ _•_
               (Eq.cong₂ _•_ (Pw-^' [ inj₁ (inj₁ tt) ]ʷ (toℕ a))
                             (Pw-^' [ inj₁ (inj₂ tt) ]ʷ (toℕ b)))
               (Pw-↑ k (vecToWord (x ∷ xs))))

-- The identity vector translates to ε.
Pw-pI : PB._≈_ (m CRel,_===_) (Pw (vecToWord (pIₙ {m}))) ε
Pw-pI {zero}  = PB.refl
Pw-pI {₁₊ k} =
  PB.trans (Pw-cons pI (pIₙ {k}))
    (PB.trans (PB.cong Pq-I (lemma-cong↑ _ _ (Pw-pI {k}))) PB.left-unit)

-- Hence a basis vector translates to a single X or Z on its wire …
Pw-basis : (q : Pauli1) → PB._≈_ ((₁₊ m) CRel,_===_)
                                 (Pw (vecToWord (q ∷ pIₙ {m}))) (Pq q)
Pw-basis {m} q =
  PB.trans (Pw-cons q (pIₙ {m}))
    (PB.trans (PB.cong PB.refl (lemma-cong↑ _ _ (Pw-pI {m}))) PB.right-unit)

-- … and a vector supported on the bottom two wires to a word on them.
Pw-basis₂ : (q q' : Pauli1) →
            PB._≈_ ((₂₊ m) CRel,_===_)
                   (Pw (vecToWord (q ∷ q' ∷ pIₙ {m}))) (Pq q • (Pq q' ↑))
Pw-basis₂ {m} q q' =
  PB.trans (Pw-cons q (q' ∷ pIₙ {m}))
           (PB.cong PB.refl (lemma-cong↑ _ _ (Pw-basis q')))

------------------------------------------------------------------------
-- Pauli generators
--
-- genToVec and pauliGen→word are both defined by cases on the wire
-- count, so the wire-0 generators need their two clauses spelling out.

genToVec-X : genToVec (X-gen {m}) ≡ pX ∷ pIₙ {m}
genToVec-X {zero}  = Eq.refl
genToVec-X {₁₊ k} = Eq.refl

genToVec-Z : genToVec (Z-gen {m}) ≡ pZ ∷ pIₙ {m}
genToVec-Z {zero}  = Eq.refl
genToVec-Z {₁₊ k} = Eq.refl

P-X : pauliGen→word (X-gen {m}) ≡ X
P-X {zero}  = Eq.refl
P-X {₁₊ k} = Eq.refl

P-Z : pauliGen→word (Z-gen {m}) ≡ Z
P-Z {zero}  = Eq.refl
P-Z {₁₊ k} = Eq.refl

-- Qubit.Presentation's correction word is the wire-0 Z generator.
Z₀≡ : Z₀ {m} ≡ [ Z-gen {m} ]ʷ
Z₀≡ {zero}  = Eq.refl
Z₀≡ {₁₊ k} = Eq.refl

-- The round trip through the vector representation.
Pw-genToVec : (y : PauliGen (₁₊ m)) →
              PB._≈_ ((₁₊ m) CRel,_===_)
                     (Pw (vecToWord (genToVec y))) (pauliGen→word y)
Pw-genToVec {zero} (inj₁ tt) = PB.trans (Pw-basis pX) Pq-X
Pw-genToVec {zero} (inj₂ tt) = PB.trans (Pw-basis pZ) Pq-Z
Pw-genToVec {₁₊ k} (inj₁ (inj₁ tt)) = PB.trans (Pw-basis pX) Pq-X
Pw-genToVec {₁₊ k} (inj₁ (inj₂ tt)) = PB.trans (Pw-basis pZ) Pq-Z
Pw-genToVec {₁₊ k} (inj₂ y) =
  PB.trans (Pw-cons pI (genToVec y))
    (PB.trans (PB.cong Pq-I (lemma-cong↑ _ _ (Pw-genToVec y))) PB.left-unit)

------------------------------------------------------------------------
-- Circuits fix the identity Pauli

act-pI : (g : Gen m) → actg g (pIₙ {m}) ≡ pIₙ {m}
act-pI (gate₁ H-gate)  = Eq.refl
act-pI (gate₁ S-gate)  = Eq.refl
act-pI (gate₂ CZ-gate) = Eq.refl
act-pI (g ↥)           = Eq.cong (pI ∷_) (act-pI g)

------------------------------------------------------------------------
-- The wire-0 view of a Pauli generator

data PView : (m : ℕ) → PauliGen (₁₊ m) → Set where
  vX : PView m (X-gen {m})
  vZ : PView m (Z-gen {m})
  v↑ : (y : PauliGen (₁₊ m)) → PView (₁₊ m) (inj₂ y)

pview : (y : PauliGen (₁₊ m)) → PView m y
pview {zero} (inj₁ tt)         = vX
pview {zero} (inj₂ tt)         = vZ
pview {₁₊ k} (inj₁ (inj₁ tt)) = vX
pview {₁₊ k} (inj₁ (inj₂ tt)) = vZ
pview {₁₊ k} (inj₂ y)         = v↑ y
