------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the plain qupit-Clifford presentation in the symplectic
-- semantics, transported from the extended gate set.
--
-- There is a group isomorphism f'* : (Word (Gen n) / ≈) ≅ the extended
-- gate presentation (Examples.Groups.Symplectic.Sim-Ext-Sym), and the
-- extended development already proves that its axioms preserve the Pauli
-- action (Examples.Groups.Symplectic.ExtendedGate.Soundness.act-sound-ax).
-- A single semantic-agreement lemma
--
--     agree :  ap ⟦ w ⟧ p  ≡  act (f'* w) p
--
-- (the plain action of w equals the extended action of its image f'* w)
-- then transports soundness to the plain presentation: given a plain
-- relation w === v, f-well-defined lifts it to f'* w ≈ f'* v, act-cong
-- (the congruence closure of act-sound-ax) makes the two extended
-- actions agree, and agree carries this back to ⟦ w ⟧ ≈ˢ ⟦ v ⟧.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Transport (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Data.Product using (_,_)
open import Data.Vec using (_∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
open import Presentation.GroupLike using (module Group-Action)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Pauli.Semantics p-2 p-prime using (Pauli)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (Circuit ; Gen ; _QRel,_===_ ; gate₁ ; gate₂ ; _↥
                      ; H-gate ; S-gate ; CZ-gate)

open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem
  using (_≈ˢ_)
open Sem.Symplectic using (ap)
open Sem.Interpretation using (⟦_⟧ ; ⟦_⟧ᵍ ; actg)

import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime as SD
open SD.Symplectic-Derived-Gen using ()
  renaming (Gen to Gen₂ ; _QRel,_===_ to _QRel,_===₂_)
open SD.Symplectic-Derived-GroupLike using ()
  renaming (grouplike to grouplike₂)

import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime as ExtP
open ExtP using (act ; act1)

open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
  using (act-sound-ax)

open import Examples.Groups.Symplectic.Sim-Ext-Sym p-2 p-prime
  using (f'* ; f ; f-well-defined)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Semantic agreement: plain action = extended action along f
--
-- On generators the two actions are definitionally equal, except that
-- the extended gates carry an explicit scalar ₁ (a * ₁ vs a).

agreeg : ∀ (x : Gen n) (p : Pauli n) → actg x p ≡ act1 (f x) p
agreeg (gate₁ H-gate)  ((a , b) ∷ ps) = Eq.refl
agreeg (gate₁ S-gate)  ((a , b) ∷ ps) =
  Eq.cong (λ z → (a , z) ∷ ps) (Eq.cong (b +_) (Eq.sym (*-identityʳ a)))
agreeg (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ ps) =
  Eq.cong₂ (λ z z' → (a , z) ∷ (a' , z') ∷ ps)
    (Eq.cong (b  +_) (Eq.sym (*-identityʳ a')))
    (Eq.cong (b' +_) (Eq.sym (*-identityʳ a)))
agreeg (x ↥)           (p ∷ ps) = Eq.cong (p ∷_) (agreeg x ps)

-- Lifted to whole circuits: both interpretations are multiplicative, so
-- agreement threads through _•_.
agree : ∀ (w : Circuit n) (p : Pauli n) → ap ⟦ w ⟧ p ≡ act (f'* w) p
agree [ x ]ʷ  p = agreeg x p
agree ε       p = Eq.refl
agree (w • v) p =
  Eq.trans (Eq.cong (ap ⟦ w ⟧) (agree v p)) (agree w (act (f'* v) p))

------------------------------------------------------------------------
-- Soundness: the plain raw relations preserve the symplectic action

module Snd (m : ℕ) where
  open Group-Action (Pauli m) (Gen₂ m) (m QRel,_===₂_) (grouplike₂ {m})
                    act1 (act-sound-ax {m} _ _) using (act-cong)

  sound-axᵐ : ∀ {w v : Circuit m} → m QRel, w === v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
  sound-axᵐ {w} {v} r p =
    Eq.trans (agree w p)
      (Eq.trans (act-cong (f'* w) (f'* v) p (f-well-defined r))
                (Eq.sym (agree v p)))

sound-ax : ∀ {n} {w v : Circuit n} → n QRel, w === v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
sound-ax {n} = Snd.sound-axᵐ n
