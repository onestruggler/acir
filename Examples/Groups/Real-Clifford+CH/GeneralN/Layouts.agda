------------------------------------------------------------------------
-- Presentations of groups
--
-- The layout of a box from its box wire and a bitstring
--
-- `layoutAt i s`: the box on wire i, the other bits of s as the
-- colours of the controls — the layout Decoding's `layout□` builds from
-- two codes that differ at i (`zip-flip`, `zip-flip′`).  Its target
-- wire is i (`tgtWire-at`), its negations are X where s is false
-- (`negs-at`, with the bit i counted as black), and the bit i does not
-- matter (`layoutAt-flip`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Layouts where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; zipWith ; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Slot ; ctrl ; tgt ; Layout ; negs ; tgtWire)
open import Examples.Groups.Real-Clifford+CH.Decoding using (slot)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)

private
  variable
    n : ℕ

-- The box on wire i, the other bits as controls.
layoutAt : ℕ → Bits n → Layout n
layoutAt i       []      = []
layoutAt zero    (b ∷ s) = tgt ∷ map ctrl s
layoutAt (suc i) (b ∷ s) = ctrl b ∷ layoutAt i s

-- The bit i set.
setT : ℕ → Bits n → Bits n
setT i       []      = []
setT zero    (b ∷ s) = true ∷ s
setT (suc i) (b ∷ s) = b ∷ setT i s

private
  slot-same : ∀ b → slot b b ≡ ctrl b
  slot-same true  = Eq.refl
  slot-same false = Eq.refl

  slot-diff : ∀ b → slot b (not b) ≡ tgt
  slot-diff true  = Eq.refl
  slot-diff false = Eq.refl

  slot-diff′ : ∀ b → slot (not b) b ≡ tgt
  slot-diff′ true  = Eq.refl
  slot-diff′ false = Eq.refl

  zip-same : (s : Bits n) → zipWith slot s s ≡ map ctrl s
  zip-same []      = Eq.refl
  zip-same (b ∷ s) = Eq.cong₂ _∷_ (slot-same b) (zip-same s)

-- The layout of two codes differing at i.
zip-flip : ∀ i (s : Bits n) → i < n → zipWith slot s (flipAt i s) ≡ layoutAt i s
zip-flip i       []      ()
zip-flip zero    (b ∷ s) _       = Eq.cong₂ _∷_ (slot-diff b) (zip-same s)
zip-flip (suc i) (b ∷ s) (s≤s p) = Eq.cong₂ _∷_ (slot-same b) (zip-flip i s p)

zip-flip′ : ∀ i (s : Bits n) → i < n → zipWith slot (flipAt i s) s ≡ layoutAt i s
zip-flip′ i       []      ()
zip-flip′ zero    (b ∷ s) _       = Eq.cong₂ _∷_ (slot-diff′ b) (zip-same s)
zip-flip′ (suc i) (b ∷ s) (s≤s p) = Eq.cong₂ _∷_ (slot-same b) (zip-flip′ i s p)

-- The bit i does not matter.
layoutAt-flip : ∀ i (s : Bits n) → layoutAt i (flipAt i s) ≡ layoutAt i s
layoutAt-flip i       []      = Eq.refl
layoutAt-flip zero    (b ∷ s) = Eq.refl
layoutAt-flip (suc i) (b ∷ s) = Eq.cong (ctrl b ∷_) (layoutAt-flip i s)

tgtWire-at : ∀ i (s : Bits n) → i < n → tgtWire (layoutAt i s) ≡ i
tgtWire-at i       []      ()
tgtWire-at zero    (b ∷ s) _       = Eq.refl
tgtWire-at (suc i) (b ∷ s) (s≤s p) = Eq.cong suc (tgtWire-at i s p)

private
  negs-map : (s : Bits n) → negs (map ctrl s) ≡ negsB s
  negs-map []          = Eq.refl
  negs-map (false ∷ s) = Eq.cong (λ w → X • w ↑) (negs-map s)
  negs-map (true ∷ s)  = Eq.cong _↑ (negs-map s)

negs-at : ∀ i (s : Bits n) → negs (layoutAt i s) ≡ negsB (setT i s)
negs-at i       []          = Eq.refl
negs-at zero    (b ∷ s)     = Eq.cong _↑ (negs-map s)
negs-at (suc i) (false ∷ s) = Eq.cong (λ w → X • w ↑) (negs-at i s)
negs-at (suc i) (true ∷ s)  = Eq.cong _↑ (negs-at i s)

-- Setting a bit either changes nothing or flips it.
setT-cases : ∀ i (s : Bits n) → (setT i s ≡ s) ⊎ (setT i s ≡ flipAt i s)
setT-cases i       []          = inj₁ Eq.refl
setT-cases zero    (true ∷ s)  = inj₁ Eq.refl
setT-cases zero    (false ∷ s) = inj₂ Eq.refl
setT-cases (suc i) (b ∷ s) with setT-cases i s
... | inj₁ e = inj₁ (Eq.cong (b ∷_) e)
... | inj₂ e = inj₂ (Eq.cong (b ∷_) e)
