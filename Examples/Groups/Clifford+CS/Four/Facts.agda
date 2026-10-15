------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 for the K-free rules of P′ on four qubits
--
-- The consecutive facts that Lemma88.Fragment asks of the decoded
-- letters hold at four wires (Four.Facts.I1 … I4: each instance is its
-- decoded letters as blocks, carried by a transport to one of the
-- canonical class facts), so every K-free rule of P′ decodes to an
-- equation of four-wire circuits.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Facts where

open import Word.Base using (_ʷ)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Numbering 4 using (N)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_)
open import Examples.Groups.Clifford+CS.Decoding 0 using (d)
open import Examples.Groups.Clifford+CS.Lemma88.KFree 0 using (Facts ; k-free)
open import Examples.Groups.Clifford+CS.Four.Facts.I1
open import Examples.Groups.Clifford+CS.Four.Facts.I2
open import Examples.Groups.Clifford+CS.Four.Facts.I3
open import Examples.Groups.Clifford+CS.Four.Facts.I4

-- The consecutive facts at four wires.
facts : Facts
facts = record
  { p-inv   = λ {i} → d-p-inv i
  ; p′-inv  = λ {i} → d-p′-inv i
  ; p-ord   = λ {i} → d-p-ord i
  ; p-adj   = λ {i} → d-p-adj i
  ; sq      = λ {i} → d-sq i
  ; l-inv   = λ {i} → d-l-inv i
  ; h-inv   = λ {i} → d-h-inv i
  ; conj₂   = λ {i} → d-conj₂ i
  ; conj-up = λ {i} → d-conj-up i
  ; conj-dn = λ {i} → d-conj-dn i
  ; far-pl⁺ = λ {i} → d-far-pl⁺ i
  ; far-pl⁻ = λ {i} → d-far-pl⁻ i
  ; far-ll  = λ {i} {j} → d-far-ll i j
  ; braid   = λ {i} → d-braid i
  }

-- Lemma 8.8 for the K-free rules on four qubits.
k-free₄ : ∀ {u t} → N F, u === t → 4 ⊢ (d ʷ) u ≈ (d ʷ) t
k-free₄ = k-free facts
