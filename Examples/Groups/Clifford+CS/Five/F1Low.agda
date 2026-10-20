------------------------------------------------------------------------
-- Presentations of groups
--
-- (F1) on the top two domain wires
--
-- λ¹ of both sides of every rule of at most two wires, placed on the
-- domain wires 2, 3 (offsets 2, 3, 4), are equal on five wires: the
-- (F1) items that the transport of a two-wire equation meets
-- (Five.Transport.Low), from the derivations Five.D.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.F1Low where

open import Relation.Binary.PropositionalEquality as Eq using ()
open import Data.Nat using (ℕ)
open import Word.Base using (Word ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Flat using (by-flat)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-comm-CS-S0at2)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F1-order-CSat2)
open import Examples.Groups.Clifford+CS.Five.D.D067 using (lem-F1-X-CS0at2)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.Five.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2)

f1₂ : Ws → ∀ {w v} → 2 SRel, w === v → 5 ⊢ₓ λ¹ʷ (w ↑ ↑) ≈ λ¹ʷ (v ↑ ↑)
f1₂ c4 order-I = trans (by-flat Eq.refl) (trans (lem-F1-order-Iat0 c4) (by-flat Eq.refl))
f1₂ c4 order-S = trans (by-flat Eq.refl) (trans (lem-F1-order-Sat2 c4) (by-flat Eq.refl))
f1₂ c4 order-K = trans (by-flat Eq.refl) (trans (lem-F1-order-Kat2 c4) (by-flat Eq.refl))
f1₂ c4 order-SK = trans (by-flat Eq.refl) (trans (lem-F1-order-SKat2 c4) (by-flat Eq.refl))
f1₂ c4 order-CS = trans (by-flat Eq.refl) (trans (lem-F1-order-CSat2 c4) (by-flat Eq.refl))
f1₂ c4 comm-CS-S₀ = trans (by-flat Eq.refl) (trans (lem-F1-comm-CS-S0at2 c4) (by-flat Eq.refl))
f1₂ c4 comm-CS-S₁ = trans (by-flat Eq.refl) (trans (lem-F1-comm-CS-S1at2 c4) (by-flat Eq.refl))
f1₂ c4 X-CS₀ = trans (by-flat Eq.refl) (trans (lem-F1-X-CS0at2 c4) (by-flat Eq.refl))
f1₂ c4 X-CS₁ = trans (by-flat Eq.refl) (trans (lem-F1-X-CS1at2 c4) (by-flat Eq.refl))
f1₂ c4 CS-K₀ = trans (by-flat Eq.refl) (trans (lem-F1-CS-K0at2 c4) (by-flat Eq.refl))
f1₂ c4 CS-K₁ = trans (by-flat Eq.refl) (trans (lem-F1-CS-K1at2 c4) (by-flat Eq.refl))

f1₃ : Ws → ∀ {w v} → 1 SRel, w === v → 5 ⊢ₓ λ¹ʷ (w ↑ ↑ ↑) ≈ λ¹ʷ (v ↑ ↑ ↑)
f1₃ c4 order-I = trans (by-flat Eq.refl) (trans (lem-F1-order-Iat0 c4) (by-flat Eq.refl))
f1₃ c4 order-S = trans (by-flat Eq.refl) (trans (lem-F1-order-Sat3 c4) (by-flat Eq.refl))
f1₃ c4 order-K = trans (by-flat Eq.refl) (trans (lem-F1-order-Kat3 c4) (by-flat Eq.refl))
f1₃ c4 order-SK = trans (by-flat Eq.refl) (trans (lem-F1-order-SKat3 c4) (by-flat Eq.refl))

f1₄ : Ws → ∀ {w v} → 0 SRel, w === v → 5 ⊢ₓ λ¹ʷ (w ↑ ↑ ↑ ↑) ≈ λ¹ʷ (v ↑ ↑ ↑ ↑)
f1₄ c4 order-I = trans (by-flat Eq.refl) (trans (lem-F1-order-Iat0 c4) (by-flat Eq.refl))
