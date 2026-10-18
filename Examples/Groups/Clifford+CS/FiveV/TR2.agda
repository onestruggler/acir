------------------------------------------------------------------------
-- Presentations of groups
--
-- The transported two-wire equations of the five-wire derivations
--
-- Each TR2 axiom of joint/tr.py: two circuits u, v on two wires with
-- the same matrix (one evaluation) are equal by completeness on two
-- wires, and so are their controlled versions on the domain wires 2, 3
-- (Five.Transport.Low, through the (F1) items of Five.F1Low); the sides
-- are then respelled in the letters of the derivations.  Written by
-- scratchpad/five/gen_tr.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.TR2 where

open import Data.List using (List ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (complete₂)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Same ; module Below)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.FiveV.Rules using (_⊢ₓ_≈_)
open import Examples.Groups.Clifford+CS.FiveV.Transport using (module Low)
open import Examples.Groups.Clifford+CS.FiveV.F1Low using (f1₂ ; f1₃ ; f1₄)
open import Examples.Groups.Clifford+CS.FiveV.Chain

private
  module S₂ = Below 2 complete₂

  tr : Ws → (u v : Circuit 2) → Same u v → 5 ⊢ₓ λ¹ʷ (u ↑ ↑) ≈ λ¹ʷ (v ↑ ↑)
  tr c4 u v e = Low.transport² c4 (f1₂ c4) (f1₃ c4) (f1₄ c4) (S₂.by-sem₀ u v e)

lem-TR2-0d166c34 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-TR2-0d166c34 c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ I-gen ]ʷ • [ S-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ) (ε) Eq.refl) (by-assoc Eq.refl))

lem-TR2-570a2ddc : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-TR2-570a2ddc c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ) ([ K-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ I-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ) Eq.refl) (by-assoc Eq.refl))

lem-TR2-4726ca8d : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-TR2-4726ca8d c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ) (ε) Eq.refl) (by-assoc Eq.refl))

lem-TR2-6ab04641 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-TR2-6ab04641 c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ) ([ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ) Eq.refl) (by-assoc Eq.refl))

lem-TR2-11f6930f : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-TR2-11f6930f c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ) (ε) Eq.refl) (by-assoc Eq.refl))

lem-TR2-3bdac6c8 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-TR2-3bdac6c8 c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ) ([ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ) Eq.refl) (by-assoc Eq.refl))

lem-TR2-fed8f7c9 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-TR2-fed8f7c9 c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ I-gen ]ʷ • [ S-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ I-gen ]ʷ) (ε) Eq.refl) (by-assoc Eq.refl))

lem-TR2-bf3fb9f8 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
lem-TR2-bf3fb9f8 c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ) ([ K-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ I-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ) Eq.refl) (by-assoc Eq.refl))

lem-TR2-1b52048e : Ws → ⟪ [] ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-TR2-1b52048e c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 (ε) ([ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ) Eq.refl) (by-assoc Eq.refl))

lem-TR2-d2b6eba7 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS34 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-TR2-d2b6eba7 c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ • [ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ) ([ K-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ) Eq.refl) (by-assoc Eq.refl))

lem-TR2-8fc9546c : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-TR2-8fc9546c c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ) (ε) Eq.refl) (by-assoc Eq.refl))

lem-TR2-e425e28a : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-TR2-e425e28a c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ) ([ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ S-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ S-gen ↥ ]ʷ) Eq.refl) (by-assoc Eq.refl))

lem-TR2-78b381c2 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-TR2-78b381c2 c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ) ([ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ) Eq.refl) (by-assoc Eq.refl))

lem-TR2-ff6c1f51 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-TR2-ff6c1f51 c4 = trans (by-assoc Eq.refl)
  (trans (tr c4 ([ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ) ([ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ K-gen ↥ ]ʷ • [ CS-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ I-gen ]ʷ • [ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ • [ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ • [ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ CS-gen ]ʷ • [ K-gen ]ʷ • [ S-gen ]ʷ • [ S-gen ]ʷ • [ K-gen ]ʷ • [ I-gen ]ʷ) Eq.refl) (by-assoc Eq.refl))
