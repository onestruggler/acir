------------------------------------------------------------------------
-- Presentations of groups
--
-- Equations on two wires, derived from the rules (machine-generated)
--
-- The equations between the macro letters of Lemmas.TwoWireMacro, on
-- the gates they stand for: how the Paulis, the CNOTs and the swap
-- conjugate one another and CS, and the relations of the controlled K
-- gates CK₀₁ and CK₁₀.  Each is derived by a Knuth–Bendix completion of
-- the rules, written for Engine (a list of rewrites checked by running
-- it), in three stages:
--
--   * the relations of Selinger's presentation of the two-qubit
--     Clifford group, C1–C11 read with H = ω K and CZ = CS² — C8–C11
--     being the only ones that take work;
--   * from those, the Clifford equations, by a completion over the
--     Clifford gates with CZ as one letter (the group is finite), each
--     step replayed on the gates by writing CZ as CS CS;
--   * the equations involving CS and the controlled K gates, from the
--     rules and the Clifford equations.
--
-- The completions run on the letters with wire 1's scalar read as the
-- scalar, which makes the rules symmetric under exchanging the wires
-- (the three rules that differ are restated below, ω↑=ω joining the
-- two readings): an equation a completion missed is the mirror image
-- of one it found, replayed with the wires exchanged (the rules named
-- m…).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Lemmas.TwoWire where

open import Data.List using ([] ; _∷_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
import Examples.Groups.Clifford+CS.Engine as Engine
open PB (2 VRel,_===_) using (axiom)

------------------------------------------------------------------------
-- The letters

ι s₀ k₀ s₁ k₁ cs : Gen 2
ι  = I-gen
s₀ = S-gen
k₀ = K-gen
s₁ = S-gen ↥
k₁ = K-gen ↥
cs = CS-gen

-- Every letter of two wires has a code.
code : Gen 2 → ℕ
code (gate₀ I-gate)      = 0
code (gate₁ S-gate)      = 1
code (gate₁ K-gate)      = 2
code (gate₂ CS-gate)     = 3
code (gate₀ I-gate ↥)    = 4
code (gate₁ S-gate ↥)    = 5
code (gate₁ K-gate ↥)    = 6
code (gate₀ I-gate ↥ ↥)  = 7

decode : ℕ → Gen 2
decode 1 = gate₁ S-gate
decode 2 = gate₁ K-gate
decode 3 = gate₂ CS-gate
decode 4 = gate₀ I-gate ↥
decode 5 = gate₁ S-gate ↥
decode 6 = gate₁ K-gate ↥
decode 7 = gate₀ I-gate ↥ ↥
decode _ = gate₀ I-gate

decode-code : ∀ x → decode (code x) ≡ x
decode-code (gate₀ I-gate)     = refl
decode-code (gate₁ S-gate)     = refl
decode-code (gate₁ K-gate)     = refl
decode-code (gate₂ CS-gate)    = refl
decode-code (gate₀ I-gate ↥)   = refl
decode-code (gate₁ S-gate ↥)   = refl
decode-code (gate₁ K-gate ↥)   = refl
decode-code (gate₀ I-gate ↥ ↥) = refl

module E = Engine (2 VRel,_===_) code decode decode-code
open E public using (Eqn ; lhs ; rhs ; prf)
open E using (⌊_⌋⁼ ; sym⁼ ; derive ; rw ; rw⁻)

-- The rules on wire 1 that mention the scalar, with the scalar.
private
  ι↑ : Gen 2
  ι↑ = I-gen ↥

  ω↑ K²₁ SK³₁ X-CS₁′ : Eqn
  ω↑ = ⌊ axiom (ω↑=ω I-gate) ⌋⁼
  K²₁ = derive (k₁ ∷ k₁ ∷ []) (ι ∷ ι ∷ ι ∷ [])
    (rw 0 ⌊ lemma-cong↑ _ _ (PB.axiom (srel order-K)) ⌋⁼ ∷ rw 0 ω↑ ∷ rw 1 ω↑ ∷ rw 2 ω↑ ∷ []) refl
  SK³₁ = derive (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ []) (ι ∷ ι ∷ ι ∷ [])
    (rw 0 ⌊ lemma-cong↑ _ _ (PB.axiom (srel order-SK)) ⌋⁼ ∷ rw 0 ω↑ ∷ rw 1 ω↑ ∷ rw 2 ω↑ ∷ []) refl
  X-CS₁′ = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ s₀ ∷ [])
    (rw⁻ 4 ω↑ ∷ rw 0 ⌊ axiom (srel X-CS₁) ⌋⁼ ∷ rw 7 ω↑ ∷ []) refl

------------------------------------------------------------------------
-- Selinger's relations for the two-qubit Clifford group

private
  rs0-0 : Eqn
  rs0-0 = ⌊ axiom (srel order-I) ⌋⁼

  rs0-1 : Eqn
  rs0-1 = ⌊ axiom (srel order-S) ⌋⁼

  rs0-2 : Eqn
  rs0-2 = sym⁼ (⌊ axiom (srel order-K) ⌋⁼)

  rs0-3 : Eqn
  rs0-3 = ⌊ axiom (srel order-SK) ⌋⁼

  rs0-4 : Eqn
  rs0-4 = ⌊ lemma-cong↑ _ _ (PB.axiom (srel order-S)) ⌋⁼

  rs0-5 : Eqn
  rs0-5 = sym⁼ (K²₁)

  rs0-6 : Eqn
  rs0-6 = SK³₁

  rs0-7 : Eqn
  rs0-7 = ⌊ comm₀ I-gate S-gen ⌋⁼

  rs0-8 : Eqn
  rs0-8 = ⌊ comm₀ I-gate K-gen ⌋⁼

  rs0-9 : Eqn
  rs0-9 = ⌊ comm₀ I-gate (S-gen ↥) ⌋⁼

  rs0-10 : Eqn
  rs0-10 = ⌊ comm₀ I-gate (K-gen ↥) ⌋⁼

  rs0-11 : Eqn
  rs0-11 = ⌊ comm₀ I-gate CS-gen ⌋⁼

  rs0-12 : Eqn
  rs0-12 = ⌊ axiom (comm₁ S-gate S-gen) ⌋⁼

  rs0-13 : Eqn
  rs0-13 = ⌊ axiom (comm₁ K-gate K-gen) ⌋⁼

  rs0-14 : Eqn
  rs0-14 = ⌊ axiom (comm₁ K-gate S-gen) ⌋⁼

  rs0-15 : Eqn
  rs0-15 = ⌊ axiom (comm₁ S-gate K-gen) ⌋⁼

  rs0-16 : Eqn
  rs0-16 = ⌊ axiom (srel order-CS) ⌋⁼

  rs0-17 : Eqn
  rs0-17 = ⌊ axiom (srel comm-CS-S₀) ⌋⁼

  rs0-18 : Eqn
  rs0-18 = ⌊ axiom (srel comm-CS-S₁) ⌋⁼

  rs0-19 : Eqn
  rs0-19 = sym⁼ (⌊ axiom (srel X-CS₀) ⌋⁼)

  rs0-20 : Eqn
  rs0-20 = sym⁼ (X-CS₁′)

  rs0-21 : Eqn
  rs0-21 = ⌊ axiom (srel CS-K₀) ⌋⁼

  rs0-22 : Eqn
  rs0-22 = ⌊ axiom (srel CS-K₁) ⌋⁼

  rs0-23 : Eqn
  rs0-23 = derive (ι ∷ k₁ ∷ k₁ ∷ [])
    ([])
    (rw⁻ 0 rs0-10 ∷ rw⁻ 1 rs0-10 ∷ rw⁻ 0 rs0-5 ∷ rw 0 rs0-0 ∷ []) refl

  rs0-24 : Eqn
  rs0-24 = derive (ι ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ [])
    (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 rs0-11 ∷ rw⁻ 1 rs0-11 ∷ rw⁻ 2 rs0-11 ∷ rw⁻ 3 rs0-8 ∷ rw⁻ 4 rs0-7 ∷ rw⁻ 5 rs0-7 ∷
       rw⁻ 6 rs0-8 ∷ rw 0 rs0-19 ∷ rw 3 rs0-8 ∷ rw 2 rs0-7 ∷ rw 1 rs0-7 ∷ rw 0 rs0-8 ∷ []) refl

  rs0-25 : Eqn
  rs0-25 = derive (ι ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 1 rs0-17 ∷ rw⁻ 2 rs0-17 ∷ rw⁻ 3 rs0-17 ∷ rw⁻ 4 rs0-15 ∷ rw⁻ 5 rs0-12 ∷ rw⁻ 6 rs0-12 ∷
       rw⁻ 7 rs0-15 ∷ rw⁻ 0 rs0-11 ∷ rw⁻ 1 rs0-11 ∷ rw⁻ 2 rs0-11 ∷ rw⁻ 3 rs0-10 ∷ rw⁻ 4 rs0-9 ∷
       rw⁻ 5 rs0-9 ∷ rw⁻ 6 rs0-10 ∷ rw 0 rs0-20 ∷ rw 3 rs0-10 ∷ rw 2 rs0-9 ∷ rw 1 rs0-9 ∷
       rw 0 rs0-10 ∷ []) refl

  rs0-26 : Eqn
  rs0-26 = derive (ι ∷ s₀ ∷ k₁ ∷ k₁ ∷ [])
    (s₀ ∷ [])
    (rw⁻ 0 rs0-7 ∷ rw 1 rs0-23 ∷ []) refl

  rs0-30 : Eqn
  rs0-30 = derive (cs ∷ k₀ ∷ s₁ ∷ [])
    (s₁ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 rs0-14 ∷ rw 0 rs0-18 ∷ []) refl

  rs0-31 : Eqn
  rs0-31 = derive (s₀ ∷ k₁ ∷ k₁ ∷ [])
    (s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rs0-15 ∷ rw⁻ 1 rs0-15 ∷ rw⁻ 0 rs0-5 ∷ rw⁻ 2 rs0-7 ∷ rw⁻ 1 rs0-7 ∷ rw⁻ 0 rs0-7 ∷
       rw 1 rs0-2 ∷ []) refl

  rs0-32 : Eqn
  rs0-32 = derive (ι ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ [])
    (rw⁻ 1 rs0-31 ∷ rw 0 rs0-26 ∷ []) refl

  rs0-37 : Eqn
  rs0-37 = derive (cs ∷ k₀ ∷ k₀ ∷ [])
    (k₁ ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 1 rs0-2 ∷ rw 0 rs0-11 ∷ rw 1 rs0-11 ∷ rw 2 rs0-11 ∷ rw 0 rs0-5 ∷ []) refl

  rs0-40 : Eqn
  rs0-40 = derive (ι ∷ k₀ ∷ k₀ ∷ [])
    ([])
    (rw⁻ 1 rs0-2 ∷ rw 0 rs0-5 ∷ rw 1 rs0-10 ∷ rw 0 rs0-10 ∷ rw 0 rs0-23 ∷ []) refl

  rs0-41 : Eqn
  rs0-41 = derive (k₁ ∷ k₁ ∷ [])
    (k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rs0-5 ∷ rw 0 rs0-2 ∷ []) refl

  rs0-42 : Eqn
  rs0-42 = derive (ι ∷ ι ∷ ι ∷ [])
    (k₀ ∷ k₀ ∷ [])
    (rw 0 rs0-5 ∷ rw 0 rs0-41 ∷ []) refl

  rs0-43 : Eqn
  rs0-43 = derive (cs ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ k₀ ∷ cs ∷ [])
    (rw 0 rs0-37 ∷ rw 0 rs0-41 ∷ []) refl

  rs0-44 : Eqn
  rs0-44 = derive (k₀ ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rs0-41 ∷ rw 1 rs0-15 ∷ rw 0 rs0-15 ∷ rw 1 rs0-41 ∷ []) refl

  rs0-45 : Eqn
  rs0-45 = derive (ι ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rs0-7 ∷ rw 1 rs0-32 ∷ []) refl

  rs0-46 : Eqn
  rs0-46 = derive (ι ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rs0-8 ∷ rw 1 rs0-32 ∷ []) refl

  rs0-47 : Eqn
  rs0-47 = derive (cs ∷ k₀ ∷ s₀ ∷ s₁ ∷ [])
    (s₁ ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 2 rs0-12 ∷ rw 0 rs0-30 ∷ []) refl

  rs0-48 : Eqn
  rs0-48 = derive (ι ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 3 rs0-44 ∷ rw 0 rs0-32 ∷ []) refl

  rs0-49 : Eqn
  rs0-49 = derive (cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 2 rs0-44 ∷ rw 0 rs0-43 ∷ []) refl

  rs0-50 : Eqn
  rs0-50 = derive (ι ∷ s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rs0-7 ∷ rw 1 rs0-45 ∷ []) refl

  rs0-51 : Eqn
  rs0-51 = derive (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rs0-8 ∷ rw 1 rs0-45 ∷ []) refl

  rs0-53 : Eqn
  rs0-53 = derive (ι ∷ k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 4 rs0-44 ∷ rw 0 rs0-46 ∷ []) refl

  rs0-54 : Eqn
  rs0-54 = derive (cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ s₁ ∷ [])
    (s₁ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 3 rs0-12 ∷ rw 0 rs0-47 ∷ []) refl

  rs0-56 : Eqn
  rs0-56 = derive (k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rs0-1 ∷ rw 3 rs0-3 ∷ rw 2 rs0-7 ∷ rw 1 rs0-7 ∷ rw 0 rs0-7 ∷ rw 3 rs0-7 ∷
       rw 2 rs0-7 ∷ rw 1 rs0-7 ∷ rw 4 rs0-7 ∷ rw 3 rs0-7 ∷ rw 2 rs0-7 ∷ rw 0 rs0-42 ∷
       rw 0 rs0-44 ∷ rw 1 rs0-44 ∷ rw 2 rs0-44 ∷ []) refl

  rs0-57 : Eqn
  rs0-57 = derive (k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rs0-53 ∷ rw 1 rs0-56 ∷ rw 0 rs0-50 ∷ []) refl

  rs0-63 : Eqn
  rs0-63 = derive (k₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rs0-57 ∷ rw 0 rs0-44 ∷ rw 2 rs0-44 ∷ []) refl

  rs0-66 : Eqn
  rs0-66 = derive (k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₀ ∷ k₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rs0-4 ∷ rw 3 rs0-6 ∷ rw 2 rs0-9 ∷ rw 1 rs0-9 ∷ rw 0 rs0-9 ∷ rw 3 rs0-9 ∷
       rw 2 rs0-9 ∷ rw 1 rs0-9 ∷ rw 4 rs0-9 ∷ rw 3 rs0-9 ∷ rw 2 rs0-9 ∷ rw 0 rs0-42 ∷ []) refl

  rs0-69 : Eqn
  rs0-69 = derive (k₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rs0-50 ∷ rw 0 rs0-8 ∷ rw 1 rs0-63 ∷ rw 0 rs0-48 ∷ []) refl

  rs0-72 : Eqn
  rs0-72 = derive (s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 2 rs0-17 ∷ rw⁻ 3 rs0-69 ∷ rw⁻ 6 rs0-17 ∷ rw⁻ 5 rs0-17 ∷ rw⁻ 4 rs0-17 ∷ rw⁻ 0 rs0-21 ∷
       rw 4 rs0-1 ∷ []) refl

  rs0-74 : Eqn
  rs0-74 = derive (s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 rs0-17 ∷ rw⁻ 1 rs0-69 ∷ rw⁻ 4 rs0-17 ∷ rw⁻ 3 rs0-17 ∷ rw⁻ 2 rs0-17 ∷ rw⁻ 3 rs0-57 ∷
       rw 0 rs0-21 ∷ rw 2 rs0-21 ∷ []) refl

  rs0-76 : Eqn
  rs0-76 = derive (s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ [])
    (cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 6 rs0-18 ∷ rw⁻ 5 rs0-18 ∷ rw⁻ 4 rs0-18 ∷ rw⁻ 0 rs0-22 ∷ rw 4 rs0-4 ∷ []) refl

  rs0-79 : Eqn
  rs0-79 = derive (cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 3 rs0-44 ∷ rw 0 rs0-49 ∷ []) refl

  rs0-81 : Eqn
  rs0-81 = derive (cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ [])
    (s₁ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 4 rs0-14 ∷ rw 0 rs0-54 ∷ []) refl

  rs0-82 : Eqn
  rs0-82 = derive (ι ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 1 rs0-18 ∷ rw⁻ 2 rs0-18 ∷ rw⁻ 3 rs0-81 ∷ rw 0 rs0-24 ∷ []) refl

  rs0-85 : Eqn
  rs0-85 = derive (k₀ ∷ k₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₀ ∷ k₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 1 rs0-13 ∷ rw⁻ 0 rs0-13 ∷ rw⁻ 1 rs0-66 ∷ rw 0 rs0-41 ∷ []) refl

  rs0-87 : Eqn
  rs0-87 = derive (k₀ ∷ k₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (k₀ ∷ k₀ ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-85 ∷ rw⁻ 1 rs0-13 ∷ rw⁻ 2 rs0-14 ∷ rw⁻ 0 rs0-13 ∷ rw⁻ 1 rs0-14 ∷ rw⁻ 2 rs0-66 ∷
       rw 0 rs0-66 ∷ rw 2 rs0-4 ∷ []) refl

  rs0-88 : Eqn
  rs0-88 = derive (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (k₁ ∷ [])
    (rw⁻ 0 rs0-40 ∷ rw⁻ 0 rs0-8 ∷ rw⁻ 1 rs0-8 ∷ rw⁻ 2 rs0-9 ∷ rw⁻ 3 rs0-10 ∷ rw⁻ 4 rs0-9 ∷
       rw⁻ 5 rs0-10 ∷ rw⁻ 6 rs0-9 ∷ rw 0 rs0-87 ∷ rw 2 rs0-10 ∷ rw 1 rs0-8 ∷ rw 0 rs0-8 ∷
       rw 0 rs0-40 ∷ []) refl

  rs0-89 : Eqn
  rs0-89 = derive (k₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-88 ∷ rw 4 rs0-4 ∷ []) refl

  rs0-91 : Eqn
  rs0-91 = derive (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 rs0-18 ∷ rw⁻ 3 rs0-89 ∷ rw 0 rs0-76 ∷ []) refl

  rs0-92 : Eqn
  rs0-92 = derive (k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-4 ∷ rw 3 rs0-88 ∷ []) refl

  rs0-93 : Eqn
  rs0-93 = derive (cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ [])
    (rw⁻ 2 rs0-18 ∷ rw⁻ 3 rs0-89 ∷ rw 0 rs0-22 ∷ rw 4 rs0-18 ∷ rw 5 rs0-18 ∷ []) refl

  rs0-94 : Eqn
  rs0-94 = derive (s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 rs0-18 ∷ rw⁻ 1 rs0-89 ∷ rw⁻ 4 rs0-18 ∷ rw⁻ 3 rs0-18 ∷ rw⁻ 2 rs0-18 ∷ rw⁻ 3 rs0-92 ∷
       rw 0 rs0-22 ∷ rw 2 rs0-22 ∷ []) refl

  rs0-95 : Eqn
  rs0-95 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 2 rs0-89 ∷ rw 0 rs0-92 ∷ []) refl

  rs0-103 : Eqn
  rs0-103 = derive (k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rs0-1 ∷ rw 3 rs0-72 ∷ []) refl

  rs0-110 : Eqn
  rs0-110 = derive (k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-4 ∷ rw 3 rs0-91 ∷ []) refl

  rs0-126 : Eqn
  rs0-126 = derive (cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 rs0-1 ∷ rw 3 rs0-74 ∷ rw 0 rs0-1 ∷ []) refl

  rs0-147 : Eqn
  rs0-147 = derive (cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 rs0-4 ∷ rw 3 rs0-94 ∷ rw 0 rs0-4 ∷ []) refl

  rs0-166 : Eqn
  rs0-166 = derive (ι ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 1 rs0-69 ∷ rw⁻ 2 rs0-103 ∷ rw 0 rs0-40 ∷ []) refl

  rs0-172 : Eqn
  rs0-172 = derive (ι ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 1 rs0-1 ∷ rw⁻ 4 rs0-69 ∷ rw⁻ 5 rs0-103 ∷ rw 0 rs0-50 ∷ rw 0 rs0-1 ∷ []) refl

  rs0-188 : Eqn
  rs0-188 = derive (ι ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 1 rs0-126 ∷ rw⁻ 0 rs0-11 ∷ rw 1 rs0-172 ∷ []) refl

  rs0-529 : Eqn
  rs0-529 = derive (ι ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (ι ∷ s₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-11 ∷ rw⁻ 1 rs0-25 ∷ rw 0 rs0-11 ∷ rw 1 rs0-17 ∷ rw 2 rs0-16 ∷ []) refl

  rs0-546 : Eqn
  rs0-546 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-40 ∷ rw⁻ 1 rs0-43 ∷ rw⁻ 3 rs0-13 ∷ rw⁻ 4 rs0-14 ∷ rw⁻ 5 rs0-14 ∷ rw⁻ 6 rs0-13 ∷
       rw⁻ 2 rs0-13 ∷ rw⁻ 3 rs0-14 ∷ rw⁻ 4 rs0-14 ∷ rw⁻ 5 rs0-13 ∷ rw⁻ 6 rs0-43 ∷ rw 0 rs0-529 ∷
       rw 5 rs0-13 ∷ rw 4 rs0-14 ∷ rw 3 rs0-14 ∷ rw 2 rs0-13 ∷ rw 6 rs0-13 ∷ rw 5 rs0-14 ∷
       rw 4 rs0-14 ∷ rw 3 rs0-13 ∷ rw 0 rs0-32 ∷ []) refl

  rs0-551 : Eqn
  rs0-551 = derive (s₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-546 ∷ rw 5 rs0-16 ∷ []) refl

  rs0-552 : Eqn
  rs0-552 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 5 rs0-18 ∷ rw 0 rs0-546 ∷ []) refl

  rs0-579 : Eqn
  rs0-579 = derive (s₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 1 rs0-546 ∷ rw⁻ 0 rs0-17 ∷ rw 1 rs0-551 ∷ []) refl

  rs0-621 : Eqn
  rs0-621 = derive (k₀ ∷ k₀ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ k₀ ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-43 ∷ rw⁻ 2 rs0-13 ∷ rw⁻ 3 rs0-14 ∷ rw⁻ 1 rs0-13 ∷ rw⁻ 2 rs0-14 ∷ rw⁻ 3 rs0-41 ∷
       rw⁻ 0 rs0-4 ∷ rw⁻ 3 rs0-18 ∷ rw⁻ 4 rs0-89 ∷ rw⁻ 2 rs0-18 ∷ rw⁻ 1 rs0-18 ∷ rw⁻ 0 rs0-18 ∷
       rw⁻ 1 rs0-95 ∷ rw⁻ 6 rs0-147 ∷ rw 0 rs0-552 ∷ rw 1 rs0-95 ∷ rw 4 rs0-89 ∷ rw 1 rs0-4 ∷
       rw 3 rs0-41 ∷ rw 2 rs0-14 ∷ rw 1 rs0-13 ∷ rw 3 rs0-14 ∷ rw 2 rs0-13 ∷ []) refl

  rs0-802 : Eqn
  rs0-802 = derive (ι ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ [])
    (rw⁻ 0 rs0-11 ∷ rw⁻ 1 rs0-82 ∷ rw 0 rs0-11 ∷ rw 1 rs0-18 ∷ rw 2 rs0-16 ∷ rw 1 rs0-14 ∷
       rw 2 rs0-12 ∷ rw 3 rs0-12 ∷ rw 4 rs0-14 ∷ []) refl

  rs0-824 : Eqn
  rs0-824 = derive (cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ [])
    (rw⁻ 0 rs0-40 ∷ rw⁻ 1 rs0-79 ∷ rw⁻ 6 rs0-43 ∷ rw 0 rs0-802 ∷ rw 5 rs0-14 ∷ rw 0 rs0-51 ∷
       rw 3 rs0-14 ∷ []) refl

  rs0-837 : Eqn
  rs0-837 = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rs0-824 ∷ rw 5 rs0-16 ∷ []) refl

  rs0-883 : Eqn
  rs0-883 = derive (s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (ι ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rs0-40 ∷ rw 2 rs0-837 ∷ []) refl

  rs0-994 : Eqn
  rs0-994 = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 3 rs0-14 ∷ rw⁻ 2 rs0-12 ∷ rw⁻ 1 rs0-12 ∷ rw⁻ 0 rs0-14 ∷ rw⁻ 1 rs0-824 ∷ rw⁻ 0 rs0-81 ∷
       rw 2 rs0-883 ∷ rw 1 rs0-8 ∷ rw 0 rs0-11 ∷ rw 1 rs0-43 ∷ rw 0 rs0-40 ∷ []) refl

  rs0-1200 : Eqn
  rs0-1200 = derive (cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (k₀ ∷ s₀ ∷ s₁ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 2 rs0-17 ∷ rw⁻ 0 rs0-1 ∷ rw⁻ 3 rs0-17 ∷ rw⁻ 2 rs0-17 ∷ rw⁻ 1 rs0-17 ∷ rw⁻ 2 rs0-57 ∷
       rw⁻ 5 rs0-17 ∷ rw⁻ 0 rs0-166 ∷ rw 7 rs0-824 ∷ rw 5 rs0-43 ∷ rw 0 rs0-48 ∷ rw 4 rs0-17 ∷
       rw 1 rs0-57 ∷ rw 0 rs0-1 ∷ rw 1 rs0-17 ∷ rw 2 rs0-30 ∷ []) refl

  rs0-1223 : Eqn
  rs0-1223 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (k₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rs0-1 ∷ rw⁻ 3 rs0-17 ∷ rw⁻ 2 rs0-17 ∷ rw⁻ 1 rs0-17 ∷ rw⁻ 2 rs0-57 ∷ rw⁻ 5 rs0-17 ∷
       rw⁻ 0 rs0-166 ∷ rw 7 rs0-1200 ∷ rw 5 rs0-43 ∷ rw 0 rs0-48 ∷ rw 4 rs0-17 ∷ rw 1 rs0-57 ∷
       rw 0 rs0-1 ∷ rw 1 rs0-18 ∷ []) refl

  rs0-1247 : Eqn
  rs0-1247 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (k₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 5 rs0-17 ∷ rw 0 rs0-1223 ∷ []) refl

  rs0-1723 : Eqn
  rs0-1723 = derive (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 2 rs0-17 ∷ rw⁻ 3 rs0-17 ∷ rw⁻ 1 rs0-17 ∷ rw⁻ 2 rs0-17 ∷ rw⁻ 0 rs0-17 ∷ rw⁻ 1 rs0-17 ∷
       rw⁻ 2 rs0-57 ∷ rw⁻ 5 rs0-17 ∷ rw⁻ 0 rs0-188 ∷ rw 4 rs0-1247 ∷ rw 0 rs0-46 ∷ []) refl

  rs0-2233 : Eqn
  rs0-2233 = derive (cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-40 ∷ rw⁻ 0 rs0-8 ∷ rw⁻ 1 rs0-8 ∷ rw⁻ 2 rs0-11 ∷ rw⁻ 3 rs0-10 ∷ rw⁻ 4 rs0-9 ∷
       rw⁻ 5 rs0-11 ∷ rw⁻ 6 rs0-10 ∷ rw⁻ 7 rs0-11 ∷ rw 0 rs0-621 ∷ rw 6 rs0-10 ∷ rw 5 rs0-11 ∷
       rw 4 rs0-9 ∷ rw 3 rs0-10 ∷ rw 2 rs0-8 ∷ rw 1 rs0-8 ∷ rw 0 rs0-7 ∷ rw 0 rs0-32 ∷ []) refl

  rs0-2235 : Eqn
  rs0-2235 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 rs0-17 ∷ rw⁻ 1 rs0-17 ∷ rw⁻ 2 rs0-17 ∷ rw⁻ 3 rs0-2233 ∷ rw 0 rs0-16 ∷ []) refl

  rs0-2237 : Eqn
  rs0-2237 = derive (cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 5 rs0-18 ∷ rw 0 rs0-2233 ∷ []) refl

  rs0-2310 : Eqn
  rs0-2310 = derive (s₀ ∷ s₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 3 rs0-2235 ∷ rw 0 rs0-1 ∷ []) refl

  rs0-2361 : Eqn
  rs0-2361 = derive (k₀ ∷ k₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-43 ∷ rw⁻ 2 rs0-13 ∷ rw⁻ 1 rs0-13 ∷ rw⁻ 2 rs0-43 ∷ rw⁻ 3 rs0-41 ∷ rw⁻ 0 rs0-4 ∷
       rw⁻ 1 rs0-110 ∷ rw⁻ 2 rs0-18 ∷ rw⁻ 3 rs0-89 ∷ rw⁻ 6 rs0-18 ∷ rw⁻ 0 rs0-93 ∷ rw⁻ 6 rs0-147 ∷
       rw 0 rs0-2237 ∷ rw 4 rs0-92 ∷ rw 3 rs0-18 ∷ rw 4 rs0-18 ∷ rw 1 rs0-89 ∷ rw 5 rs0-18 ∷
       rw 2 rs0-92 ∷ rw 1 rs0-4 ∷ rw 3 rs0-41 ∷ rw 2 rs0-43 ∷ rw 1 rs0-13 ∷ rw 2 rs0-13 ∷ []) refl

  rs0-4608 : Eqn
  rs0-4608 = derive (s₀ ∷ k₀ ∷ s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 rs0-1723 ∷ rw 0 rs0-1 ∷ []) refl

  rs0-5132 : Eqn
  rs0-5132 = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-40 ∷ rw⁻ 0 rs0-8 ∷ rw⁻ 1 rs0-8 ∷ rw⁻ 2 rs0-11 ∷ rw⁻ 3 rs0-10 ∷ rw⁻ 4 rs0-11 ∷
       rw⁻ 5 rs0-11 ∷ rw⁻ 6 rs0-10 ∷ rw⁻ 7 rs0-11 ∷ rw 0 rs0-2361 ∷ rw 6 rs0-10 ∷ rw 5 rs0-11 ∷
       rw 4 rs0-11 ∷ rw 3 rs0-10 ∷ rw 2 rs0-8 ∷ rw 1 rs0-8 ∷ rw 0 rs0-7 ∷ rw 0 rs0-32 ∷ []) refl

  rs0-5144 : Eqn
  rs0-5144 = derive (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-5132 ∷ rw 5 rs0-16 ∷ []) refl

  rs0-5213 : Eqn
  rs0-5213 = derive (s₀ ∷ k₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 rs0-43 ∷ rw⁻ 2 rs0-43 ∷ rw⁻ 4 rs0-13 ∷ rw⁻ 5 rs0-14 ∷ rw⁻ 3 rs0-13 ∷ rw⁻ 4 rs0-14 ∷
       rw⁻ 5 rs0-43 ∷ rw⁻ 6 rs0-41 ∷ rw⁻ 0 rs0-17 ∷ rw⁻ 1 rs0-17 ∷ rw⁻ 2 rs0-2233 ∷ rw⁻ 0 rs0-2310 ∷
       rw 5 rs0-5132 ∷ rw 4 rs0-12 ∷ rw 3 rs0-15 ∷ rw 0 rs0-1 ∷ []) refl

  rs0-5233 : Eqn
  rs0-5233 = derive (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 5 rs0-18 ∷ rw⁻ 6 rs0-18 ∷ rw⁻ 7 rs0-18 ∷ rw 0 rs0-5144 ∷ []) refl

  rs0-6695 : Eqn
  rs0-6695 = derive (s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-32 ∷ rw⁻ 0 rs0-7 ∷ rw⁻ 1 rs0-8 ∷ rw⁻ 2 rs0-8 ∷ rw⁻ 3 rs0-11 ∷ rw⁻ 4 rs0-11 ∷
       rw⁻ 5 rs0-10 ∷ rw⁻ 6 rs0-9 ∷ rw⁻ 7 rs0-11 ∷ rw⁻ 8 rs0-11 ∷ rw 0 rs0-5213 ∷ rw 5 rs0-10 ∷
       rw 4 rs0-11 ∷ rw 3 rs0-11 ∷ rw 2 rs0-10 ∷ rw 1 rs0-9 ∷ rw 0 rs0-10 ∷ []) refl

  rs0-6761 : Eqn
  rs0-6761 = derive (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-15 ∷ rw 1 rs0-6695 ∷ rw 0 rs0-10 ∷ rw 1 rs0-41 ∷ rw 0 rs0-40 ∷ []) refl

  rs0-6765 : Eqn
  rs0-6765 = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 rs0-5233 ∷ rw 0 rs0-6761 ∷ []) refl

  rs0-6867 : Eqn
  rs0-6867 = derive (s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rs0-12 ∷ rw⁻ 1 rs0-17 ∷ rw⁻ 2 rs0-17 ∷ rw⁻ 3 rs0-5132 ∷ rw⁻ 0 rs0-18 ∷ rw⁻ 1 rs0-18 ∷
       rw⁻ 2 rs0-18 ∷ rw⁻ 3 rs0-6765 ∷ rw 0 rs0-16 ∷ []) refl

  rs0-7030 : Eqn
  rs0-7030 = derive (s₀ ∷ k₀ ∷ k₀ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 2 rs0-14 ∷ rw⁻ 1 rs0-14 ∷ rw⁻ 2 rs0-43 ∷ rw⁻ 3 rs0-43 ∷ rw⁻ 5 rs0-13 ∷ rw⁻ 4 rs0-13 ∷
       rw⁻ 5 rs0-43 ∷ rw⁻ 6 rs0-43 ∷ rw⁻ 7 rs0-41 ∷ rw 0 rs0-6867 ∷ []) refl

  rs0-7904 : Eqn
  rs0-7904 = derive (s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-32 ∷ rw⁻ 0 rs0-7 ∷ rw⁻ 1 rs0-8 ∷ rw⁻ 2 rs0-8 ∷ rw⁻ 3 rs0-9 ∷ rw⁻ 4 rs0-11 ∷
       rw⁻ 5 rs0-11 ∷ rw⁻ 6 rs0-10 ∷ rw⁻ 7 rs0-11 ∷ rw⁻ 8 rs0-11 ∷ rw 0 rs0-7030 ∷ rw 5 rs0-10 ∷
       rw 4 rs0-9 ∷ rw 3 rs0-10 ∷ rw 2 rs0-11 ∷ rw 1 rs0-11 ∷ rw 0 rs0-10 ∷ []) refl

  rs0-7947 : Eqn
  rs0-7947 = derive (s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-15 ∷ rw 1 rs0-7904 ∷ rw 0 rs0-10 ∷ rw 1 rs0-41 ∷ rw 0 rs0-40 ∷ []) refl

  rs0-7979 : Eqn
  rs0-7979 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rs0-7947 ∷ rw 6 rs0-16 ∷ []) refl

  rs0-8031 : Eqn
  rs0-8031 = derive (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 2 rs0-18 ∷ rw⁻ 3 rs0-18 ∷ rw⁻ 1 rs0-18 ∷ rw⁻ 2 rs0-18 ∷ rw⁻ 0 rs0-18 ∷ rw⁻ 1 rs0-18 ∷
       rw⁻ 2 rs0-92 ∷ rw⁻ 5 rs0-18 ∷ rw⁻ 6 rs0-18 ∷ rw 0 rs0-7979 ∷ []) refl

  rs0-8506 : Eqn
  rs0-8506 = derive (s₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rs0-12 ∷ rw⁻ 1 rs0-8031 ∷ rw 0 rs0-4 ∷ []) refl

private
  ax-order-I : Eqn
  ax-order-I = derive (ι ∷ ι ∷ ι ∷ ι ∷ [])
    ([])
    (rw 0 rs0-5 ∷ rw 1 rs0-10 ∷ rw 0 rs0-10 ∷ rw 0 rs0-23 ∷ []) refl

  ax-order-S0 : Eqn
  ax-order-S0 = derive (s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
    ([])
    (rw 0 rs0-1 ∷ []) refl

  ax-order-K0 : Eqn
  ax-order-K0 = derive (k₀ ∷ k₀ ∷ [])
    (ι ∷ ι ∷ ι ∷ [])
    (rw⁻ 0 rs0-42 ∷ []) refl

  ax-order-SK0 : Eqn
  ax-order-SK0 = derive (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (ι ∷ ι ∷ ι ∷ [])
    (rw 0 rs0-3 ∷ rw 0 rs0-5 ∷ rw⁻ 0 rs0-5 ∷ []) refl

  ax-order-S1 : Eqn
  ax-order-S1 = derive (s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
    ([])
    (rw 0 rs0-4 ∷ []) refl

  ax-order-K1 : Eqn
  ax-order-K1 = derive (k₁ ∷ k₁ ∷ [])
    (ι ∷ ι ∷ ι ∷ [])
    (rw⁻ 0 rs0-5 ∷ []) refl

  ax-order-SK1 : Eqn
  ax-order-SK1 = derive (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (ι ∷ ι ∷ ι ∷ [])
    (rw 0 rs0-6 ∷ rw 0 rs0-5 ∷ rw⁻ 0 rs0-5 ∷ []) refl

  ax-comm-IS0 : Eqn
  ax-comm-IS0 = derive (s₀ ∷ ι ∷ [])
    (ι ∷ s₀ ∷ [])
    (rw 0 rs0-7 ∷ []) refl

  ax-comm-IK0 : Eqn
  ax-comm-IK0 = derive (k₀ ∷ ι ∷ [])
    (ι ∷ k₀ ∷ [])
    (rw 0 rs0-8 ∷ []) refl

  ax-comm-IS1 : Eqn
  ax-comm-IS1 = derive (s₁ ∷ ι ∷ [])
    (ι ∷ s₁ ∷ [])
    (rw 0 rs0-9 ∷ []) refl

  ax-comm-IK1 : Eqn
  ax-comm-IK1 = derive (k₁ ∷ ι ∷ [])
    (ι ∷ k₁ ∷ [])
    (rw 0 rs0-10 ∷ []) refl

  ax-comm-Iz : Eqn
  ax-comm-Iz = derive (cs ∷ cs ∷ ι ∷ [])
    (ι ∷ cs ∷ cs ∷ [])
    (rw 1 rs0-11 ∷ rw 0 rs0-11 ∷ []) refl

  ax-comm-ts : Eqn
  ax-comm-ts = derive (s₁ ∷ s₀ ∷ [])
    (s₀ ∷ s₁ ∷ [])
    (rw 0 rs0-12 ∷ []) refl

  ax-comm-lk : Eqn
  ax-comm-lk = derive (k₁ ∷ k₀ ∷ [])
    (k₀ ∷ k₁ ∷ [])
    (rw 0 rs0-13 ∷ []) refl

  ax-comm-tk : Eqn
  ax-comm-tk = derive (s₁ ∷ k₀ ∷ [])
    (k₀ ∷ s₁ ∷ [])
    (rw 0 rs0-14 ∷ []) refl

  ax-comm-ls : Eqn
  ax-comm-ls = derive (k₁ ∷ s₀ ∷ [])
    (s₀ ∷ k₁ ∷ [])
    (rw 0 rs0-15 ∷ []) refl

  ax-z2 : Eqn
  ax-z2 = derive (cs ∷ cs ∷ cs ∷ cs ∷ [])
    ([])
    (rw 0 rs0-16 ∷ []) refl

  ax-z-s : Eqn
  ax-z-s = derive (cs ∷ cs ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ cs ∷ [])
    (rw 1 rs0-17 ∷ rw 0 rs0-17 ∷ []) refl

  ax-z-t : Eqn
  ax-z-t = derive (cs ∷ cs ∷ s₁ ∷ [])
    (s₁ ∷ cs ∷ cs ∷ [])
    (rw 1 rs0-18 ∷ rw 0 rs0-18 ∷ []) refl

  ax-C8 : Eqn
  ax-C8 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rs0-579 ∷ rw⁻ 1 rs0-15 ∷ rw⁻ 2 rs0-12 ∷ rw⁻ 3 rs0-12 ∷ rw⁻ 4 rs0-15 ∷ rw⁻ 0 rs0-15 ∷
       rw⁻ 1 rs0-12 ∷ rw⁻ 2 rs0-12 ∷ rw⁻ 3 rs0-15 ∷ []) refl

  ax-C9 : Eqn
  ax-C9 = derive (cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rs0-994 ∷ []) refl

  ax-C10 : Eqn
  ax-C10 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rs0-8506 ∷ rw⁻ 0 rs0-12 ∷ rw⁻ 1 rs0-15 ∷ rw⁻ 2 rs0-12 ∷ []) refl

  ax-C11 : Eqn
  ax-C11 = derive (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rs0-4608 ∷ []) refl

------------------------------------------------------------------------
-- The Clifford equations

private
  rtc-0 : Eqn
  rtc-0 = ax-order-I

  rtc-1 : Eqn
  rtc-1 = ax-order-S0

  rtc-2 : Eqn
  rtc-2 = sym⁼ (ax-order-K0)

  rtc-3 : Eqn
  rtc-3 = ax-order-SK0

  rtc-4 : Eqn
  rtc-4 = ax-order-S1

  rtc-5 : Eqn
  rtc-5 = sym⁼ (ax-order-K1)

  rtc-6 : Eqn
  rtc-6 = ax-order-SK1

  rtc-7 : Eqn
  rtc-7 = ax-comm-IS0

  rtc-8 : Eqn
  rtc-8 = ax-comm-IK0

  rtc-9 : Eqn
  rtc-9 = ax-comm-IS1

  rtc-10 : Eqn
  rtc-10 = ax-comm-IK1

  rtc-11 : Eqn
  rtc-11 = ax-comm-Iz

  rtc-12 : Eqn
  rtc-12 = ax-comm-ts

  rtc-13 : Eqn
  rtc-13 = ax-comm-lk

  rtc-14 : Eqn
  rtc-14 = ax-comm-tk

  rtc-15 : Eqn
  rtc-15 = ax-comm-ls

  rtc-16 : Eqn
  rtc-16 = ax-z2

  rtc-17 : Eqn
  rtc-17 = ax-z-s

  rtc-18 : Eqn
  rtc-18 = ax-z-t

  rtc-19 : Eqn
  rtc-19 = sym⁼ (ax-C8)

  rtc-20 : Eqn
  rtc-20 = sym⁼ (ax-C9)

  rtc-21 : Eqn
  rtc-21 = sym⁼ (ax-C10)

  rtc-22 : Eqn
  rtc-22 = sym⁼ (ax-C11)

  rtc-23 : Eqn
  rtc-23 = derive (ι ∷ k₁ ∷ k₁ ∷ [])
    ([])
    (rw⁻ 0 rtc-10 ∷ rw⁻ 1 rtc-10 ∷ rw⁻ 0 rtc-5 ∷ rw 0 rtc-0 ∷ []) refl

  rtc-24 : Eqn
  rtc-24 = derive (s₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 1 rtc-15 ∷ rw⁻ 2 rtc-12 ∷ rw⁻ 3 rtc-12 ∷ rw⁻ 4 rtc-15 ∷ rw⁻ 0 rtc-15 ∷ rw⁻ 1 rtc-12 ∷
       rw⁻ 2 rtc-12 ∷ rw⁻ 3 rtc-15 ∷ rw 0 rtc-19 ∷ []) refl

  rtc-25 : Eqn
  rtc-25 = derive (s₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-12 ∷ rw⁻ 1 rtc-15 ∷ rw⁻ 2 rtc-12 ∷ rw 0 rtc-21 ∷ []) refl

  rtc-26 : Eqn
  rtc-26 = derive (ι ∷ s₀ ∷ k₁ ∷ k₁ ∷ [])
    (s₀ ∷ [])
    (rw⁻ 0 rtc-7 ∷ rw 1 rtc-23 ∷ []) refl

  rtc-30 : Eqn
  rtc-30 = derive (cs ∷ cs ∷ k₀ ∷ s₁ ∷ [])
    (s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 2 rtc-14 ∷ rw 0 rtc-18 ∷ []) refl

  rtc-31 : Eqn
  rtc-31 = derive (s₀ ∷ k₁ ∷ k₁ ∷ [])
    (s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-15 ∷ rw⁻ 1 rtc-15 ∷ rw⁻ 0 rtc-5 ∷ rw⁻ 2 rtc-7 ∷ rw⁻ 1 rtc-7 ∷ rw⁻ 0 rtc-7 ∷
       rw 1 rtc-2 ∷ []) refl

  rtc-32 : Eqn
  rtc-32 = derive (ι ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ [])
    (rw⁻ 1 rtc-31 ∷ rw 0 rtc-26 ∷ []) refl

  rtc-33 : Eqn
  rtc-33 = derive (k₀ ∷ k₁ ∷ k₁ ∷ [])
    (k₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-13 ∷ rw⁻ 1 rtc-13 ∷ rw⁻ 0 rtc-5 ∷ rw⁻ 2 rtc-8 ∷ rw⁻ 1 rtc-8 ∷ rw⁻ 0 rtc-8 ∷
       rw 1 rtc-2 ∷ []) refl

  rtc-37 : Eqn
  rtc-37 = derive (cs ∷ cs ∷ k₀ ∷ k₀ ∷ [])
    (k₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 rtc-2 ∷ rw 0 rtc-11 ∷ rw 1 rtc-11 ∷ rw 2 rtc-11 ∷ rw 0 rtc-5 ∷ []) refl

  rtc-38 : Eqn
  rtc-38 = derive (k₀ ∷ k₀ ∷ k₀ ∷ k₀ ∷ [])
    (ι ∷ ι ∷ [])
    (rw⁻ 1 rtc-33 ∷ rw⁻ 0 rtc-2 ∷ rw 2 rtc-23 ∷ []) refl

  rtc-40 : Eqn
  rtc-40 = derive (ι ∷ k₀ ∷ k₀ ∷ [])
    ([])
    (rw⁻ 1 rtc-2 ∷ rw 0 rtc-5 ∷ rw 1 rtc-10 ∷ rw 0 rtc-10 ∷ rw 0 rtc-23 ∷ []) refl

  rtc-41 : Eqn
  rtc-41 = derive (k₁ ∷ k₁ ∷ [])
    (k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-5 ∷ rw 0 rtc-2 ∷ []) refl

  rtc-42 : Eqn
  rtc-42 = derive (ι ∷ ι ∷ ι ∷ [])
    (k₀ ∷ k₀ ∷ [])
    (rw 0 rtc-5 ∷ rw 0 rtc-41 ∷ []) refl

  rtc-43 : Eqn
  rtc-43 = derive (cs ∷ cs ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw 0 rtc-37 ∷ rw 0 rtc-41 ∷ []) refl

  rtc-44 : Eqn
  rtc-44 = derive (k₀ ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-41 ∷ rw 1 rtc-15 ∷ rw 0 rtc-15 ∷ rw 1 rtc-41 ∷ []) refl

  rtc-45 : Eqn
  rtc-45 = derive (ι ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rtc-7 ∷ rw 1 rtc-32 ∷ []) refl

  rtc-46 : Eqn
  rtc-46 = derive (ι ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rtc-8 ∷ rw 1 rtc-32 ∷ []) refl

  rtc-47 : Eqn
  rtc-47 = derive (cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₁ ∷ [])
    (s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 3 rtc-12 ∷ rw 0 rtc-30 ∷ []) refl

  rtc-48 : Eqn
  rtc-48 = derive (ι ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 3 rtc-44 ∷ rw 0 rtc-32 ∷ []) refl

  rtc-49 : Eqn
  rtc-49 = derive (cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 3 rtc-44 ∷ rw 0 rtc-43 ∷ []) refl

  rtc-50 : Eqn
  rtc-50 = derive (ι ∷ s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rtc-7 ∷ rw 1 rtc-45 ∷ []) refl

  rtc-51 : Eqn
  rtc-51 = derive (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rtc-8 ∷ rw 1 rtc-45 ∷ []) refl

  rtc-53 : Eqn
  rtc-53 = derive (ι ∷ k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 4 rtc-44 ∷ rw 0 rtc-46 ∷ []) refl

  rtc-55 : Eqn
  rtc-55 = derive (cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ [])
    (s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 4 rtc-14 ∷ rw 0 rtc-47 ∷ []) refl

  rtc-56 : Eqn
  rtc-56 = derive (k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-1 ∷ rw 3 rtc-3 ∷ rw 2 rtc-7 ∷ rw 1 rtc-7 ∷ rw 0 rtc-7 ∷ rw 3 rtc-7 ∷
       rw 2 rtc-7 ∷ rw 1 rtc-7 ∷ rw 4 rtc-7 ∷ rw 3 rtc-7 ∷ rw 2 rtc-7 ∷ rw 0 rtc-42 ∷
       rw 0 rtc-44 ∷ rw 1 rtc-44 ∷ rw 2 rtc-44 ∷ []) refl

  rtc-57 : Eqn
  rtc-57 = derive (k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-53 ∷ rw 1 rtc-56 ∷ rw 0 rtc-50 ∷ []) refl

  rtc-63 : Eqn
  rtc-63 = derive (k₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rtc-57 ∷ rw 0 rtc-44 ∷ rw 2 rtc-44 ∷ []) refl

  rtc-66 : Eqn
  rtc-66 = derive (k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₀ ∷ k₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rtc-4 ∷ rw 3 rtc-6 ∷ rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 0 rtc-9 ∷ rw 3 rtc-9 ∷
       rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 4 rtc-9 ∷ rw 3 rtc-9 ∷ rw 2 rtc-9 ∷ rw 0 rtc-42 ∷ []) refl

  rtc-69 : Eqn
  rtc-69 = derive (k₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rtc-50 ∷ rw 0 rtc-8 ∷ rw 1 rtc-63 ∷ rw 0 rtc-48 ∷ []) refl

  rtc-72 : Eqn
  rtc-72 = derive (s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-17 ∷ rw⁻ 2 rtc-69 ∷ rw⁻ 5 rtc-17 ∷ rw⁻ 4 rtc-17 ∷ rw⁻ 3 rtc-17 ∷ rw⁻ 0 rtc-22 ∷
       rw 7 rtc-1 ∷ []) refl

  rtc-73 : Eqn
  rtc-73 = derive (k₀ ∷ s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-1 ∷ rw 3 rtc-22 ∷ []) refl

  rtc-74 : Eqn
  rtc-74 = derive (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-1 ∷ rw 3 rtc-25 ∷ []) refl

  rtc-75 : Eqn
  rtc-75 = derive (cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 4 rtc-44 ∷ rw 0 rtc-49 ∷ []) refl

  rtc-79 : Eqn
  rtc-79 = derive (k₀ ∷ k₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₀ ∷ k₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 1 rtc-13 ∷ rw⁻ 0 rtc-13 ∷ rw⁻ 1 rtc-66 ∷ rw 0 rtc-41 ∷ []) refl

  rtc-81 : Eqn
  rtc-81 = derive (k₀ ∷ k₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (k₀ ∷ k₀ ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-79 ∷ rw⁻ 1 rtc-13 ∷ rw⁻ 2 rtc-14 ∷ rw⁻ 0 rtc-13 ∷ rw⁻ 1 rtc-14 ∷ rw⁻ 2 rtc-66 ∷
       rw 0 rtc-66 ∷ rw 2 rtc-4 ∷ []) refl

  rtc-82 : Eqn
  rtc-82 = derive (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (k₁ ∷ [])
    (rw⁻ 0 rtc-40 ∷ rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-8 ∷ rw⁻ 2 rtc-9 ∷ rw⁻ 3 rtc-10 ∷ rw⁻ 4 rtc-9 ∷
       rw⁻ 5 rtc-10 ∷ rw⁻ 6 rtc-9 ∷ rw 0 rtc-81 ∷ rw 2 rtc-10 ∷ rw 1 rtc-8 ∷ rw 0 rtc-8 ∷
       rw 0 rtc-40 ∷ []) refl

  rtc-83 : Eqn
  rtc-83 = derive (k₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-82 ∷ rw 4 rtc-4 ∷ []) refl

  rtc-84 : Eqn
  rtc-84 = derive (k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-4 ∷ rw 3 rtc-82 ∷ []) refl

  rtc-85 : Eqn
  rtc-85 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 2 rtc-83 ∷ rw 0 rtc-84 ∷ []) refl

  rtc-91 : Eqn
  rtc-91 = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 3 rtc-13 ∷ rw⁻ 2 rtc-15 ∷ rw⁻ 1 rtc-15 ∷ rw⁻ 0 rtc-13 ∷ rw 1 rtc-20 ∷ []) refl

  rtc-93 : Eqn
  rtc-93 = derive (cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rtc-20 ∷ rw 6 rtc-16 ∷ []) refl

  rtc-97 : Eqn
  rtc-97 = derive (ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 rtc-20 ∷ rw 0 rtc-40 ∷ []) refl

  rtc-112 : Eqn
  rtc-112 = derive (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 rtc-24 ∷ rw 0 rtc-1 ∷ []) refl

  rtc-115 : Eqn
  rtc-115 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-24 ∷ rw 6 rtc-16 ∷ []) refl

  rtc-123 : Eqn
  rtc-123 = derive (cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-1 ∷ rw 3 rtc-72 ∷ rw 0 rtc-1 ∷ []) refl

  rtc-125 : Eqn
  rtc-125 = derive (k₀ ∷ s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-123 ∷ rw 5 rtc-16 ∷ []) refl

  rtc-126 : Eqn
  rtc-126 = derive (s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-47 ∷ rw⁻ 2 rtc-123 ∷ rw 0 rtc-16 ∷ []) refl

  rtc-130 : Eqn
  rtc-130 = derive (k₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rtc-15 ∷ rw⁻ 0 rtc-13 ∷ rw 1 rtc-125 ∷ []) refl

  rtc-134 : Eqn
  rtc-134 = derive (ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 rtc-125 ∷ rw 0 rtc-40 ∷ []) refl

  rtc-149 : Eqn
  rtc-149 = derive (k₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 2 rtc-14 ∷ rw⁻ 3 rtc-14 ∷ rw⁻ 4 rtc-14 ∷ rw⁻ 1 rtc-12 ∷ rw⁻ 2 rtc-12 ∷ rw⁻ 3 rtc-12 ∷
       rw⁻ 0 rtc-14 ∷ rw⁻ 1 rtc-14 ∷ rw⁻ 2 rtc-14 ∷ rw⁻ 3 rtc-126 ∷ rw 0 rtc-4 ∷ []) refl

  rtc-163 : Eqn
  rtc-163 = derive (s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-134 ∷ rw 6 rtc-44 ∷ rw 0 rtc-97 ∷ []) refl

  rtc-164 : Eqn
  rtc-164 = derive (s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rtc-134 ∷ rw 2 rtc-49 ∷ rw 0 rtc-40 ∷ []) refl

  rtc-165 : Eqn
  rtc-165 = derive (s₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rtc-163 ∷ rw 0 rtc-164 ∷ []) refl

  rtc-170 : Eqn
  rtc-170 = derive (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 3 rtc-164 ∷ rw 0 rtc-1 ∷ []) refl

  rtc-174 : Eqn
  rtc-174 = derive (s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rtc-15 ∷ rw 1 rtc-164 ∷ rw 0 rtc-13 ∷ []) refl

  rtc-175 : Eqn
  rtc-175 = derive (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 2 rtc-164 ∷ rw 0 rtc-17 ∷ rw 1 rtc-18 ∷ rw 2 rtc-16 ∷ rw 1 rtc-14 ∷ []) refl

  rtc-192 : Eqn
  rtc-192 = derive (k₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 rtc-15 ∷ rw⁻ 0 rtc-13 ∷ rw 1 rtc-73 ∷ rw 0 rtc-15 ∷ rw 1 rtc-15 ∷ rw 2 rtc-15 ∷ []) refl

  rtc-203 : Eqn
  rtc-203 = derive (ι ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 1 rtc-1 ∷ rw⁻ 4 rtc-69 ∷ rw⁻ 5 rtc-73 ∷ rw 0 rtc-50 ∷ rw 0 rtc-1 ∷ []) refl

  rtc-209 : Eqn
  rtc-209 = derive (ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 rtc-1 ∷ rw⁻ 2 rtc-57 ∷ rw⁻ 5 rtc-17 ∷ rw⁻ 1 rtc-69 ∷ rw⁻ 4 rtc-17 ∷ rw⁻ 3 rtc-17 ∷
       rw⁻ 5 rtc-57 ∷ rw⁻ 2 rtc-17 ∷ rw⁻ 4 rtc-69 ∷ rw⁻ 6 rtc-73 ∷ rw 0 rtc-134 ∷ rw 5 rtc-17 ∷
       rw 6 rtc-18 ∷ rw 2 rtc-47 ∷ rw 7 rtc-16 ∷ rw 5 rtc-57 ∷ rw 3 rtc-17 ∷ rw 2 rtc-12 ∷
       rw 1 rtc-12 ∷ rw 4 rtc-17 ∷ rw 3 rtc-12 ∷ rw 2 rtc-12 ∷ rw 5 rtc-17 ∷ rw 4 rtc-12 ∷
       rw 3 rtc-12 ∷ rw 0 rtc-1 ∷ []) refl

  rtc-210 : Eqn
  rtc-210 = derive (k₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 rtc-203 ∷ rw 0 rtc-8 ∷ rw 0 rtc-40 ∷ []) refl

  rtc-219 : Eqn
  rtc-219 = derive (k₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-13 ∷ rw 1 rtc-210 ∷ rw 0 rtc-15 ∷ rw 1 rtc-13 ∷ []) refl

  rtc-220 : Eqn
  rtc-220 = derive (k₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-14 ∷ rw 1 rtc-210 ∷ rw 0 rtc-12 ∷ rw 1 rtc-14 ∷ []) refl

  rtc-227 : Eqn
  rtc-227 = derive (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-40 ∷ rw⁻ 0 rtc-8 ∷ rw 1 rtc-209 ∷ []) refl

  rtc-229 : Eqn
  rtc-229 = derive (k₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-227 ∷ rw 6 rtc-16 ∷ []) refl

  rtc-230 : Eqn
  rtc-230 = derive (s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 rtc-30 ∷ rw⁻ 0 rtc-30 ∷ rw⁻ 2 rtc-227 ∷ rw 0 rtc-16 ∷ []) refl

  rtc-235 : Eqn
  rtc-235 = derive (k₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-13 ∷ rw 1 rtc-229 ∷ []) refl

  rtc-239 : Eqn
  rtc-239 = derive (ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 rtc-229 ∷ rw 0 rtc-40 ∷ []) refl

  rtc-253 : Eqn
  rtc-253 = derive (ι ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 rtc-13 ∷ rw⁻ 0 rtc-10 ∷ rw 1 rtc-239 ∷ []) refl

  rtc-257 : Eqn
  rtc-257 = derive (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 5 rtc-13 ∷ rw⁻ 6 rtc-14 ∷ rw 0 rtc-74 ∷ []) refl

  rtc-266 : Eqn
  rtc-266 = derive (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-74 ∷ rw 5 rtc-84 ∷ rw 3 rtc-18 ∷ rw 4 rtc-18 ∷ rw 1 rtc-83 ∷ rw 5 rtc-18 ∷
       rw 2 rtc-84 ∷ rw 0 rtc-4 ∷ []) refl

  rtc-289 : Eqn
  rtc-289 = derive (s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 rtc-43 ∷ rw⁻ 5 rtc-13 ∷ rw⁻ 6 rtc-14 ∷ rw⁻ 7 rtc-14 ∷ rw⁻ 4 rtc-13 ∷ rw⁻ 5 rtc-14 ∷
       rw⁻ 6 rtc-14 ∷ rw⁻ 7 rtc-41 ∷ rw 0 rtc-112 ∷ []) refl

  rtc-294 : Eqn
  rtc-294 = derive (s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-17 ∷ rw⁻ 2 rtc-15 ∷ rw⁻ 3 rtc-12 ∷ rw⁻ 0 rtc-1 ∷ rw⁻ 3 rtc-17 ∷ rw⁻ 5 rtc-15 ∷
       rw⁻ 6 rtc-12 ∷ rw⁻ 2 rtc-17 ∷ rw⁻ 4 rtc-15 ∷ rw⁻ 5 rtc-12 ∷ rw⁻ 6 rtc-74 ∷ rw 0 rtc-112 ∷
       rw 4 rtc-18 ∷ rw 5 rtc-16 ∷ rw 0 rtc-85 ∷ rw 3 rtc-83 ∷ rw 0 rtc-4 ∷ []) refl

  rtc-301 : Eqn
  rtc-301 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-1 ∷ rw 3 rtc-294 ∷ []) refl

  rtc-317 : Eqn
  rtc-317 = derive (s₀ ∷ k₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-44 ∷ rw⁻ 2 rtc-17 ∷ rw⁻ 0 rtc-43 ∷ rw 3 rtc-130 ∷ []) refl

  rtc-326 : Eqn
  rtc-326 = derive (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-57 ∷ rw 2 rtc-130 ∷ []) refl

  rtc-357 : Eqn
  rtc-357 = derive (k₀ ∷ s₀ ∷ k₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 3 rtc-83 ∷ rw⁻ 2 rtc-13 ∷ rw⁻ 1 rtc-15 ∷ rw⁻ 0 rtc-13 ∷ rw 1 rtc-149 ∷ []) refl

  rtc-374 : Eqn
  rtc-374 = derive (s₀ ∷ s₀ ∷ k₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 2 rtc-13 ∷ rw⁻ 1 rtc-15 ∷ rw⁻ 0 rtc-15 ∷ rw 1 rtc-165 ∷ rw 0 rtc-13 ∷ []) refl

  rtc-376 : Eqn
  rtc-376 = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-165 ∷ rw 2 rtc-229 ∷ []) refl

  rtc-377 : Eqn
  rtc-377 = derive (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 3 rtc-13 ∷ rw⁻ 2 rtc-15 ∷ rw⁻ 1 rtc-15 ∷ rw⁻ 0 rtc-15 ∷ rw 1 rtc-170 ∷ []) refl

  rtc-386 : Eqn
  rtc-386 = derive (s₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rtc-12 ∷ rw 1 rtc-174 ∷ rw 0 rtc-14 ∷ []) refl

  rtc-394 : Eqn
  rtc-394 = derive (s₀ ∷ k₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 rtc-83 ∷ rw⁻ 1 rtc-13 ∷ rw⁻ 2 rtc-14 ∷ rw⁻ 3 rtc-227 ∷ rw 0 rtc-174 ∷ []) refl

  rtc-409 : Eqn
  rtc-409 = derive (k₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 rtc-47 ∷ rw 0 rtc-219 ∷ rw 6 rtc-18 ∷ rw 3 rtc-30 ∷ []) refl

  rtc-424 : Eqn
  rtc-424 = derive (k₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-14 ∷ rw 1 rtc-220 ∷ rw 0 rtc-12 ∷ rw 1 rtc-14 ∷ rw 1 rtc-229 ∷ []) refl

  rtc-483 : Eqn
  rtc-483 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-1 ∷ rw 1 rtc-266 ∷ []) refl

  rtc-488 : Eqn
  rtc-488 = derive (s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 rtc-18 ∷ rw⁻ 0 rtc-17 ∷ rw⁻ 2 rtc-483 ∷ rw 0 rtc-16 ∷ []) refl

  rtc-492 : Eqn
  rtc-492 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₀ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 3 rtc-18 ∷ rw⁻ 5 rtc-83 ∷ rw 0 rtc-483 ∷ []) refl

  rtc-506 : Eqn
  rtc-506 = derive (s₀ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-483 ∷ rw 6 rtc-230 ∷ rw 5 rtc-13 ∷ []) refl

  rtc-507 : Eqn
  rtc-507 = derive (s₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rtc-12 ∷ rw 1 rtc-488 ∷ []) refl

  rtc-510 : Eqn
  rtc-510 = derive (s₀ ∷ k₀ ∷ k₀ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 2 rtc-14 ∷ rw⁻ 1 rtc-14 ∷ rw⁻ 2 rtc-43 ∷ rw⁻ 5 rtc-13 ∷ rw⁻ 4 rtc-13 ∷ rw⁻ 5 rtc-43 ∷
       rw⁻ 7 rtc-41 ∷ rw 0 rtc-488 ∷ []) refl

  rtc-523 : Eqn
  rtc-523 = derive (s₀ ∷ s₀ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 1 rtc-12 ∷ rw⁻ 2 rtc-483 ∷ rw 0 rtc-488 ∷ []) refl

  rtc-539 : Eqn
  rtc-539 = derive (s₀ ∷ s₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-301 ∷ rw 7 rtc-16 ∷ []) refl

  rtc-540 : Eqn
  rtc-540 = derive (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 rtc-17 ∷ rw⁻ 1 rtc-17 ∷ rw⁻ 0 rtc-17 ∷ rw⁻ 2 rtc-301 ∷ rw 0 rtc-16 ∷ []) refl

  rtc-541 : Eqn
  rtc-541 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 7 rtc-18 ∷ rw 0 rtc-301 ∷ rw 3 rtc-84 ∷ []) refl

  rtc-578 : Eqn
  rtc-578 = derive (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-13 ∷ rw 1 rtc-376 ∷ rw 0 rtc-15 ∷ rw 1 rtc-15 ∷ []) refl

  rtc-591 : Eqn
  rtc-591 = derive (k₀ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 rtc-83 ∷ rw⁻ 0 rtc-13 ∷ rw 1 rtc-424 ∷ rw 0 rtc-15 ∷ []) refl

  rtc-644 : Eqn
  rtc-644 = derive (s₀ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 8 rtc-13 ∷ rw 0 rtc-507 ∷ rw 5 rtc-14 ∷ rw 4 rtc-13 ∷ []) refl

  rtc-653 : Eqn
  rtc-653 = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 rtc-4 ∷ rw⁻ 4 rtc-30 ∷ rw⁻ 7 rtc-507 ∷ rw 0 rtc-424 ∷ rw 4 rtc-30 ∷ rw 1 rtc-30 ∷
       rw 0 rtc-164 ∷ rw 1 rtc-47 ∷ rw 0 rtc-210 ∷ rw 5 rtc-16 ∷ []) refl

  rtc-684 : Eqn
  rtc-684 = derive (ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₀ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-10 ∷ rw⁻ 1 rtc-11 ∷ rw⁻ 3 rtc-10 ∷ rw⁻ 4 rtc-9 ∷ rw⁻ 5 rtc-10 ∷ rw⁻ 0 rtc-510 ∷
       rw 7 rtc-11 ∷ rw 6 rtc-10 ∷ rw 4 rtc-11 ∷ rw 3 rtc-9 ∷ rw 2 rtc-8 ∷ rw 1 rtc-8 ∷
       rw 0 rtc-7 ∷ rw 0 rtc-32 ∷ []) refl

  rtc-713 : Eqn
  rtc-713 = derive (s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-15 ∷ rw⁻ 1 rtc-684 ∷ rw 0 rtc-10 ∷ rw 1 rtc-41 ∷ rw 0 rtc-40 ∷ []) refl

  rtc-718 : Eqn
  rtc-718 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-713 ∷ rw 6 rtc-16 ∷ []) refl

  rtc-735 : Eqn
  rtc-735 = derive (s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-17 ∷ rw⁻ 2 rtc-718 ∷ rw 0 rtc-16 ∷ []) refl

  rtc-772 : Eqn
  rtc-772 = derive (s₀ ∷ k₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 rtc-43 ∷ rw⁻ 4 rtc-13 ∷ rw⁻ 5 rtc-14 ∷ rw⁻ 3 rtc-13 ∷ rw⁻ 4 rtc-14 ∷ rw⁻ 5 rtc-43 ∷
       rw⁻ 7 rtc-41 ∷ rw 0 rtc-735 ∷ []) refl

  rtc-773 : Eqn
  rtc-773 = derive (cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-317 ∷ rw 0 rtc-772 ∷ rw 5 rtc-13 ∷ []) refl

  rtc-786 : Eqn
  rtc-786 = derive (s₀ ∷ s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 rtc-523 ∷ rw 0 rtc-1 ∷ []) refl

  rtc-814 : Eqn
  rtc-814 = derive (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 rtc-17 ∷ rw⁻ 3 rtc-15 ∷ rw⁻ 0 rtc-17 ∷ rw⁻ 2 rtc-15 ∷ rw⁻ 0 rtc-1 ∷ rw⁻ 3 rtc-17 ∷
       rw⁻ 5 rtc-15 ∷ rw⁻ 6 rtc-74 ∷ rw 0 rtc-540 ∷ rw 5 rtc-18 ∷ rw 6 rtc-16 ∷ rw 4 rtc-84 ∷
       rw 2 rtc-18 ∷ rw 3 rtc-18 ∷ rw 0 rtc-83 ∷ rw 4 rtc-18 ∷ rw 1 rtc-84 ∷ rw 0 rtc-4 ∷ []) refl

  rtc-821 : Eqn
  rtc-821 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-1 ∷ rw 2 rtc-814 ∷ []) refl

  rtc-824 : Eqn
  rtc-824 = derive (s₀ ∷ s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-821 ∷ rw 6 rtc-16 ∷ []) refl

  rtc-825 : Eqn
  rtc-825 = derive (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 rtc-17 ∷ rw⁻ 0 rtc-17 ∷ rw⁻ 2 rtc-821 ∷ rw 0 rtc-16 ∷ []) refl

  rtc-846 : Eqn
  rtc-846 = derive (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-229 ∷ rw 6 rtc-821 ∷ rw 0 rtc-220 ∷ rw 6 rtc-17 ∷ rw 1 rtc-210 ∷ rw 6 rtc-16 ∷ []) refl

  rtc-850 : Eqn
  rtc-850 = derive (s₀ ∷ s₀ ∷ s₀ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 rtc-12 ∷ rw⁻ 1 rtc-12 ∷ rw⁻ 2 rtc-821 ∷ rw 0 rtc-488 ∷ []) refl

  rtc-856 : Eqn
  rtc-856 = derive (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rtc-507 ∷ rw 3 rtc-821 ∷ rw 2 rtc-12 ∷ rw 1 rtc-12 ∷ rw 3 rtc-12 ∷ rw 2 rtc-12 ∷
       rw 1 rtc-523 ∷ []) refl

  rtc-857 : Eqn
  rtc-857 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-506 ∷ rw 1 rtc-856 ∷ rw 0 rtc-786 ∷ rw 5 rtc-13 ∷ []) refl

  rtc-863 : Eqn
  rtc-863 = derive (s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 rtc-41 ∷ rw⁻ 1 rtc-15 ∷ rw⁻ 0 rtc-15 ∷ rw 1 rtc-824 ∷ []) refl

  rtc-878 : Eqn
  rtc-878 = derive (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 6 rtc-16 ∷ rw⁻ 1 rtc-210 ∷ rw⁻ 6 rtc-17 ∷ rw⁻ 0 rtc-220 ∷ rw 6 rtc-824 ∷ rw 0 rtc-229 ∷ []) refl

  rtc-881 : Eqn
  rtc-881 = derive (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 rtc-825 ∷ rw 0 rtc-12 ∷ rw 1 rtc-12 ∷ rw 1 rtc-488 ∷ []) refl

  rtc-884 : Eqn
  rtc-884 = derive (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 7 rtc-13 ∷ rw 0 rtc-825 ∷ []) refl

  rtc-894 : Eqn
  rtc-894 = derive (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-881 ∷ rw 5 rtc-16 ∷ []) refl

  rtc-913 : Eqn
  rtc-913 = derive (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 5 rtc-15 ∷ rw⁻ 4 rtc-13 ∷ rw⁻ 0 rtc-894 ∷ rw 5 rtc-126 ∷ rw 4 rtc-13 ∷ rw 5 rtc-15 ∷
       rw 6 rtc-13 ∷ []) refl

  rtc-1079 : Eqn
  rtc-1079 = derive (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-376 ∷ rw 4 rtc-884 ∷ []) refl

  rtc-1150 : Eqn
  rtc-1150 = derive (ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 5 rtc-863 ∷ rw 0 rtc-97 ∷ rw 0 rtc-165 ∷ rw 0 rtc-376 ∷ []) refl

  rtc-1230 : Eqn
  rtc-1230 = derive (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 4 rtc-13 ∷ rw⁻ 5 rtc-16 ∷ rw⁻ 3 rtc-15 ∷ rw⁻ 4 rtc-17 ∷ rw⁻ 2 rtc-15 ∷ rw⁻ 3 rtc-17 ∷
       rw⁻ 5 rtc-376 ∷ rw 0 rtc-253 ∷ rw 6 rtc-17 ∷ rw 7 rtc-17 ∷ rw 8 rtc-16 ∷ []) refl

  rtc-1339 : Eqn
  rtc-1339 = derive (s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rtc-44 ∷ rw⁻ 3 rtc-17 ∷ rw⁻ 0 rtc-44 ∷ rw⁻ 2 rtc-17 ∷ rw⁻ 0 rtc-43 ∷ rw 3 rtc-91 ∷ []) refl

  rtc-1802 : Eqn
  rtc-1802 = derive (s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ [])
    (rw⁻ 6 rtc-13 ∷ rw⁻ 7 rtc-14 ∷ rw⁻ 8 rtc-14 ∷ rw 0 rtc-289 ∷ rw 6 rtc-13 ∷ []) refl

  rtc-1803 : Eqn
  rtc-1803 = derive (cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-1339 ∷ rw 0 rtc-1802 ∷ []) refl

  rtc-1982 : Eqn
  rtc-1982 = derive (s₀ ∷ s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 2 rtc-174 ∷ rw⁻ 4 rtc-30 ∷ rw⁻ 7 rtc-30 ∷ rw⁻ 0 rtc-192 ∷ rw 6 rtc-357 ∷ rw 1 rtc-713 ∷
       rw 5 rtc-13 ∷ rw 4 rtc-14 ∷ rw 3 rtc-13 ∷ rw 6 rtc-15 ∷ rw 5 rtc-12 ∷ rw 4 rtc-15 ∷ []) refl

  rtc-2072 : Eqn
  rtc-2072 = derive (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 8 rtc-488 ∷ rw 0 rtc-377 ∷ rw 5 rtc-30 ∷ rw 2 rtc-30 ∷ rw 1 rtc-230 ∷ rw 0 rtc-13 ∷
       rw 5 rtc-16 ∷ []) refl

  rtc-2074 : Eqn
  rtc-2074 = derive (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 rtc-2072 ∷ rw⁻ 8 rtc-523 ∷ rw 0 rtc-377 ∷ rw 2 rtc-175 ∷ rw 1 rtc-12 ∷ rw 0 rtc-15 ∷
       rw 2 rtc-14 ∷ rw 1 rtc-13 ∷ rw 5 rtc-30 ∷ rw 2 rtc-83 ∷ rw 0 rtc-394 ∷ rw 6 rtc-18 ∷
       rw 2 rtc-47 ∷ rw 0 rtc-219 ∷ rw 6 rtc-16 ∷ []) refl

  rtc-2081 : Eqn
  rtc-2081 = derive (s₀ ∷ s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 rtc-578 ∷ rw⁻ 0 rtc-374 ∷ rw⁻ 5 rtc-30 ∷ rw⁻ 8 rtc-18 ∷ rw⁻ 1 rtc-409 ∷ rw⁻ 1 rtc-13 ∷
       rw⁻ 2 rtc-14 ∷ rw⁻ 0 rtc-15 ∷ rw⁻ 1 rtc-12 ∷ rw⁻ 2 rtc-175 ∷ rw⁻ 0 rtc-377 ∷ rw 8 rtc-850 ∷
       rw 3 rtc-2074 ∷ rw 0 rtc-1 ∷ []) refl

  rtc-2277 : Eqn
  rtc-2277 = derive (k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-235 ∷ rw⁻ 7 rtc-539 ∷ rw 0 rtc-409 ∷ rw 7 rtc-17 ∷ rw 1 rtc-219 ∷ rw 7 rtc-16 ∷
       rw 0 rtc-1982 ∷ []) refl

  rtc-2286 : Eqn
  rtc-2286 = derive (s₀ ∷ s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 7 rtc-16 ∷ rw⁻ 1 rtc-219 ∷ rw⁻ 7 rtc-17 ∷ rw⁻ 0 rtc-409 ∷ rw 7 rtc-824 ∷ rw 0 rtc-235 ∷ []) refl

  rtc-2348 : Eqn
  rtc-2348 = derive (s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ [])
    (s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 rtc-229 ∷ rw⁻ 3 rtc-30 ∷ rw⁻ 6 rtc-18 ∷ rw⁻ 2 rtc-30 ∷ rw⁻ 5 rtc-18 ∷ rw⁻ 0 rtc-210 ∷
       rw⁻ 1 rtc-47 ∷ rw⁻ 5 rtc-84 ∷ rw⁻ 8 rtc-30 ∷ rw⁻ 0 rtc-2277 ∷ rw⁻ 0 rtc-235 ∷ rw 7 rtc-492 ∷
       rw 0 rtc-409 ∷ rw 7 rtc-18 ∷ rw 4 rtc-30 ∷ rw 1 rtc-235 ∷ rw 4 rtc-653 ∷ rw 2 rtc-17 ∷
       rw 1 rtc-15 ∷ rw 0 rtc-2081 ∷ rw 9 rtc-18 ∷ rw 0 rtc-2074 ∷ []) refl

  rtc-2350 : Eqn
  rtc-2350 = derive (k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-2286 ∷ rw⁻ 1 rtc-2348 ∷ rw 0 rtc-1079 ∷ []) refl

  rtc-2352 : Eqn
  rtc-2352 = derive (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ [])
    (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 9 rtc-13 ∷ rw⁻ 0 rtc-878 ∷ rw⁻ 2 rtc-2350 ∷ rw 0 rtc-2081 ∷ []) refl

  rtc-2409 : Eqn
  rtc-2409 = derive (s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ [])
    (rw⁻ 1 rtc-229 ∷ rw⁻ 3 rtc-30 ∷ rw⁻ 6 rtc-18 ∷ rw⁻ 2 rtc-30 ∷ rw⁻ 5 rtc-18 ∷ rw⁻ 0 rtc-210 ∷
       rw⁻ 1 rtc-47 ∷ rw⁻ 5 rtc-84 ∷ rw⁻ 8 rtc-30 ∷ rw⁻ 0 rtc-2277 ∷ rw⁻ 0 rtc-235 ∷ rw 7 rtc-541 ∷
       rw 0 rtc-409 ∷ rw 7 rtc-17 ∷ rw 1 rtc-219 ∷ rw 7 rtc-16 ∷ rw 4 rtc-47 ∷ rw 2 rtc-219 ∷
       rw 8 rtc-18 ∷ rw 5 rtc-30 ∷ rw 0 rtc-326 ∷ rw 3 rtc-55 ∷ rw 0 rtc-192 ∷ []) refl

  rtc-2693 : Eqn
  rtc-2693 = derive (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ [])
    (rw⁻ 1 rtc-4 ∷ rw⁻ 2 rtc-84 ∷ rw⁻ 5 rtc-30 ∷ rw⁻ 8 rtc-644 ∷ rw 0 rtc-591 ∷ rw 5 rtc-30 ∷
       rw 2 rtc-30 ∷ rw 0 rtc-174 ∷ rw 2 rtc-47 ∷ rw 0 rtc-219 ∷ rw 6 rtc-16 ∷ []) refl

  rtc-2921 : Eqn
  rtc-2921 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rtc-1 ∷ rw⁻ 1 rtc-257 ∷ rw⁻ 7 rtc-773 ∷ rw 0 rtc-386 ∷ rw 1 rtc-913 ∷ rw 9 rtc-17 ∷
       rw 8 rtc-15 ∷ rw 5 rtc-57 ∷ rw 3 rtc-17 ∷ rw 2 rtc-15 ∷ rw 4 rtc-17 ∷ rw 3 rtc-15 ∷
       rw 0 rtc-69 ∷ rw 5 rtc-17 ∷ rw 4 rtc-15 ∷ rw 1 rtc-57 ∷ rw 0 rtc-1 ∷ []) refl

  rtc-6224 : Eqn
  rtc-6224 = derive (k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 rtc-13 ∷ rw⁻ 0 rtc-1 ∷ rw⁻ 3 rtc-15 ∷ rw⁻ 4 rtc-17 ∷ rw⁻ 6 rtc-15 ∷ rw⁻ 2 rtc-15 ∷
       rw⁻ 3 rtc-17 ∷ rw⁻ 5 rtc-15 ∷ rw⁻ 6 rtc-846 ∷ rw 0 rtc-824 ∷ rw 5 rtc-13 ∷ rw 0 rtc-2921 ∷ []) refl

  rtc-6255 : Eqn
  rtc-6255 = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 rtc-4 ∷ rw⁻ 4 rtc-30 ∷ rw⁻ 3 rtc-30 ∷ rw⁻ 6 rtc-857 ∷ rw 0 rtc-229 ∷ rw 0 rtc-2352 ∷
       rw 9 rtc-16 ∷ rw 8 rtc-13 ∷ []) refl

ax-m-I4 : Eqn
ax-m-I4 = derive (ι ∷ ι ∷ ι ∷ ι ∷ [])
  ([])
  (rw 0 rtc-5 ∷ rw 1 rtc-10 ∷ rw 0 rtc-10 ∷ rw 0 rtc-23 ∷ []) refl

ax-m-s4 : Eqn
ax-m-s4 = derive (s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
  ([])
  (rw 0 rtc-1 ∷ []) refl

ax-m-t4 : Eqn
ax-m-t4 = derive (s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
  ([])
  (rw 0 rtc-4 ∷ []) refl

ax-m-C4 : Eqn
ax-m-C4 = derive (cs ∷ cs ∷ cs ∷ cs ∷ [])
  ([])
  (rw 0 rtc-16 ∷ []) refl

ax-m-x2 : Eqn
ax-m-x2 = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  ([])
  (rw 3 rtc-8 ∷ rw 2 rtc-7 ∷ rw 1 rtc-7 ∷ rw 0 rtc-8 ∷ rw 4 rtc-44 ∷ rw 5 rtc-44 ∷
     rw 2 rtc-1 ∷ rw 0 rtc-40 ∷ rw 1 rtc-8 ∷ rw 0 rtc-8 ∷ rw 0 rtc-40 ∷ []) refl

ax-m-y2 : Eqn
ax-m-y2 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  ([])
  (rw 3 rtc-10 ∷ rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 0 rtc-10 ∷ rw 4 rtc-41 ∷ rw 3 rtc-14 ∷
     rw 2 rtc-14 ∷ rw 1 rtc-13 ∷ rw 4 rtc-14 ∷ rw 3 rtc-14 ∷ rw 2 rtc-13 ∷ rw 0 rtc-40 ∷
     rw 1 rtc-4 ∷ rw 0 rtc-41 ∷ rw 1 rtc-8 ∷ rw 0 rtc-8 ∷ rw 0 rtc-40 ∷ []) refl

ax-m-a2 : Eqn
ax-m-a2 = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  ([])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 4 rtc-41 ∷ rw 2 rtc-43 ∷ rw 1 rtc-13 ∷
     rw 2 rtc-13 ∷ rw 0 rtc-40 ∷ rw 1 rtc-16 ∷ rw 0 rtc-41 ∷ rw 1 rtc-8 ∷ rw 0 rtc-8 ∷
     rw 0 rtc-40 ∷ []) refl

ax-m-b2 : Eqn
ax-m-b2 = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  ([])
  (rw 3 rtc-8 ∷ rw 1 rtc-11 ∷ rw 0 rtc-8 ∷ rw 2 rtc-43 ∷ rw 0 rtc-40 ∷ rw 1 rtc-16 ∷
     rw 1 rtc-8 ∷ rw 0 rtc-8 ∷ rw 0 rtc-40 ∷ []) refl

ax-m-Is : Eqn
ax-m-Is = derive (s₀ ∷ ι ∷ [])
  (ι ∷ s₀ ∷ [])
  (rw 0 rtc-7 ∷ []) refl

ax-m-It : Eqn
ax-m-It = derive (s₁ ∷ ι ∷ [])
  (ι ∷ s₁ ∷ [])
  (rw 0 rtc-9 ∷ []) refl

ax-m-st : Eqn
ax-m-st = derive (s₁ ∷ s₀ ∷ [])
  (s₀ ∷ s₁ ∷ [])
  (rw 0 rtc-12 ∷ []) refl

ax-m-Ix : Eqn
ax-m-Ix = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ ι ∷ [])
  (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (rw 3 rtc-8 ∷ rw 2 rtc-7 ∷ rw 1 rtc-7 ∷ rw 0 rtc-8 ∷ rw 4 rtc-8 ∷ rw 3 rtc-7 ∷
     rw 2 rtc-7 ∷ rw 1 rtc-8 ∷ rw⁻ 1 rtc-8 ∷ rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-7 ∷ rw⁻ 4 rtc-8 ∷ []) refl

ax-m-Iy : Eqn
ax-m-Iy = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ ι ∷ [])
  (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 0 rtc-10 ∷ rw 4 rtc-10 ∷ rw 3 rtc-9 ∷
     rw 2 rtc-9 ∷ rw 1 rtc-10 ∷ rw⁻ 1 rtc-10 ∷ rw⁻ 2 rtc-9 ∷ rw⁻ 3 rtc-9 ∷ rw⁻ 4 rtc-10 ∷ []) refl

ax-m-Ia : Eqn
ax-m-Ia = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ ι ∷ [])
  (ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 4 rtc-10 ∷ rw 2 rtc-11 ∷ rw 1 rtc-10 ∷
     rw⁻ 1 rtc-10 ∷ rw⁻ 2 rtc-11 ∷ rw⁻ 4 rtc-10 ∷ []) refl

ax-m-Ib : Eqn
ax-m-Ib = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ ι ∷ [])
  (ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  (rw 3 rtc-8 ∷ rw 1 rtc-11 ∷ rw 0 rtc-8 ∷ rw 4 rtc-8 ∷ rw 2 rtc-11 ∷ rw 1 rtc-8 ∷
     rw⁻ 1 rtc-8 ∷ rw⁻ 2 rtc-11 ∷ rw⁻ 4 rtc-8 ∷ []) refl

ax-m-xy : Eqn
ax-m-xy = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 0 rtc-10 ∷ rw 4 rtc-13 ∷ rw 3 rtc-14 ∷
     rw 2 rtc-14 ∷ rw 1 rtc-13 ∷ rw 5 rtc-15 ∷ rw 4 rtc-12 ∷ rw 3 rtc-12 ∷ rw 2 rtc-15 ∷
     rw 6 rtc-15 ∷ rw 5 rtc-12 ∷ rw 4 rtc-12 ∷ rw 3 rtc-15 ∷ rw 7 rtc-13 ∷ rw 6 rtc-14 ∷
     rw 5 rtc-14 ∷ rw 4 rtc-13 ∷ rw 8 rtc-10 ∷ rw 7 rtc-9 ∷ rw 6 rtc-9 ∷ rw 5 rtc-10 ∷
     rw 4 rtc-8 ∷ rw 3 rtc-7 ∷ rw 2 rtc-7 ∷ rw 1 rtc-8 ∷ rw⁻ 1 rtc-8 ∷ rw⁻ 2 rtc-7 ∷
     rw⁻ 3 rtc-7 ∷ rw⁻ 4 rtc-8 ∷ rw⁻ 5 rtc-10 ∷ rw⁻ 6 rtc-9 ∷ rw⁻ 7 rtc-9 ∷ rw⁻ 8 rtc-10 ∷
     rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-7 ∷ rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-8 ∷ []) refl

ax-m-xs : Eqn
ax-m-xs = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ s₀ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (ι ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
  (rw 3 rtc-8 ∷ rw 2 rtc-7 ∷ rw 1 rtc-7 ∷ rw 0 rtc-8 ∷ rw 4 rtc-57 ∷ rw 2 rtc-1 ∷
     rw 1 rtc-57 ∷ rw 0 rtc-50 ∷ rw 2 rtc-7 ∷ rw 1 rtc-7 ∷ rw 0 rtc-7 ∷ []) refl

ax-m-xt : Eqn
ax-m-xt = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ s₁ ∷ [])
  (s₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (rw 3 rtc-8 ∷ rw 2 rtc-7 ∷ rw 1 rtc-7 ∷ rw 0 rtc-8 ∷ rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-7 ∷
     rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-8 ∷ rw⁻ 4 rtc-9 ∷ rw⁻ 3 rtc-14 ∷ rw⁻ 2 rtc-12 ∷ rw⁻ 1 rtc-12 ∷
     rw⁻ 0 rtc-14 ∷ []) refl

ax-m-ys : Eqn
ax-m-ys = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ s₀ ∷ [])
  (s₀ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 0 rtc-10 ∷ rw 4 rtc-15 ∷ rw 3 rtc-12 ∷
     rw 2 rtc-12 ∷ rw 1 rtc-15 ∷ rw⁻ 0 rtc-7 ∷ rw⁻ 1 rtc-10 ∷ rw⁻ 2 rtc-9 ∷ rw⁻ 3 rtc-9 ∷
     rw⁻ 4 rtc-10 ∷ []) refl

ax-m-yt : Eqn
ax-m-yt = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (ι ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
  (rw 3 rtc-10 ∷ rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 0 rtc-10 ∷ rw 3 rtc-82 ∷ rw 1 rtc-66 ∷
     rw 0 rtc-40 ∷ rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 0 rtc-9 ∷ []) refl

ax-m-as : Eqn
ax-m-as = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ s₀ ∷ [])
  (s₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 4 rtc-15 ∷ rw 2 rtc-17 ∷ rw 1 rtc-15 ∷
     rw⁻ 0 rtc-7 ∷ rw⁻ 1 rtc-10 ∷ rw⁻ 2 rtc-11 ∷ rw⁻ 4 rtc-10 ∷ []) refl

ax-m-at : Eqn
ax-m-at = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (s₀ ∷ s₁ ∷ cs ∷ cs ∷ [])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 0 rtc-684 ∷ rw 5 rtc-16 ∷ rw 4 rtc-41 ∷
     rw 2 rtc-43 ∷ rw 1 rtc-14 ∷ rw 2 rtc-14 ∷ rw 4 rtc-11 ∷ rw 3 rtc-9 ∷ rw 2 rtc-8 ∷
     rw 1 rtc-8 ∷ rw 0 rtc-7 ∷ rw 0 rtc-32 ∷ []) refl

ax-m-bt : Eqn
ax-m-bt = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ s₁ ∷ [])
  (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  (rw 3 rtc-8 ∷ rw 1 rtc-11 ∷ rw 0 rtc-8 ∷ rw 2 rtc-30 ∷ rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-9 ∷
     rw⁻ 2 rtc-11 ∷ rw⁻ 4 rtc-8 ∷ rw⁻ 0 rtc-14 ∷ []) refl

ax-m-bs : Eqn
ax-m-bs = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  (s₀ ∷ s₁ ∷ cs ∷ cs ∷ [])
  (rw 3 rtc-8 ∷ rw 1 rtc-11 ∷ rw 0 rtc-8 ∷ rw 2 rtc-123 ∷ rw 0 rtc-40 ∷ rw 2 rtc-43 ∷
     rw 1 rtc-14 ∷ rw 2 rtc-14 ∷ rw 4 rtc-11 ∷ rw 3 rtc-9 ∷ rw 2 rtc-8 ∷ rw 1 rtc-8 ∷
     rw 0 rtc-7 ∷ rw 0 rtc-32 ∷ []) refl

ax-m-ax : Eqn
ax-m-ax = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 4 rtc-13 ∷ rw 5 rtc-15 ∷ rw 6 rtc-15 ∷
     rw 7 rtc-13 ∷ rw 8 rtc-10 ∷ rw 7 rtc-8 ∷ rw 6 rtc-7 ∷ rw 5 rtc-7 ∷ rw 4 rtc-8 ∷
     rw 2 rtc-11 ∷ rw 1 rtc-10 ∷ rw 9 rtc-41 ∷ rw 3 rtc-75 ∷ rw 2 rtc-13 ∷ rw 3 rtc-13 ∷
     rw 1 rtc-40 ∷ rw 2 rtc-93 ∷ rw 1 rtc-13 ∷ rw 2 rtc-15 ∷ rw 3 rtc-15 ∷ rw 4 rtc-13 ∷
     rw 8 rtc-10 ∷ rw 7 rtc-9 ∷ rw 6 rtc-9 ∷ rw 5 rtc-10 ∷ rw 4 rtc-8 ∷ rw 3 rtc-7 ∷
     rw 2 rtc-7 ∷ rw 1 rtc-8 ∷ rw⁻ 1 rtc-8 ∷ rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-7 ∷ rw⁻ 4 rtc-8 ∷
     rw⁻ 5 rtc-10 ∷ rw⁻ 6 rtc-9 ∷ rw⁻ 7 rtc-9 ∷ rw⁻ 8 rtc-10 ∷ rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-7 ∷
     rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-8 ∷ []) refl

ax-m-ay : Eqn
ax-m-ay = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 4 rtc-41 ∷ rw 2 rtc-43 ∷ rw 1 rtc-13 ∷
     rw 2 rtc-13 ∷ rw 0 rtc-40 ∷ rw 1 rtc-18 ∷ rw 2 rtc-18 ∷ rw 5 rtc-10 ∷ rw 3 rtc-11 ∷
     rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 0 rtc-10 ∷ rw⁻ 0 rtc-10 ∷ rw⁻ 1 rtc-9 ∷ rw⁻ 2 rtc-9 ∷
     rw⁻ 3 rtc-11 ∷ rw⁻ 5 rtc-10 ∷ rw⁻ 0 rtc-40 ∷ rw⁻ 2 rtc-13 ∷ rw⁻ 3 rtc-14 ∷ rw⁻ 4 rtc-14 ∷
     rw⁻ 1 rtc-13 ∷ rw⁻ 2 rtc-14 ∷ rw⁻ 3 rtc-14 ∷ rw⁻ 4 rtc-41 ∷ rw⁻ 0 rtc-10 ∷ rw⁻ 1 rtc-9 ∷
     rw⁻ 2 rtc-9 ∷ rw⁻ 3 rtc-10 ∷ []) refl

ax-m-by : Eqn
ax-m-by = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-8 ∷ rw 1 rtc-11 ∷ rw 0 rtc-8 ∷ rw 8 rtc-10 ∷ rw 7 rtc-9 ∷ rw 6 rtc-9 ∷
     rw 5 rtc-10 ∷ rw 4 rtc-8 ∷ rw 2 rtc-11 ∷ rw 1 rtc-8 ∷ rw 9 rtc-13 ∷ rw 8 rtc-14 ∷
     rw 7 rtc-14 ∷ rw 6 rtc-13 ∷ rw 3 rtc-43 ∷ rw 1 rtc-40 ∷ rw 2 rtc-115 ∷ rw 7 rtc-13 ∷
     rw 6 rtc-14 ∷ rw 5 rtc-14 ∷ rw 4 rtc-13 ∷ rw 8 rtc-10 ∷ rw 7 rtc-9 ∷ rw 6 rtc-9 ∷
     rw 5 rtc-10 ∷ rw 4 rtc-8 ∷ rw 3 rtc-7 ∷ rw 2 rtc-7 ∷ rw 1 rtc-8 ∷ rw⁻ 1 rtc-8 ∷
     rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-7 ∷ rw⁻ 4 rtc-8 ∷ rw⁻ 5 rtc-10 ∷ rw⁻ 6 rtc-9 ∷ rw⁻ 7 rtc-9 ∷
     rw⁻ 8 rtc-10 ∷ rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-7 ∷ rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-8 ∷ []) refl

ax-m-bx : Eqn
ax-m-bx = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  (rw 3 rtc-8 ∷ rw 1 rtc-11 ∷ rw 0 rtc-8 ∷ rw 2 rtc-43 ∷ rw 0 rtc-40 ∷ rw 1 rtc-17 ∷
     rw 2 rtc-17 ∷ rw 5 rtc-8 ∷ rw 3 rtc-11 ∷ rw 2 rtc-7 ∷ rw 1 rtc-7 ∷ rw 0 rtc-8 ∷
     rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-7 ∷ rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-11 ∷ rw⁻ 5 rtc-8 ∷ rw⁻ 0 rtc-51 ∷
     rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-7 ∷ rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-8 ∷ []) refl

ax-m-ab : Eqn
ax-m-ab = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 4 rtc-13 ∷ rw 8 rtc-8 ∷ rw 6 rtc-11 ∷
     rw 5 rtc-10 ∷ rw 4 rtc-8 ∷ rw 2 rtc-11 ∷ rw 1 rtc-10 ∷ rw 2 rtc-6224 ∷ rw 12 rtc-11 ∷
     rw 11 rtc-10 ∷ rw 10 rtc-8 ∷ rw 8 rtc-11 ∷ rw 7 rtc-10 ∷ rw 6 rtc-8 ∷ rw 4 rtc-11 ∷
     rw 3 rtc-10 ∷ rw 2 rtc-8 ∷ rw 0 rtc-42 ∷ rw⁻ 0 rtc-42 ∷ rw⁻ 2 rtc-8 ∷ rw⁻ 3 rtc-10 ∷
     rw⁻ 4 rtc-11 ∷ rw⁻ 6 rtc-8 ∷ rw⁻ 7 rtc-10 ∷ rw⁻ 8 rtc-11 ∷ rw⁻ 10 rtc-8 ∷ rw⁻ 11 rtc-10 ∷
     rw⁻ 12 rtc-11 ∷ rw⁻ 2 rtc-6255 ∷ rw⁻ 9 rtc-13 ∷ rw⁻ 1 rtc-8 ∷ rw⁻ 2 rtc-11 ∷ rw⁻ 4 rtc-8 ∷
     rw⁻ 5 rtc-10 ∷ rw⁻ 6 rtc-11 ∷ rw⁻ 8 rtc-10 ∷ rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-11 ∷ rw⁻ 3 rtc-8 ∷ []) refl

ax-k-l : Eqn
ax-k-l = derive (k₁ ∷ k₀ ∷ [])
  (k₀ ∷ k₁ ∷ [])
  (rw 0 rtc-13 ∷ []) refl

ax-k2 : Eqn
ax-k2 = derive (k₀ ∷ k₀ ∷ [])
  (ι ∷ ι ∷ ι ∷ [])
  (rw⁻ 0 rtc-42 ∷ []) refl

ax-l2 : Eqn
ax-l2 = derive (k₁ ∷ k₁ ∷ [])
  (ι ∷ ι ∷ ι ∷ [])
  (rw⁻ 0 rtc-5 ∷ []) refl

ax-k-I : Eqn
ax-k-I = derive (k₀ ∷ ι ∷ [])
  (ι ∷ k₀ ∷ [])
  (rw 0 rtc-8 ∷ []) refl

ax-l-I : Eqn
ax-l-I = derive (k₁ ∷ ι ∷ [])
  (ι ∷ k₁ ∷ [])
  (rw 0 rtc-10 ∷ []) refl

ax-k-t : Eqn
ax-k-t = derive (s₁ ∷ k₀ ∷ [])
  (k₀ ∷ s₁ ∷ [])
  (rw 0 rtc-14 ∷ []) refl

ax-l-s : Eqn
ax-l-s = derive (k₁ ∷ s₀ ∷ [])
  (s₀ ∷ k₁ ∷ [])
  (rw 0 rtc-15 ∷ []) refl

ax-x-def : Eqn
ax-x-def = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (rw 3 rtc-8 ∷ rw 2 rtc-7 ∷ rw 1 rtc-7 ∷ rw 0 rtc-8 ∷ rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-7 ∷
     rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-8 ∷ []) refl

ax-y-def : Eqn
ax-y-def = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 2 rtc-9 ∷ rw 1 rtc-9 ∷ rw 0 rtc-10 ∷ rw⁻ 0 rtc-10 ∷ rw⁻ 1 rtc-9 ∷
     rw⁻ 2 rtc-9 ∷ rw⁻ 3 rtc-10 ∷ []) refl

ax-sw-x : Eqn
ax-sw-x = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 4 rtc-13 ∷ rw 8 rtc-8 ∷ rw 6 rtc-11 ∷
     rw 5 rtc-10 ∷ rw 4 rtc-8 ∷ rw 2 rtc-11 ∷ rw 1 rtc-10 ∷ rw 13 rtc-10 ∷ rw 11 rtc-11 ∷
     rw 10 rtc-10 ∷ rw 9 rtc-8 ∷ rw 7 rtc-11 ∷ rw 6 rtc-10 ∷ rw 5 rtc-8 ∷ rw 3 rtc-11 ∷
     rw 2 rtc-10 ∷ rw 0 rtc-42 ∷ rw 13 rtc-13 ∷ rw 14 rtc-15 ∷ rw 15 rtc-15 ∷ rw 16 rtc-13 ∷
     rw 7 rtc-1803 ∷ rw 6 rtc-41 ∷ rw 3 rtc-43 ∷ rw 2 rtc-13 ∷ rw 3 rtc-13 ∷ rw 0 rtc-38 ∷
     rw 3 rtc-30 ∷ rw 4 rtc-30 ∷ rw 15 rtc-10 ∷ rw 13 rtc-11 ∷ rw 12 rtc-10 ∷ rw 11 rtc-8 ∷
     rw 9 rtc-11 ∷ rw 8 rtc-10 ∷ rw 7 rtc-8 ∷ rw 5 rtc-11 ∷ rw 4 rtc-9 ∷ rw 3 rtc-9 ∷
     rw 2 rtc-10 ∷ rw 0 rtc-42 ∷ rw⁻ 0 rtc-42 ∷ rw⁻ 2 rtc-10 ∷ rw⁻ 3 rtc-9 ∷ rw⁻ 4 rtc-9 ∷
     rw⁻ 5 rtc-11 ∷ rw⁻ 7 rtc-8 ∷ rw⁻ 8 rtc-10 ∷ rw⁻ 9 rtc-11 ∷ rw⁻ 11 rtc-8 ∷ rw⁻ 12 rtc-10 ∷
     rw⁻ 13 rtc-11 ∷ rw⁻ 15 rtc-10 ∷ rw⁻ 1 rtc-10 ∷ rw⁻ 2 rtc-9 ∷ rw⁻ 3 rtc-9 ∷ rw⁻ 4 rtc-11 ∷
     rw⁻ 6 rtc-8 ∷ rw⁻ 7 rtc-10 ∷ rw⁻ 8 rtc-11 ∷ rw⁻ 10 rtc-8 ∷ rw⁻ 6 rtc-13 ∷ rw⁻ 0 rtc-10 ∷
     rw⁻ 1 rtc-9 ∷ rw⁻ 2 rtc-9 ∷ rw⁻ 3 rtc-11 ∷ rw⁻ 5 rtc-10 ∷ rw⁻ 0 rtc-40 ∷ rw⁻ 2 rtc-13 ∷
     rw⁻ 3 rtc-14 ∷ rw⁻ 4 rtc-14 ∷ rw⁻ 1 rtc-13 ∷ rw⁻ 2 rtc-14 ∷ rw⁻ 3 rtc-14 ∷ rw⁻ 4 rtc-41 ∷
     rw⁻ 0 rtc-10 ∷ rw⁻ 1 rtc-9 ∷ rw⁻ 2 rtc-9 ∷ rw⁻ 3 rtc-10 ∷ []) refl

ax-sw-y : Eqn
ax-sw-y = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 4 rtc-13 ∷ rw 8 rtc-8 ∷ rw 6 rtc-11 ∷
     rw 5 rtc-10 ∷ rw 4 rtc-8 ∷ rw 2 rtc-11 ∷ rw 1 rtc-10 ∷ rw 13 rtc-10 ∷ rw 11 rtc-11 ∷
     rw 10 rtc-10 ∷ rw 9 rtc-8 ∷ rw 7 rtc-11 ∷ rw 6 rtc-10 ∷ rw 5 rtc-8 ∷ rw 3 rtc-11 ∷
     rw 2 rtc-10 ∷ rw 0 rtc-42 ∷ rw 13 rtc-41 ∷ rw 11 rtc-43 ∷ rw 10 rtc-13 ∷ rw 7 rtc-43 ∷
     rw 6 rtc-13 ∷ rw 3 rtc-43 ∷ rw 2 rtc-13 ∷ rw 3 rtc-13 ∷ rw 0 rtc-38 ∷ rw 5 rtc-13 ∷
     rw 9 rtc-13 ∷ rw 11 rtc-18 ∷ rw 12 rtc-18 ∷ rw 15 rtc-10 ∷ rw 13 rtc-11 ∷ rw 12 rtc-9 ∷
     rw 11 rtc-9 ∷ rw 10 rtc-10 ∷ rw 9 rtc-8 ∷ rw 7 rtc-11 ∷ rw 6 rtc-10 ∷ rw 5 rtc-8 ∷
     rw 3 rtc-11 ∷ rw 2 rtc-10 ∷ rw 0 rtc-42 ∷ rw 1 rtc-2693 ∷ rw 2 rtc-2693 ∷ rw⁻ 8 rtc-16 ∷
     rw⁻ 2 rtc-219 ∷ rw⁻ 8 rtc-17 ∷ rw⁻ 1 rtc-409 ∷ rw⁻ 0 rtc-42 ∷ rw⁻ 2 rtc-10 ∷ rw⁻ 3 rtc-9 ∷
     rw⁻ 4 rtc-9 ∷ rw⁻ 5 rtc-11 ∷ rw⁻ 7 rtc-8 ∷ rw⁻ 8 rtc-7 ∷ rw⁻ 9 rtc-7 ∷ rw⁻ 10 rtc-10 ∷
     rw⁻ 11 rtc-11 ∷ rw⁻ 13 rtc-8 ∷ rw⁻ 14 rtc-10 ∷ rw⁻ 15 rtc-11 ∷ rw⁻ 17 rtc-10 ∷ rw⁻ 1 rtc-10 ∷
     rw⁻ 2 rtc-9 ∷ rw⁻ 3 rtc-9 ∷ rw⁻ 4 rtc-11 ∷ rw⁻ 6 rtc-8 ∷ rw⁻ 7 rtc-7 ∷ rw⁻ 8 rtc-7 ∷
     rw⁻ 9 rtc-10 ∷ rw⁻ 10 rtc-11 ∷ rw⁻ 12 rtc-8 ∷ rw⁻ 1 rtc-1230 ∷ rw⁻ 9 rtc-13 ∷ rw⁻ 1 rtc-8 ∷
     rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-7 ∷ rw⁻ 4 rtc-8 ∷ rw⁻ 5 rtc-10 ∷ rw⁻ 6 rtc-11 ∷ rw⁻ 8 rtc-10 ∷
     rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-7 ∷ rw⁻ 2 rtc-7 ∷ rw⁻ 3 rtc-8 ∷ []) refl

ax-aka : Eqn
ax-aka = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  (rw 3 rtc-10 ∷ rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw 4 rtc-13 ∷ rw 5 rtc-41 ∷ rw 2 rtc-43 ∷
     rw 1 rtc-13 ∷ rw 2 rtc-13 ∷ rw 0 rtc-40 ∷ rw 6 rtc-10 ∷ rw 4 rtc-11 ∷ rw 3 rtc-8 ∷
     rw 1 rtc-11 ∷ rw 0 rtc-10 ∷ rw⁻ 0 rtc-10 ∷ rw⁻ 1 rtc-11 ∷ rw⁻ 3 rtc-8 ∷ rw⁻ 4 rtc-11 ∷
     rw⁻ 6 rtc-10 ∷ rw⁻ 0 rtc-40 ∷ rw⁻ 2 rtc-13 ∷ rw⁻ 1 rtc-13 ∷ rw⁻ 2 rtc-43 ∷ rw⁻ 5 rtc-43 ∷
     rw⁻ 8 rtc-13 ∷ rw⁻ 1 rtc-1 ∷ rw⁻ 2 rtc-2409 ∷ rw⁻ 0 rtc-7 ∷ rw⁻ 1 rtc-7 ∷ rw⁻ 2 rtc-11 ∷
     rw⁻ 4 rtc-8 ∷ rw⁻ 5 rtc-11 ∷ rw⁻ 7 rtc-8 ∷ rw⁻ 8 rtc-10 ∷ rw⁻ 9 rtc-11 ∷ rw⁻ 0 rtc-1150 ∷
     rw⁻ 4 rtc-13 ∷ rw⁻ 1 rtc-40 ∷ rw⁻ 3 rtc-43 ∷ rw⁻ 6 rtc-13 ∷ rw⁻ 7 rtc-43 ∷ rw⁻ 9 rtc-41 ∷
     rw⁻ 1 rtc-8 ∷ rw⁻ 2 rtc-11 ∷ rw⁻ 4 rtc-8 ∷ rw⁻ 5 rtc-10 ∷ rw⁻ 6 rtc-11 ∷ rw⁻ 8 rtc-10 ∷
     rw⁻ 0 rtc-8 ∷ rw⁻ 1 rtc-11 ∷ rw⁻ 3 rtc-8 ∷ []) refl

------------------------------------------------------------------------
-- The equations with CS and the controlled K gates

private
  ms1m-0 : Eqn
  ms1m-0 = ⌊ axiom (srel order-I) ⌋⁼

  ms1m-1 : Eqn
  ms1m-1 = ⌊ lemma-cong↑ _ _ (PB.axiom (srel order-S)) ⌋⁼

  ms1m-2 : Eqn
  ms1m-2 = sym⁼ (K²₁)

  ms1m-3 : Eqn
  ms1m-3 = SK³₁

  ms1m-4 : Eqn
  ms1m-4 = ⌊ axiom (srel order-S) ⌋⁼

  ms1m-5 : Eqn
  ms1m-5 = sym⁼ (⌊ axiom (srel order-K) ⌋⁼)

  ms1m-6 : Eqn
  ms1m-6 = ⌊ axiom (srel order-SK) ⌋⁼

  ms1m-7 : Eqn
  ms1m-7 = ⌊ comm₀ I-gate (S-gen ↥) ⌋⁼

  ms1m-8 : Eqn
  ms1m-8 = ⌊ comm₀ I-gate (K-gen ↥) ⌋⁼

  ms1m-9 : Eqn
  ms1m-9 = ⌊ comm₀ I-gate S-gen ⌋⁼

  ms1m-10 : Eqn
  ms1m-10 = ⌊ comm₀ I-gate K-gen ⌋⁼

  ms1m-11 : Eqn
  ms1m-11 = ⌊ comm₀ I-gate CS-gen ⌋⁼

  ms1m-12 : Eqn
  ms1m-12 = sym⁼ (⌊ axiom (comm₁ S-gate S-gen) ⌋⁼)

  ms1m-13 : Eqn
  ms1m-13 = sym⁼ (⌊ axiom (comm₁ K-gate K-gen) ⌋⁼)

  ms1m-14 : Eqn
  ms1m-14 = sym⁼ (⌊ axiom (comm₁ S-gate K-gen) ⌋⁼)

  ms1m-15 : Eqn
  ms1m-15 = sym⁼ (⌊ axiom (comm₁ K-gate S-gen) ⌋⁼)

  ms1m-16 : Eqn
  ms1m-16 = ⌊ axiom (srel order-CS) ⌋⁼

  ms1m-17 : Eqn
  ms1m-17 = ⌊ axiom (srel comm-CS-S₁) ⌋⁼

  ms1m-18 : Eqn
  ms1m-18 = ⌊ axiom (srel comm-CS-S₀) ⌋⁼

  ms1m-19 : Eqn
  ms1m-19 = sym⁼ (X-CS₁′)

  ms1m-20 : Eqn
  ms1m-20 = sym⁼ (⌊ axiom (srel X-CS₀) ⌋⁼)

  ms1m-21 : Eqn
  ms1m-21 = ⌊ axiom (srel CS-K₁) ⌋⁼

  ms1m-22 : Eqn
  ms1m-22 = ⌊ axiom (srel CS-K₀) ⌋⁼

  ms1m-24 : Eqn
  ms1m-24 = ⌊ lemma-cong↑ _ _ (PB.axiom (srel order-S)) ⌋⁼

  ms1m-25 : Eqn
  ms1m-25 = ⌊ axiom (srel order-S) ⌋⁼

  ms1m-26 : Eqn
  ms1m-26 = ⌊ axiom (srel order-CS) ⌋⁼

  ms1m-28 : Eqn
  ms1m-28 = ax-m-x2

  ms1m-31 : Eqn
  ms1m-31 = ⌊ comm₀ I-gate (S-gen ↥) ⌋⁼

  ms1m-32 : Eqn
  ms1m-32 = ⌊ comm₀ I-gate S-gen ⌋⁼

  ms1m-33 : Eqn
  ms1m-33 = sym⁼ (⌊ axiom (comm₁ S-gate S-gen) ⌋⁼)

  ms1m-52 : Eqn
  ms1m-52 = sym⁼ (⌊ axiom (comm₁ K-gate K-gen) ⌋⁼)

  ms1m-54 : Eqn
  ms1m-54 = sym⁼ (⌊ axiom (srel order-K) ⌋⁼)

  ms1m-57 : Eqn
  ms1m-57 = ⌊ comm₀ I-gate (K-gen ↥) ⌋⁼

  ms1m-58 : Eqn
  ms1m-58 = ⌊ comm₀ I-gate K-gen ⌋⁼

  ms1m-59 : Eqn
  ms1m-59 = sym⁼ (⌊ axiom (comm₁ S-gate K-gen) ⌋⁼)

  ms1m-60 : Eqn
  ms1m-60 = sym⁼ (⌊ axiom (comm₁ K-gate S-gen) ⌋⁼)

  ms1m-71 : Eqn
  ms1m-71 = derive (ι ∷ k₀ ∷ k₀ ∷ [])
    ([])
    (rw⁻ 0 ms1m-58 ∷ rw⁻ 1 ms1m-58 ∷ rw⁻ 0 ms1m-54 ∷ rw 0 ms1m-0 ∷ []) refl

  ms1m-72 : Eqn
  ms1m-72 = derive (ι ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-11 ∷ rw⁻ 1 ms1m-11 ∷ rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-57 ∷ rw⁻ 4 ms1m-31 ∷ rw⁻ 5 ms1m-31 ∷
       rw⁻ 6 ms1m-57 ∷ rw 0 ms1m-19 ∷ rw 3 ms1m-57 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-57 ∷ []) refl

  ms1m-73 : Eqn
  ms1m-73 = derive (ι ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-33 ∷ rw⁻ 6 ms1m-33 ∷
       rw⁻ 7 ms1m-60 ∷ rw⁻ 0 ms1m-11 ∷ rw⁻ 1 ms1m-11 ∷ rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-58 ∷ rw⁻ 4 ms1m-32 ∷
       rw⁻ 5 ms1m-32 ∷ rw⁻ 6 ms1m-58 ∷ rw 0 ms1m-20 ∷ rw 3 ms1m-58 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷
       rw 0 ms1m-58 ∷ []) refl

  ms1m-75 : Eqn
  ms1m-75 = derive (ι ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    ([])
    (rw⁻ 1 ms1m-58 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-32 ∷ rw⁻ 4 ms1m-58 ∷ rw⁻ 5 ms1m-58 ∷ rw⁻ 6 ms1m-32 ∷
       rw⁻ 7 ms1m-32 ∷ rw⁻ 8 ms1m-58 ∷ rw⁻ 0 ms1m-58 ∷ rw⁻ 1 ms1m-32 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-58 ∷
       rw 0 ms1m-28 ∷ []) refl

  ms1m-93 : Eqn
  ms1m-93 = derive (ι ∷ s₁ ∷ k₀ ∷ k₀ ∷ [])
    (s₁ ∷ [])
    (rw⁻ 0 ms1m-7 ∷ rw 1 ms1m-71 ∷ []) refl

  ms1m-94 : Eqn
  ms1m-94 = derive (ι ∷ k₁ ∷ k₀ ∷ k₀ ∷ [])
    (k₁ ∷ [])
    (rw⁻ 0 ms1m-8 ∷ rw 1 ms1m-71 ∷ []) refl

  ms1m-102 : Eqn
  ms1m-102 = derive (cs ∷ k₁ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-14 ∷ rw 0 ms1m-18 ∷ []) refl

  ms1m-103 : Eqn
  ms1m-103 = derive (s₁ ∷ k₀ ∷ k₀ ∷ [])
    (s₁ ∷ k₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-60 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 0 ms1m-54 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷ rw⁻ 0 ms1m-7 ∷
       rw 1 ms1m-2 ∷ []) refl

  ms1m-104 : Eqn
  ms1m-104 = derive (ι ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (s₁ ∷ [])
    (rw⁻ 1 ms1m-103 ∷ rw 0 ms1m-93 ∷ []) refl

  ms1m-105 : Eqn
  ms1m-105 = derive (k₁ ∷ k₀ ∷ k₀ ∷ [])
    (k₁ ∷ k₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-52 ∷ rw⁻ 1 ms1m-52 ∷ rw⁻ 0 ms1m-54 ∷ rw⁻ 2 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 0 ms1m-8 ∷
       rw 1 ms1m-2 ∷ []) refl

  ms1m-110 : Eqn
  ms1m-110 = derive (ι ∷ k₁ ∷ k₁ ∷ k₁ ∷ [])
    (k₁ ∷ [])
    (rw⁻ 1 ms1m-105 ∷ rw 0 ms1m-94 ∷ []) refl

  ms1m-112 : Eqn
  ms1m-112 = derive (k₀ ∷ k₀ ∷ s₀ ∷ [])
    (k₁ ∷ k₁ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-54 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 1 ms1m-32 ∷ rw⁻ 0 ms1m-9 ∷ rw 1 ms1m-2 ∷ rw 0 ms1m-59 ∷
       rw 1 ms1m-59 ∷ []) refl

  ms1m-113 : Eqn
  ms1m-113 = derive (ι ∷ k₁ ∷ k₁ ∷ [])
    ([])
    (rw⁻ 1 ms1m-110 ∷ rw⁻ 3 ms1m-105 ∷ rw⁻ 5 ms1m-25 ∷ rw⁻ 3 ms1m-52 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-59 ∷
       rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-112 ∷ rw 0 ms1m-75 ∷ []) refl

  ms1m-119 : Eqn
  ms1m-119 = derive (cs ∷ k₁ ∷ k₁ ∷ [])
    (k₀ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 1 ms1m-2 ∷ rw 0 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 2 ms1m-11 ∷ rw 0 ms1m-54 ∷ []) refl

  ms1m-127 : Eqn
  ms1m-127 = derive (k₁ ∷ k₁ ∷ k₁ ∷ k₁ ∷ [])
    (ι ∷ ι ∷ [])
    (rw⁻ 1 ms1m-105 ∷ rw⁻ 0 ms1m-2 ∷ rw 2 ms1m-71 ∷ []) refl

  ms1m-129 : Eqn
  ms1m-129 = derive (k₀ ∷ k₀ ∷ [])
    (k₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-5 ∷ rw 0 ms1m-2 ∷ []) refl

  ms1m-131 : Eqn
  ms1m-131 = derive (ι ∷ ι ∷ ι ∷ [])
    (k₁ ∷ k₁ ∷ [])
    (rw 0 ms1m-54 ∷ rw 0 ms1m-129 ∷ []) refl

  ms1m-132 : Eqn
  ms1m-132 = derive (cs ∷ k₁ ∷ k₁ ∷ [])
    (k₁ ∷ k₁ ∷ cs ∷ [])
    (rw 0 ms1m-119 ∷ rw 0 ms1m-129 ∷ []) refl

  ms1m-138 : Eqn
  ms1m-138 = derive (k₁ ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-129 ∷ rw 1 ms1m-15 ∷ rw 0 ms1m-60 ∷ rw 1 ms1m-129 ∷ []) refl

  ms1m-140 : Eqn
  ms1m-140 = derive (ι ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-7 ∷ rw 1 ms1m-104 ∷ []) refl

  ms1m-141 : Eqn
  ms1m-141 = derive (ι ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-8 ∷ rw 1 ms1m-104 ∷ []) refl

  ms1m-142 : Eqn
  ms1m-142 = derive (cs ∷ k₁ ∷ s₁ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-12 ∷ rw 0 ms1m-102 ∷ []) refl

  ms1m-143 : Eqn
  ms1m-143 = derive (ι ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 3 ms1m-138 ∷ rw 0 ms1m-104 ∷ []) refl

  ms1m-144 : Eqn
  ms1m-144 = derive (cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (k₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-138 ∷ rw 0 ms1m-132 ∷ []) refl

  ms1m-145 : Eqn
  ms1m-145 = derive (ι ∷ s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-7 ∷ rw 1 ms1m-140 ∷ []) refl

  ms1m-146 : Eqn
  ms1m-146 = derive (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-8 ∷ rw 1 ms1m-140 ∷ []) refl

  ms1m-148 : Eqn
  ms1m-148 = derive (ι ∷ k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 4 ms1m-138 ∷ rw 0 ms1m-141 ∷ []) refl

  ms1m-149 : Eqn
  ms1m-149 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 3 ms1m-12 ∷ rw 0 ms1m-142 ∷ []) refl

  ms1m-150 : Eqn
  ms1m-150 = derive (cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 3 ms1m-14 ∷ rw 0 ms1m-142 ∷ []) refl

  ms1m-151 : Eqn
  ms1m-151 = derive (k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1 ∷ rw 3 ms1m-3 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw 3 ms1m-31 ∷
       rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 4 ms1m-31 ∷ rw 3 ms1m-31 ∷ rw 2 ms1m-31 ∷ rw 0 ms1m-131 ∷
       rw 0 ms1m-138 ∷ rw 1 ms1m-138 ∷ rw 2 ms1m-138 ∷ []) refl

  ms1m-152 : Eqn
  ms1m-152 = derive (k₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-148 ∷ rw 1 ms1m-151 ∷ rw 0 ms1m-145 ∷ []) refl

  ms1m-158 : Eqn
  ms1m-158 = derive (k₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-152 ∷ rw 0 ms1m-138 ∷ rw 2 ms1m-138 ∷ []) refl

  ms1m-160 : Eqn
  ms1m-160 = derive (ι ∷ s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 ms1m-152 ∷ rw⁻ 4 ms1m-152 ∷ rw 0 ms1m-141 ∷ []) refl

  ms1m-161 : Eqn
  ms1m-161 = derive (k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (k₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-6 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-32 ∷ rw 3 ms1m-32 ∷
       rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 4 ms1m-32 ∷ rw 3 ms1m-32 ∷ rw 2 ms1m-32 ∷ rw 0 ms1m-131 ∷ []) refl

  ms1m-162 : Eqn
  ms1m-162 = derive (ι ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 4 ms1m-138 ∷ rw 0 ms1m-143 ∷ []) refl

  ms1m-163 : Eqn
  ms1m-163 = derive (s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-143 ∷ rw 5 ms1m-152 ∷ rw 2 ms1m-152 ∷ rw 1 ms1m-24 ∷ []) refl

  ms1m-164 : Eqn
  ms1m-164 = derive (k₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-145 ∷ rw 0 ms1m-8 ∷ rw 1 ms1m-158 ∷ rw 0 ms1m-143 ∷ []) refl

  ms1m-165 : Eqn
  ms1m-165 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-164 ∷ rw 0 ms1m-152 ∷ []) refl

  ms1m-167 : Eqn
  ms1m-167 = derive (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-164 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 0 ms1m-21 ∷
       rw 4 ms1m-1 ∷ []) refl

  ms1m-168 : Eqn
  ms1m-168 = derive (s₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-21 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-169 : Eqn
  ms1m-169 = derive (s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-164 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-152 ∷
       rw 0 ms1m-21 ∷ rw 2 ms1m-21 ∷ []) refl

  ms1m-170 : Eqn
  ms1m-170 = derive (cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ [])
    (rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-164 ∷ rw 0 ms1m-21 ∷ rw 4 ms1m-17 ∷ rw 5 ms1m-17 ∷ []) refl

  ms1m-171 : Eqn
  ms1m-171 = derive (s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ [])
    (cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 6 ms1m-18 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 0 ms1m-22 ∷ rw 4 ms1m-4 ∷ []) refl

  ms1m-173 : Eqn
  ms1m-173 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-22 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-174 : Eqn
  ms1m-174 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (k₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 3 ms1m-138 ∷ rw 0 ms1m-144 ∷ []) refl

  ms1m-179 : Eqn
  ms1m-179 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 4 ms1m-14 ∷ rw 0 ms1m-149 ∷ []) refl

  ms1m-180 : Eqn
  ms1m-180 = derive (ι ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-179 ∷ rw 0 ms1m-72 ∷ []) refl

  ms1m-183 : Eqn
  ms1m-183 = derive (k₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
    (k₁ ∷ k₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-52 ∷ rw⁻ 0 ms1m-52 ∷ rw⁻ 1 ms1m-161 ∷ rw 0 ms1m-129 ∷ []) refl

  ms1m-185 : Eqn
  ms1m-185 = derive (k₁ ∷ k₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (k₁ ∷ k₁ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-183 ∷ rw⁻ 1 ms1m-52 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 0 ms1m-52 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-161 ∷
       rw 0 ms1m-161 ∷ rw 2 ms1m-25 ∷ []) refl

  ms1m-186 : Eqn
  ms1m-186 = derive (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (k₀ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-58 ∷ rw⁻ 4 ms1m-32 ∷
       rw⁻ 5 ms1m-58 ∷ rw⁻ 6 ms1m-9 ∷ rw 0 ms1m-185 ∷ rw 2 ms1m-58 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-57 ∷
       rw 0 ms1m-113 ∷ []) refl

  ms1m-187 : Eqn
  ms1m-187 = derive (k₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-186 ∷ rw 4 ms1m-4 ∷ []) refl

  ms1m-189 : Eqn
  ms1m-189 = derive (s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-187 ∷ rw 0 ms1m-171 ∷ []) refl

  ms1m-190 : Eqn
  ms1m-190 = derive (k₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-186 ∷ []) refl

  ms1m-191 : Eqn
  ms1m-191 = derive (cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ [])
    (rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-187 ∷ rw 0 ms1m-22 ∷ rw 4 ms1m-18 ∷ rw 5 ms1m-18 ∷ []) refl

  ms1m-192 : Eqn
  ms1m-192 = derive (s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-187 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-190 ∷
       rw 0 ms1m-22 ∷ rw 2 ms1m-22 ∷ []) refl

  ms1m-193 : Eqn
  ms1m-193 = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 2 ms1m-187 ∷ rw 0 ms1m-190 ∷ []) refl

  ms1m-201 : Eqn
  ms1m-201 = derive (k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1 ∷ rw 3 ms1m-167 ∷ []) refl

  ms1m-202 : Eqn
  ms1m-202 = derive (cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-1 ∷ rw 3 ms1m-168 ∷ []) refl

  ms1m-206 : Eqn
  ms1m-206 = derive (cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-173 ∷ []) refl

  ms1m-207 : Eqn
  ms1m-207 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 5 ms1m-12 ∷ rw 0 ms1m-179 ∷ []) refl

  ms1m-208 : Eqn
  ms1m-208 = derive (k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-189 ∷ []) refl

  ms1m-209 : Eqn
  ms1m-209 = derive (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (k₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-193 ∷ rw 5 ms1m-129 ∷ rw 4 ms1m-59 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 1 ms1m-59 ∷
       rw 0 ms1m-52 ∷ rw 5 ms1m-59 ∷ rw 4 ms1m-52 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-59 ∷ rw 1 ms1m-52 ∷ []) refl

  ms1m-210 : Eqn
  ms1m-210 = derive (ι ∷ s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 3 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 0 ms1m-11 ∷ rw 1 ms1m-160 ∷ []) refl

  ms1m-212 : Eqn
  ms1m-212 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (ι ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-160 ∷ rw 4 ms1m-165 ∷ rw 1 ms1m-24 ∷ []) refl

  ms1m-223 : Eqn
  ms1m-223 = derive (ι ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-212 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-224 : Eqn
  ms1m-224 = derive (cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-1 ∷ rw 3 ms1m-169 ∷ rw 0 ms1m-24 ∷ []) refl

  ms1m-245 : Eqn
  ms1m-245 = derive (cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-192 ∷ rw 0 ms1m-25 ∷ []) refl

  ms1m-250 : Eqn
  ms1m-250 = derive (k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (k₁ ∷ k₁ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-245 ∷ rw 5 ms1m-129 ∷ rw 4 ms1m-132 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 1 ms1m-52 ∷
       rw 4 ms1m-52 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-52 ∷ rw 0 ms1m-132 ∷ []) refl

  ms1m-252 : Eqn
  ms1m-252 = derive (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-190 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-187 ∷ rw⁻ 7 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 5 ms1m-18 ∷
       rw⁻ 0 ms1m-245 ∷ rw 5 ms1m-187 ∷ rw 4 ms1m-18 ∷ rw 1 ms1m-190 ∷ rw 0 ms1m-18 ∷ rw 1 ms1m-18 ∷
       rw 2 ms1m-18 ∷ rw 3 ms1m-22 ∷ rw 0 ms1m-25 ∷ []) refl

  ms1m-259 : Eqn
  ms1m-259 = derive (k₁ ∷ s₁ ∷ s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-14 ∷ rw 1 ms1m-201 ∷ rw 0 ms1m-33 ∷ rw 1 ms1m-33 ∷ rw 2 ms1m-33 ∷ []) refl

  ms1m-264 : Eqn
  ms1m-264 = derive (ι ∷ s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 1 ms1m-164 ∷ rw⁻ 2 ms1m-201 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-270 : Eqn
  ms1m-270 = derive (ι ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 1 ms1m-24 ∷ rw⁻ 4 ms1m-164 ∷ rw⁻ 5 ms1m-201 ∷ rw 0 ms1m-145 ∷ rw 0 ms1m-24 ∷ []) refl

  ms1m-276 : Eqn
  ms1m-276 = derive (s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-170 ∷ rw 1 ms1m-201 ∷ rw 0 ms1m-17 ∷ rw 1 ms1m-17 ∷ rw 2 ms1m-17 ∷ []) refl

  ms1m-283 : Eqn
  ms1m-283 = derive (k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-270 ∷ rw 0 ms1m-8 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-286 : Eqn
  ms1m-286 = derive (ι ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 1 ms1m-224 ∷ rw⁻ 0 ms1m-11 ∷ rw 1 ms1m-270 ∷ []) refl

  ms1m-288 : Eqn
  ms1m-288 = derive (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-152 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 0 ms1m-270 ∷
       rw 6 ms1m-170 ∷ rw 3 ms1m-283 ∷ rw 7 ms1m-132 ∷ rw 5 ms1m-132 ∷ rw 0 ms1m-146 ∷ rw 6 ms1m-17 ∷
       rw 7 ms1m-17 ∷ rw 2 ms1m-276 ∷ rw 0 ms1m-164 ∷ rw 1 ms1m-152 ∷ rw 0 ms1m-24 ∷ []) refl

  ms1m-289 : Eqn
  ms1m-289 = derive (ι ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 1 ms1m-24 ∷ rw⁻ 4 ms1m-283 ∷ rw⁻ 1 ms1m-152 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-164 ∷ rw⁻ 8 ms1m-17 ∷
       rw⁻ 7 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-201 ∷ rw 0 ms1m-270 ∷ rw 4 ms1m-17 ∷ rw 1 ms1m-152 ∷
       rw 0 ms1m-17 ∷ rw 1 ms1m-17 ∷ rw 2 ms1m-17 ∷ rw 0 ms1m-288 ∷ []) refl

  ms1m-296 : Eqn
  ms1m-296 = derive (s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-283 ∷ rw 0 ms1m-21 ∷ []) refl

  ms1m-308 : Eqn
  ms1m-308 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-202 ∷ rw 6 ms1m-16 ∷ []) refl

  ms1m-324 : Eqn
  ms1m-324 = derive (s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-22 ∷ rw⁻ 6 ms1m-18 ∷ rw 0 ms1m-206 ∷ []) refl

  ms1m-358 : Eqn
  ms1m-358 = derive (k₁ ∷ k₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-59 ∷ rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-209 ∷ rw 0 ms1m-4 ∷ []) refl

  ms1m-360 : Eqn
  ms1m-360 = derive (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (k₁ ∷ k₁ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 2 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 0 ms1m-18 ∷ rw 1 ms1m-209 ∷ rw 0 ms1m-132 ∷ []) refl

  ms1m-373 : Eqn
  ms1m-373 = derive (s₀ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-58 ∷ rw⁻ 4 ms1m-32 ∷
       rw⁻ 5 ms1m-32 ∷ rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-9 ∷ rw 0 ms1m-358 ∷ rw 3 ms1m-58 ∷ rw 2 ms1m-32 ∷
       rw 1 ms1m-32 ∷ rw 0 ms1m-58 ∷ []) refl

  ms1m-437 : Eqn
  ms1m-437 = derive (k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 1 ms1m-252 ∷ []) refl

  ms1m-441 : Eqn
  ms1m-441 = derive (s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-437 ∷ rw 0 ms1m-22 ∷ []) refl

  ms1m-506 : Eqn
  ms1m-506 = derive (cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-1 ∷ rw 3 ms1m-296 ∷ rw 0 ms1m-24 ∷ []) refl

  ms1m-507 : Eqn
  ms1m-507 = derive (cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 2 ms1m-506 ∷ rw 0 ms1m-289 ∷ []) refl

  ms1m-521 : Eqn
  ms1m-521 = derive (cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-270 ∷ rw 4 ms1m-506 ∷ rw 0 ms1m-141 ∷ []) refl

  ms1m-542 : Eqn
  ms1m-542 = derive (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-441 ∷ rw 0 ms1m-25 ∷ []) refl

  ms1m-544 : Eqn
  ms1m-544 = derive (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 5 ms1m-13 ∷ rw 0 ms1m-542 ∷ []) refl

  ms1m-591 : Eqn
  ms1m-591 = derive (cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 3 ms1m-521 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-627 : Eqn
  ms1m-627 = derive (ι ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 1 ms1m-60 ∷ rw⁻ 0 ms1m-10 ∷ rw 1 ms1m-73 ∷ rw 0 ms1m-58 ∷ rw 1 ms1m-129 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-628 : Eqn
  ms1m-628 = derive (ι ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (ι ∷ s₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-11 ∷ rw⁻ 1 ms1m-73 ∷ rw 0 ms1m-11 ∷ rw 1 ms1m-17 ∷ rw 2 ms1m-26 ∷ []) refl

  ms1m-631 : Eqn
  ms1m-631 = derive (s₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 3 ms1m-132 ∷ rw⁻ 4 ms1m-132 ∷ rw⁻ 6 ms1m-52 ∷ rw⁻ 7 ms1m-59 ∷
       rw⁻ 8 ms1m-59 ∷ rw⁻ 5 ms1m-52 ∷ rw⁻ 6 ms1m-59 ∷ rw⁻ 7 ms1m-59 ∷ rw⁻ 8 ms1m-129 ∷ rw 0 ms1m-73 ∷ []) refl

  ms1m-645 : Eqn
  ms1m-645 = derive (cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 1 ms1m-132 ∷ rw⁻ 3 ms1m-52 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-59 ∷ rw⁻ 6 ms1m-52 ∷
       rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-52 ∷ rw⁻ 6 ms1m-132 ∷ rw 0 ms1m-628 ∷
       rw 5 ms1m-52 ∷ rw 4 ms1m-59 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-52 ∷ rw 6 ms1m-52 ∷ rw 5 ms1m-59 ∷
       rw 4 ms1m-59 ∷ rw 3 ms1m-52 ∷ rw 0 ms1m-104 ∷ []) refl

  ms1m-650 : Eqn
  ms1m-650 = derive (s₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-645 ∷ rw 5 ms1m-16 ∷ []) refl

  ms1m-651 : Eqn
  ms1m-651 = derive (cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw 0 ms1m-645 ∷ []) refl

  ms1m-654 : Eqn
  ms1m-654 = derive (s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 4 ms1m-18 ∷ rw⁻ 0 ms1m-22 ∷ rw 2 ms1m-645 ∷ rw 1 ms1m-60 ∷ rw 0 ms1m-17 ∷ rw 2 ms1m-129 ∷
       rw 1 ms1m-132 ∷ rw 3 ms1m-18 ∷ rw 4 ms1m-18 ∷ []) refl

  ms1m-677 : Eqn
  ms1m-677 = derive (s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-129 ∷ rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-650 ∷ []) refl

  ms1m-678 : Eqn
  ms1m-678 = derive (s₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-645 ∷ rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-650 ∷ []) refl

  ms1m-691 : Eqn
  ms1m-691 = derive (cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 ms1m-52 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-52 ∷ rw⁻ 0 ms1m-650 ∷ rw 5 ms1m-202 ∷
       rw 4 ms1m-60 ∷ rw 3 ms1m-33 ∷ rw 2 ms1m-33 ∷ rw 1 ms1m-60 ∷ rw 5 ms1m-60 ∷ rw 4 ms1m-33 ∷
       rw 3 ms1m-33 ∷ rw 2 ms1m-60 ∷ rw 6 ms1m-60 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-33 ∷ rw 3 ms1m-60 ∷
       rw 0 ms1m-24 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 1 ms1m-59 ∷ rw 0 ms1m-52 ∷ []) refl

  ms1m-711 : Eqn
  ms1m-711 = derive (cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (s₁ ∷ k₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-25 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-190 ∷ rw⁻ 0 ms1m-18 ∷
       rw⁻ 1 ms1m-187 ∷ rw⁻ 4 ms1m-208 ∷ rw 0 ms1m-651 ∷ rw 1 ms1m-193 ∷ rw 4 ms1m-187 ∷ rw 1 ms1m-25 ∷
       rw 3 ms1m-129 ∷ rw 2 ms1m-59 ∷ rw 1 ms1m-52 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-52 ∷ []) refl

  ms1m-720 : Eqn
  ms1m-720 = derive (k₁ ∷ k₁ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-132 ∷ rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 1 ms1m-52 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-129 ∷
       rw⁻ 0 ms1m-25 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-187 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 0 ms1m-18 ∷
       rw⁻ 1 ms1m-193 ∷ rw⁻ 6 ms1m-245 ∷ rw 0 ms1m-651 ∷ rw 1 ms1m-193 ∷ rw 4 ms1m-187 ∷ rw 1 ms1m-25 ∷
       rw 3 ms1m-129 ∷ rw 2 ms1m-59 ∷ rw 1 ms1m-52 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-52 ∷ []) refl

  ms1m-733 : Eqn
  ms1m-733 = derive (s₁ ∷ k₁ ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-132 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 3 ms1m-132 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷
       rw⁻ 3 ms1m-711 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-758 : Eqn
  ms1m-758 = derive (s₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw⁻ 3 ms1m-52 ∷ rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-132 ∷ rw⁻ 4 ms1m-132 ∷ rw⁻ 5 ms1m-132 ∷
       rw⁻ 7 ms1m-52 ∷ rw⁻ 8 ms1m-59 ∷ rw⁻ 9 ms1m-59 ∷ rw⁻ 6 ms1m-52 ∷ rw⁻ 7 ms1m-59 ∷ rw⁻ 8 ms1m-59 ∷
       rw⁻ 9 ms1m-129 ∷ rw 0 ms1m-627 ∷ []) refl

  ms1m-759 : Eqn
  ms1m-759 = derive (s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 3 ms1m-758 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-760 : Eqn
  ms1m-760 = derive (s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-187 ∷ rw⁻ 0 ms1m-758 ∷ rw 7 ms1m-4 ∷ []) refl

  ms1m-761 : Eqn
  ms1m-761 = derive (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-758 ∷ rw 6 ms1m-4 ∷ []) refl

  ms1m-762 : Eqn
  ms1m-762 = derive (s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw 0 ms1m-324 ∷ rw 1 ms1m-761 ∷ rw 0 ms1m-33 ∷ []) refl

  ms1m-765 : Eqn
  ms1m-765 = derive (s₁ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-758 ∷ []) refl

  ms1m-784 : Eqn
  ms1m-784 = derive (s₁ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-761 ∷ rw 0 ms1m-4 ∷ []) refl

  ms1m-786 : Eqn
  ms1m-786 = derive (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 6 ms1m-18 ∷ rw⁻ 2 ms1m-22 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 0 ms1m-18 ∷ rw 1 ms1m-761 ∷ rw 0 ms1m-17 ∷ []) refl

  ms1m-812 : Eqn
  ms1m-812 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 3 ms1m-784 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-851 : Eqn
  ms1m-851 = derive (s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-645 ∷ rw 0 ms1m-631 ∷ rw 6 ms1m-129 ∷ rw 5 ms1m-132 ∷
       rw 4 ms1m-52 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-59 ∷ rw 1 ms1m-52 ∷ rw 5 ms1m-52 ∷ rw 4 ms1m-59 ∷
       rw 3 ms1m-59 ∷ rw 2 ms1m-52 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-856 : Eqn
  ms1m-856 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 2 ms1m-645 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-678 ∷ []) refl

  ms1m-902 : Eqn
  ms1m-902 = derive (ι ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-11 ∷ rw⁻ 1 ms1m-180 ∷ rw 0 ms1m-11 ∷ rw 1 ms1m-18 ∷ rw 2 ms1m-26 ∷ rw 1 ms1m-59 ∷
       rw 2 ms1m-33 ∷ rw 3 ms1m-33 ∷ rw 4 ms1m-59 ∷ []) refl

  ms1m-909 : Eqn
  ms1m-909 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 3 ms1m-132 ∷ rw⁻ 4 ms1m-174 ∷
       rw 0 ms1m-180 ∷ []) refl

  ms1m-924 : Eqn
  ms1m-924 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 1 ms1m-174 ∷ rw⁻ 6 ms1m-132 ∷ rw 0 ms1m-902 ∷ rw 5 ms1m-59 ∷ rw 0 ms1m-146 ∷
       rw 3 ms1m-59 ∷ []) refl

  ms1m-937 : Eqn
  ms1m-937 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-924 ∷ rw 5 ms1m-16 ∷ []) refl

  ms1m-938 : Eqn
  ms1m-938 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₁ ∷ s₀ ∷ [])
    (rw⁻ 5 ms1m-17 ∷ rw 0 ms1m-924 ∷ rw 4 ms1m-33 ∷ []) refl

  ms1m-952 : Eqn
  ms1m-952 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 5 ms1m-245 ∷ rw 0 ms1m-924 ∷ []) refl

  ms1m-982 : Eqn
  ms1m-982 = derive (s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw 2 ms1m-937 ∷ []) refl

  ms1m-989 : Eqn
  ms1m-989 = derive (cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-152 ∷ rw⁻ 0 ms1m-17 ∷
       rw⁻ 1 ms1m-164 ∷ rw⁻ 4 ms1m-201 ∷ rw 0 ms1m-938 ∷ rw 5 ms1m-59 ∷ rw 0 ms1m-165 ∷ rw 6 ms1m-33 ∷
       rw 3 ms1m-164 ∷ rw 0 ms1m-24 ∷ rw 3 ms1m-59 ∷ []) refl

  ms1m-994 : Eqn
  ms1m-994 = derive (k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-142 ∷ rw⁻ 0 ms1m-132 ∷ rw⁻ 1 ms1m-144 ∷ rw⁻ 2 ms1m-989 ∷ rw 0 ms1m-591 ∷ []) refl

  ms1m-1020 : Eqn
  ms1m-1020 = derive (k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-142 ∷ rw⁻ 0 ms1m-132 ∷ rw⁻ 1 ms1m-132 ∷ rw⁻ 2 ms1m-144 ∷
       rw⁻ 3 ms1m-989 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-1024 : Eqn
  ms1m-1024 = derive (s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-170 ∷ rw⁻ 6 ms1m-132 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-138 ∷ rw 0 ms1m-989 ∷ []) refl

  ms1m-1050 : Eqn
  ms1m-1050 = derive (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-909 ∷ rw 5 ms1m-1 ∷ []) refl

  ms1m-1054 : Eqn
  ms1m-1054 = derive (s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (s₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-102 ∷ rw 2 ms1m-909 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-11 ∷ rw 1 ms1m-132 ∷ rw 0 ms1m-113 ∷
       rw 0 ms1m-17 ∷ rw 1 ms1m-17 ∷ []) refl

  ms1m-1093 : Eqn
  ms1m-1093 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 3 ms1m-59 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-924 ∷ rw⁻ 0 ms1m-179 ∷
       rw 2 ms1m-982 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-11 ∷ rw 1 ms1m-132 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-1112 : Eqn
  ms1m-1112 = derive (s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-8 ∷ rw 1 ms1m-1050 ∷ []) refl

  ms1m-1114 : Eqn
  ms1m-1114 = derive (s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-59 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-1112 ∷ rw 0 ms1m-59 ∷ []) refl

  ms1m-1116 : Eqn
  ms1m-1116 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 6 ms1m-17 ∷ rw⁻ 2 ms1m-21 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-1112 ∷ rw 0 ms1m-102 ∷ []) refl

  ms1m-1119 : Eqn
  ms1m-1119 = derive (s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1116 ∷ rw 0 ms1m-308 ∷ []) refl

  ms1m-1139 : Eqn
  ms1m-1139 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-146 ∷ rw⁻ 5 ms1m-132 ∷ rw⁻ 0 ms1m-909 ∷ rw 5 ms1m-1112 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-132 ∷
       rw 1 ms1m-132 ∷ rw 0 ms1m-59 ∷ rw 1 ms1m-59 ∷ rw 5 ms1m-18 ∷ rw 4 ms1m-18 ∷ rw 3 ms1m-18 ∷
       rw 4 ms1m-26 ∷ []) refl

  ms1m-1207 : Eqn
  ms1m-1207 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷
       rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-924 ∷ rw⁻ 1 ms1m-179 ∷ rw⁻ 0 ms1m-179 ∷ rw 1 ms1m-1093 ∷ []) refl

  ms1m-1293 : Eqn
  ms1m-1293 = derive (s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-1112 ∷ rw⁻ 8 ms1m-17 ∷ rw⁻ 7 ms1m-17 ∷ rw⁻ 0 ms1m-162 ∷ rw⁻ 6 ms1m-132 ∷ rw⁻ 8 ms1m-132 ∷
       rw⁻ 4 ms1m-283 ∷ rw⁻ 7 ms1m-170 ∷ rw 0 ms1m-264 ∷ rw 5 ms1m-17 ∷ rw 2 ms1m-152 ∷ rw 1 ms1m-17 ∷
       rw 2 ms1m-17 ∷ rw 3 ms1m-17 ∷ rw 0 ms1m-24 ∷ []) refl

  ms1m-1299 : Eqn
  ms1m-1299 = derive (cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ s₀ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-17 ∷ rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-152 ∷
       rw⁻ 5 ms1m-17 ∷ rw⁻ 0 ms1m-264 ∷ rw 7 ms1m-924 ∷ rw 5 ms1m-132 ∷ rw 0 ms1m-143 ∷ rw 4 ms1m-17 ∷
       rw 1 ms1m-152 ∷ rw 0 ms1m-24 ∷ rw 1 ms1m-17 ∷ rw 2 ms1m-102 ∷ []) refl

  ms1m-1306 : Eqn
  ms1m-1306 = derive (cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-17 ∷ rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-152 ∷
       rw⁻ 5 ms1m-17 ∷ rw⁻ 0 ms1m-264 ∷ rw 7 ms1m-938 ∷ rw 5 ms1m-132 ∷ rw 0 ms1m-143 ∷ rw 4 ms1m-17 ∷
       rw 1 ms1m-152 ∷ rw 0 ms1m-24 ∷ rw 1 ms1m-17 ∷ rw 2 ms1m-142 ∷ []) refl

  ms1m-1309 : Eqn
  ms1m-1309 = derive (k₁ ∷ s₁ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1299 ∷ rw 5 ms1m-16 ∷ []) refl

  ms1m-1310 : Eqn
  ms1m-1310 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-142 ∷ rw⁻ 3 ms1m-1299 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-1322 : Eqn
  ms1m-1322 = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-152 ∷ rw⁻ 5 ms1m-17 ∷
       rw⁻ 0 ms1m-264 ∷ rw 7 ms1m-1299 ∷ rw 5 ms1m-132 ∷ rw 0 ms1m-143 ∷ rw 4 ms1m-17 ∷ rw 1 ms1m-152 ∷
       rw 0 ms1m-24 ∷ rw 1 ms1m-18 ∷ []) refl

  ms1m-1343 : Eqn
  ms1m-1343 = derive (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1322 ∷ rw 5 ms1m-16 ∷ []) refl

  ms1m-1344 : Eqn
  ms1m-1344 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 3 ms1m-1322 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-1346 : Eqn
  ms1m-1346 = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 5 ms1m-17 ∷ rw 0 ms1m-1322 ∷ []) refl

  ms1m-1405 : Eqn
  ms1m-1405 = derive (s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-1322 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 0 ms1m-21 ∷ rw 3 ms1m-1309 ∷
       rw 0 ms1m-1346 ∷ []) refl

  ms1m-1407 : Eqn
  ms1m-1407 = derive (s₁ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw 2 ms1m-1309 ∷ []) refl

  ms1m-1408 : Eqn
  ms1m-1408 = derive (k₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-59 ∷
       rw⁻ 3 ms1m-1310 ∷ rw 0 ms1m-4 ∷ []) refl

  ms1m-1421 : Eqn
  ms1m-1421 = derive (k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 4 ms1m-17 ∷ rw⁻ 0 ms1m-1310 ∷ rw 6 ms1m-170 ∷ rw 0 ms1m-909 ∷ rw 5 ms1m-132 ∷ rw 0 ms1m-146 ∷
       rw 0 ms1m-1139 ∷ []) refl

  ms1m-1427 : Eqn
  ms1m-1427 = derive (k₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1421 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 0 ms1m-1310 ∷ rw 7 ms1m-201 ∷ rw 6 ms1m-17 ∷ rw 0 ms1m-909 ∷
       rw 7 ms1m-17 ∷ rw 8 ms1m-17 ∷ rw 2 ms1m-1112 ∷ rw 0 ms1m-113 ∷ rw 0 ms1m-1344 ∷ []) refl

  ms1m-1428 : Eqn
  ms1m-1428 = derive (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-1427 ∷ rw 0 ms1m-1405 ∷ []) refl

  ms1m-1449 : Eqn
  ms1m-1449 = derive (k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-1322 ∷ rw⁻ 0 ms1m-102 ∷ rw 1 ms1m-1343 ∷ []) refl

  ms1m-1453 : Eqn
  ms1m-1453 = derive (s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw 2 ms1m-1343 ∷ []) refl

  ms1m-1454 : Eqn
  ms1m-1454 = derive (k₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-1344 ∷ rw 0 ms1m-4 ∷ []) refl

  ms1m-1459 : Eqn
  ms1m-1459 = derive (k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-59 ∷ rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-132 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 3 ms1m-132 ∷ rw⁻ 5 ms1m-132 ∷
       rw⁻ 6 ms1m-132 ∷ rw 0 ms1m-1344 ∷ []) refl

  ms1m-1460 : Eqn
  ms1m-1460 = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1293 ∷ rw 1 ms1m-1459 ∷ []) refl

  ms1m-1465 : Eqn
  ms1m-1465 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-164 ∷ rw 0 ms1m-1344 ∷ rw 4 ms1m-17 ∷ rw 5 ms1m-17 ∷
       rw 6 ms1m-17 ∷ rw 3 ms1m-164 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-17 ∷ []) refl

  ms1m-1489 : Eqn
  ms1m-1489 = derive (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 3 ms1m-1322 ∷ rw 0 ms1m-1344 ∷ []) refl

  ms1m-1490 : Eqn
  ms1m-1490 = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 6 ms1m-17 ∷ rw 0 ms1m-1346 ∷ []) refl

  ms1m-1530 : Eqn
  ms1m-1530 = derive (k₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-1299 ∷ rw⁻ 0 ms1m-142 ∷ rw 2 ms1m-1407 ∷ rw 1 ms1m-57 ∷
       rw 0 ms1m-11 ∷ rw 1 ms1m-132 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-1598 : Eqn
  ms1m-1598 = derive (k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-17 ∷ rw 0 ms1m-1449 ∷ []) refl

  ms1m-1600 : Eqn
  ms1m-1600 = derive (s₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw 3 ms1m-1449 ∷ rw 1 ms1m-1428 ∷ []) refl

  ms1m-1601 : Eqn
  ms1m-1601 = derive (ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 ms1m-1449 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-1678 : Eqn
  ms1m-1678 = derive (s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-59 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 3 ms1m-132 ∷ rw⁻ 5 ms1m-132 ∷ rw⁻ 6 ms1m-132 ∷
       rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 3 ms1m-1322 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷
       rw⁻ 3 ms1m-1460 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-1734 : Eqn
  ms1m-1734 = derive (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 ms1m-102 ∷ rw⁻ 3 ms1m-1322 ∷ rw 0 ms1m-1489 ∷ []) refl

  ms1m-1743 : Eqn
  ms1m-1743 = derive (ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 ms1m-1530 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-1811 : Eqn
  ms1m-1811 = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-286 ∷ rw 0 ms1m-8 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-1817 : Eqn
  ms1m-1817 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-286 ∷ rw 4 ms1m-1322 ∷ rw 0 ms1m-141 ∷ []) refl

  ms1m-1820 : Eqn
  ms1m-1820 = derive (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷
       rw⁻ 2 ms1m-152 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 0 ms1m-286 ∷ rw 4 ms1m-1346 ∷ rw 0 ms1m-141 ∷ []) refl

  ms1m-1823 : Eqn
  ms1m-1823 = derive (k₁ ∷ s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1817 ∷ rw 5 ms1m-16 ∷ []) refl

  ms1m-1824 : Eqn
  ms1m-1824 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-142 ∷ rw⁻ 3 ms1m-1817 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-1825 : Eqn
  ms1m-1825 = derive (s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-142 ∷ rw⁻ 2 ms1m-1817 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-1826 : Eqn
  ms1m-1826 = derive (k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1465 ∷ rw 0 ms1m-1824 ∷ rw 5 ms1m-17 ∷ rw 4 ms1m-17 ∷ rw 1 ms1m-152 ∷ rw 0 ms1m-17 ∷
       rw 1 ms1m-17 ∷ rw 2 ms1m-17 ∷ []) refl

  ms1m-1872 : Eqn
  ms1m-1872 = derive (s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw 2 ms1m-1823 ∷ []) refl

  ms1m-1873 : Eqn
  ms1m-1873 = derive (k₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷
       rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-1825 ∷ rw 0 ms1m-4 ∷ []) refl

  ms1m-1914 : Eqn
  ms1m-1914 = derive (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-150 ∷ rw⁻ 6 ms1m-22 ∷ rw 0 ms1m-1811 ∷ []) refl

  ms1m-1938 : Eqn
  ms1m-1938 = derive (s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-1872 ∷ rw 0 ms1m-58 ∷ rw 1 ms1m-52 ∷ []) refl

  ms1m-1940 : Eqn
  ms1m-1940 = derive (s₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (ι ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-18 ∷ rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-1872 ∷ rw 0 ms1m-11 ∷ rw 1 ms1m-1460 ∷ []) refl

  ms1m-2133 : Eqn
  ms1m-2133 = derive (k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-654 ∷ rw 2 ms1m-33 ∷ rw 1 ms1m-33 ∷ rw 0 ms1m-33 ∷ rw 3 ms1m-59 ∷
       rw 2 ms1m-59 ∷ rw 1 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-59 ∷ rw 3 ms1m-25 ∷ []) refl

  ms1m-2134 : Eqn
  ms1m-2134 = derive (s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-2133 ∷ rw 6 ms1m-16 ∷ []) refl

  ms1m-2212 : Eqn
  ms1m-2212 = derive (s₁ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (ι ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-57 ∷ rw⁻ 3 ms1m-32 ∷ rw⁻ 4 ms1m-32 ∷
       rw⁻ 5 ms1m-58 ∷ rw⁻ 6 ms1m-11 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-11 ∷ rw 0 ms1m-677 ∷ rw 5 ms1m-58 ∷
       rw 4 ms1m-32 ∷ rw 3 ms1m-32 ∷ rw 2 ms1m-58 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-58 ∷ []) refl

  ms1m-2247 : Eqn
  ms1m-2247 = derive (s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (ι ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-2212 ∷ rw 0 ms1m-32 ∷ []) refl

  ms1m-2329 : Eqn
  ms1m-2329 = derive (cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-58 ∷ rw⁻ 4 ms1m-32 ∷
       rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-11 ∷ rw 0 ms1m-720 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷
       rw 4 ms1m-32 ∷ rw 3 ms1m-58 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-31 ∷ rw 0 ms1m-104 ∷ []) refl

  ms1m-2330 : Eqn
  ms1m-2330 = derive (s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-2329 ∷ rw 5 ms1m-16 ∷ []) refl

  ms1m-2331 : Eqn
  ms1m-2331 = derive (s₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-2329 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-2333 : Eqn
  ms1m-2333 = derive (cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw 0 ms1m-2329 ∷ []) refl

  ms1m-2369 : Eqn
  ms1m-2369 = derive (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 ms1m-2330 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-2406 : Eqn
  ms1m-2406 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 3 ms1m-2331 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-2417 : Eqn
  ms1m-2417 = derive (k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 4 ms1m-18 ∷ rw⁻ 0 ms1m-2331 ∷ rw 7 ms1m-190 ∷ rw 6 ms1m-18 ∷ rw 0 ms1m-631 ∷ rw 7 ms1m-18 ∷
       rw 8 ms1m-18 ∷ rw 2 ms1m-761 ∷ rw 1 ms1m-60 ∷ rw 2 ms1m-129 ∷ rw 0 ms1m-104 ∷ []) refl

  ms1m-2450 : Eqn
  ms1m-2450 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (s₁ ∷ k₁ ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-25 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-190 ∷ rw⁻ 5 ms1m-18 ∷
       rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-187 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-208 ∷ rw 0 ms1m-2333 ∷
       rw 4 ms1m-190 ∷ rw 3 ms1m-18 ∷ rw 4 ms1m-18 ∷ rw 1 ms1m-187 ∷ rw 5 ms1m-18 ∷ rw 2 ms1m-190 ∷
       rw 1 ms1m-25 ∷ rw 3 ms1m-129 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-52 ∷ rw 2 ms1m-52 ∷ []) refl

  ms1m-2457 : Eqn
  ms1m-2457 = derive (k₁ ∷ k₁ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-132 ∷ rw⁻ 2 ms1m-52 ∷ rw⁻ 1 ms1m-52 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 3 ms1m-129 ∷ rw⁻ 0 ms1m-25 ∷
       rw⁻ 1 ms1m-208 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-187 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 0 ms1m-191 ∷ rw⁻ 6 ms1m-245 ∷
       rw 0 ms1m-2333 ∷ rw 4 ms1m-190 ∷ rw 3 ms1m-18 ∷ rw 4 ms1m-18 ∷ rw 1 ms1m-187 ∷ rw 5 ms1m-18 ∷
       rw 2 ms1m-190 ∷ rw 1 ms1m-25 ∷ rw 3 ms1m-129 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-52 ∷ rw 2 ms1m-52 ∷ []) refl

  ms1m-2582 : Eqn
  ms1m-2582 = derive (s₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (ι ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-57 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-11 ∷
       rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-32 ∷ rw⁻ 8 ms1m-11 ∷ rw 0 ms1m-733 ∷ rw 5 ms1m-58 ∷
       rw 4 ms1m-11 ∷ rw 3 ms1m-58 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-58 ∷ []) refl

  ms1m-2626 : Eqn
  ms1m-2626 = derive (s₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-2582 ∷ rw 0 ms1m-58 ∷ rw 1 ms1m-129 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-2652 : Eqn
  ms1m-2652 = derive (s₁ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-2626 ∷ []) refl

  ms1m-2653 : Eqn
  ms1m-2653 = derive (s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-2626 ∷ rw 7 ms1m-16 ∷ []) refl

  ms1m-2701 : Eqn
  ms1m-2701 = derive (s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 2 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-759 ∷ []) refl

  ms1m-2725 : Eqn
  ms1m-2725 = derive (s₁ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-760 ∷ rw 0 ms1m-18 ∷ rw 1 ms1m-18 ∷ rw 2 ms1m-191 ∷ rw 1 ms1m-761 ∷
       rw 0 ms1m-33 ∷ []) refl

  ms1m-2750 : Eqn
  ms1m-2750 = derive (cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-762 ∷ rw 2 ms1m-33 ∷ rw 1 ms1m-33 ∷ rw 0 ms1m-33 ∷ rw 1 ms1m-25 ∷ []) refl

  ms1m-2916 : Eqn
  ms1m-2916 = derive (s₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-187 ∷ rw 0 ms1m-765 ∷ []) refl

  ms1m-3074 : Eqn
  ms1m-3074 = derive (s₁ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-786 ∷ rw 0 ms1m-4 ∷ []) refl

  ms1m-3130 : Eqn
  ms1m-3130 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 3 ms1m-3074 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-3242 : Eqn
  ms1m-3242 = derive (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-812 ∷ rw 6 ms1m-4 ∷ []) refl

  ms1m-3244 : Eqn
  ms1m-3244 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (rw⁻ 5 ms1m-52 ∷ rw⁻ 6 ms1m-59 ∷ rw⁻ 7 ms1m-14 ∷ rw 0 ms1m-812 ∷ rw 6 ms1m-52 ∷ []) refl

  ms1m-3385 : Eqn
  ms1m-3385 = derive (s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-11 ∷
       rw⁻ 5 ms1m-57 ∷ rw⁻ 6 ms1m-31 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-11 ∷ rw 0 ms1m-994 ∷ rw 5 ms1m-57 ∷
       rw 4 ms1m-11 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-57 ∷ []) refl

  ms1m-3389 : Eqn
  ms1m-3389 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1598 ∷ rw 2 ms1m-3385 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-57 ∷ rw 2 ms1m-59 ∷ rw 0 ms1m-113 ∷
       rw 0 ms1m-33 ∷ rw 1 ms1m-59 ∷ []) refl

  ms1m-3395 : Eqn
  ms1m-3395 = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-16 ∷ rw 3 ms1m-3389 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-17 ∷ rw 0 ms1m-17 ∷ rw 3 ms1m-102 ∷
       rw 2 ms1m-18 ∷ rw 1 ms1m-18 ∷ rw 0 ms1m-1940 ∷ rw 6 ms1m-132 ∷ rw 4 ms1m-132 ∷ rw 3 ms1m-132 ∷
       rw 0 ms1m-104 ∷ []) refl

  ms1m-3399 : Eqn
  ms1m-3399 = derive (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-3395 ∷ rw 0 ms1m-1346 ∷ []) refl

  ms1m-3401 : Eqn
  ms1m-3401 = derive (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 5 ms1m-17 ∷ rw⁻ 0 ms1m-3395 ∷ rw 0 ms1m-1490 ∷ []) refl

  ms1m-3414 : Eqn
  ms1m-3414 = derive (cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 0 ms1m-113 ∷ rw⁻ 1 ms1m-132 ∷
       rw⁻ 3 ms1m-132 ∷ rw⁻ 4 ms1m-132 ∷ rw⁻ 0 ms1m-11 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-11 ∷
       rw⁻ 4 ms1m-57 ∷ rw⁻ 5 ms1m-163 ∷ rw 0 ms1m-3395 ∷ rw 3 ms1m-21 ∷ rw 2 ms1m-17 ∷ rw 7 ms1m-17 ∷
       rw 3 ms1m-21 ∷ rw 5 ms1m-3395 ∷ rw 0 ms1m-163 ∷ rw 0 ms1m-146 ∷ []) refl

  ms1m-3428 : Eqn
  ms1m-3428 = derive (cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ [])
    (rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-164 ∷ rw 0 ms1m-3395 ∷ rw 5 ms1m-17 ∷ rw 6 ms1m-17 ∷ []) refl

  ms1m-3472 : Eqn
  ms1m-3472 = derive (s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-1322 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-3395 ∷ rw 0 ms1m-1872 ∷
       rw 3 ms1m-144 ∷ rw 2 ms1m-132 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-3490 : Eqn
  ms1m-3490 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 ms1m-3399 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-3491 : Eqn
  ms1m-3491 = derive (s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 ms1m-59 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-3399 ∷ rw 0 ms1m-59 ∷ []) refl

  ms1m-3508 : Eqn
  ms1m-3508 = derive (s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷ rw 0 ms1m-3385 ∷ []) refl

  ms1m-3517 : Eqn
  ms1m-3517 = derive (k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (s₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-3491 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-3395 ∷ rw⁻ 0 ms1m-102 ∷ rw 2 ms1m-3385 ∷
       rw 1 ms1m-57 ∷ rw 0 ms1m-11 ∷ rw 1 ms1m-132 ∷ rw 0 ms1m-113 ∷ rw 0 ms1m-17 ∷ []) refl

  ms1m-3565 : Eqn
  ms1m-3565 = derive (cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 2 ms1m-17 ∷ rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-152 ∷
       rw⁻ 5 ms1m-17 ∷ rw⁻ 0 ms1m-264 ∷ rw 7 ms1m-3414 ∷ rw 5 ms1m-132 ∷ rw 0 ms1m-143 ∷ rw 4 ms1m-17 ∷
       rw 1 ms1m-152 ∷ rw 0 ms1m-24 ∷ rw 1 ms1m-17 ∷ []) refl

  ms1m-3616 : Eqn
  ms1m-3616 = derive (s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-3472 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-3617 : Eqn
  ms1m-3617 = derive (s₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-52 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-3472 ∷ rw 0 ms1m-52 ∷ []) refl

  ms1m-3632 : Eqn
  ms1m-3632 = derive (k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-13 ∷ rw 1 ms1m-3517 ∷ rw 0 ms1m-60 ∷ []) refl

  ms1m-3728 : Eqn
  ms1m-3728 = derive (k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-3616 ∷ rw 6 ms1m-1 ∷ []) refl

  ms1m-3730 : Eqn
  ms1m-3730 = derive (s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-59 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-3616 ∷ rw 0 ms1m-59 ∷ []) refl

  ms1m-3776 : Eqn
  ms1m-3776 = derive (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-3728 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-3803 : Eqn
  ms1m-3803 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-11 ∷
       rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-57 ∷ rw⁻ 7 ms1m-31 ∷ rw⁻ 8 ms1m-11 ∷ rw 0 ms1m-1020 ∷ rw 5 ms1m-57 ∷
       rw 4 ms1m-11 ∷ rw 3 ms1m-57 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-57 ∷ []) refl

  ms1m-3849 : Eqn
  ms1m-3849 = derive (k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 0 ms1m-113 ∷ rw⁻ 2 ms1m-132 ∷
       rw⁻ 4 ms1m-132 ∷ rw⁻ 5 ms1m-132 ∷ rw⁻ 0 ms1m-1453 ∷ rw⁻ 0 ms1m-18 ∷ rw 1 ms1m-1054 ∷ rw 0 ms1m-17 ∷
       rw 1 ms1m-17 ∷ []) refl

  ms1m-3927 : Eqn
  ms1m-3927 = derive (k₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1112 ∷ rw 2 ms1m-3849 ∷ rw 0 ms1m-24 ∷ []) refl

  ms1m-3950 : Eqn
  ms1m-3950 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-3927 ∷ rw 6 ms1m-16 ∷ []) refl

  ms1m-3955 : Eqn
  ms1m-3955 = derive (s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-21 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷ rw 0 ms1m-3950 ∷ []) refl

  ms1m-4068 : Eqn
  ms1m-4068 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 7 ms1m-17 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-21 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 1 ms1m-17 ∷
       rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-1114 ∷ rw 0 ms1m-102 ∷ rw 1 ms1m-102 ∷ []) refl

  ms1m-4250 : Eqn
  ms1m-4250 = derive (k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (s₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 2 ms1m-144 ∷ rw⁻ 5 ms1m-132 ∷ rw⁻ 0 ms1m-1407 ∷ rw 1 ms1m-1119 ∷ []) refl

  ms1m-4261 : Eqn
  ms1m-4261 = derive (k₁ ∷ s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (s₁ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-14 ∷ rw 1 ms1m-4250 ∷ rw 0 ms1m-33 ∷ []) refl

  ms1m-4468 : Eqn
  ms1m-4468 = derive (k₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 7 ms1m-17 ∷ rw 0 ms1m-1408 ∷ []) refl

  ms1m-4659 : Eqn
  ms1m-4659 = derive (ι ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-59 ∷ rw⁻ 0 ms1m-9 ∷ rw 1 ms1m-1601 ∷ []) refl

  ms1m-4669 : Eqn
  ms1m-4669 = derive (s₁ ∷ k₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-52 ∷ rw⁻ 1 ms1m-52 ∷ rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-1678 ∷ rw 0 ms1m-52 ∷ []) refl

  ms1m-4731 : Eqn
  ms1m-4731 = derive (s₁ ∷ k₁ ∷ s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-1820 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-4746 : Eqn
  ms1m-4746 = derive (s₀ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-102 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-21 ∷
       rw⁻ 7 ms1m-1817 ∷ rw 0 ms1m-1820 ∷ rw 4 ms1m-170 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-33 ∷ rw 4 ms1m-21 ∷
       rw 3 ms1m-33 ∷ rw 0 ms1m-164 ∷ rw 4 ms1m-59 ∷ rw 8 ms1m-17 ∷ rw 4 ms1m-4261 ∷ rw 1 ms1m-152 ∷
       rw 0 ms1m-24 ∷ rw 2 ms1m-202 ∷ rw 1 ms1m-33 ∷ rw 2 ms1m-33 ∷ rw 3 ms1m-33 ∷ rw 0 ms1m-164 ∷
       rw 4 ms1m-59 ∷ []) refl

  ms1m-4755 : Eqn
  ms1m-4755 = derive (s₁ ∷ k₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 ms1m-33 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-4731 ∷ []) refl

  ms1m-4756 : Eqn
  ms1m-4756 = derive (s₁ ∷ k₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 ms1m-60 ∷ rw⁻ 1 ms1m-52 ∷ rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-4731 ∷ []) refl

  ms1m-4762 : Eqn
  ms1m-4762 = derive (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-163 ∷ rw 3 ms1m-4731 ∷ []) refl

  ms1m-4810 : Eqn
  ms1m-4810 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-1873 ∷ rw 6 ms1m-16 ∷ []) refl

  ms1m-4811 : Eqn
  ms1m-4811 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-152 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-33 ∷ rw⁻ 5 ms1m-33 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-17 ∷
       rw 0 ms1m-1873 ∷ []) refl

  ms1m-4904 : Eqn
  ms1m-4904 = derive (s₁ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (ι ∷ k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-57 ∷ rw⁻ 3 ms1m-32 ∷ rw⁻ 4 ms1m-11 ∷
       rw⁻ 5 ms1m-58 ∷ rw⁻ 6 ms1m-11 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-11 ∷ rw 0 ms1m-2134 ∷ rw 5 ms1m-58 ∷
       rw 4 ms1m-11 ∷ rw 3 ms1m-32 ∷ rw 2 ms1m-58 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-58 ∷ []) refl

  ms1m-5260 : Eqn
  ms1m-5260 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-58 ∷ rw⁻ 4 ms1m-11 ∷
       rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-11 ∷ rw 0 ms1m-2457 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷
       rw 4 ms1m-11 ∷ rw 3 ms1m-58 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-31 ∷ rw 0 ms1m-104 ∷ []) refl

  ms1m-5272 : Eqn
  ms1m-5272 = derive (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-5260 ∷ rw 5 ms1m-16 ∷ []) refl

  ms1m-5273 : Eqn
  ms1m-5273 = derive (s₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-5260 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-5276 : Eqn
  ms1m-5276 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw 0 ms1m-5260 ∷ []) refl

  ms1m-5316 : Eqn
  ms1m-5316 = derive (k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-1322 ∷ rw 5 ms1m-5260 ∷ rw 0 ms1m-3395 ∷ []) refl

  ms1m-5336 : Eqn
  ms1m-5336 = derive (cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-33 ∷ rw⁻ 6 ms1m-5260 ∷ rw 0 ms1m-2369 ∷
       rw 4 ms1m-26 ∷ []) refl

  ms1m-5342 : Eqn
  ms1m-5342 = derive (s₁ ∷ k₁ ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-132 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 4 ms1m-52 ∷ rw⁻ 5 ms1m-59 ∷ rw⁻ 3 ms1m-52 ∷ rw⁻ 4 ms1m-59 ∷
       rw⁻ 5 ms1m-132 ∷ rw⁻ 6 ms1m-129 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-2329 ∷ rw⁻ 0 ms1m-2406 ∷
       rw 5 ms1m-5260 ∷ rw 4 ms1m-33 ∷ rw 3 ms1m-60 ∷ rw 0 ms1m-24 ∷ []) refl

  ms1m-5345 : Eqn
  ms1m-5345 = derive (ι ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-3385 ∷ rw 6 ms1m-5260 ∷ rw 5 ms1m-17 ∷ []) refl

  ms1m-5360 : Eqn
  ms1m-5360 = derive (s₁ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-5272 ∷ []) refl

  ms1m-5361 : Eqn
  ms1m-5361 = derive (s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-5260 ∷ rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-5272 ∷ []) refl

  ms1m-5362 : Eqn
  ms1m-5362 = derive (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 7 ms1m-18 ∷ rw 0 ms1m-5272 ∷ []) refl

  ms1m-5389 : Eqn
  ms1m-5389 = derive (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-102 ∷ rw⁻ 7 ms1m-1322 ∷ rw 0 ms1m-5272 ∷ rw 4 ms1m-52 ∷ []) refl

  ms1m-5393 : Eqn
  ms1m-5393 = derive (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 5 ms1m-52 ∷ rw⁻ 0 ms1m-5361 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷
       rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-3395 ∷ rw 0 ms1m-5272 ∷ rw 4 ms1m-52 ∷ []) refl

  ms1m-5401 : Eqn
  ms1m-5401 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 3 ms1m-5273 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-5410 : Eqn
  ms1m-5410 = derive (k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-187 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 4 ms1m-18 ∷
       rw⁻ 0 ms1m-5273 ∷ rw 7 ms1m-187 ∷ rw 6 ms1m-18 ∷ rw 5 ms1m-18 ∷ rw 0 ms1m-2582 ∷ rw 3 ms1m-542 ∷
       rw 1 ms1m-250 ∷ rw 0 ms1m-113 ∷ rw 5 ms1m-18 ∷ rw 4 ms1m-18 ∷ rw 1 ms1m-190 ∷ rw 0 ms1m-18 ∷
       rw 1 ms1m-18 ∷ rw 2 ms1m-18 ∷ []) refl

  ms1m-5449 : Eqn
  ms1m-5449 = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 5 ms1m-5273 ∷ rw 0 ms1m-3395 ∷ rw 0 ms1m-3399 ∷ rw 1 ms1m-3385 ∷ rw 0 ms1m-57 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-5458 : Eqn
  ms1m-5458 = derive (s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-5260 ∷ rw 0 ms1m-5273 ∷ []) refl

  ms1m-5461 : Eqn
  ms1m-5461 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 6 ms1m-18 ∷ rw 0 ms1m-5276 ∷ []) refl

  ms1m-5492 : Eqn
  ms1m-5492 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-1449 ∷ rw 7 ms1m-5276 ∷ rw 6 ms1m-17 ∷ rw 0 ms1m-3517 ∷ []) refl

  ms1m-5511 : Eqn
  ms1m-5511 = derive (s₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-3517 ∷ rw 7 ms1m-5276 ∷ rw 0 ms1m-3728 ∷ []) refl

  ms1m-5522 : Eqn
  ms1m-5522 = derive (cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 6 ms1m-13 ∷ rw 0 ms1m-5336 ∷ []) refl

  ms1m-5599 : Eqn
  ms1m-5599 = derive (s₁ ∷ s₁ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-5361 ∷ []) refl

  ms1m-5637 : Eqn
  ms1m-5637 = derive (s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-3728 ∷ rw 6 ms1m-5361 ∷ rw 0 ms1m-1449 ∷ []) refl

  ms1m-5640 : Eqn
  ms1m-5640 = derive (s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 7 ms1m-13 ∷ rw 0 ms1m-5458 ∷ []) refl

  ms1m-5770 : Eqn
  ms1m-5770 = derive (k₀ ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 4 ms1m-18 ∷ rw⁻ 0 ms1m-113 ∷ rw⁻ 2 ms1m-52 ∷ rw⁻ 1 ms1m-52 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 4 ms1m-52 ∷
       rw⁻ 5 ms1m-59 ∷ rw⁻ 3 ms1m-52 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-132 ∷ rw⁻ 6 ms1m-129 ∷ rw⁻ 0 ms1m-4904 ∷
       rw⁻ 1 ms1m-18 ∷ rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-2652 ∷ rw 0 ms1m-18 ∷ rw 1 ms1m-18 ∷ []) refl

  ms1m-5845 : Eqn
  ms1m-5845 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₁ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 3 ms1m-129 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 0 ms1m-60 ∷ rw⁻ 1 ms1m-3242 ∷ rw⁻ 0 ms1m-851 ∷
       rw 7 ms1m-5770 ∷ rw 4 ms1m-187 ∷ rw 3 ms1m-18 ∷ rw 2 ms1m-18 ∷ rw 5 ms1m-190 ∷ rw 4 ms1m-18 ∷
       rw 3 ms1m-18 ∷ rw 5 ms1m-18 ∷ rw 4 ms1m-18 ∷ rw 6 ms1m-18 ∷ rw 5 ms1m-18 ∷ rw 2 ms1m-25 ∷
       rw 0 ms1m-5458 ∷ []) refl

  ms1m-5868 : Eqn
  ms1m-5868 = derive (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-2653 ∷ rw 2 ms1m-33 ∷ rw 1 ms1m-33 ∷ rw 0 ms1m-33 ∷ rw 0 ms1m-2247 ∷
       rw 7 ms1m-129 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-59 ∷ rw 4 ms1m-52 ∷ rw 7 ms1m-59 ∷ rw 6 ms1m-59 ∷
       rw 5 ms1m-52 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-52 ∷ rw 1 ms1m-59 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷
       rw 0 ms1m-113 ∷ rw 3 ms1m-187 ∷ rw 2 ms1m-18 ∷ []) refl

  ms1m-6396 : Eqn
  ms1m-6396 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 ms1m-52 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-3490 ∷ rw 0 ms1m-52 ∷ []) refl

  ms1m-6423 : Eqn
  ms1m-6423 = derive (k₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-3491 ∷ rw 0 ms1m-12 ∷ rw 1 ms1m-59 ∷ rw 1 ms1m-1449 ∷ []) refl

  ms1m-6512 : Eqn
  ms1m-6512 = derive (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 4 ms1m-59 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 0 ms1m-9 ∷ rw 1 ms1m-3776 ∷ []) refl

  ms1m-6513 : Eqn
  ms1m-6513 = derive (s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-164 ∷
       rw⁻ 0 ms1m-6512 ∷ rw 0 ms1m-4762 ∷ []) refl

  ms1m-6515 : Eqn
  ms1m-6515 = derive (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-17 ∷ rw⁻ 0 ms1m-6513 ∷ rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷
       rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-164 ∷ rw⁻ 0 ms1m-6512 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-149 ∷
       rw 0 ms1m-3776 ∷ rw 4 ms1m-164 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-33 ∷ rw 0 ms1m-33 ∷
       rw 5 ms1m-152 ∷ rw 4 ms1m-17 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-33 ∷ rw 1 ms1m-33 ∷ rw 5 ms1m-17 ∷
       rw 4 ms1m-17 ∷ rw 3 ms1m-33 ∷ rw 2 ms1m-33 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-17 ∷ rw 4 ms1m-33 ∷
       rw 3 ms1m-33 ∷ rw 0 ms1m-24 ∷ rw 3 ms1m-102 ∷ rw 2 ms1m-18 ∷ []) refl

  ms1m-6547 : Eqn
  ms1m-6547 = derive (cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-1 ∷ rw 3 ms1m-3955 ∷ rw 1 ms1m-982 ∷ rw 0 ms1m-31 ∷ rw 3 ms1m-174 ∷ rw 0 ms1m-104 ∷
       rw 3 ms1m-164 ∷ rw 2 ms1m-17 ∷ []) refl

  ms1m-6639 : Eqn
  ms1m-6639 = derive (ι ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-3385 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 0 ms1m-4755 ∷ rw 8 ms1m-1 ∷ []) refl

  ms1m-6678 : Eqn
  ms1m-6678 = derive (s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-33 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-164 ∷ rw 0 ms1m-4756 ∷
       rw 5 ms1m-17 ∷ rw 4 ms1m-17 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-17 ∷ []) refl

  ms1m-6827 : Eqn
  ms1m-6827 = derive (s₁ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (ι ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-57 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-11 ∷
       rw⁻ 5 ms1m-58 ∷ rw⁻ 6 ms1m-32 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-11 ∷ rw 0 ms1m-5342 ∷ rw 5 ms1m-58 ∷
       rw 4 ms1m-11 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-58 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-58 ∷ []) refl

  ms1m-6880 : Eqn
  ms1m-6880 = derive (k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 6 ms1m-60 ∷ rw⁻ 5 ms1m-52 ∷ rw⁻ 0 ms1m-5342 ∷ rw 6 ms1m-3385 ∷ rw 5 ms1m-58 ∷ rw 4 ms1m-11 ∷
       rw 3 ms1m-11 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-31 ∷ rw 0 ms1m-104 ∷ rw 3 ms1m-52 ∷
       rw 4 ms1m-60 ∷ rw 5 ms1m-52 ∷ []) refl

  ms1m-6893 : Eqn
  ms1m-6893 = derive (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-6827 ∷ rw 0 ms1m-58 ∷ rw 1 ms1m-129 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-6897 : Eqn
  ms1m-6897 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-5362 ∷ rw 0 ms1m-6893 ∷ []) refl

  ms1m-6919 : Eqn
  ms1m-6919 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-5389 ∷ rw 0 ms1m-6893 ∷ rw 4 ms1m-52 ∷ []) refl

  ms1m-6920 : Eqn
  ms1m-6920 = derive (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-6897 ∷ rw 0 ms1m-5276 ∷ []) refl

  ms1m-6922 : Eqn
  ms1m-6922 = derive (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw⁻ 0 ms1m-6897 ∷ rw 0 ms1m-5461 ∷ []) refl

  ms1m-6929 : Eqn
  ms1m-6929 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-5393 ∷ rw 1 ms1m-6919 ∷ rw 0 ms1m-18 ∷ []) refl

  ms1m-6932 : Eqn
  ms1m-6932 = derive (s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-6920 ∷ rw 0 ms1m-5360 ∷ []) refl

  ms1m-6933 : Eqn
  ms1m-6933 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 2 ms1m-6920 ∷ rw 0 ms1m-5599 ∷ []) refl

  ms1m-7002 : Eqn
  ms1m-7002 = derive (s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-5260 ∷ rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷
       rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-6897 ∷ rw 0 ms1m-16 ∷ []) refl

  ms1m-7037 : Eqn
  ms1m-7037 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-1449 ∷ rw 7 ms1m-6897 ∷ rw 6 ms1m-18 ∷ rw 4 ms1m-102 ∷ rw 3 ms1m-18 ∷ rw 0 ms1m-1454 ∷
       rw 2 ms1m-5449 ∷ rw 1 ms1m-17 ∷ rw 0 ms1m-17 ∷ []) refl

  ms1m-7038 : Eqn
  ms1m-7038 = derive (s₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-5492 ∷ rw 0 ms1m-7037 ∷ rw 2 ms1m-5449 ∷ rw 1 ms1m-17 ∷ []) refl

  ms1m-7039 : Eqn
  ms1m-7039 = derive (s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-5511 ∷ rw 0 ms1m-7038 ∷ rw 2 ms1m-5449 ∷ []) refl

  ms1m-7043 : Eqn
  ms1m-7043 = derive (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-6922 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 0 ms1m-6897 ∷ rw 5 ms1m-1489 ∷ rw 4 ms1m-52 ∷ rw 0 ms1m-6919 ∷ []) refl

  ms1m-7072 : Eqn
  ms1m-7072 = derive (s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-5260 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-6897 ∷ rw 0 ms1m-5458 ∷ rw 5 ms1m-18 ∷
       rw 4 ms1m-18 ∷ []) refl

  ms1m-7075 : Eqn
  ms1m-7075 = derive (s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-6922 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-6893 ∷ []) refl

  ms1m-7102 : Eqn
  ms1m-7102 = derive (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 6 ms1m-142 ∷ rw⁻ 7 ms1m-1817 ∷ rw 0 ms1m-6893 ∷ []) refl

  ms1m-7104 : Eqn
  ms1m-7104 = derive (k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₁ ∷ k₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-132 ∷ rw⁻ 3 ms1m-52 ∷
       rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-132 ∷ rw⁻ 4 ms1m-132 ∷ rw⁻ 5 ms1m-129 ∷ rw⁻ 0 ms1m-6932 ∷ rw⁻ 1 ms1m-60 ∷
       rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-33 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-2329 ∷
       rw 0 ms1m-6893 ∷ rw 4 ms1m-129 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-52 ∷ rw 0 ms1m-59 ∷
       rw 2 ms1m-52 ∷ rw 1 ms1m-59 ∷ rw 5 ms1m-18 ∷ rw 4 ms1m-18 ∷ []) refl

  ms1m-7113 : Eqn
  ms1m-7113 = derive (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 4 ms1m-52 ∷ rw⁻ 0 ms1m-6893 ∷ rw 7 ms1m-3395 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-60 ∷
       rw 3 ms1m-17 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-60 ∷ rw 0 ms1m-6932 ∷ rw 5 ms1m-52 ∷ rw 1 ms1m-6919 ∷ []) refl

  ms1m-7159 : Eqn
  ms1m-7159 = derive (s₁ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-7002 ∷ []) refl

  ms1m-7164 : Eqn
  ms1m-7164 = derive (s₁ ∷ k₁ ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 2 ms1m-59 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 3 ms1m-132 ∷ rw⁻ 5 ms1m-52 ∷ rw⁻ 4 ms1m-52 ∷
       rw⁻ 5 ms1m-132 ∷ rw⁻ 6 ms1m-132 ∷ rw⁻ 7 ms1m-129 ∷ rw 0 ms1m-7002 ∷ []) refl

  ms1m-7203 : Eqn
  ms1m-7203 = derive (s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-5260 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-6897 ∷ rw 0 ms1m-7002 ∷ []) refl

  ms1m-7243 : Eqn
  ms1m-7243 = derive (k₁ ∷ k₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 9 ms1m-18 ∷ rw⁻ 0 ms1m-7104 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 0 ms1m-59 ∷
       rw⁻ 1 ms1m-132 ∷ rw⁻ 3 ms1m-52 ∷ rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-132 ∷ rw⁻ 4 ms1m-132 ∷ rw⁻ 5 ms1m-129 ∷
       rw⁻ 0 ms1m-6932 ∷ rw 5 ms1m-2417 ∷ rw 4 ms1m-17 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-60 ∷ rw 4 ms1m-26 ∷ []) refl

  ms1m-7248 : Eqn
  ms1m-7248 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-7039 ∷ rw⁻ 0 ms1m-3728 ∷ rw 6 ms1m-6932 ∷ rw 4 ms1m-102 ∷ rw 3 ms1m-18 ∷ rw 0 ms1m-1454 ∷ []) refl

  ms1m-7400 : Eqn
  ms1m-7400 = derive (s₁ ∷ s₁ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-7075 ∷ []) refl

  ms1m-7401 : Eqn
  ms1m-7401 = derive (s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (rw⁻ 5 ms1m-52 ∷ rw⁻ 6 ms1m-59 ∷ rw⁻ 7 ms1m-14 ∷ rw 0 ms1m-7075 ∷ rw 5 ms1m-52 ∷ []) refl

  ms1m-7514 : Eqn
  ms1m-7514 = derive (s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ [])
    (rw⁻ 7 ms1m-13 ∷ rw 0 ms1m-7203 ∷ rw 5 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 3 ms1m-52 ∷ []) refl

  ms1m-7610 : Eqn
  ms1m-7610 = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (s₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-7072 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-5401 ∷ []) refl

  ms1m-7726 : Eqn
  ms1m-7726 = derive (ι ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-6423 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-7780 : Eqn
  ms1m-7780 = derive (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-6515 ∷ rw 7 ms1m-16 ∷ []) refl

  ms1m-7781 : Eqn
  ms1m-7781 = derive (ι ∷ k₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw 0 ms1m-4659 ∷ rw 0 ms1m-7780 ∷ []) refl

  ms1m-7896 : Eqn
  ms1m-7896 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 6 ms1m-52 ∷ rw⁻ 5 ms1m-60 ∷ rw⁻ 4 ms1m-52 ∷ rw⁻ 0 ms1m-25 ∷ rw⁻ 1 ms1m-5410 ∷ rw⁻ 2 ms1m-18 ∷
       rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-187 ∷ rw⁻ 7 ms1m-150 ∷ rw⁻ 6 ms1m-150 ∷ rw⁻ 7 ms1m-4810 ∷ rw 0 ms1m-6922 ∷
       rw 0 ms1m-7102 ∷ rw 9 ms1m-26 ∷ []) refl

  ms1m-7903 : Eqn
  ms1m-7903 = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 0 ms1m-7072 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-12 ∷
       rw 1 ms1m-6933 ∷ []) refl

  ms1m-7905 : Eqn
  ms1m-7905 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (rw⁻ 6 ms1m-52 ∷ rw⁻ 7 ms1m-14 ∷ rw 0 ms1m-6933 ∷ rw 6 ms1m-52 ∷ []) refl

  ms1m-7933 : Eqn
  ms1m-7933 = derive (s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-1600 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-102 ∷
       rw⁻ 7 ms1m-6933 ∷ rw 0 ms1m-4731 ∷ rw 4 ms1m-17 ∷ rw 3 ms1m-17 ∷ rw 5 ms1m-17 ∷ rw 4 ms1m-17 ∷
       rw 3 ms1m-5458 ∷ rw 8 ms1m-18 ∷ rw 7 ms1m-18 ∷ []) refl

  ms1m-7980 : Eqn
  ms1m-7980 = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 1 ms1m-25 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-102 ∷ rw⁻ 7 ms1m-7159 ∷ rw 0 ms1m-6423 ∷ rw 5 ms1m-102 ∷
       rw 4 ms1m-18 ∷ rw 2 ms1m-102 ∷ rw 1 ms1m-18 ∷ rw 0 ms1m-1872 ∷ rw 3 ms1m-144 ∷ rw 2 ms1m-132 ∷
       rw 0 ms1m-113 ∷ rw 2 ms1m-142 ∷ rw 1 ms1m-18 ∷ rw 1 ms1m-3385 ∷ rw 0 ms1m-57 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-8038 : Eqn
  ms1m-8038 = derive (s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-57 ∷ rw⁻ 3 ms1m-32 ∷ rw⁻ 4 ms1m-11 ∷
       rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-11 ∷ rw 0 ms1m-7164 ∷ rw 5 ms1m-58 ∷
       rw 4 ms1m-32 ∷ rw 3 ms1m-58 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-58 ∷ []) refl

  ms1m-8081 : Eqn
  ms1m-8081 = derive (s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-8038 ∷ rw 0 ms1m-58 ∷ rw 1 ms1m-129 ∷ rw 0 ms1m-113 ∷ []) refl

  ms1m-8113 : Eqn
  ms1m-8113 = derive (cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-8081 ∷ rw 6 ms1m-16 ∷ []) refl

  ms1m-8166 : Eqn
  ms1m-8166 = derive (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷
       rw⁻ 2 ms1m-190 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw 0 ms1m-8113 ∷ []) refl

  ms1m-8358 : Eqn
  ms1m-8358 = derive (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-187 ∷ rw 1 ms1m-7780 ∷ rw 0 ms1m-60 ∷ rw 1 ms1m-52 ∷ rw 2 ms1m-60 ∷ []) refl

  ms1m-8395 : Eqn
  ms1m-8395 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-152 ∷ rw⁻ 1 ms1m-7780 ∷ rw 0 ms1m-1454 ∷ rw 2 ms1m-1322 ∷ rw 1 ms1m-102 ∷ rw 0 ms1m-18 ∷ []) refl

  ms1m-8400 : Eqn
  ms1m-8400 = derive (k₀ ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-33 ∷ rw⁻ 5 ms1m-33 ∷ rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷
       rw⁻ 0 ms1m-113 ∷ rw⁻ 2 ms1m-52 ∷ rw⁻ 1 ms1m-52 ∷ rw⁻ 2 ms1m-132 ∷ rw⁻ 4 ms1m-52 ∷ rw⁻ 5 ms1m-59 ∷
       rw⁻ 6 ms1m-59 ∷ rw⁻ 3 ms1m-52 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-59 ∷ rw⁻ 6 ms1m-129 ∷ rw⁻ 0 ms1m-2212 ∷
       rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-17 ∷
       rw⁻ 6 ms1m-60 ∷ rw⁻ 7 ms1m-7780 ∷ rw 0 ms1m-3242 ∷ rw 0 ms1m-3130 ∷ []) refl

  ms1m-8407 : Eqn
  ms1m-8407 = derive (k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 4 ms1m-60 ∷ rw⁻ 3 ms1m-52 ∷ rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-17 ∷
       rw⁻ 6 ms1m-60 ∷ rw⁻ 7 ms1m-7780 ∷ rw 0 ms1m-6933 ∷ rw 2 ms1m-6897 ∷ rw 1 ms1m-18 ∷ rw 2 ms1m-5260 ∷
       rw 1 ms1m-33 ∷ rw 0 ms1m-33 ∷ rw 2 ms1m-6922 ∷ rw 1 ms1m-33 ∷ rw 0 ms1m-7400 ∷ rw 6 ms1m-52 ∷ []) refl

  ms1m-8640 : Eqn
  ms1m-8640 = derive (s₁ ∷ s₀ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-8166 ∷ rw 0 ms1m-4 ∷ []) refl

  ms1m-8641 : Eqn
  ms1m-8641 = derive (s₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-8166 ∷ rw 0 ms1m-4 ∷ []) refl

  ms1m-8652 : Eqn
  ms1m-8652 = derive (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 2 ms1m-102 ∷ rw⁻ 1 ms1m-102 ∷ rw⁻ 0 ms1m-102 ∷ rw 2 ms1m-8166 ∷ []) refl

  ms1m-8680 : Eqn
  ms1m-8680 = derive (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 3 ms1m-8641 ∷ rw 0 ms1m-1 ∷ []) refl

  ms1m-8681 : Eqn
  ms1m-8681 = derive (s₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ [])
    (cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 6 ms1m-52 ∷ rw⁻ 7 ms1m-14 ∷ rw 0 ms1m-8641 ∷ []) refl

  ms1m-8685 : Eqn
  ms1m-8685 = derive (s₁ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-18 ∷ rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-8641 ∷ []) refl

  ms1m-8728 : Eqn
  ms1m-8728 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 3 ms1m-52 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-8395 ∷ []) refl

  ms1m-8891 : Eqn
  ms1m-8891 = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-25 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-102 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-102 ∷ rw⁻ 0 ms1m-3616 ∷
       rw 7 ms1m-8640 ∷ rw 4 ms1m-142 ∷ rw 3 ms1m-18 ∷ rw 3 ms1m-3385 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-31 ∷
       rw 0 ms1m-31 ∷ rw 0 ms1m-140 ∷ []) refl

  ms1m-8949 : Eqn
  ms1m-8949 = derive (s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-8680 ∷ rw 1 ms1m-5458 ∷ []) refl

  ms1m-9006 : Eqn
  ms1m-9006 = derive (s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-33 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-17 ∷
       rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-33 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 1 ms1m-33 ∷
       rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-152 ∷ rw⁻ 9 ms1m-60 ∷
       rw⁻ 8 ms1m-52 ∷ rw⁻ 7 ms1m-60 ∷ rw⁻ 8 ms1m-7780 ∷ rw 0 ms1m-8681 ∷ rw 4 ms1m-102 ∷ rw 3 ms1m-18 ∷
       rw 5 ms1m-102 ∷ rw 4 ms1m-18 ∷ rw 3 ms1m-1489 ∷ rw 2 ms1m-52 ∷ rw 7 ms1m-26 ∷ []) refl

  ms1m-9033 : Eqn
  ms1m-9033 = derive (s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-2333 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-33 ∷
       rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-2329 ∷ rw 0 ms1m-8685 ∷ []) refl

  ms1m-9157 : Eqn
  ms1m-9157 = derive (s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ k₀ ∷ [])
    (s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 5 ms1m-52 ∷ rw⁻ 6 ms1m-59 ∷ rw⁻ 7 ms1m-13 ∷ rw 0 ms1m-8949 ∷ []) refl

  ms1m-9646 : Eqn
  ms1m-9646 = derive (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-7781 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-102 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 1 ms1m-24 ∷ rw⁻ 4 ms1m-3395 ∷
       rw⁻ 1 ms1m-1826 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-164 ∷ rw⁻ 7 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷
       rw⁻ 7 ms1m-259 ∷ rw 0 ms1m-1743 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-17 ∷ rw 7 ms1m-18 ∷ rw 6 ms1m-18 ∷
       rw 3 ms1m-142 ∷ rw 4 ms1m-3565 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-59 ∷ rw 1 ms1m-59 ∷ rw 4 ms1m-33 ∷
       rw 3 ms1m-33 ∷ rw 2 ms1m-33 ∷ rw 10 ms1m-17 ∷ rw 5 ms1m-3803 ∷ rw 4 ms1m-32 ∷ rw 3 ms1m-32 ∷
       rw 2 ms1m-31 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-31 ∷ rw 5 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 6 ms1m-33 ∷
       rw 5 ms1m-33 ∷ rw 2 ms1m-152 ∷ rw 1 ms1m-24 ∷ rw 6 ms1m-132 ∷ rw 4 ms1m-132 ∷ rw 3 ms1m-59 ∷
       rw 2 ms1m-59 ∷ rw 0 ms1m-113 ∷ rw 1 ms1m-59 ∷ rw 0 ms1m-59 ∷ []) refl

  ms1m-12502 : Eqn
  ms1m-12502 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-1 ∷ rw 3 ms1m-2725 ∷ rw 0 ms1m-24 ∷ []) refl

  ms1m-12504 : Eqn
  ms1m-12504 = derive (cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 5 ms1m-52 ∷ rw⁻ 6 ms1m-14 ∷ rw 0 ms1m-12502 ∷ []) refl

  ms1m-12842 : Eqn
  ms1m-12842 = derive (s₁ ∷ s₁ ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 1 ms1m-17 ∷ rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-3617 ∷ []) refl

  ms1m-12989 : Eqn
  ms1m-12989 = derive (s₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (k₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 2 ms1m-52 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-3730 ∷ rw 0 ms1m-52 ∷ rw 1 ms1m-187 ∷ []) refl

  ms1m-14457 : Eqn
  ms1m-14457 = derive (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-6929 ∷ rw⁻ 6 ms1m-52 ∷ rw⁻ 0 ms1m-6933 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-17 ∷
       rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷ rw⁻ 6 ms1m-33 ∷ rw⁻ 0 ms1m-140 ∷ rw⁻ 4 ms1m-52 ∷ rw⁻ 3 ms1m-52 ∷
       rw⁻ 4 ms1m-132 ∷ rw⁻ 5 ms1m-132 ∷ rw⁻ 7 ms1m-52 ∷ rw⁻ 8 ms1m-59 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷
       rw⁻ 2 ms1m-58 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 5 ms1m-57 ∷ rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-32 ∷
       rw⁻ 8 ms1m-3508 ∷ rw 0 ms1m-7401 ∷ rw 1 ms1m-7113 ∷ rw 2 ms1m-7113 ∷ rw 0 ms1m-25 ∷ []) refl

  ms1m-14607 : Eqn
  ms1m-14607 = derive (k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 ms1m-25 ∷ rw⁻ 1 ms1m-190 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-102 ∷ rw⁻ 0 ms1m-187 ∷ rw⁻ 3 ms1m-18 ∷
       rw⁻ 4 ms1m-102 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-102 ∷ rw⁻ 5 ms1m-190 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-102 ∷
       rw⁻ 4 ms1m-187 ∷ rw⁻ 0 ms1m-7514 ∷ rw 7 ms1m-3632 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-17 ∷ rw 4 ms1m-60 ∷
       rw 3 ms1m-33 ∷ rw 2 ms1m-33 ∷ rw 1 ms1m-7203 ∷ rw 0 ms1m-7043 ∷ []) refl

  ms1m-14734 : Eqn
  ms1m-14734 = derive (ι ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 2 ms1m-60 ∷ rw⁻ 1 ms1m-52 ∷ rw⁻ 0 ms1m-10 ∷ rw 1 ms1m-7726 ∷ rw 0 ms1m-187 ∷ []) refl

  ms1m-14909 : Eqn
  ms1m-14909 = derive (k₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-59 ∷ rw⁻ 1 ms1m-9646 ∷ rw 0 ms1m-12 ∷ rw 1 ms1m-59 ∷ rw 2 ms1m-33 ∷ rw 0 ms1m-4731 ∷ []) refl

  ms1m-15181 : Eqn
  ms1m-15181 = derive (s₀ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 5 ms1m-52 ∷ rw⁻ 6 ms1m-1322 ∷ rw⁻ 0 ms1m-12504 ∷ rw 7 ms1m-1453 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-57 ∷
       rw 4 ms1m-11 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-58 ∷ rw 0 ms1m-11 ∷ rw 7 ms1m-52 ∷
       rw 5 ms1m-132 ∷ rw 4 ms1m-132 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-52 ∷ rw 3 ms1m-52 ∷ rw 1 ms1m-132 ∷
       rw 0 ms1m-113 ∷ []) refl

  ms1m-18905 : Eqn
  ms1m-18905 = derive (s₀ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 ms1m-15181 ∷ rw⁻ 0 ms1m-3244 ∷ rw 7 ms1m-7780 ∷ rw 6 ms1m-60 ∷ rw 7 ms1m-52 ∷ rw 8 ms1m-60 ∷
       rw 5 ms1m-152 ∷ rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 0 ms1m-24 ∷ rw 1 ms1m-17 ∷ rw 0 ms1m-60 ∷
       rw 2 ms1m-17 ∷ rw 1 ms1m-60 ∷ []) refl

  ms1m-21321 : Eqn
  ms1m-21321 = derive (s₁ ∷ k₁ ∷ k₁ ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (rw⁻ 1 ms1m-132 ∷ rw⁻ 0 ms1m-17 ∷ rw 1 ms1m-4669 ∷ []) refl

  ms1m-23102 : Eqn
  ms1m-23102 = derive (ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ [])
    (s₁ ∷ s₁ ∷ s₁ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-58 ∷ rw⁻ 1 ms1m-11 ∷ rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-58 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 5 ms1m-11 ∷
       rw⁻ 6 ms1m-11 ∷ rw⁻ 7 ms1m-58 ∷ rw⁻ 0 ms1m-5845 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷
       rw 5 ms1m-11 ∷ rw 4 ms1m-57 ∷ rw 3 ms1m-57 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷
       rw 0 ms1m-145 ∷ []) refl

  ms1m-23129 : Eqn
  ms1m-23129 = derive (s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-187 ∷ rw⁻ 7 ms1m-18 ∷ rw⁻ 8 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 7 ms1m-18 ∷
       rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 0 ms1m-23102 ∷ rw 8 ms1m-187 ∷ rw 7 ms1m-18 ∷ rw 6 ms1m-18 ∷
       rw 5 ms1m-18 ∷ rw 1 ms1m-7610 ∷ rw 8 ms1m-129 ∷ rw 7 ms1m-132 ∷ rw 6 ms1m-132 ∷ rw 5 ms1m-52 ∷
       rw 6 ms1m-52 ∷ rw 4 ms1m-132 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-59 ∷ rw 2 ms1m-59 ∷
       rw 0 ms1m-113 ∷ rw 6 ms1m-18 ∷ rw 5 ms1m-18 ∷ []) refl

  ms1m-23886 : Eqn
  ms1m-23886 = derive (s₁ ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-162 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-163 ∷ rw⁻ 0 ms1m-223 ∷ rw 6 ms1m-6396 ∷ rw 1 ms1m-146 ∷ []) refl

  ms1m-23887 : Eqn
  ms1m-23887 = derive (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-23886 ∷ rw 0 ms1m-6678 ∷ []) refl

  ms1m-24397 : Eqn
  ms1m-24397 = derive (s₁ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-104 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-1600 ∷ rw⁻ 0 ms1m-6639 ∷ rw 7 ms1m-5640 ∷
       rw 0 ms1m-5345 ∷ rw 6 ms1m-5260 ∷ rw 3 ms1m-164 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-17 ∷ rw 0 ms1m-33 ∷
       rw 0 ms1m-7933 ∷ []) refl

  ms1m-25314 : Eqn
  ms1m-25314 = derive (k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 3 ms1m-52 ∷ rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-60 ∷
       rw⁻ 0 ms1m-145 ∷ rw⁻ 5 ms1m-52 ∷ rw⁻ 4 ms1m-52 ∷ rw⁻ 5 ms1m-132 ∷ rw⁻ 6 ms1m-132 ∷ rw⁻ 8 ms1m-52 ∷
       rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-58 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 5 ms1m-11 ∷
       rw⁻ 6 ms1m-57 ∷ rw⁻ 7 ms1m-58 ∷ rw⁻ 8 ms1m-3508 ∷ rw 0 ms1m-7905 ∷ rw 2 ms1m-6929 ∷ rw 1 ms1m-18 ∷
       rw 0 ms1m-14457 ∷ rw 9 ms1m-17 ∷ rw 8 ms1m-17 ∷ rw 0 ms1m-14607 ∷ rw 9 ms1m-26 ∷ []) refl

  ms1m-25658 : Eqn
  ms1m-25658 = derive (s₀ ∷ cs ∷ k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 ms1m-18 ∷ rw 1 ms1m-8358 ∷ rw 0 ms1m-17 ∷ []) refl

  ms1m-26326 : Eqn
  ms1m-26326 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-102 ∷ rw⁻ 8 ms1m-6893 ∷ rw 0 ms1m-8728 ∷ rw 4 ms1m-7980 ∷ rw 3 ms1m-17 ∷
       rw 2 ms1m-17 ∷ rw 1 ms1m-33 ∷ rw 0 ms1m-60 ∷ rw 0 ms1m-1938 ∷ rw 4 ms1m-144 ∷ rw 3 ms1m-132 ∷
       rw 2 ms1m-52 ∷ rw 0 ms1m-113 ∷ rw 0 ms1m-52 ∷ []) refl

  ms1m-32453 : Eqn
  ms1m-32453 = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (rw⁻ 7 ms1m-52 ∷ rw⁻ 8 ms1m-14 ∷ rw 0 ms1m-7980 ∷ rw 8 ms1m-52 ∷ []) refl

  ms1m-32486 : Eqn
  ms1m-32486 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 9 ms1m-52 ∷ rw⁻ 0 ms1m-5637 ∷ rw⁻ 1 ms1m-7980 ∷ rw⁻ 0 ms1m-7980 ∷ rw 8 ms1m-1489 ∷ rw 7 ms1m-52 ∷ []) refl

  ms1m-32490 : Eqn
  ms1m-32490 = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-32486 ∷ rw⁻ 10 ms1m-52 ∷ rw⁻ 0 ms1m-7248 ∷ rw⁻ 2 ms1m-7980 ∷ rw⁻ 1 ms1m-7980 ∷ rw⁻ 0 ms1m-7980 ∷
       rw 8 ms1m-1734 ∷ rw 7 ms1m-52 ∷ []) refl

  ms1m-33019 : Eqn
  ms1m-33019 = derive (k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 0 ms1m-4 ∷ rw 3 ms1m-9006 ∷ []) refl

  ms1m-37510 : Eqn
  ms1m-37510 = derive (s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₀ ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 1 ms1m-60 ∷ rw⁻ 0 ms1m-15 ∷ rw 1 ms1m-12842 ∷ []) refl

  ms1m-37683 : Eqn
  ms1m-37683 = derive (cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (rw⁻ 7 ms1m-17 ∷ rw⁻ 8 ms1m-17 ∷ rw⁻ 3 ms1m-4756 ∷ rw⁻ 0 ms1m-210 ∷ rw 6 ms1m-12989 ∷ rw 4 ms1m-132 ∷
       rw 0 ms1m-145 ∷ rw 3 ms1m-18 ∷ rw 0 ms1m-23129 ∷ rw 8 ms1m-52 ∷ []) refl

  ms1m-39246 : Eqn
  ms1m-39246 = derive (s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 10 ms1m-52 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-102 ∷ rw⁻ 3 ms1m-7903 ∷
       rw⁻ 8 ms1m-18 ∷ rw⁻ 9 ms1m-102 ∷ rw⁻ 0 ms1m-24397 ∷ rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-6880 ∷ rw⁻ 0 ms1m-14734 ∷
       rw 6 ms1m-7980 ∷ rw 5 ms1m-17 ∷ rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 0 ms1m-23887 ∷ rw 4 ms1m-5458 ∷ []) refl

  ms1m-41432 : Eqn
  ms1m-41432 = derive (k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-142 ∷ rw 0 ms1m-25314 ∷ rw 7 ms1m-102 ∷ rw 6 ms1m-18 ∷ []) refl

  ms1m-45869 : Eqn
  ms1m-45869 = derive (s₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₁ ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-32453 ∷ rw⁻ 8 ms1m-52 ∷ rw⁻ 9 ms1m-3950 ∷ rw 0 ms1m-5449 ∷ []) refl

  ms1m-46768 : Eqn
  ms1m-46768 = derive (s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (ι ∷ s₁ ∷ s₁ ∷ s₁ ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-58 ∷ rw⁻ 4 ms1m-32 ∷
       rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-11 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-58 ∷ rw⁻ 9 ms1m-32 ∷ rw⁻ 10 ms1m-11 ∷
       rw 0 ms1m-7243 ∷ rw 7 ms1m-58 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-58 ∷ rw 4 ms1m-11 ∷ rw 3 ms1m-58 ∷
       rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ []) refl

  ms1m-47422 : Eqn
  ms1m-47422 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 ms1m-14909 ∷ rw 1 ms1m-8652 ∷ []) refl

  ms1m-53929 : Eqn
  ms1m-53929 = derive (cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₀ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 ms1m-21321 ∷ rw 0 ms1m-17 ∷ rw 1 ms1m-132 ∷ rw 0 ms1m-5342 ∷ rw 5 ms1m-52 ∷ []) refl

  ms1m-54139 : Eqn
  ms1m-54139 = derive (cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (rw⁻ 7 ms1m-4756 ∷ rw 0 ms1m-53929 ∷ rw 8 ms1m-17 ∷ rw 7 ms1m-17 ∷ rw 6 ms1m-60 ∷ rw 0 ms1m-6880 ∷
       rw 6 ms1m-41432 ∷ rw 2 ms1m-150 ∷ rw 1 ms1m-18 ∷ rw 0 ms1m-24397 ∷ rw 9 ms1m-102 ∷ rw 8 ms1m-18 ∷
       rw 3 ms1m-7903 ∷ rw 1 ms1m-102 ∷ rw 0 ms1m-18 ∷ rw 2 ms1m-102 ∷ rw 1 ms1m-18 ∷ rw 10 ms1m-52 ∷
       rw 0 ms1m-39246 ∷ rw 8 ms1m-26 ∷ rw 7 ms1m-52 ∷ []) refl

  ms1m-54141 : Eqn
  ms1m-54141 = derive (cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ [])
    (k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 2 ms1m-54139 ∷ rw 0 ms1m-32490 ∷ rw 1 ms1m-54139 ∷ []) refl

  ms1m-57153 : Eqn
  ms1m-57153 = derive (s₁ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-25658 ∷ rw 0 ms1m-18 ∷ rw 1 ms1m-8113 ∷ rw 0 ms1m-33 ∷ rw 6 ms1m-52 ∷ []) refl

  ms1m-63307 : Eqn
  ms1m-63307 = derive (k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-13 ∷ rw 1 ms1m-5316 ∷ rw 0 ms1m-60 ∷ rw 1 ms1m-52 ∷ []) refl

  ms1m-65162 : Eqn
  ms1m-65162 = derive (cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (s₁ ∷ k₁ ∷ s₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-113 ∷ rw 2 ms1m-8891 ∷ rw 1 ms1m-164 ∷ rw 0 ms1m-143 ∷ []) refl

  ms1m-65352 : Eqn
  ms1m-65352 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 3 ms1m-60 ∷ rw⁻ 2 ms1m-52 ∷ rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷
       rw⁻ 6 ms1m-65162 ∷ rw 0 ms1m-8680 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-52 ∷ rw 0 ms1m-9157 ∷ rw 6 ms1m-102 ∷
       rw 5 ms1m-18 ∷ rw 0 ms1m-6893 ∷ rw 4 ms1m-52 ∷ []) refl

  ms1m-72874 : Eqn
  ms1m-72874 = derive (cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-25 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-102 ∷ rw⁻ 6 ms1m-25314 ∷ rw⁻ 0 ms1m-33019 ∷ rw 5 ms1m-8407 ∷
       rw 3 ms1m-102 ∷ rw 2 ms1m-18 ∷ rw 4 ms1m-102 ∷ rw 3 ms1m-18 ∷ rw 0 ms1m-187 ∷ rw 5 ms1m-102 ∷
       rw 4 ms1m-18 ∷ rw 1 ms1m-190 ∷ rw 0 ms1m-25 ∷ []) refl

  ms1m-76221 : Eqn
  ms1m-76221 = derive (s₁ ∷ s₁ ∷ s₀ ∷ k₀ ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ [])
    (s₀ ∷ k₀ ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ [])
    (rw⁻ 1 ms1m-33 ∷ rw⁻ 0 ms1m-12 ∷ rw 1 ms1m-37510 ∷ []) refl

  ms1m-81531 : Eqn
  ms1m-81531 = derive (cs ∷ cs ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 3 ms1m-5522 ∷ rw⁻ 4 ms1m-53929 ∷ rw 0 ms1m-47422 ∷ rw 9 ms1m-59 ∷ rw 8 ms1m-52 ∷ rw 10 ms1m-33 ∷
       rw 9 ms1m-60 ∷ rw 11 ms1m-59 ∷ rw 10 ms1m-52 ∷ []) refl

  ms1m-83247 : Eqn
  ms1m-83247 = derive (cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-1 ∷ rw 3 ms1m-57153 ∷ rw 0 ms1m-24 ∷ []) refl

  ms1m-83437 : Eqn
  ms1m-83437 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 4 ms1m-25 ∷ rw⁻ 7 ms1m-83247 ∷ rw 0 ms1m-4811 ∷ rw 1 ms1m-3428 ∷ rw 0 ms1m-17 ∷ rw 1 ms1m-3395 ∷
       rw 6 ms1m-17 ∷ rw 1 ms1m-3401 ∷ rw 5 ms1m-164 ∷ rw 4 ms1m-17 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-33 ∷
       rw 0 ms1m-4731 ∷ []) refl

  ms1m-83438 : Eqn
  ms1m-83438 = derive (cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ [])
    (k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-83437 ∷ rw 0 ms1m-26326 ∷ []) refl

  ms1m-83508 : Eqn
  ms1m-83508 = derive (s₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 4 ms1m-83247 ∷ rw 0 ms1m-8395 ∷ []) refl

  ms1m-125136 : Eqn
  ms1m-125136 = derive (k₁ ∷ s₀ ∷ k₀ ∷ s₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ k₁ ∷ s₀ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 ms1m-14 ∷ rw 1 ms1m-63307 ∷ rw 0 ms1m-33 ∷ rw 1 ms1m-59 ∷ []) refl

  ms1m-128448 : Eqn
  ms1m-128448 = derive (k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ k₁ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 0 ms1m-54141 ∷ rw 3 ms1m-72874 ∷ rw 2 ms1m-129 ∷ rw 0 ms1m-132 ∷ []) refl

ax-m-IC : Eqn
ax-m-IC = derive (cs ∷ ι ∷ [])
  (ι ∷ cs ∷ [])
  (rw 0 ms1m-11 ∷ []) refl

ax-m-sC : Eqn
ax-m-sC = derive (cs ∷ s₀ ∷ [])
  (s₀ ∷ cs ∷ [])
  (rw 0 ms1m-18 ∷ []) refl

ax-m-tC : Eqn
ax-m-tC = derive (cs ∷ s₁ ∷ [])
  (s₁ ∷ cs ∷ [])
  (rw 0 ms1m-17 ∷ []) refl

ax-m-xC : Eqn
ax-m-xC = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ cs ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (cs ∷ cs ∷ cs ∷ s₁ ∷ [])
  (rw 3 ms1m-58 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-58 ∷ rw 2 ms1m-761 ∷ rw 1 ms1m-60 ∷
     rw 2 ms1m-129 ∷ rw 0 ms1m-104 ∷ rw 4 ms1m-129 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-132 ∷
     rw 5 ms1m-11 ∷ rw 4 ms1m-11 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-31 ∷
     rw 0 ms1m-104 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ []) refl

ax-m-yC : Eqn
ax-m-yC = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ cs ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (cs ∷ cs ∷ cs ∷ s₀ ∷ [])
  (rw 3 ms1m-57 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-57 ∷ rw 0 ms1m-1050 ∷ rw 3 ms1m-132 ∷
     rw 2 ms1m-132 ∷ rw 1 ms1m-132 ∷ rw 0 ms1m-59 ∷ rw 1 ms1m-59 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-11 ∷
     rw 3 ms1m-11 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-57 ∷ rw 0 ms1m-113 ∷ rw⁻ 0 ms1m-18 ∷
     rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ []) refl

ax-m-aC : Eqn
ax-m-aC = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (cs ∷ cs ∷ cs ∷ s₀ ∷ [])
  (rw 3 ms1m-57 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-57 ∷ rw 3 ms1m-507 ∷ rw 2 ms1m-1322 ∷
     rw 0 ms1m-113 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-132 ∷ rw 0 ms1m-59 ∷ rw 1 ms1m-59 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-11 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-57 ∷ rw 0 ms1m-113 ∷
     rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ []) refl

ax-m-bC : Eqn
ax-m-bC = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  (cs ∷ cs ∷ cs ∷ s₁ ∷ [])
  (rw 3 ms1m-58 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-58 ∷ rw 2 ms1m-2750 ∷ rw 1 ms1m-60 ∷
     rw 2 ms1m-129 ∷ rw 0 ms1m-104 ∷ rw 4 ms1m-129 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-132 ∷
     rw 5 ms1m-11 ∷ rw 4 ms1m-11 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-31 ∷
     rw 0 ms1m-104 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ []) refl

ax-p-13 : Eqn
ax-p-13 = derive (cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ cs ∷ cs ∷ [])
  (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ [])
  (rw 4 ms1m-18 ∷ rw 2 ms1m-102 ∷ rw 0 ms1m-102 ∷ rw 5 ms1m-18 ∷ rw 3 ms1m-102 ∷ rw 1 ms1m-102 ∷
     rw 6 ms1m-18 ∷ rw 4 ms1m-102 ∷ rw 2 ms1m-102 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-57 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-32 ∷ rw⁻ 0 ms1m-32 ∷
     rw⁻ 1 ms1m-32 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-57 ∷ rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-57 ∷
     rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-11 ∷ rw⁻ 9 ms1m-11 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 4 ms1m-102 ∷ rw⁻ 6 ms1m-18 ∷
     rw⁻ 7 ms1m-18 ∷ rw⁻ 8 ms1m-18 ∷ rw⁻ 1 ms1m-102 ∷ rw⁻ 3 ms1m-102 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷
     rw⁻ 7 ms1m-18 ∷ rw⁻ 0 ms1m-102 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷
     rw⁻ 0 ms1m-113 ∷ rw⁻ 2 ms1m-506 ∷ rw⁻ 3 ms1m-506 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-11 ∷ rw⁻ 2 ms1m-11 ∷
     rw⁻ 3 ms1m-57 ∷ []) refl

ax-p-14 : Eqn
ax-p-14 = derive (cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ cs ∷ cs ∷ cs ∷ [])
  (cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ [])
  (rw 4 ms1m-18 ∷ rw 2 ms1m-102 ∷ rw 0 ms1m-102 ∷ rw 5 ms1m-18 ∷ rw 3 ms1m-102 ∷ rw 1 ms1m-102 ∷
     rw 6 ms1m-18 ∷ rw 4 ms1m-102 ∷ rw 2 ms1m-102 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-57 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-32 ∷ rw 8 ms1m-26 ∷
     rw⁻ 0 ms1m-32 ∷ rw⁻ 1 ms1m-32 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-57 ∷ rw⁻ 5 ms1m-11 ∷
     rw⁻ 6 ms1m-57 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 4 ms1m-102 ∷ rw⁻ 1 ms1m-102 ∷ rw⁻ 3 ms1m-102 ∷ rw⁻ 0 ms1m-24 ∷
     rw⁻ 1 ms1m-259 ∷ rw⁻ 0 ms1m-143 ∷ rw⁻ 2 ms1m-1024 ∷ rw⁻ 4 ms1m-25 ∷ rw⁻ 7 ms1m-149 ∷ rw⁻ 11 ms1m-102 ∷
     rw⁻ 13 ms1m-102 ∷ rw⁻ 15 ms1m-18 ∷ rw⁻ 10 ms1m-17 ∷ rw⁻ 11 ms1m-21 ∷ rw⁻ 9 ms1m-17 ∷ rw⁻ 10 ms1m-17 ∷
     rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-59 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-33 ∷
     rw⁻ 5 ms1m-21 ∷ rw⁻ 9 ms1m-17 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-17 ∷
     rw⁻ 5 ms1m-21 ∷ rw⁻ 9 ms1m-202 ∷ rw⁻ 0 ms1m-32 ∷ rw⁻ 1 ms1m-32 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-11 ∷
     rw⁻ 4 ms1m-11 ∷ rw⁻ 5 ms1m-57 ∷ rw⁻ 6 ms1m-11 ∷ rw⁻ 7 ms1m-57 ∷ rw⁻ 8 ms1m-11 ∷ rw⁻ 2 ms1m-18 ∷
     rw⁻ 3 ms1m-102 ∷ rw⁻ 5 ms1m-102 ∷ rw⁻ 7 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 4 ms1m-102 ∷
     rw⁻ 6 ms1m-18 ∷ rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-102 ∷ rw⁻ 3 ms1m-102 ∷ rw⁻ 5 ms1m-18 ∷ []) refl

ax-p-15 : Eqn
ax-p-15 = derive (cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ s₀ ∷ [])
  (s₀ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ [])
  (rw 4 ms1m-18 ∷ rw 2 ms1m-102 ∷ rw 0 ms1m-102 ∷ rw 5 ms1m-18 ∷ rw 3 ms1m-102 ∷ rw 1 ms1m-102 ∷
     rw 6 ms1m-18 ∷ rw 4 ms1m-102 ∷ rw 2 ms1m-102 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-57 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-32 ∷ rw 8 ms1m-18 ∷
     rw 6 ms1m-102 ∷ rw 4 ms1m-102 ∷ rw 1 ms1m-25 ∷ rw⁻ 0 ms1m-11 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-11 ∷
     rw⁻ 3 ms1m-57 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 0 ms1m-25 ∷ rw⁻ 3 ms1m-102 ∷ rw⁻ 5 ms1m-102 ∷ rw⁻ 7 ms1m-18 ∷
     rw⁻ 2 ms1m-102 ∷ rw⁻ 4 ms1m-102 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 1 ms1m-102 ∷ rw⁻ 3 ms1m-102 ∷ rw⁻ 5 ms1m-18 ∷ []) refl

ax-p-16 : Eqn
ax-p-16 = derive (cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ s₀ ∷ [])
  ([])
  (rw 4 ms1m-18 ∷ rw 2 ms1m-102 ∷ rw 0 ms1m-102 ∷ rw 5 ms1m-18 ∷ rw 3 ms1m-102 ∷ rw 1 ms1m-102 ∷
     rw 6 ms1m-18 ∷ rw 4 ms1m-102 ∷ rw 2 ms1m-102 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-57 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-32 ∷ rw 4 ms1m-507 ∷
     rw 3 ms1m-59 ∷ rw 2 ms1m-59 ∷ rw 1 ms1m-59 ∷ rw 6 ms1m-507 ∷ rw 5 ms1m-1322 ∷ rw 4 ms1m-59 ∷
     rw 3 ms1m-59 ∷ rw 2 ms1m-59 ∷ rw 0 ms1m-113 ∷ rw 0 ms1m-25 ∷ rw 1 ms1m-132 ∷ rw 0 ms1m-132 ∷
     rw 2 ms1m-26 ∷ rw 4 ms1m-32 ∷ rw 3 ms1m-32 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-57 ∷
     rw 0 ms1m-113 ∷ rw 0 ms1m-25 ∷ []) refl

ax-q-13 : Eqn
ax-q-13 = derive (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ cs ∷ cs ∷ [])
  (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ [])
  (rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-60 ∷ rw 0 ms1m-17 ∷ rw 5 ms1m-17 ∷
     rw 4 ms1m-60 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-60 ∷ rw 1 ms1m-17 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-60 ∷
     rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-58 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw⁻ 0 ms1m-31 ∷
     rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-58 ∷ rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-58 ∷
     rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-11 ∷ rw⁻ 9 ms1m-11 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷
     rw⁻ 5 ms1m-60 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-17 ∷ rw⁻ 8 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-60 ∷
     rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-17 ∷ rw⁻ 0 ms1m-17 ∷
     rw⁻ 1 ms1m-60 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷
     rw⁻ 0 ms1m-113 ∷ rw⁻ 1 ms1m-129 ∷ rw⁻ 2 ms1m-542 ∷ rw⁻ 3 ms1m-542 ∷ rw⁻ 0 ms1m-58 ∷ rw⁻ 1 ms1m-11 ∷
     rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-58 ∷ []) refl

ax-q-14 : Eqn
ax-q-14 = derive (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ cs ∷ cs ∷ cs ∷ [])
  (cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ [])
  (rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-60 ∷ rw 0 ms1m-17 ∷ rw 5 ms1m-17 ∷
     rw 4 ms1m-60 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-60 ∷ rw 1 ms1m-17 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-60 ∷
     rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-58 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw 8 ms1m-26 ∷
     rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-58 ∷ rw⁻ 5 ms1m-11 ∷
     rw⁻ 6 ms1m-58 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷ rw⁻ 1 ms1m-17 ∷
     rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 2 ms1m-17 ∷
     rw⁻ 3 ms1m-60 ∷ rw⁻ 0 ms1m-25 ∷ rw⁻ 1 ms1m-208 ∷ rw⁻ 0 ms1m-113 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-52 ∷
     rw⁻ 4 ms1m-59 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-129 ∷ rw⁻ 1 ms1m-187 ∷
     rw⁻ 2 ms1m-206 ∷ rw⁻ 1 ms1m-25 ∷ rw⁻ 2 ms1m-190 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 7 ms1m-18 ∷
     rw⁻ 1 ms1m-187 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 3 ms1m-18 ∷ rw⁻ 4 ms1m-18 ∷
     rw⁻ 5 ms1m-18 ∷ rw⁻ 6 ms1m-190 ∷ rw⁻ 9 ms1m-18 ∷ rw⁻ 10 ms1m-22 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-18 ∷
     rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-187 ∷ rw⁻ 8 ms1m-18 ∷ rw⁻ 9 ms1m-18 ∷ rw⁻ 1 ms1m-759 ∷ rw⁻ 5 ms1m-22 ∷
     rw⁻ 9 ms1m-18 ∷ rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-22 ∷ rw⁻ 9 ms1m-206 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷
     rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 5 ms1m-58 ∷ rw⁻ 6 ms1m-11 ∷ rw⁻ 7 ms1m-58 ∷
     rw⁻ 8 ms1m-11 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-60 ∷
     rw⁻ 7 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷
     rw⁻ 6 ms1m-17 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷
     rw⁻ 5 ms1m-17 ∷ []) refl

ax-q-15 : Eqn
ax-q-15 = derive (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ s₁ ∷ [])
  (s₁ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ [])
  (rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-60 ∷ rw 0 ms1m-17 ∷ rw 5 ms1m-17 ∷
     rw 4 ms1m-60 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-60 ∷ rw 1 ms1m-17 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-60 ∷
     rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-58 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw 8 ms1m-17 ∷
     rw 7 ms1m-60 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-60 ∷ rw 4 ms1m-17 ∷ rw 1 ms1m-24 ∷ rw⁻ 0 ms1m-11 ∷
     rw⁻ 1 ms1m-58 ∷ rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-58 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-17 ∷
     rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-60 ∷ rw⁻ 7 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷
     rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-17 ∷
     rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-17 ∷ []) refl

ax-q-16 : Eqn
ax-q-16 = derive (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ s₁ ∷ [])
  ([])
  (rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-60 ∷ rw 0 ms1m-17 ∷ rw 5 ms1m-17 ∷
     rw 4 ms1m-60 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-60 ∷ rw 1 ms1m-17 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-60 ∷
     rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-58 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw 6 ms1m-2450 ∷
     rw 5 ms1m-60 ∷ rw 4 ms1m-17 ∷ rw 1 ms1m-24 ∷ rw 2 ms1m-52 ∷ rw 3 ms1m-52 ∷ rw 1 ms1m-132 ∷
     rw 0 ms1m-113 ∷ rw 1 ms1m-129 ∷ rw 0 ms1m-132 ∷ rw 2 ms1m-26 ∷ rw 0 ms1m-138 ∷ rw 1 ms1m-138 ∷
     rw 2 ms1m-138 ∷ rw 4 ms1m-57 ∷ rw 3 ms1m-57 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷
     rw 0 ms1m-145 ∷ rw 0 ms1m-24 ∷ []) refl

ax-q-I : Eqn
ax-q-I = derive (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ ι ∷ [])
  (ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ [])
  (rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-60 ∷ rw 0 ms1m-17 ∷ rw 5 ms1m-17 ∷
     rw 4 ms1m-60 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-60 ∷ rw 1 ms1m-17 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-60 ∷
     rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-58 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw 8 ms1m-11 ∷
     rw 7 ms1m-58 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-58 ∷ rw 4 ms1m-11 ∷ rw 3 ms1m-31 ∷ rw 2 ms1m-31 ∷
     rw 1 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-31 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 5 ms1m-58 ∷
     rw⁻ 6 ms1m-11 ∷ rw⁻ 7 ms1m-58 ∷ rw⁻ 8 ms1m-11 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-17 ∷
     rw⁻ 6 ms1m-60 ∷ rw⁻ 7 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷
     rw⁻ 6 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-17 ∷ []) refl

ax-p-y : Eqn
ax-p-y = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (s₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ cs ∷ cs ∷ [])
  (rw 3 ms1m-57 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-57 ∷ rw 9 ms1m-18 ∷ rw 7 ms1m-102 ∷
     rw 5 ms1m-102 ∷ rw 10 ms1m-18 ∷ rw 8 ms1m-102 ∷ rw 6 ms1m-102 ∷ rw 11 ms1m-18 ∷ rw 9 ms1m-102 ∷
     rw 7 ms1m-102 ∷ rw 1 ms1m-1207 ∷ rw 3 ms1m-174 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-132 ∷ rw 0 ms1m-113 ∷
     rw 8 ms1m-11 ∷ rw 7 ms1m-57 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-31 ∷ rw 4 ms1m-31 ∷ rw 3 ms1m-57 ∷
     rw 2 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-11 ∷ rw 7 ms1m-21 ∷ rw 4 ms1m-164 ∷ rw 3 ms1m-17 ∷
     rw 2 ms1m-17 ∷ rw 1 ms1m-17 ∷ rw 4 ms1m-144 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-132 ∷ rw 0 ms1m-104 ∷
     rw 3 ms1m-1299 ∷ rw 2 ms1m-142 ∷ rw 1 ms1m-18 ∷ rw 3 ms1m-170 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-33 ∷
     rw 3 ms1m-21 ∷ rw 2 ms1m-33 ∷ rw 3 ms1m-59 ∷ rw 7 ms1m-17 ∷ rw 9 ms1m-11 ∷ rw 8 ms1m-11 ∷
     rw 7 ms1m-31 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-32 ∷ rw 3 ms1m-57 ∷ rw 2 ms1m-31 ∷
     rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-57 ∷
     rw⁻ 4 ms1m-32 ∷ rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-57 ∷ rw⁻ 7 ms1m-31 ∷ rw⁻ 4 ms1m-142 ∷ rw⁻ 4 ms1m-25 ∷
     rw⁻ 7 ms1m-142 ∷ rw⁻ 6 ms1m-142 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷
     rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-202 ∷ []) refl

ax-p-a : Eqn
ax-p-a = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (s₀ ∷ s₀ ∷ cs ∷ cs ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ cs ∷ cs ∷ [])
  (rw 3 ms1m-57 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-57 ∷ rw 3 ms1m-506 ∷ rw 2 ms1m-506 ∷
     rw 0 ms1m-113 ∷ rw 6 ms1m-18 ∷ rw 5 ms1m-18 ∷ rw 4 ms1m-18 ∷ rw 2 ms1m-102 ∷ rw 0 ms1m-102 ∷
     rw 7 ms1m-18 ∷ rw 6 ms1m-18 ∷ rw 5 ms1m-18 ∷ rw 3 ms1m-102 ∷ rw 1 ms1m-102 ∷ rw 8 ms1m-18 ∷
     rw 7 ms1m-18 ∷ rw 6 ms1m-18 ∷ rw 4 ms1m-102 ∷ rw 2 ms1m-102 ∷ rw 9 ms1m-11 ∷ rw 8 ms1m-11 ∷
     rw 7 ms1m-11 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-57 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-32 ∷
     rw 1 ms1m-32 ∷ rw 0 ms1m-32 ∷ rw 3 ms1m-4746 ∷ rw 2 ms1m-33 ∷ rw 1 ms1m-33 ∷ rw 3 ms1m-59 ∷
     rw 2 ms1m-59 ∷ rw 4 ms1m-33 ∷ rw 3 ms1m-33 ∷ rw 5 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 6 ms1m-59 ∷
     rw 5 ms1m-59 ∷ rw 0 ms1m-143 ∷ rw 1 ms1m-4468 ∷ rw 3 ms1m-1306 ∷ rw 2 ms1m-142 ∷ rw 1 ms1m-18 ∷
     rw 3 ms1m-170 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-33 ∷ rw 3 ms1m-21 ∷ rw 2 ms1m-33 ∷ rw 3 ms1m-59 ∷
     rw 7 ms1m-17 ∷ rw 0 ms1m-4068 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-57 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-11 ∷ rw 3 ms1m-57 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-32 ∷ rw⁻ 1 ms1m-4068 ∷
     rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-57 ∷ rw⁻ 4 ms1m-32 ∷ rw⁻ 5 ms1m-11 ∷
     rw⁻ 6 ms1m-57 ∷ rw⁻ 7 ms1m-31 ∷ rw⁻ 4 ms1m-142 ∷ rw⁻ 4 ms1m-25 ∷ rw⁻ 7 ms1m-142 ∷ rw⁻ 6 ms1m-142 ∷
     rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷
     rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-202 ∷ []) refl

ax-q-x : Eqn
ax-q-x = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (s₁ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ cs ∷ cs ∷ [])
  (rw 3 ms1m-58 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-58 ∷ rw 9 ms1m-17 ∷ rw 8 ms1m-60 ∷
     rw 7 ms1m-17 ∷ rw 6 ms1m-60 ∷ rw 5 ms1m-17 ∷ rw 4 ms1m-60 ∷ rw 3 ms1m-33 ∷ rw 2 ms1m-33 ∷
     rw 1 ms1m-60 ∷ rw 10 ms1m-17 ∷ rw 9 ms1m-60 ∷ rw 8 ms1m-17 ∷ rw 7 ms1m-60 ∷ rw 6 ms1m-17 ∷
     rw 5 ms1m-60 ∷ rw 4 ms1m-33 ∷ rw 3 ms1m-33 ∷ rw 2 ms1m-60 ∷ rw 11 ms1m-17 ∷ rw 10 ms1m-60 ∷
     rw 9 ms1m-17 ∷ rw 8 ms1m-60 ∷ rw 7 ms1m-17 ∷ rw 6 ms1m-60 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-33 ∷
     rw 3 ms1m-60 ∷ rw 1 ms1m-856 ∷ rw 7 ms1m-129 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-59 ∷ rw 4 ms1m-52 ∷
     rw 7 ms1m-59 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-52 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-132 ∷
     rw 0 ms1m-113 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-58 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-32 ∷ rw 4 ms1m-32 ∷
     rw 3 ms1m-58 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-11 ∷ rw 7 ms1m-22 ∷ rw 4 ms1m-187 ∷
     rw 3 ms1m-18 ∷ rw 2 ms1m-18 ∷ rw 1 ms1m-18 ∷ rw 7 ms1m-129 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-52 ∷
     rw 7 ms1m-59 ∷ rw 6 ms1m-52 ∷ rw 4 ms1m-132 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-59 ∷
     rw 2 ms1m-59 ∷ rw 0 ms1m-113 ∷ rw 3 ms1m-2329 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-17 ∷ rw 0 ms1m-33 ∷
     rw 3 ms1m-191 ∷ rw 2 ms1m-18 ∷ rw 3 ms1m-22 ∷ rw 7 ms1m-18 ∷ rw 1 ms1m-786 ∷ rw 8 ms1m-11 ∷
     rw 7 ms1m-58 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-11 ∷ rw 3 ms1m-58 ∷ rw 2 ms1m-11 ∷
     rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw⁻ 2 ms1m-786 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-32 ∷ rw⁻ 2 ms1m-32 ∷
     rw⁻ 3 ms1m-32 ∷ rw⁻ 4 ms1m-58 ∷ rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-32 ∷ rw⁻ 0 ms1m-33 ∷
     rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷ rw⁻ 6 ms1m-33 ∷
     rw⁻ 0 ms1m-24 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-33 ∷ rw⁻ 5 ms1m-33 ∷ rw⁻ 6 ms1m-60 ∷ rw⁻ 7 ms1m-17 ∷
     rw⁻ 8 ms1m-60 ∷ rw⁻ 9 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-33 ∷ rw⁻ 5 ms1m-60 ∷
     rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-60 ∷ rw⁻ 8 ms1m-33 ∷ rw⁻ 2 ms1m-206 ∷ []) refl

ax-q-b : Eqn
ax-q-b = derive (k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ [])
  (s₁ ∷ s₁ ∷ cs ∷ cs ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ cs ∷ cs ∷ [])
  (rw 3 ms1m-58 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-58 ∷ rw 3 ms1m-542 ∷ rw 2 ms1m-542 ∷
     rw 1 ms1m-129 ∷ rw 0 ms1m-113 ∷ rw 0 ms1m-5868 ∷ rw 6 ms1m-60 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-60 ∷
     rw 3 ms1m-17 ∷ rw 2 ms1m-33 ∷ rw 1 ms1m-60 ∷ rw 0 ms1m-33 ∷ rw 7 ms1m-60 ∷ rw 6 ms1m-33 ∷
     rw 5 ms1m-60 ∷ rw 4 ms1m-17 ∷ rw 3 ms1m-33 ∷ rw 2 ms1m-60 ∷ rw 1 ms1m-33 ∷ rw 8 ms1m-60 ∷
     rw 7 ms1m-33 ∷ rw 6 ms1m-60 ∷ rw 5 ms1m-17 ∷ rw 4 ms1m-33 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-33 ∷
     rw 0 ms1m-9033 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-58 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-11 ∷
     rw 3 ms1m-58 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-11 ∷ rw 5 ms1m-206 ∷ rw 4 ms1m-187 ∷
     rw 3 ms1m-18 ∷ rw 2 ms1m-18 ∷ rw 1 ms1m-18 ∷ rw 7 ms1m-129 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-52 ∷
     rw 7 ms1m-59 ∷ rw 6 ms1m-52 ∷ rw 4 ms1m-132 ∷ rw 3 ms1m-132 ∷ rw 2 ms1m-132 ∷ rw 1 ms1m-59 ∷
     rw 2 ms1m-59 ∷ rw 0 ms1m-113 ∷ rw 3 ms1m-2333 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-17 ∷ rw 0 ms1m-33 ∷
     rw 3 ms1m-191 ∷ rw 2 ms1m-18 ∷ rw 3 ms1m-22 ∷ rw 7 ms1m-18 ∷ rw 1 ms1m-786 ∷ rw 8 ms1m-11 ∷
     rw 7 ms1m-58 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-11 ∷ rw 3 ms1m-58 ∷ rw 2 ms1m-11 ∷
     rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw⁻ 2 ms1m-786 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-32 ∷ rw⁻ 2 ms1m-32 ∷
     rw⁻ 3 ms1m-32 ∷ rw⁻ 4 ms1m-58 ∷ rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-32 ∷ rw⁻ 0 ms1m-33 ∷
     rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷ rw⁻ 6 ms1m-33 ∷
     rw⁻ 0 ms1m-2916 ∷ rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-17 ∷
     rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-60 ∷ rw⁻ 7 ms1m-33 ∷ rw⁻ 8 ms1m-60 ∷ rw⁻ 2 ms1m-18 ∷ rw⁻ 3 ms1m-18 ∷
     rw⁻ 4 ms1m-18 ∷ rw⁻ 5 ms1m-187 ∷ rw⁻ 0 ms1m-2701 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-33 ∷
     rw⁻ 5 ms1m-60 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-60 ∷ rw⁻ 8 ms1m-33 ∷ rw⁻ 2 ms1m-206 ∷ []) refl

ax-pq-sw : Eqn
ax-pq-sw = derive (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ k₀ ∷ cs ∷ cs ∷ k₀ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ [])
  (rw 3 ms1m-57 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-11 ∷ rw 0 ms1m-57 ∷ rw 8 ms1m-58 ∷ rw 7 ms1m-11 ∷
     rw 6 ms1m-11 ∷ rw 5 ms1m-58 ∷ rw 4 ms1m-57 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-57 ∷
     rw 9 ms1m-52 ∷ rw 3 ms1m-72874 ∷ rw 13 ms1m-11 ∷ rw 12 ms1m-11 ∷ rw 11 ms1m-58 ∷ rw 10 ms1m-57 ∷
     rw 9 ms1m-11 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-58 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-11 ∷
     rw 3 ms1m-58 ∷ rw 2 ms1m-57 ∷ rw 0 ms1m-131 ∷ rw 2 ms1m-128448 ∷ rw 0 ms1m-127 ∷ rw 16 ms1m-18 ∷
     rw 14 ms1m-102 ∷ rw 13 ms1m-18 ∷ rw 12 ms1m-18 ∷ rw 3 ms1m-32453 ∷ rw 2 ms1m-17 ∷ rw 2 ms1m-45869 ∷
     rw 11 ms1m-6547 ∷ rw 10 ms1m-60 ∷ rw 9 ms1m-17 ∷ rw 8 ms1m-17 ∷ rw 7 ms1m-60 ∷ rw 11 ms1m-52 ∷
     rw 12 ms1m-60 ∷ rw 4 ms1m-83247 ∷ rw 3 ms1m-125136 ∷ rw 14 ms1m-52 ∷ rw 15 ms1m-60 ∷ rw 16 ms1m-52 ∷
     rw 10 ms1m-7896 ∷ rw 8 ms1m-102 ∷ rw 7 ms1m-18 ∷ rw 4 ms1m-125136 ∷ rw 15 ms1m-52 ∷ rw 16 ms1m-60 ∷
     rw 17 ms1m-52 ∷ rw 11 ms1m-7896 ∷ rw 9 ms1m-102 ∷ rw 8 ms1m-18 ∷ rw 2 ms1m-83508 ∷ rw 3 ms1m-83438 ∷
     rw 2 ms1m-59 ∷ rw 8 ms1m-5272 ∷ rw 12 ms1m-52 ∷ rw 13 ms1m-60 ∷ rw 14 ms1m-52 ∷ rw 15 ms1m-58 ∷
     rw 14 ms1m-57 ∷ rw 13 ms1m-31 ∷ rw 12 ms1m-57 ∷ rw 11 ms1m-11 ∷ rw 10 ms1m-11 ∷ rw 9 ms1m-58 ∷
     rw 8 ms1m-11 ∷ rw 7 ms1m-57 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-58 ∷ rw 3 ms1m-32 ∷
     rw 2 ms1m-57 ∷ rw 0 ms1m-131 ∷ rw 15 ms1m-52 ∷ rw 11 ms1m-144 ∷ rw 10 ms1m-132 ∷ rw 9 ms1m-52 ∷
     rw 10 ms1m-52 ∷ rw 8 ms1m-132 ∷ rw 6 ms1m-132 ∷ rw 5 ms1m-132 ∷ rw 4 ms1m-52 ∷ rw 3 ms1m-59 ∷
     rw 0 ms1m-127 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 17 ms1m-57 ∷ rw 16 ms1m-11 ∷ rw 15 ms1m-11 ∷
     rw 14 ms1m-58 ∷ rw 13 ms1m-31 ∷ rw 12 ms1m-57 ∷ rw 11 ms1m-11 ∷ rw 10 ms1m-11 ∷ rw 9 ms1m-58 ∷
     rw 8 ms1m-11 ∷ rw 7 ms1m-57 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-58 ∷ rw 3 ms1m-32 ∷
     rw 2 ms1m-57 ∷ rw 0 ms1m-131 ∷ rw 10 ms1m-65352 ∷ rw 8 ms1m-5522 ∷ rw 5 ms1m-81531 ∷ rw 4 ms1m-52 ∷
     rw 3 ms1m-59 ∷ rw 0 ms1m-127 ∷ rw 14 ms1m-190 ∷ rw 10 ms1m-150 ∷ rw 9 ms1m-18 ∷ rw 3 ms1m-8400 ∷
     rw 3 ms1m-18905 ∷ rw 2 ms1m-33 ∷ rw 3 ms1m-33 ∷ rw 10 ms1m-142 ∷ rw 9 ms1m-18 ∷ rw 11 ms1m-142 ∷
     rw 10 ms1m-18 ∷ rw 2 ms1m-76221 ∷ rw 9 ms1m-164 ∷ rw 8 ms1m-17 ∷ rw 7 ms1m-17 ∷ rw 6 ms1m-60 ∷
     rw 13 ms1m-129 ∷ rw 9 ms1m-144 ∷ rw 8 ms1m-132 ∷ rw 7 ms1m-52 ∷ rw 8 ms1m-52 ∷ rw 4 ms1m-144 ∷
     rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 4 ms1m-52 ∷ rw 3 ms1m-59 ∷ rw 1 ms1m-113 ∷ rw 11 ms1m-57 ∷
     rw 10 ms1m-31 ∷ rw 9 ms1m-57 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-31 ∷
     rw 4 ms1m-57 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-58 ∷ rw 1 ms1m-32 ∷ rw 9 ms1m-144 ∷ rw 8 ms1m-132 ∷
     rw 7 ms1m-52 ∷ rw 8 ms1m-52 ∷ rw 4 ms1m-144 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 4 ms1m-52 ∷
     rw 3 ms1m-59 ∷ rw 1 ms1m-113 ∷ rw 3 ms1m-37683 ∷ rw 1 ms1m-46768 ∷ rw 6 ms1m-544 ∷ rw 5 ms1m-129 ∷
     rw 1 ms1m-145 ∷ rw 8 ms1m-132 ∷ rw 7 ms1m-52 ∷ rw 8 ms1m-52 ∷ rw 6 ms1m-132 ∷ rw 5 ms1m-52 ∷
     rw 6 ms1m-52 ∷ rw 4 ms1m-132 ∷ rw 0 ms1m-145 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-58 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw⁻ 0 ms1m-31 ∷
     rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-58 ∷ rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-58 ∷
     rw⁻ 7 ms1m-11 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷ rw⁻ 6 ms1m-17 ∷
     rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 0 ms1m-17 ∷
     rw⁻ 1 ms1m-60 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ []) refl

ax-p-xpx : Eqn
ax-p-xpx = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ [])
  (cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
  (rw 3 ms1m-58 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-58 ∷ rw 9 ms1m-18 ∷ rw 7 ms1m-102 ∷
     rw 5 ms1m-102 ∷ rw 10 ms1m-18 ∷ rw 8 ms1m-102 ∷ rw 6 ms1m-102 ∷ rw 11 ms1m-18 ∷ rw 9 ms1m-102 ∷
     rw 7 ms1m-102 ∷ rw 4 ms1m-187 ∷ rw 1 ms1m-187 ∷ rw 4 ms1m-129 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-52 ∷
     rw 1 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 0 ms1m-113 ∷ rw 9 ms1m-11 ∷
     rw 8 ms1m-57 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-58 ∷ rw 3 ms1m-32 ∷
     rw 2 ms1m-32 ∷ rw 1 ms1m-58 ∷ rw 0 ms1m-32 ∷ rw 14 ms1m-58 ∷ rw 13 ms1m-32 ∷ rw 12 ms1m-32 ∷
     rw 11 ms1m-58 ∷ rw 10 ms1m-11 ∷ rw 9 ms1m-57 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-57 ∷ rw 6 ms1m-11 ∷
     rw 5 ms1m-58 ∷ rw 4 ms1m-32 ∷ rw 3 ms1m-32 ∷ rw 2 ms1m-58 ∷ rw 1 ms1m-32 ∷ rw 11 ms1m-645 ∷
     rw 7 ms1m-21 ∷ rw 6 ms1m-60 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-33 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-33 ∷
     rw 7 ms1m-52 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-59 ∷ rw 4 ms1m-52 ∷ rw 3 ms1m-59 ∷ rw 15 ms1m-52 ∷
     rw 14 ms1m-59 ∷ rw 13 ms1m-59 ∷ rw 12 ms1m-52 ∷ rw 11 ms1m-691 ∷ rw 9 ms1m-132 ∷ rw 8 ms1m-52 ∷
     rw 7 ms1m-59 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-52 ∷ rw 4 ms1m-59 ∷ rw 1 ms1m-104 ∷ rw 6 ms1m-52 ∷
     rw 5 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 8 ms1m-645 ∷ rw 7 ms1m-60 ∷
     rw 6 ms1m-33 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-60 ∷ rw 3 ms1m-33 ∷ rw 8 ms1m-129 ∷ rw 7 ms1m-59 ∷
     rw 6 ms1m-59 ∷ rw 5 ms1m-52 ∷ rw 4 ms1m-59 ∷ rw 8 ms1m-59 ∷ rw 7 ms1m-59 ∷ rw 6 ms1m-52 ∷
     rw 5 ms1m-59 ∷ rw 0 ms1m-143 ∷ rw 4 ms1m-187 ∷ rw 5 ms1m-190 ∷ rw 3 ms1m-25 ∷ rw 4 ms1m-129 ∷
     rw 3 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 5 ms1m-59 ∷ rw 6 ms1m-33 ∷ rw 4 ms1m-138 ∷ rw 1 ms1m-152 ∷
     rw 0 ms1m-24 ∷ rw 3 ms1m-25 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-57 ∷ rw 0 ms1m-113 ∷
     rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-57 ∷ rw⁻ 1 ms1m-129 ∷ rw⁻ 1 ms1m-25 ∷
     rw⁻ 2 ms1m-190 ∷ rw⁻ 1 ms1m-187 ∷ rw⁻ 0 ms1m-52 ∷ rw⁻ 1 ms1m-59 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 0 ms1m-113 ∷
     rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-129 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-58 ∷
     rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-32 ∷ rw⁻ 4 ms1m-58 ∷ rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷
     rw⁻ 2 ms1m-57 ∷ rw⁻ 3 ms1m-373 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-52 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 1 ms1m-59 ∷
     rw⁻ 2 ms1m-52 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-129 ∷ rw⁻ 1 ms1m-187 ∷ rw⁻ 4 ms1m-187 ∷ rw⁻ 0 ms1m-24 ∷
     rw⁻ 1 ms1m-152 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-33 ∷ rw⁻ 6 ms1m-33 ∷ rw⁻ 7 ms1m-60 ∷ rw⁻ 8 ms1m-33 ∷
     rw⁻ 3 ms1m-52 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-59 ∷ rw⁻ 6 ms1m-52 ∷ rw⁻ 7 ms1m-59 ∷ rw⁻ 2 ms1m-651 ∷
     rw⁻ 0 ms1m-104 ∷ rw⁻ 3 ms1m-360 ∷ rw⁻ 2 ms1m-59 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 1 ms1m-104 ∷
     rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-59 ∷ rw⁻ 6 ms1m-59 ∷ rw⁻ 7 ms1m-132 ∷ rw⁻ 9 ms1m-691 ∷ rw⁻ 10 ms1m-52 ∷
     rw⁻ 11 ms1m-59 ∷ rw⁻ 12 ms1m-59 ∷ rw⁻ 13 ms1m-52 ∷ rw⁻ 3 ms1m-59 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-59 ∷
     rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-33 ∷ rw⁻ 5 ms1m-21 ∷ rw⁻ 9 ms1m-645 ∷ rw⁻ 1 ms1m-32 ∷
     rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-32 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 5 ms1m-57 ∷ rw⁻ 6 ms1m-11 ∷ rw⁻ 7 ms1m-57 ∷
     rw⁻ 8 ms1m-11 ∷ rw⁻ 9 ms1m-58 ∷ rw⁻ 10 ms1m-32 ∷ rw⁻ 11 ms1m-32 ∷ rw⁻ 12 ms1m-58 ∷ rw⁻ 0 ms1m-32 ∷
     rw⁻ 1 ms1m-32 ∷ rw⁻ 2 ms1m-32 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-57 ∷ rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-57 ∷
     rw⁻ 7 ms1m-11 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 4 ms1m-102 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 1 ms1m-102 ∷ rw⁻ 3 ms1m-102 ∷
     rw⁻ 5 ms1m-18 ∷ rw⁻ 0 ms1m-102 ∷ rw⁻ 2 ms1m-102 ∷ rw⁻ 4 ms1m-18 ∷ []) refl

ax-q-yqy : Eqn
ax-q-yqy = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ [])
  (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
  (rw 3 ms1m-57 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-57 ∷ rw 9 ms1m-17 ∷ rw 8 ms1m-60 ∷
     rw 7 ms1m-17 ∷ rw 6 ms1m-60 ∷ rw 5 ms1m-17 ∷ rw 10 ms1m-17 ∷ rw 9 ms1m-60 ∷ rw 8 ms1m-17 ∷
     rw 7 ms1m-60 ∷ rw 6 ms1m-17 ∷ rw 11 ms1m-17 ∷ rw 10 ms1m-60 ∷ rw 9 ms1m-17 ∷ rw 8 ms1m-60 ∷
     rw 7 ms1m-17 ∷ rw 4 ms1m-164 ∷ rw 1 ms1m-164 ∷ rw 0 ms1m-143 ∷ rw 9 ms1m-11 ∷ rw 8 ms1m-58 ∷
     rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-57 ∷ rw 3 ms1m-31 ∷ rw 2 ms1m-31 ∷
     rw 1 ms1m-57 ∷ rw 0 ms1m-31 ∷ rw 14 ms1m-57 ∷ rw 13 ms1m-31 ∷ rw 12 ms1m-31 ∷ rw 11 ms1m-57 ∷
     rw 10 ms1m-11 ∷ rw 9 ms1m-58 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-58 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-57 ∷
     rw 4 ms1m-31 ∷ rw 3 ms1m-31 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-31 ∷ rw 11 ms1m-924 ∷ rw 10 ms1m-52 ∷
     rw 11 ms1m-60 ∷ rw 12 ms1m-60 ∷ rw 13 ms1m-52 ∷ rw 9 ms1m-952 ∷ rw 8 ms1m-52 ∷ rw 9 ms1m-60 ∷
     rw 10 ms1m-60 ∷ rw 11 ms1m-52 ∷ rw 12 ms1m-190 ∷ rw 7 ms1m-179 ∷ rw 8 ms1m-179 ∷ rw 9 ms1m-179 ∷
     rw 15 ms1m-129 ∷ rw 10 ms1m-174 ∷ rw 9 ms1m-59 ∷ rw 8 ms1m-59 ∷ rw 7 ms1m-59 ∷ rw 1 ms1m-162 ∷
     rw 7 ms1m-59 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-59 ∷ rw 9 ms1m-924 ∷ rw 8 ms1m-59 ∷ rw 7 ms1m-59 ∷
     rw 6 ms1m-59 ∷ rw 0 ms1m-162 ∷ rw 6 ms1m-33 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-33 ∷ rw 1 ms1m-164 ∷
     rw 7 ms1m-33 ∷ rw 6 ms1m-33 ∷ rw 5 ms1m-33 ∷ rw 2 ms1m-152 ∷ rw 0 ms1m-24 ∷ rw 4 ms1m-59 ∷
     rw 3 ms1m-59 ∷ rw 2 ms1m-59 ∷ rw 3 ms1m-25 ∷ rw 3 ms1m-60 ∷ rw 1 ms1m-138 ∷ rw 4 ms1m-60 ∷
     rw 2 ms1m-138 ∷ rw 5 ms1m-60 ∷ rw 3 ms1m-138 ∷ rw 0 ms1m-24 ∷ rw 2 ms1m-58 ∷ rw 1 ms1m-57 ∷
     rw 0 ms1m-57 ∷ rw 0 ms1m-113 ∷ rw⁻ 0 ms1m-113 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-58 ∷
     rw⁻ 1 ms1m-52 ∷ rw⁻ 0 ms1m-24 ∷ rw⁻ 1 ms1m-152 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 0 ms1m-164 ∷ rw⁻ 3 ms1m-60 ∷
     rw⁻ 0 ms1m-146 ∷ rw⁻ 5 ms1m-52 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-57 ∷
     rw⁻ 4 ms1m-58 ∷ rw⁻ 0 ms1m-146 ∷ rw⁻ 0 ms1m-163 ∷ rw⁻ 5 ms1m-138 ∷ rw⁻ 7 ms1m-60 ∷ rw⁻ 3 ms1m-138 ∷
     rw⁻ 0 ms1m-164 ∷ rw⁻ 3 ms1m-164 ∷ rw⁻ 6 ms1m-60 ∷ rw⁻ 5 ms1m-60 ∷ rw⁻ 5 ms1m-25 ∷ rw⁻ 0 ms1m-160 ∷
     rw⁻ 7 ms1m-59 ∷ rw⁻ 8 ms1m-59 ∷ rw⁻ 9 ms1m-59 ∷ rw⁻ 6 ms1m-33 ∷ rw⁻ 7 ms1m-33 ∷ rw⁻ 8 ms1m-33 ∷
     rw⁻ 5 ms1m-33 ∷ rw⁻ 6 ms1m-33 ∷ rw⁻ 7 ms1m-33 ∷ rw⁻ 4 ms1m-59 ∷ rw⁻ 5 ms1m-59 ∷ rw⁻ 6 ms1m-59 ∷
     rw⁻ 7 ms1m-924 ∷ rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-33 ∷ rw⁻ 5 ms1m-33 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 2 ms1m-33 ∷
     rw⁻ 3 ms1m-33 ∷ rw⁻ 4 ms1m-33 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-33 ∷
     rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-165 ∷ rw⁻ 10 ms1m-129 ∷ rw⁻ 3 ms1m-207 ∷ rw⁻ 2 ms1m-207 ∷ rw⁻ 1 ms1m-207 ∷
     rw⁻ 7 ms1m-190 ∷ rw⁻ 1 ms1m-210 ∷ rw⁻ 9 ms1m-52 ∷ rw⁻ 8 ms1m-60 ∷ rw⁻ 7 ms1m-60 ∷ rw⁻ 6 ms1m-52 ∷
     rw⁻ 7 ms1m-952 ∷ rw⁻ 11 ms1m-52 ∷ rw⁻ 10 ms1m-60 ∷ rw⁻ 9 ms1m-60 ∷ rw⁻ 8 ms1m-52 ∷ rw⁻ 9 ms1m-924 ∷
     rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-31 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 5 ms1m-58 ∷ rw⁻ 6 ms1m-11 ∷
     rw⁻ 7 ms1m-58 ∷ rw⁻ 8 ms1m-11 ∷ rw⁻ 9 ms1m-57 ∷ rw⁻ 10 ms1m-31 ∷ rw⁻ 11 ms1m-31 ∷ rw⁻ 12 ms1m-57 ∷
     rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-11 ∷ rw⁻ 4 ms1m-58 ∷ rw⁻ 5 ms1m-11 ∷
     rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ rw⁻ 5 ms1m-60 ∷
     rw⁻ 6 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷ rw⁻ 5 ms1m-17 ∷
     rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷ []) refl

ax-p-i1 : Eqn
ax-p-i1 = derive (cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ cs ∷ cs ∷ cs ∷ s₁ ∷ [])
  (cs ∷ cs ∷ cs ∷ s₁ ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ [])
  (rw 4 ms1m-18 ∷ rw 5 ms1m-18 ∷ rw 6 ms1m-18 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-32 ∷ rw 5 ms1m-32 ∷
     rw 4 ms1m-32 ∷ rw 3 ms1m-57 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-11 ∷ rw 8 ms1m-26 ∷
     rw 7 ms1m-33 ∷ rw 6 ms1m-33 ∷ rw 5 ms1m-33 ∷ rw 1 ms1m-21 ∷ rw 5 ms1m-18 ∷ rw 6 ms1m-18 ∷
     rw 7 ms1m-18 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-57 ∷ rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-57 ∷ rw⁻ 4 ms1m-32 ∷
     rw⁻ 5 ms1m-32 ∷ rw⁻ 6 ms1m-32 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 6 ms1m-18 ∷ rw⁻ 5 ms1m-18 ∷ rw⁻ 4 ms1m-18 ∷
     rw⁻ 1 ms1m-26 ∷ rw⁻ 0 ms1m-17 ∷ rw⁻ 1 ms1m-17 ∷ rw⁻ 2 ms1m-17 ∷ []) refl

ax-q-i2 : Eqn
ax-q-i2 = derive (cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ cs ∷ cs ∷ cs ∷ s₀ ∷ [])
  (cs ∷ cs ∷ cs ∷ s₀ ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ [])
  (rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 1 ms1m-60 ∷ rw 0 ms1m-17 ∷ rw 5 ms1m-17 ∷
     rw 4 ms1m-60 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-60 ∷ rw 1 ms1m-17 ∷ rw 6 ms1m-17 ∷ rw 5 ms1m-60 ∷
     rw 4 ms1m-17 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-17 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-58 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-31 ∷ rw 8 ms1m-26 ∷
     rw 4 ms1m-22 ∷ rw⁻ 0 ms1m-31 ∷ rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-32 ∷ rw⁻ 4 ms1m-58 ∷
     rw⁻ 5 ms1m-11 ∷ rw⁻ 6 ms1m-58 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 2 ms1m-33 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷
     rw⁻ 5 ms1m-60 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 1 ms1m-33 ∷ rw⁻ 2 ms1m-60 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-60 ∷
     rw⁻ 5 ms1m-17 ∷ rw⁻ 0 ms1m-33 ∷ rw⁻ 1 ms1m-60 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-60 ∷ rw⁻ 4 ms1m-17 ∷
     rw⁻ 1 ms1m-26 ∷ rw⁻ 0 ms1m-18 ∷ rw⁻ 1 ms1m-18 ∷ rw⁻ 2 ms1m-18 ∷ []) refl

ax-K1 : Eqn
ax-K1 = derive (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ cs ∷ k₁ ∷ cs ∷ k₁ ∷ cs ∷ s₀ ∷ s₀ ∷ s₀ ∷ ι ∷ [])
  (k₁ ∷ [])
  (rw 3 ms1m-58 ∷ rw 2 ms1m-32 ∷ rw 1 ms1m-32 ∷ rw 0 ms1m-58 ∷ rw 9 ms1m-18 ∷ rw 7 ms1m-102 ∷
     rw 5 ms1m-102 ∷ rw 10 ms1m-18 ∷ rw 8 ms1m-102 ∷ rw 6 ms1m-102 ∷ rw 11 ms1m-18 ∷ rw 9 ms1m-102 ∷
     rw 7 ms1m-102 ∷ rw 4 ms1m-187 ∷ rw 1 ms1m-187 ∷ rw 4 ms1m-129 ∷ rw 3 ms1m-59 ∷ rw 2 ms1m-52 ∷
     rw 1 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 0 ms1m-113 ∷ rw 9 ms1m-11 ∷
     rw 8 ms1m-57 ∷ rw 7 ms1m-11 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-58 ∷ rw 3 ms1m-32 ∷
     rw 2 ms1m-32 ∷ rw 1 ms1m-58 ∷ rw 0 ms1m-32 ∷ rw 14 ms1m-58 ∷ rw 13 ms1m-32 ∷ rw 12 ms1m-32 ∷
     rw 11 ms1m-58 ∷ rw 10 ms1m-11 ∷ rw 9 ms1m-57 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-57 ∷ rw 6 ms1m-11 ∷
     rw 5 ms1m-58 ∷ rw 4 ms1m-32 ∷ rw 3 ms1m-32 ∷ rw 2 ms1m-58 ∷ rw 1 ms1m-32 ∷ rw 11 ms1m-645 ∷
     rw 7 ms1m-21 ∷ rw 6 ms1m-60 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-33 ∷ rw 3 ms1m-60 ∷ rw 2 ms1m-33 ∷
     rw 7 ms1m-52 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-59 ∷ rw 4 ms1m-52 ∷ rw 3 ms1m-59 ∷ rw 15 ms1m-52 ∷
     rw 14 ms1m-59 ∷ rw 13 ms1m-59 ∷ rw 12 ms1m-52 ∷ rw 11 ms1m-691 ∷ rw 9 ms1m-132 ∷ rw 8 ms1m-52 ∷
     rw 7 ms1m-59 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-52 ∷ rw 4 ms1m-59 ∷ rw 1 ms1m-104 ∷ rw 6 ms1m-52 ∷
     rw 5 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 3 ms1m-52 ∷ rw 2 ms1m-59 ∷ rw 8 ms1m-645 ∷ rw 7 ms1m-60 ∷
     rw 6 ms1m-33 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-60 ∷ rw 3 ms1m-33 ∷ rw 8 ms1m-129 ∷ rw 7 ms1m-59 ∷
     rw 6 ms1m-59 ∷ rw 5 ms1m-52 ∷ rw 4 ms1m-59 ∷ rw 8 ms1m-59 ∷ rw 7 ms1m-59 ∷ rw 6 ms1m-52 ∷
     rw 5 ms1m-59 ∷ rw 0 ms1m-143 ∷ rw 4 ms1m-187 ∷ rw 5 ms1m-190 ∷ rw 3 ms1m-25 ∷ rw 4 ms1m-129 ∷
     rw 3 ms1m-59 ∷ rw 4 ms1m-59 ∷ rw 5 ms1m-59 ∷ rw 6 ms1m-33 ∷ rw 4 ms1m-138 ∷ rw 1 ms1m-152 ∷
     rw 0 ms1m-24 ∷ rw 3 ms1m-25 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-57 ∷ rw 0 ms1m-113 ∷ []) refl

ax-K0 : Eqn
ax-K0 = derive (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ [])
  (k₀ ∷ [])
  (rw 3 ms1m-57 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-31 ∷ rw 0 ms1m-57 ∷ rw 9 ms1m-17 ∷ rw 8 ms1m-60 ∷
     rw 7 ms1m-17 ∷ rw 6 ms1m-60 ∷ rw 5 ms1m-17 ∷ rw 10 ms1m-17 ∷ rw 9 ms1m-60 ∷ rw 8 ms1m-17 ∷
     rw 7 ms1m-60 ∷ rw 6 ms1m-17 ∷ rw 11 ms1m-17 ∷ rw 10 ms1m-60 ∷ rw 9 ms1m-17 ∷ rw 8 ms1m-60 ∷
     rw 7 ms1m-17 ∷ rw 4 ms1m-164 ∷ rw 1 ms1m-164 ∷ rw 0 ms1m-143 ∷ rw 9 ms1m-11 ∷ rw 8 ms1m-58 ∷
     rw 7 ms1m-11 ∷ rw 6 ms1m-58 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-57 ∷ rw 3 ms1m-31 ∷ rw 2 ms1m-31 ∷
     rw 1 ms1m-57 ∷ rw 0 ms1m-31 ∷ rw 14 ms1m-57 ∷ rw 13 ms1m-31 ∷ rw 12 ms1m-31 ∷ rw 11 ms1m-57 ∷
     rw 10 ms1m-11 ∷ rw 9 ms1m-58 ∷ rw 8 ms1m-11 ∷ rw 7 ms1m-58 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-57 ∷
     rw 4 ms1m-31 ∷ rw 3 ms1m-31 ∷ rw 2 ms1m-57 ∷ rw 1 ms1m-31 ∷ rw 11 ms1m-924 ∷ rw 10 ms1m-52 ∷
     rw 11 ms1m-60 ∷ rw 12 ms1m-60 ∷ rw 13 ms1m-52 ∷ rw 9 ms1m-952 ∷ rw 8 ms1m-52 ∷ rw 9 ms1m-60 ∷
     rw 10 ms1m-60 ∷ rw 11 ms1m-52 ∷ rw 12 ms1m-190 ∷ rw 7 ms1m-179 ∷ rw 8 ms1m-179 ∷ rw 9 ms1m-179 ∷
     rw 15 ms1m-129 ∷ rw 10 ms1m-174 ∷ rw 9 ms1m-59 ∷ rw 8 ms1m-59 ∷ rw 7 ms1m-59 ∷ rw 1 ms1m-162 ∷
     rw 7 ms1m-59 ∷ rw 6 ms1m-59 ∷ rw 5 ms1m-59 ∷ rw 9 ms1m-924 ∷ rw 8 ms1m-59 ∷ rw 7 ms1m-59 ∷
     rw 6 ms1m-59 ∷ rw 0 ms1m-162 ∷ rw 6 ms1m-33 ∷ rw 5 ms1m-33 ∷ rw 4 ms1m-33 ∷ rw 1 ms1m-164 ∷
     rw 7 ms1m-33 ∷ rw 6 ms1m-33 ∷ rw 5 ms1m-33 ∷ rw 2 ms1m-152 ∷ rw 0 ms1m-24 ∷ rw 4 ms1m-59 ∷
     rw 3 ms1m-59 ∷ rw 2 ms1m-59 ∷ rw 3 ms1m-25 ∷ rw 3 ms1m-60 ∷ rw 1 ms1m-138 ∷ rw 4 ms1m-60 ∷
     rw 2 ms1m-138 ∷ rw 5 ms1m-60 ∷ rw 3 ms1m-138 ∷ rw 0 ms1m-24 ∷ rw 2 ms1m-58 ∷ rw 1 ms1m-57 ∷
     rw 0 ms1m-57 ∷ rw 0 ms1m-113 ∷ []) refl

ax-aqa-C : Eqn
ax-aqa-C = derive (cs ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ [])
  (k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ cs ∷ k₀ ∷ cs ∷ k₀ ∷ cs ∷ s₁ ∷ s₁ ∷ s₁ ∷ ι ∷ k₁ ∷ cs ∷ cs ∷ k₁ ∷ ι ∷ cs ∷ [])
  (rw 4 ms1m-57 ∷ rw 3 ms1m-11 ∷ rw 2 ms1m-11 ∷ rw 1 ms1m-57 ∷ rw 0 ms1m-11 ∷ rw 1 ms1m-1322 ∷
     rw 9 ms1m-17 ∷ rw 8 ms1m-60 ∷ rw 7 ms1m-17 ∷ rw 6 ms1m-60 ∷ rw 10 ms1m-17 ∷ rw 9 ms1m-60 ∷
     rw 8 ms1m-17 ∷ rw 7 ms1m-60 ∷ rw 11 ms1m-17 ∷ rw 10 ms1m-60 ∷ rw 9 ms1m-17 ∷ rw 8 ms1m-60 ∷
     rw 5 ms1m-164 ∷ rw 4 ms1m-17 ∷ rw 3 ms1m-17 ∷ rw 2 ms1m-33 ∷ rw 12 ms1m-11 ∷ rw 11 ms1m-58 ∷
     rw 10 ms1m-11 ∷ rw 9 ms1m-58 ∷ rw 8 ms1m-57 ∷ rw 7 ms1m-31 ∷ rw 6 ms1m-57 ∷ rw 5 ms1m-11 ∷
     rw 4 ms1m-11 ∷ rw 3 ms1m-32 ∷ rw 2 ms1m-31 ∷ rw 1 ms1m-57 ∷ rw 17 ms1m-57 ∷ rw 16 ms1m-11 ∷
     rw 15 ms1m-11 ∷ rw 14 ms1m-57 ∷ rw 13 ms1m-11 ∷ rw 12 ms1m-58 ∷ rw 11 ms1m-11 ∷ rw 10 ms1m-58 ∷
     rw 9 ms1m-57 ∷ rw 8 ms1m-31 ∷ rw 7 ms1m-57 ∷ rw 6 ms1m-11 ∷ rw 5 ms1m-11 ∷ rw 4 ms1m-32 ∷
     rw 3 ms1m-31 ∷ rw 2 ms1m-57 ∷ rw 0 ms1m-131 ∷ rw 1 ms1m-138 ∷ rw 3 ms1m-1914 ∷ rw 0 ms1m-152 ∷
     rw 13 ms1m-59 ∷ rw 12 ms1m-52 ∷ rw⁻ 12 ms1m-52 ∷ rw⁻ 13 ms1m-1322 ∷ rw⁻ 2 ms1m-138 ∷ rw⁻ 1 ms1m-138 ∷
     rw⁻ 0 ms1m-138 ∷ rw⁻ 0 ms1m-131 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-31 ∷ rw⁻ 4 ms1m-31 ∷ rw⁻ 5 ms1m-11 ∷
     rw⁻ 6 ms1m-57 ∷ rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-11 ∷ rw⁻ 9 ms1m-57 ∷ rw⁻ 10 ms1m-58 ∷ rw⁻ 11 ms1m-11 ∷
     rw⁻ 12 ms1m-58 ∷ rw⁻ 13 ms1m-11 ∷ rw⁻ 14 ms1m-57 ∷ rw⁻ 15 ms1m-11 ∷ rw⁻ 16 ms1m-11 ∷ rw⁻ 17 ms1m-57 ∷
     rw⁻ 1 ms1m-31 ∷ rw⁻ 2 ms1m-31 ∷ rw⁻ 3 ms1m-31 ∷ rw⁻ 4 ms1m-11 ∷ rw⁻ 5 ms1m-57 ∷ rw⁻ 6 ms1m-11 ∷
     rw⁻ 7 ms1m-11 ∷ rw⁻ 8 ms1m-57 ∷ rw⁻ 9 ms1m-58 ∷ rw⁻ 10 ms1m-11 ∷ rw⁻ 11 ms1m-58 ∷ rw⁻ 12 ms1m-11 ∷
     rw⁻ 1 ms1m-1826 ∷ rw⁻ 2 ms1m-17 ∷ rw⁻ 3 ms1m-17 ∷ rw⁻ 4 ms1m-164 ∷ rw⁻ 7 ms1m-17 ∷ rw⁻ 8 ms1m-60 ∷
     rw⁻ 9 ms1m-17 ∷ rw⁻ 10 ms1m-60 ∷ rw⁻ 11 ms1m-17 ∷ rw⁻ 6 ms1m-17 ∷ rw⁻ 7 ms1m-60 ∷ rw⁻ 8 ms1m-17 ∷
     rw⁻ 9 ms1m-60 ∷ rw⁻ 10 ms1m-17 ∷ rw⁻ 5 ms1m-17 ∷ rw⁻ 6 ms1m-60 ∷ rw⁻ 7 ms1m-17 ∷ rw⁻ 8 ms1m-60 ∷
     rw⁻ 9 ms1m-17 ∷ rw⁻ 0 ms1m-57 ∷ rw⁻ 1 ms1m-11 ∷ rw⁻ 2 ms1m-11 ∷ rw⁻ 3 ms1m-57 ∷ []) refl

