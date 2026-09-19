------------------------------------------------------------------------
-- Presentations of groups
--
-- The derivable rules (Amy, Chen and Ross, Figure 2 and Lemma 5.2)
--
-- The existence of normal forms rests on commuting every diagonal gate
-- past every affine gate (Figure 2: 24 rules, "a tedious but
-- straightforward exercise") and on diagonal gates commuting with each
-- other (Lemma 5.2: four rules).  Each is derived here from the
-- relations R₁ … R₁₃, the laws of the symmetry and the structural
-- rules, with the associativity solvers doing the rebracketing.
--
-- Two families of lemmas carry the weight.  The naturality of the
-- symmetry extends from generators to whole circuits: a circuit on
-- the bottom k wires followed by the swaps that carry those wires up
-- by one is those swaps followed by the circuit shifted up (nat₁, nat₂,
-- nat₃); the gates on non-adjacent wires are then what naturality says
-- they are, and the swap rules of Figure 2 follow.  And the three CNOTs
-- on three wires generate a dihedral group of order 8 in which R₆ makes
-- CNOT₂₀ the commutator of the other two, hence central (I₆ … I₁₄);
-- that is what lets a CNOT pass a U or a V it shares a wire with.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT-Dihedral.Derived where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.CNOT-Dihedral.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Tools: the congruence at a width, its reasoning combinators, and the
-- associativity solvers

module Tools {X : Set} (Γ : WRel X) where
  open PB Γ public
    using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
  open PP Γ public using (word-setoid ; by-assoc)
  open PP.Pattern-Assoc Γ public using (by-passoc ; □)
  open SR word-setoid public

  -- Rewriting a subword in front, at the back, or in the middle.
  front : ∀ {a b} (s : Word X) → a ≈ b → a • s ≈ b • s
  front s e = cong e refl

  back : ∀ (p : Word X) {a b} → a ≈ b → p • a ≈ p • b
  back p e = cong refl e

  mid : ∀ (p : Word X) {a b} (s : Word X) → a ≈ b → p • a • s ≈ p • b • s
  mid p s e = cong refl (cong e refl)

-- The axioms, at the widths they are used.
private
  ax : ∀ {k} {w v : Circuit k} → k SRel, w === v → k ⊢ w ≈ v
  ax r = PB.axiom (srel r)

  ax↑ : ∀ {k} {w v : Circuit k} → k SRel, w === v → (₁₊ k) ⊢ w ↑ ≈ v ↑
  ax↑ r = PB.axiom (cong↑ (srel r))

  ax↑↑ : ∀ {k} {w v : Circuit k} → k SRel, w === v → (₂₊ k) ⊢ w ↑ ↑ ≈ v ↑ ↑
  ax↑↑ r = PB.axiom (cong↑ (cong↑ (srel r)))

------------------------------------------------------------------------
-- Cancelling CNOTs and swaps

CNOT²↑ : (₃₊ n) ⊢ CNOT ↑ • CNOT ↑ ≈ ε
CNOT²↑ = ax↑ R₄

CNOT²↑↑ : (₄₊ n) ⊢ CNOT ↑ ↑ • CNOT ↑ ↑ ≈ ε
CNOT²↑↑ = ax↑↑ R₄

SWAP²↑ : (₃₊ n) ⊢ SWAP ↑ • SWAP ↑ ≈ ε
SWAP²↑ = ax↑ swap-order

SWAP²↑↑ : (₄₊ n) ⊢ SWAP ↑ ↑ • SWAP ↑ ↑ ≈ ε
SWAP²↑↑ = ax↑↑ swap-order

------------------------------------------------------------------------
-- X and T past CNOT, from R₂, R₃, R₁₂ and R₄

-- X on the target commutes with CNOT.
CNOT-X : (₂₊ n) ⊢ CNOT • X ≈ X • CNOT
CNOT-X {n} = begin
  CNOT • X                    ≈⟨ sym right-unit ⟩
  (CNOT • X) • ε              ≈⟨ back _ (sym (ax R₄)) ⟩
  (CNOT • X) • (CNOT • CNOT)  ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • X • CNOT) • CNOT    ≈⟨ front _ (ax R₂) ⟩
  X • CNOT                    ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- X on the control passes CNOT and copies itself onto the target.
X↑-CNOT : (₂₊ n) ⊢ X ↑ • CNOT ≈ CNOT • X ↑ • X
X↑-CNOT {n} = begin
  X ↑ • CNOT                    ≈⟨ sym left-unit ⟩
  ε • X ↑ • CNOT                ≈⟨ front _ (sym (ax R₄)) ⟩
  (CNOT • CNOT) • X ↑ • CNOT    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (CNOT • X ↑ • CNOT)    ≈⟨ back _ (ax R₃) ⟩
  CNOT • X ↑ • X                ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- T on the control commutes with CNOT (Figure 2, CNOT and T).
CNOT-T↑ : (₂₊ n) ⊢ CNOT • T ↑ ≈ T ↑ • CNOT
CNOT-T↑ {n} = begin
  CNOT • T ↑                    ≈⟨ sym right-unit ⟩
  (CNOT • T ↑) • ε              ≈⟨ back _ (sym (ax R₄)) ⟩
  (CNOT • T ↑) • (CNOT • CNOT)  ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • T ↑ • CNOT) • CNOT    ≈⟨ front _ (ax R₁₂) ⟩
  T ↑ • CNOT                    ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- T on the target becomes U (Figure 2, CNOT and T, U).
CNOT-T : (₂₊ n) ⊢ CNOT • T ≈ U • CNOT
CNOT-T {n} = sym (begin
  U • CNOT                    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • (CNOT • CNOT)    ≈⟨ back _ (back _ (ax R₄)) ⟩
  CNOT • T • ε                ≈⟨ back _ right-unit ⟩
  CNOT • T                    ∎)
  where open Tools ((₂₊ n) VRel,_===_)

CNOT-U : (₂₊ n) ⊢ CNOT • U ≈ T • CNOT
CNOT-U {n} = begin
  CNOT • U                    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT) • T • CNOT    ≈⟨ front _ (ax R₄) ⟩
  ε • T • CNOT                ≈⟨ left-unit ⟩
  T • CNOT                    ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- U on the bottom wires and the upper CNOT: V (Figure 2, CNOT and U, V).
CNOT↑-U : (₃₊ n) ⊢ CNOT ↑ • U ≈ V • CNOT ↑
CNOT↑-U {n} = sym (begin
  V • CNOT ↑                            ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • U • (CNOT ↑ • CNOT ↑)        ≈⟨ back _ (back _ CNOT²↑) ⟩
  CNOT ↑ • U • ε                        ≈⟨ back _ right-unit ⟩
  CNOT ↑ • U                            ∎)
  where open Tools ((₃₊ n) VRel,_===_)

CNOT↑-V : (₃₊ n) ⊢ CNOT ↑ • V ≈ U • CNOT ↑
CNOT↑-V {n} = begin
  CNOT ↑ • V                            ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • CNOT ↑) • U • CNOT ↑        ≈⟨ front _ CNOT²↑ ⟩
  ε • U • CNOT ↑                        ≈⟨ left-unit ⟩
  U • CNOT ↑                            ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Powers of the derived gates: the CNOTs in between cancel

U-pow : ∀ k → (₂₊ n) ⊢ U ^ (₁₊ k) ≈ CNOT • T ^ (₁₊ k) • CNOT
U-pow {n} ₀ = refl
  where open Tools ((₂₊ n) VRel,_===_)
U-pow {n} (₁₊ k) = begin
  U • U ^ (₁₊ k)
    ≈⟨ back _ (U-pow k) ⟩
  U • (CNOT • T ^ (₁₊ k) • CNOT)
    ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  CNOT • T • (CNOT • CNOT) • T ^ (₁₊ k) • CNOT
    ≈⟨ back _ (back _ (front _ (ax R₄))) ⟩
  CNOT • T • ε • T ^ (₁₊ k) • CNOT
    ≈⟨ back _ (back _ left-unit) ⟩
  CNOT • T • T ^ (₁₊ k) • CNOT
    ≈⟨ by-passoc (□ • □ • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  CNOT • T ^ (₂₊ k) • CNOT ∎
  where open Tools ((₂₊ n) VRel,_===_)

V-pow : ∀ k → (₃₊ n) ⊢ V ^ (₁₊ k) ≈ CNOT ↑ • CNOT • T ^ (₁₊ k) • CNOT • CNOT ↑
V-pow {n} ₀ = refl
  where open Tools ((₃₊ n) VRel,_===_)
V-pow {n} (₁₊ k) = begin
  V • V ^ (₁₊ k)
    ≈⟨ back _ (V-pow k) ⟩
  V • (CNOT ↑ • CNOT • T ^ (₁₊ k) • CNOT • CNOT ↑)
    ≈⟨ by-passoc ((□ • □ • □ • □ • □) • (□ • □ • □ • □ • □))
                 (□ • □ • □ • □ • (□ • □) • □ • □ • □ • □) Eq.refl ⟩
  CNOT ↑ • CNOT • T • CNOT • (CNOT ↑ • CNOT ↑) • CNOT • T ^ (₁₊ k) • CNOT • CNOT ↑
    ≈⟨ back _ (back _ (back _ (back _ (front _ CNOT²↑)))) ⟩
  CNOT ↑ • CNOT • T • CNOT • ε • CNOT • T ^ (₁₊ k) • CNOT • CNOT ↑
    ≈⟨ back _ (back _ (back _ (back _ left-unit))) ⟩
  CNOT ↑ • CNOT • T • CNOT • CNOT • T ^ (₁₊ k) • CNOT • CNOT ↑
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □ • □) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
  CNOT ↑ • CNOT • T • (CNOT • CNOT) • T ^ (₁₊ k) • CNOT • CNOT ↑
    ≈⟨ back _ (back _ (back _ (front _ (ax R₄)))) ⟩
  CNOT ↑ • CNOT • T • ε • T ^ (₁₊ k) • CNOT • CNOT ↑
    ≈⟨ back _ (back _ (back _ left-unit)) ⟩
  CNOT ↑ • CNOT • T • T ^ (₁₊ k) • CNOT • CNOT ↑
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  CNOT ↑ • CNOT • T ^ (₂₊ k) • CNOT • CNOT ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- X past T (Figure 2, X and T), from R₁₁ and R₁

X-T : (₁₊ n) ⊢ X • T ≈ ω • T ^ 7 • X
X-T {n} = begin
  X • T                ≈⟨ sym right-unit ⟩
  (X • T) • ε          ≈⟨ back _ (sym (ax R₁)) ⟩
  (X • T) • (X • X)    ≈⟨ by-assoc Eq.refl ⟩
  (X • T • X) • X      ≈⟨ front _ (ax R₁₁) ⟩
  (ω • T ^ 7) • X      ≈⟨ by-assoc Eq.refl ⟩
  ω • T ^ 7 • X        ∎
  where open Tools ((₁₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Naturality of the symmetry, for whole circuits
--
-- The swaps σₖ carry the bottom k wires up by one.  A generator on the
-- bottom k wires followed by σₖ is σₖ followed by the generator shifted
-- up: for k = 1 this is swap-X, swap-T and the spatial law; for larger
-- k a generator on the very bottom commutes with the upper swaps and
-- meets the lower ones as before, and a shifted generator is the case
-- one wire down, shifted, followed by the commutation of a doubly
-- shifted generator with the bottom swap.  Words follow by induction.

-- ω is the same on every wire.
ω↑ : (₁₊ n) ⊢ ω ↑ ≈ ω
ω↑ = PB.axiom (ω↑=ω ω-gate)

ω↑↑ : (₂₊ n) ⊢ ω ↑ ↑ ≈ ω
ω↑↑ = PB.trans (lemma-cong↑ _ _ ω↑) ω↑

σ₁ : Circuit (₂₊ n)
σ₁ = SWAP

σ₂ : Circuit (₃₊ n)
σ₂ = SWAP ↑ • SWAP

σ₃ : Circuit (₄₊ n)
σ₃ = SWAP ↑ ↑ • SWAP ↑ • SWAP

nat₁-gen : (g : Gen 1) → (₂₊ n) ⊢ [ g ↧ᵏ (₁₊ n) ]ʷ • σ₁ ≈ σ₁ • [ (g ↥) ↧ᵏ n ]ʷ
nat₁-gen {n} ω-gen =
  trans (sym (comm-gate₀-w ω-gate SWAP)) (back SWAP (sym ω↑))
  where open Tools ((₂₊ n) VRel,_===_)
nat₁-gen X-gen = ax swap-X
nat₁-gen T-gen = ax swap-T
nat₁-gen {n} (ω-gen ↥) = begin
  ω ↑ • SWAP      ≈⟨ front _ ω↑ ⟩
  ω • SWAP        ≈⟨ sym (comm-gate₀-w ω-gate SWAP) ⟩
  SWAP • ω        ≈⟨ back _ (sym ω↑↑) ⟩
  SWAP • ω ↑ ↑    ∎
  where open Tools ((₂₊ n) VRel,_===_)

nat₂-gen : (g : Gen 2) → (₃₊ n) ⊢ [ g ↧ᵏ (₁₊ n) ]ʷ • σ₂ ≈ σ₂ • [ (g ↥) ↧ᵏ n ]ʷ
nat₂-gen {n} ω-gen =
  trans (sym (comm-gate₀-w ω-gate σ₂)) (back σ₂ (sym ω↑))
  where open Tools ((₃₊ n) VRel,_===_)
nat₂-gen {n} X-gen = begin
  X • SWAP ↑ • SWAP      ≈⟨ by-assoc Eq.refl ⟩
  (X • SWAP ↑) • SWAP    ≈⟨ front _ (sym (PB.axiom (comm₁ X-gate SWAP-gen))) ⟩
  (SWAP ↑ • X) • SWAP    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • (X • SWAP)    ≈⟨ back _ (ax swap-X) ⟩
  SWAP ↑ • (SWAP • X ↑)  ≈⟨ sym assoc ⟩
  σ₂ • X ↑               ∎
  where open Tools ((₃₊ n) VRel,_===_)
nat₂-gen {n} T-gen = begin
  T • SWAP ↑ • SWAP      ≈⟨ by-assoc Eq.refl ⟩
  (T • SWAP ↑) • SWAP    ≈⟨ front _ (sym (PB.axiom (comm₁ T-gate SWAP-gen))) ⟩
  (SWAP ↑ • T) • SWAP    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • (T • SWAP)    ≈⟨ back _ (ax swap-T) ⟩
  SWAP ↑ • (SWAP • T ↑)  ≈⟨ sym assoc ⟩
  σ₂ • T ↑               ∎
  where open Tools ((₃₊ n) VRel,_===_)
nat₂-gen {n} CNOT-gen = trans (ax swap-CNOT) (sym assoc)
  where open Tools ((₃₊ n) VRel,_===_)
nat₂-gen {n} SWAP-gen = trans (ax swap-braid) (sym assoc)
  where open Tools ((₃₊ n) VRel,_===_)
nat₂-gen {n} (g ↥) = begin
  [ (g ↧ᵏ (₁₊ n)) ↥ ]ʷ • SWAP ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  ([ g ↧ᵏ (₁₊ n) ]ʷ • SWAP) ↑ • SWAP
    ≈⟨ front _ (lemma-cong↑ _ _ (nat₁-gen g)) ⟩
  (SWAP • [ (g ↥) ↧ᵏ n ]ʷ) ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • ([ (g ↧ᵏ n) ↥ ↥ ]ʷ • SWAP)
    ≈⟨ back _ (PB.axiom (comm₂ SWAP-gate (g ↧ᵏ n))) ⟩
  SWAP ↑ • (SWAP • [ (g ↧ᵏ n) ↥ ↥ ]ʷ)
    ≈⟨ sym assoc ⟩
  σ₂ • [ (g ↧ᵏ n) ↥ ↥ ]ʷ ∎
  where open Tools ((₃₊ n) VRel,_===_)

nat₃-gen : (g : Gen 3) → (₄₊ n) ⊢ [ g ↧ᵏ (₁₊ n) ]ʷ • σ₃ ≈ σ₃ • [ (g ↥) ↧ᵏ n ]ʷ
nat₃-gen {n} ω-gen =
  trans (sym (comm-gate₀-w ω-gate σ₃)) (back σ₃ (sym ω↑))
  where open Tools ((₄₊ n) VRel,_===_)
nat₃-gen {n} (gate₁ h) = begin
  [ gate₁ h ]ʷ • SWAP ↑ ↑ • σ₂
    ≈⟨ by-assoc Eq.refl ⟩
  ([ gate₁ h ]ʷ • SWAP ↑ ↑) • σ₂
    ≈⟨ front _ (sym (PB.axiom (comm₁ h (SWAP-gen ↥)))) ⟩
  (SWAP ↑ ↑ • [ gate₁ h ]ʷ) • σ₂
    ≈⟨ assoc ⟩
  SWAP ↑ ↑ • ([ gate₁ h ]ʷ • σ₂)
    ≈⟨ back _ (nat₂-gen (gate₁ h)) ⟩
  SWAP ↑ ↑ • (σ₂ • [ gate₁ h ↥ ]ʷ)
    ≈⟨ by-assoc Eq.refl ⟩
  σ₃ • [ gate₁ h ↥ ]ʷ ∎
  where open Tools ((₄₊ n) VRel,_===_)
nat₃-gen {n} (gate₂ h) = begin
  [ gate₂ h ]ʷ • SWAP ↑ ↑ • σ₂
    ≈⟨ by-assoc Eq.refl ⟩
  ([ gate₂ h ]ʷ • SWAP ↑ ↑) • σ₂
    ≈⟨ front _ (sym (PB.axiom (comm₂ h SWAP-gen))) ⟩
  (SWAP ↑ ↑ • [ gate₂ h ]ʷ) • σ₂
    ≈⟨ assoc ⟩
  SWAP ↑ ↑ • ([ gate₂ h ]ʷ • σ₂)
    ≈⟨ back _ (nat₂-gen (gate₂ h)) ⟩
  SWAP ↑ ↑ • (σ₂ • [ gate₂ h ↥ ]ʷ)
    ≈⟨ by-assoc Eq.refl ⟩
  σ₃ • [ gate₂ h ↥ ]ʷ ∎
  where open Tools ((₄₊ n) VRel,_===_)
nat₃-gen {n} (g ↥) = begin
  [ (g ↧ᵏ (₁₊ n)) ↥ ]ʷ • SWAP ↑ ↑ • SWAP ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  ([ g ↧ᵏ (₁₊ n) ]ʷ • σ₂) ↑ • SWAP
    ≈⟨ front _ (lemma-cong↑ _ _ (nat₂-gen g)) ⟩
  (σ₂ • [ (g ↥) ↧ᵏ n ]ʷ) ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ ↑ • SWAP ↑ • ([ (g ↧ᵏ n) ↥ ↥ ]ʷ • SWAP)
    ≈⟨ back _ (back _ (PB.axiom (comm₂ SWAP-gate (g ↧ᵏ n)))) ⟩
  SWAP ↑ ↑ • SWAP ↑ • SWAP • [ (g ↧ᵏ n) ↥ ↥ ]ʷ
    ≈⟨ by-assoc Eq.refl ⟩
  σ₃ • [ (g ↧ᵏ n) ↥ ↥ ]ʷ ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- The three inductions on words.
nat₁ : (w : Circuit 1) → (₂₊ n) ⊢ (w ↓ᵏ (₁₊ n)) • σ₁ ≈ σ₁ • ((w ↑) ↓ᵏ n)
nat₁ [ g ]ʷ      = nat₁-gen g
nat₁ {n} ε       = trans left-unit (sym right-unit)
  where open Tools ((₂₊ n) VRel,_===_)
nat₁ {n} (w • v) = begin
  ((w ↓ᵏ (₁₊ n)) • (v ↓ᵏ (₁₊ n))) • σ₁     ≈⟨ assoc ⟩
  (w ↓ᵏ (₁₊ n)) • ((v ↓ᵏ (₁₊ n)) • σ₁)     ≈⟨ back _ (nat₁ v) ⟩
  (w ↓ᵏ (₁₊ n)) • (σ₁ • ((v ↑) ↓ᵏ n))      ≈⟨ sym assoc ⟩
  ((w ↓ᵏ (₁₊ n)) • σ₁) • ((v ↑) ↓ᵏ n)      ≈⟨ front _ (nat₁ w) ⟩
  (σ₁ • ((w ↑) ↓ᵏ n)) • ((v ↑) ↓ᵏ n)       ≈⟨ assoc ⟩
  σ₁ • (((w ↑) ↓ᵏ n) • ((v ↑) ↓ᵏ n))       ∎
  where open Tools ((₂₊ n) VRel,_===_)

nat₂ : (w : Circuit 2) → (₃₊ n) ⊢ (w ↓ᵏ (₁₊ n)) • σ₂ ≈ σ₂ • ((w ↑) ↓ᵏ n)
nat₂ [ g ]ʷ      = nat₂-gen g
nat₂ {n} ε       = trans left-unit (sym right-unit)
  where open Tools ((₃₊ n) VRel,_===_)
nat₂ {n} (w • v) = begin
  ((w ↓ᵏ (₁₊ n)) • (v ↓ᵏ (₁₊ n))) • σ₂     ≈⟨ assoc ⟩
  (w ↓ᵏ (₁₊ n)) • ((v ↓ᵏ (₁₊ n)) • σ₂)     ≈⟨ back _ (nat₂ v) ⟩
  (w ↓ᵏ (₁₊ n)) • (σ₂ • ((v ↑) ↓ᵏ n))      ≈⟨ sym assoc ⟩
  ((w ↓ᵏ (₁₊ n)) • σ₂) • ((v ↑) ↓ᵏ n)      ≈⟨ front _ (nat₂ w) ⟩
  (σ₂ • ((w ↑) ↓ᵏ n)) • ((v ↑) ↓ᵏ n)       ≈⟨ assoc ⟩
  σ₂ • (((w ↑) ↓ᵏ n) • ((v ↑) ↓ᵏ n))       ∎
  where open Tools ((₃₊ n) VRel,_===_)

nat₃ : (w : Circuit 3) → (₄₊ n) ⊢ (w ↓ᵏ (₁₊ n)) • σ₃ ≈ σ₃ • ((w ↑) ↓ᵏ n)
nat₃ [ g ]ʷ      = nat₃-gen g
nat₃ {n} ε       = trans left-unit (sym right-unit)
  where open Tools ((₄₊ n) VRel,_===_)
nat₃ {n} (w • v) = begin
  ((w ↓ᵏ (₁₊ n)) • (v ↓ᵏ (₁₊ n))) • σ₃     ≈⟨ assoc ⟩
  (w ↓ᵏ (₁₊ n)) • ((v ↓ᵏ (₁₊ n)) • σ₃)     ≈⟨ back _ (nat₃ v) ⟩
  (w ↓ᵏ (₁₊ n)) • (σ₃ • ((v ↑) ↓ᵏ n))      ≈⟨ sym assoc ⟩
  ((w ↓ᵏ (₁₊ n)) • σ₃) • ((v ↑) ↓ᵏ n)      ≈⟨ front _ (nat₃ w) ⟩
  (σ₃ • ((w ↑) ↓ᵏ n)) • ((v ↑) ↓ᵏ n)       ≈⟨ assoc ⟩
  σ₃ • (((w ↑) ↓ᵏ n) • ((v ↑) ↓ᵏ n))       ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- The derived gates, moved up: the words padded from their own width
-- are the polymorphic words, so these are instances.
nat-U : (₃₊ n) ⊢ U • σ₂ ≈ σ₂ • U ↑
nat-U = nat₂ (CNOT • T • CNOT)

nat-V : (₄₊ n) ⊢ V • σ₃ ≈ σ₃ • V ↑
nat-V = nat₃ (CNOT ↑ • CNOT • T • CNOT • CNOT ↑)

------------------------------------------------------------------------
-- Conjugating by a swap

-- T moved up a wire and back (the two swap rules for T of Figure 2).
conj-T : (₂₊ n) ⊢ SWAP • T • SWAP ≈ T ↑
conj-T {n} = begin
  SWAP • T • SWAP          ≈⟨ back _ (ax swap-T) ⟩
  SWAP • (SWAP • T ↑)      ≈⟨ sym assoc ⟩
  (SWAP • SWAP) • T ↑      ≈⟨ front _ (ax swap-order) ⟩
  ε • T ↑                  ≈⟨ left-unit ⟩
  T ↑                      ∎
  where open Tools ((₂₊ n) VRel,_===_)

SWAP-T : (₂₊ n) ⊢ SWAP • T ≈ T ↑ • SWAP
SWAP-T {n} = begin
  SWAP • T                    ≈⟨ sym right-unit ⟩
  (SWAP • T) • ε              ≈⟨ back _ (sym (ax swap-order)) ⟩
  (SWAP • T) • (SWAP • SWAP)  ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • T • SWAP) • SWAP    ≈⟨ front _ conj-T ⟩
  T ↑ • SWAP                  ∎
  where open Tools ((₂₊ n) VRel,_===_)

SWAP-T↑ : (₂₊ n) ⊢ SWAP • T ↑ ≈ T • SWAP
SWAP-T↑ {n} = sym (ax swap-T)
  where open Tools ((₂₊ n) VRel,_===_)

T↑-SWAP : (₂₊ n) ⊢ T ↑ • SWAP ≈ SWAP • T
T↑-SWAP {n} = sym SWAP-T
  where open Tools ((₂₊ n) VRel,_===_)

-- CNOT₂₀ and the swap that defines it.
SWAP-CNOT₂₀ : (₃₊ n) ⊢ SWAP • CNOT₂₀ ≈ CNOT ↑ • SWAP
SWAP-CNOT₂₀ {n} = begin
  SWAP • CNOT₂₀                     ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • SWAP) • CNOT ↑ • SWAP     ≈⟨ front _ (ax swap-order) ⟩
  ε • CNOT ↑ • SWAP                 ≈⟨ left-unit ⟩
  CNOT ↑ • SWAP                     ∎
  where open Tools ((₃₊ n) VRel,_===_)

CNOT₂₀-SWAP : (₃₊ n) ⊢ CNOT₂₀ • SWAP ≈ SWAP • CNOT ↑
CNOT₂₀-SWAP {n} = begin
  CNOT₂₀ • SWAP                     ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT ↑ • (SWAP • SWAP)     ≈⟨ back _ (back _ (ax swap-order)) ⟩
  SWAP • CNOT ↑ • ε                 ≈⟨ back _ right-unit ⟩
  SWAP • CNOT ↑                     ∎
  where open Tools ((₃₊ n) VRel,_===_)

CNOT₂₀² : (₃₊ n) ⊢ CNOT₂₀ • CNOT₂₀ ≈ ε
CNOT₂₀² {n} = begin
  CNOT₂₀ • CNOT₂₀                                 ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT ↑ • (SWAP • SWAP) • CNOT ↑ • SWAP   ≈⟨ back _ (back _ (front _ (ax swap-order))) ⟩
  SWAP • CNOT ↑ • ε • CNOT ↑ • SWAP               ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (CNOT ↑ • CNOT ↑) • SWAP                 ≈⟨ back _ (front _ CNOT²↑) ⟩
  SWAP • ε • SWAP                                 ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP                                     ≈⟨ ax swap-order ⟩
  ε                                               ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- R₅ in the two forms used: a swap passes a CNOT, and back.
SWAP-CNOT : (₂₊ n) ⊢ SWAP • CNOT ≈ CNOT • SWAP • CNOT • SWAP
SWAP-CNOT {n} = begin
  SWAP • CNOT
    ≈⟨ front _ (ax R₅) ⟩
  (CNOT • SWAP • CNOT • SWAP • CNOT) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CNOT • SWAP • (CNOT • CNOT)
    ≈⟨ back _ (back _ (back _ (back _ (ax R₄)))) ⟩
  CNOT • SWAP • CNOT • SWAP • ε
    ≈⟨ back _ (back _ (back _ right-unit)) ⟩
  CNOT • SWAP • CNOT • SWAP ∎
  where open Tools ((₂₊ n) VRel,_===_)

SCSC : (₂₊ n) ⊢ SWAP • CNOT • SWAP • CNOT ≈ CNOT • SWAP
SCSC {n} = sym (begin
  CNOT • SWAP
    ≈⟨ back _ (ax R₅) ⟩
  CNOT • (CNOT • SWAP • CNOT • SWAP • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT) • SWAP • CNOT • SWAP • CNOT
    ≈⟨ front _ (ax R₄) ⟩
  ε • SWAP • CNOT • SWAP • CNOT
    ≈⟨ left-unit ⟩
  SWAP • CNOT • SWAP • CNOT ∎)
  where open Tools ((₂₊ n) VRel,_===_)

------------------------------------------------------------------------
-- The dihedral group of the three CNOTs (R₆)
--
-- CNOT₂₀ is the commutator of CNOT and CNOT ↑ (R₆), and has order 2, so
-- (CNOT · CNOT ↑)⁴ = 1: the three generate a dihedral group of order 8
-- in which the commutator is central.

-- R₆ rearranged.
CC≈C₂₀CC : (₃₊ n) ⊢ CNOT • CNOT ↑ ≈ CNOT₂₀ • CNOT ↑ • CNOT
CC≈C₂₀CC {n} = sym (begin
  CNOT₂₀ • CNOT ↑ • CNOT
    ≈⟨ front _ (ax R₆) ⟩
  (CNOT • CNOT ↑ • CNOT • CNOT ↑) • CNOT ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CNOT ↑ • CNOT • (CNOT ↑ • CNOT ↑) • CNOT
    ≈⟨ back _ (back _ (back _ (front _ CNOT²↑))) ⟩
  CNOT • CNOT ↑ • CNOT • ε • CNOT
    ≈⟨ back _ (back _ (back _ left-unit)) ⟩
  CNOT • CNOT ↑ • CNOT • CNOT
    ≈⟨ back _ (back _ (ax R₄)) ⟩
  CNOT • CNOT ↑ • ε
    ≈⟨ back _ right-unit ⟩
  CNOT • CNOT ↑ ∎)
  where open Tools ((₃₊ n) VRel,_===_)

CCC≈C₂₀C : (₃₊ n) ⊢ CNOT • CNOT ↑ • CNOT ≈ CNOT₂₀ • CNOT ↑
CCC≈C₂₀C {n} = sym (begin
  CNOT₂₀ • CNOT ↑
    ≈⟨ front _ (ax R₆) ⟩
  (CNOT • CNOT ↑ • CNOT • CNOT ↑) • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CNOT ↑ • CNOT • (CNOT ↑ • CNOT ↑)
    ≈⟨ back _ (back _ (back _ CNOT²↑)) ⟩
  CNOT • CNOT ↑ • CNOT • ε
    ≈⟨ back _ (back _ right-unit) ⟩
  CNOT • CNOT ↑ • CNOT ∎)
  where open Tools ((₃₊ n) VRel,_===_)

-- (CNOT · CNOT ↑)⁴ = 1.
CC⁴ : (₃₊ n) ⊢ (CNOT • CNOT ↑) ^ 4 ≈ ε
CC⁴ {n} = begin
  (CNOT • CNOT ↑) ^ 4
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT ↑ • CNOT • CNOT ↑) • (CNOT • CNOT ↑ • CNOT • CNOT ↑)
    ≈⟨ cong (sym (ax R₆)) (sym (ax R₆)) ⟩
  CNOT₂₀ • CNOT₂₀
    ≈⟨ CNOT₂₀² ⟩
  ε ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- Hence (CNOT ↑ · CNOT)² = (CNOT · CNOT ↑)²: both are the commutator.
braid-CNOT : (₃₊ n) ⊢ CNOT ↑ • CNOT • CNOT ↑ • CNOT ≈ CNOT • CNOT ↑ • CNOT • CNOT ↑
braid-CNOT {n} = begin
  CNOT ↑ • CNOT • CNOT ↑ • CNOT
    ≈⟨ sym right-unit ⟩
  (CNOT ↑ • CNOT • CNOT ↑ • CNOT) • ε
    ≈⟨ back _ (sym CC⁴) ⟩
  (CNOT ↑ • CNOT • CNOT ↑ • CNOT) • (CNOT • CNOT ↑) ^ 4
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • CNOT • CNOT ↑ • (CNOT • CNOT) • CNOT ↑ • CNOT • CNOT ↑ • CNOT • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ back _ (back _ (back _ (front _ (ax R₄)))) ⟩
  CNOT ↑ • CNOT • CNOT ↑ • ε • CNOT ↑ • CNOT • CNOT ↑ • CNOT • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • CNOT • (CNOT ↑ • CNOT ↑) • CNOT • CNOT ↑ • CNOT • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ back _ (back _ (front _ CNOT²↑)) ⟩
  CNOT ↑ • CNOT • ε • CNOT • CNOT ↑ • CNOT • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (CNOT • CNOT) • CNOT ↑ • CNOT • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ back _ (front _ (ax R₄)) ⟩
  CNOT ↑ • ε • CNOT ↑ • CNOT • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • CNOT ↑) • CNOT • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ front _ CNOT²↑ ⟩
  ε • CNOT • CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ left-unit ⟩
  CNOT • CNOT ↑ • CNOT • CNOT ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- The commutator is central: it commutes with CNOT ↑ …
CNOT↑-CNOT₂₀ : (₃₊ n) ⊢ CNOT ↑ • CNOT₂₀ ≈ CNOT₂₀ • CNOT ↑
CNOT↑-CNOT₂₀ {n} = begin
  CNOT ↑ • CNOT₂₀
    ≈⟨ back _ (ax R₆) ⟩
  CNOT ↑ • (CNOT • CNOT ↑ • CNOT • CNOT ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • CNOT • CNOT ↑ • CNOT) • CNOT ↑
    ≈⟨ front _ braid-CNOT ⟩
  (CNOT • CNOT ↑ • CNOT • CNOT ↑) • CNOT ↑
    ≈⟨ front _ (sym (ax R₆)) ⟩
  CNOT₂₀ • CNOT ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- … and with T on wire 1, which is off its wires.
T↑-CNOT₂₀ : (₃₊ n) ⊢ T ↑ • CNOT₂₀ ≈ CNOT₂₀ • T ↑
T↑-CNOT₂₀ {n} = begin
  T ↑ • CNOT₂₀                     ≈⟨ by-assoc Eq.refl ⟩
  (T ↑ • SWAP) • CNOT ↑ • SWAP     ≈⟨ front _ T↑-SWAP ⟩
  (SWAP • T) • CNOT ↑ • SWAP       ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (T • CNOT ↑) • SWAP       ≈⟨ mid _ _ (sym (PB.axiom (comm₁ T-gate CNOT-gen))) ⟩
  SWAP • (CNOT ↑ • T) • SWAP       ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT ↑ • (T • SWAP)       ≈⟨ back _ (back _ (ax swap-T)) ⟩
  SWAP • CNOT ↑ • (SWAP • T ↑)     ≈⟨ by-assoc Eq.refl ⟩
  CNOT₂₀ • T ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- So CNOT₂₀ commutes with U on the upper wires, and CNOT ↑ with U on
-- wires 0 and 2.
CNOT₂₀-U↑ : (₃₊ n) ⊢ CNOT₂₀ • U ↑ ≈ U ↑ • CNOT₂₀
CNOT₂₀-U↑ {n} = begin
  CNOT₂₀ • U ↑                          ≈⟨ by-assoc Eq.refl ⟩
  (CNOT₂₀ • CNOT ↑) • T ↑ • CNOT ↑      ≈⟨ front _ (sym CNOT↑-CNOT₂₀) ⟩
  (CNOT ↑ • CNOT₂₀) • T ↑ • CNOT ↑      ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (CNOT₂₀ • T ↑) • CNOT ↑      ≈⟨ mid _ _ (sym T↑-CNOT₂₀) ⟩
  CNOT ↑ • (T ↑ • CNOT₂₀) • CNOT ↑      ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • T ↑ • (CNOT₂₀ • CNOT ↑)      ≈⟨ back _ (back _ (sym CNOT↑-CNOT₂₀)) ⟩
  CNOT ↑ • T ↑ • (CNOT ↑ • CNOT₂₀)      ≈⟨ by-assoc Eq.refl ⟩
  U ↑ • CNOT₂₀ ∎
  where open Tools ((₃₊ n) VRel,_===_)

CNOT↑-U₀₂ : (₃₊ n) ⊢ CNOT ↑ • U₀₂ ≈ U₀₂ • CNOT ↑
CNOT↑-U₀₂ {n} = begin
  CNOT ↑ • U₀₂                        ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • SWAP) • U ↑ • SWAP        ≈⟨ front _ (sym SWAP-CNOT₂₀) ⟩
  (SWAP • CNOT₂₀) • U ↑ • SWAP        ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (CNOT₂₀ • U ↑) • SWAP        ≈⟨ mid _ _ CNOT₂₀-U↑ ⟩
  SWAP • (U ↑ • CNOT₂₀) • SWAP        ≈⟨ by-assoc Eq.refl ⟩
  SWAP • U ↑ • (CNOT₂₀ • SWAP)        ≈⟨ back _ (back _ CNOT₂₀-SWAP) ⟩
  SWAP • U ↑ • (SWAP • CNOT ↑)        ≈⟨ by-assoc Eq.refl ⟩
  U₀₂ • CNOT ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Commuting past powers, and a few more commutations

-- A word that commutes with w commutes with its powers.
pow-comm : ∀ {X : Set} {Γ : WRel X} {a w : Word X} →
           let open PB Γ in a • w ≈ w • a → ∀ k → a • w ^ k ≈ w ^ k • a
pow-comm {Γ = Γ} e ₀ = trans right-unit (sym left-unit)
  where open Tools Γ
pow-comm {Γ = Γ} e (₁₊ ₀) = e
pow-comm {Γ = Γ} {a} {w} e (₂₊ k) = begin
  a • (w • w ^ (₁₊ k))     ≈⟨ sym assoc ⟩
  (a • w) • w ^ (₁₊ k)     ≈⟨ front _ e ⟩
  (w • a) • w ^ (₁₊ k)     ≈⟨ assoc ⟩
  w • (a • w ^ (₁₊ k))     ≈⟨ back _ (pow-comm e (₁₊ k)) ⟩
  w • (w ^ (₁₊ k) • a)     ≈⟨ sym assoc ⟩
  (w • w ^ (₁₊ k)) • a     ∎
  where open Tools Γ

X↑-Tᵏ : ∀ k → (₂₊ n) ⊢ X ↑ • T ^ k ≈ T ^ k • X ↑
X↑-Tᵏ = pow-comm (PB.axiom (comm₁ T-gate X-gen))

-- X on wire 2 commutes with U on wires 0 and 1.
X↑↑-U : (₃₊ n) ⊢ X ↑ ↑ • U ≈ U • X ↑ ↑
X↑↑-U {n} = begin
  X ↑ ↑ • U                    ≈⟨ by-assoc Eq.refl ⟩
  (X ↑ ↑ • CNOT) • T • CNOT    ≈⟨ front _ (PB.axiom (comm₂ CNOT-gate X-gen)) ⟩
  (CNOT • X ↑ ↑) • T • CNOT    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (X ↑ ↑ • T) • CNOT    ≈⟨ mid _ _ (PB.axiom (comm₁ T-gate (X-gen ↥))) ⟩
  CNOT • (T • X ↑ ↑) • CNOT    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • (X ↑ ↑ • CNOT)    ≈⟨ back _ (back _ (PB.axiom (comm₂ CNOT-gate X-gen))) ⟩
  CNOT • T • (CNOT • X ↑ ↑)    ≈⟨ by-assoc Eq.refl ⟩
  U • X ↑ ↑                    ∎
  where open Tools ((₃₊ n) VRel,_===_)

X↑↑-Uᵏ : ∀ k → (₃₊ n) ⊢ X ↑ ↑ • U ^ k ≈ U ^ k • X ↑ ↑
X↑↑-Uᵏ = pow-comm X↑↑-U

-- X on both wires, then CNOT: the target's X cancels.
X↑X-CNOT : (₂₊ n) ⊢ X ↑ • X • CNOT ≈ CNOT • X ↑
X↑X-CNOT {n} = begin
  X ↑ • X • CNOT              ≈⟨ back _ (sym CNOT-X) ⟩
  X ↑ • (CNOT • X)            ≈⟨ sym assoc ⟩
  (X ↑ • CNOT) • X            ≈⟨ front _ X↑-CNOT ⟩
  (CNOT • X ↑ • X) • X        ≈⟨ by-assoc Eq.refl ⟩
  CNOT • X ↑ • (X • X)        ≈⟨ back _ (back _ (ax R₁)) ⟩
  CNOT • X ↑ • ε              ≈⟨ back _ right-unit ⟩
  CNOT • X ↑                  ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- The X–CNOT rules one wire up.
X↑-CNOT↑ : (₃₊ n) ⊢ X ↑ ↑ • CNOT ↑ ≈ CNOT ↑ • X ↑ ↑ • X ↑
X↑-CNOT↑ = lemma-cong↑ (X ↑ • CNOT) (CNOT • X ↑ • X) X↑-CNOT

X↑X-CNOT↑ : (₃₊ n) ⊢ X ↑ ↑ • X ↑ • CNOT ↑ ≈ CNOT ↑ • X ↑ ↑
X↑X-CNOT↑ = lemma-cong↑ (X ↑ • X • CNOT) (CNOT • X ↑) X↑X-CNOT

X↑-CNOT↑′ : (₃₊ n) ⊢ X ↑ • CNOT ↑ ≈ CNOT ↑ • X ↑
X↑-CNOT↑′ {n} = lemma-cong↑ (X • CNOT) (CNOT • X) (sym CNOT-X)
  where open Tools ((₂₊ n) VRel,_===_)

-- V⁷ through U⁷.
V⁷ : (₃₊ n) ⊢ V ^ 7 ≈ CNOT ↑ • U ^ 7 • CNOT ↑
V⁷ {n} = begin
  V ^ 7                                       ≈⟨ V-pow 6 ⟩
  CNOT ↑ • CNOT • T ^ 7 • CNOT • CNOT ↑       ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (CNOT • T ^ 7 • CNOT) • CNOT ↑     ≈⟨ mid _ _ (sym (U-pow 6)) ⟩
  CNOT ↑ • U ^ 7 • CNOT ↑                     ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Figure 2, first row: X past a diagonal gate

X↑-U : (₂₊ n) ⊢ X ↑ • U ≈ ω • U ^ 7 • X ↑
X↑-U {n} = begin
  X ↑ • U
    ≈⟨ by-assoc Eq.refl ⟩
  (X ↑ • CNOT) • T • CNOT
    ≈⟨ front _ X↑-CNOT ⟩
  (CNOT • X ↑ • X) • T • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • X ↑ • (X • T) • CNOT
    ≈⟨ back _ (mid _ _ X-T) ⟩
  CNOT • X ↑ • (ω • T ^ 7 • X) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  ((CNOT • X ↑) • ω) • (T ^ 7 • X • CNOT)
    ≈⟨ front _ (comm-gate₀-w ω-gate (CNOT • X ↑)) ⟩
  (ω • (CNOT • X ↑)) • (T ^ 7 • X • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • CNOT • (X ↑ • T ^ 7) • (X • CNOT)
    ≈⟨ back _ (mid _ _ (X↑-Tᵏ 7)) ⟩
  ω • CNOT • (T ^ 7 • X ↑) • (X • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • CNOT • T ^ 7 • (X ↑ • X • CNOT)
    ≈⟨ back _ (back _ (back _ X↑X-CNOT)) ⟩
  ω • CNOT • T ^ 7 • (CNOT • X ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • (CNOT • T ^ 7 • CNOT) • X ↑
    ≈⟨ back _ (front _ (sym (U-pow 6))) ⟩
  ω • U ^ 7 • X ↑ ∎
  where open Tools ((₂₊ n) VRel,_===_)

X-U : (₂₊ n) ⊢ X • U ≈ ω • U ^ 7 • X
X-U {n} = begin
  X • U
    ≈⟨ by-assoc Eq.refl ⟩
  (X • CNOT) • T • CNOT
    ≈⟨ front _ (sym CNOT-X) ⟩
  (CNOT • X) • T • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (X • T) • CNOT
    ≈⟨ mid _ _ X-T ⟩
  CNOT • (ω • T ^ 7 • X) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • ω) • (T ^ 7 • X • CNOT)
    ≈⟨ front _ (comm-gate₀-w ω-gate CNOT) ⟩
  (ω • CNOT) • (T ^ 7 • X • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • CNOT • T ^ 7 • (X • CNOT)
    ≈⟨ back _ (back _ (back _ (sym CNOT-X))) ⟩
  ω • CNOT • T ^ 7 • (CNOT • X)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • (CNOT • T ^ 7 • CNOT) • X
    ≈⟨ back _ (front _ (sym (U-pow 6))) ⟩
  ω • U ^ 7 • X ∎
  where open Tools ((₂₊ n) VRel,_===_)

X↑↑-V : (₃₊ n) ⊢ X ↑ ↑ • V ≈ ω • V ^ 7 • X ↑ ↑
X↑↑-V {n} = begin
  X ↑ ↑ • V
    ≈⟨ by-assoc Eq.refl ⟩
  (X ↑ ↑ • CNOT ↑) • U • CNOT ↑
    ≈⟨ front _ X↑-CNOT↑ ⟩
  (CNOT ↑ • X ↑ ↑ • X ↑) • U • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • X ↑ ↑ • (X ↑ • U) • CNOT ↑
    ≈⟨ back _ (mid _ _ X↑-U) ⟩
  CNOT ↑ • X ↑ ↑ • (ω • U ^ 7 • X ↑) • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  ((CNOT ↑ • X ↑ ↑) • ω) • (U ^ 7 • X ↑ • CNOT ↑)
    ≈⟨ front _ (comm-gate₀-w ω-gate (CNOT ↑ • X ↑ ↑)) ⟩
  (ω • (CNOT ↑ • X ↑ ↑)) • (U ^ 7 • X ↑ • CNOT ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • CNOT ↑ • (X ↑ ↑ • U ^ 7) • (X ↑ • CNOT ↑)
    ≈⟨ back _ (mid _ _ (X↑↑-Uᵏ 7)) ⟩
  ω • CNOT ↑ • (U ^ 7 • X ↑ ↑) • (X ↑ • CNOT ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • CNOT ↑ • U ^ 7 • (X ↑ ↑ • X ↑ • CNOT ↑)
    ≈⟨ back _ (back _ (back _ X↑X-CNOT↑)) ⟩
  ω • CNOT ↑ • U ^ 7 • (CNOT ↑ • X ↑ ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • (CNOT ↑ • U ^ 7 • CNOT ↑) • X ↑ ↑
    ≈⟨ back _ (front _ (sym V⁷)) ⟩
  ω • V ^ 7 • X ↑ ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

X↑-V : (₃₊ n) ⊢ X ↑ • V ≈ ω • V ^ 7 • X ↑
X↑-V {n} = begin
  X ↑ • V
    ≈⟨ by-assoc Eq.refl ⟩
  (X ↑ • CNOT ↑) • U • CNOT ↑
    ≈⟨ front _ X↑-CNOT↑′ ⟩
  (CNOT ↑ • X ↑) • U • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (X ↑ • U) • CNOT ↑
    ≈⟨ mid _ _ X↑-U ⟩
  CNOT ↑ • (ω • U ^ 7 • X ↑) • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • ω) • (U ^ 7 • X ↑ • CNOT ↑)
    ≈⟨ front _ (comm-gate₀-w ω-gate (CNOT ↑)) ⟩
  (ω • CNOT ↑) • (U ^ 7 • X ↑ • CNOT ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • CNOT ↑ • U ^ 7 • (X ↑ • CNOT ↑)
    ≈⟨ back _ (back _ (back _ X↑-CNOT↑′)) ⟩
  ω • CNOT ↑ • U ^ 7 • (CNOT ↑ • X ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • (CNOT ↑ • U ^ 7 • CNOT ↑) • X ↑
    ≈⟨ back _ (front _ (sym V⁷)) ⟩
  ω • V ^ 7 • X ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

X-V : (₃₊ n) ⊢ X • V ≈ ω • V ^ 7 • X
X-V {n} = begin
  X • V
    ≈⟨ by-assoc Eq.refl ⟩
  (X • CNOT ↑) • U • CNOT ↑
    ≈⟨ front _ (sym (PB.axiom (comm₁ X-gate CNOT-gen))) ⟩
  (CNOT ↑ • X) • U • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (X • U) • CNOT ↑
    ≈⟨ mid _ _ X-U ⟩
  CNOT ↑ • (ω • U ^ 7 • X) • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • ω) • (U ^ 7 • X • CNOT ↑)
    ≈⟨ front _ (comm-gate₀-w ω-gate (CNOT ↑)) ⟩
  (ω • CNOT ↑) • (U ^ 7 • X • CNOT ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • CNOT ↑ • U ^ 7 • (X • CNOT ↑)
    ≈⟨ back _ (back _ (back _ (sym (PB.axiom (comm₁ X-gate CNOT-gen))))) ⟩
  ω • CNOT ↑ • U ^ 7 • (CNOT ↑ • X)
    ≈⟨ by-assoc Eq.refl ⟩
  ω • (CNOT ↑ • U ^ 7 • CNOT ↑) • X
    ≈⟨ back _ (front _ (sym V⁷)) ⟩
  ω • V ^ 7 • X ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Figure 2, second row: CNOT past a diagonal gate
--
-- CNOT-T↑, CNOT-T, CNOT-U, CNOT↑-U and CNOT↑-V are above.

-- The lower CNOT and U on the upper wires: they share the control.
CNOT-U↑ : (₃₊ n) ⊢ CNOT • U ↑ ≈ U ↑ • CNOT
CNOT-U↑ {n} = begin
  CNOT • U ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT ↑) • T ↑ • CNOT ↑
    ≈⟨ front _ CC≈C₂₀CC ⟩
  (CNOT₂₀ • CNOT ↑ • CNOT) • T ↑ • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT₂₀ • CNOT ↑ • (CNOT • T ↑) • CNOT ↑
    ≈⟨ back _ (back _ (front _ CNOT-T↑)) ⟩
  CNOT₂₀ • CNOT ↑ • (T ↑ • CNOT) • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT₂₀ • CNOT ↑ • T ↑ • (CNOT • CNOT ↑)
    ≈⟨ back _ (back _ (back _ CC≈C₂₀CC)) ⟩
  CNOT₂₀ • CNOT ↑ • T ↑ • (CNOT₂₀ • CNOT ↑ • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT₂₀ • CNOT ↑ • (T ↑ • CNOT₂₀) • CNOT ↑ • CNOT
    ≈⟨ back _ (back _ (front _ T↑-CNOT₂₀)) ⟩
  CNOT₂₀ • CNOT ↑ • (CNOT₂₀ • T ↑) • CNOT ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT₂₀ • (CNOT ↑ • CNOT₂₀) • T ↑ • CNOT ↑ • CNOT
    ≈⟨ back _ (front _ CNOT↑-CNOT₂₀) ⟩
  CNOT₂₀ • (CNOT₂₀ • CNOT ↑) • T ↑ • CNOT ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT₂₀ • CNOT₂₀) • CNOT ↑ • T ↑ • CNOT ↑ • CNOT
    ≈⟨ front _ CNOT₂₀² ⟩
  ε • CNOT ↑ • T ↑ • CNOT ↑ • CNOT
    ≈⟨ left-unit ⟩
  CNOT ↑ • T ↑ • CNOT ↑ • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  U ↑ • CNOT ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- The other three-CNOT identity, and CNOT₂₀ conjugating T into U₀₂.
C↑CC↑ : (₃₊ n) ⊢ CNOT ↑ • CNOT • CNOT ↑ ≈ CNOT₂₀ • CNOT
C↑CC↑ {n} = begin
  CNOT ↑ • CNOT • CNOT ↑
    ≈⟨ sym right-unit ⟩
  (CNOT ↑ • CNOT • CNOT ↑) • ε
    ≈⟨ back _ (sym (ax R₄)) ⟩
  (CNOT ↑ • CNOT • CNOT ↑) • (CNOT • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ • CNOT • CNOT ↑ • CNOT) • CNOT
    ≈⟨ front _ braid-CNOT ⟩
  (CNOT • CNOT ↑ • CNOT • CNOT ↑) • CNOT
    ≈⟨ front _ (sym (ax R₆)) ⟩
  CNOT₂₀ • CNOT ∎
  where open Tools ((₃₊ n) VRel,_===_)

C₂₀TC₂₀ : (₃₊ n) ⊢ CNOT₂₀ • T • CNOT₂₀ ≈ U₀₂
C₂₀TC₂₀ {n} = begin
  CNOT₂₀ • T • CNOT₂₀
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT ↑ • (SWAP • T • SWAP) • CNOT ↑ • SWAP
    ≈⟨ back _ (back _ (front _ conj-T)) ⟩
  SWAP • CNOT ↑ • T ↑ • CNOT ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  U₀₂ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- The lower CNOT and V.
CNOT-V : (₃₊ n) ⊢ CNOT • V ≈ U₀₂ • CNOT
CNOT-V {n} = begin
  CNOT • V
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT ↑ • CNOT) • T • CNOT • CNOT ↑
    ≈⟨ front _ CCC≈C₂₀C ⟩
  (CNOT₂₀ • CNOT ↑) • T • CNOT • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT₂₀ • (CNOT ↑ • T) • CNOT • CNOT ↑
    ≈⟨ back _ (front _ (PB.axiom (comm₁ T-gate CNOT-gen))) ⟩
  CNOT₂₀ • (T • CNOT ↑) • CNOT • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT₂₀ • T • (CNOT ↑ • CNOT • CNOT ↑)
    ≈⟨ back _ (back _ C↑CC↑) ⟩
  CNOT₂₀ • T • (CNOT₂₀ • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT₂₀ • T • CNOT₂₀) • CNOT
    ≈⟨ front _ C₂₀TC₂₀ ⟩
  U₀₂ • CNOT ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- The lower CNOT and V on the upper wires: off its wires but for the
-- control, which U ↑ tolerates.
CNOT-V↑ : (₄₊ n) ⊢ CNOT • V ↑ ≈ V ↑ • CNOT
CNOT-V↑ {n} = begin
  CNOT • V ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • CNOT ↑ ↑) • U ↑ • CNOT ↑ ↑
    ≈⟨ front _ (sym (PB.axiom (comm₂ CNOT-gate CNOT-gen))) ⟩
  (CNOT ↑ ↑ • CNOT) • U ↑ • CNOT ↑ ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ ↑ • (CNOT • U ↑) • CNOT ↑ ↑
    ≈⟨ mid _ _ CNOT-U↑ ⟩
  CNOT ↑ ↑ • (U ↑ • CNOT) • CNOT ↑ ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ ↑ • U ↑ • (CNOT • CNOT ↑ ↑)
    ≈⟨ back _ (back _ (sym (PB.axiom (comm₂ CNOT-gate CNOT-gen)))) ⟩
  CNOT ↑ ↑ • U ↑ • (CNOT ↑ ↑ • CNOT)
    ≈⟨ by-assoc Eq.refl ⟩
  V ↑ • CNOT ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- The right side of R₁₃.
Φ : Circuit (₄₊ n)
Φ = T ^ 5 • (T ↑) ^ 5 • (T ↑ ↑) ^ 5 • (T ↑ ↑ ↑) ^ 5 •
    (U ↑ ↑) ^ 3 • U₁₃ ^ 3 • U₀₃ ^ 3 • (U ↑) ^ 3 • U₀₂ ^ 3 • U ^ 3 •
    V ↑ • V₀₂₃ • V₀₁₃ • V

-- The upper CNOT and V: R₁₃ itself.
CNOT↑↑-V : (₄₊ n) ⊢ CNOT ↑ ↑ • V ≈ Φ • CNOT ↑ ↑
CNOT↑↑-V {n} = begin
  CNOT ↑ ↑ • V
    ≈⟨ sym right-unit ⟩
  (CNOT ↑ ↑ • V) • ε
    ≈⟨ back _ (sym CNOT²↑↑) ⟩
  (CNOT ↑ ↑ • V) • (CNOT ↑ ↑ • CNOT ↑ ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT ↑ ↑ • V • CNOT ↑ ↑) • CNOT ↑ ↑
    ≈⟨ front _ (ax R₁₃) ⟩
  Φ • CNOT ↑ ↑ ∎
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Figure 2, third row: SWAP past a diagonal gate
--
-- SWAP-T↑ and SWAP-T are above.  The rest are naturality: a gate
-- moved by a swap is the gate on the wires the swap sends it to, which
-- is how the gates on non-adjacent wires were defined.

-- U is symmetric (the paper's example derivation, from R₅).
SWAP-U : (₂₊ n) ⊢ SWAP • U ≈ U • SWAP
SWAP-U {n} = begin
  SWAP • U
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • CNOT) • T • CNOT
    ≈⟨ front _ SWAP-CNOT ⟩
  (CNOT • SWAP • CNOT • SWAP) • T • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • CNOT • (SWAP • T) • CNOT
    ≈⟨ back _ (back _ (back _ (front _ SWAP-T))) ⟩
  CNOT • SWAP • CNOT • (T ↑ • SWAP) • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • (CNOT • T ↑) • SWAP • CNOT
    ≈⟨ back _ (back _ (front _ CNOT-T↑)) ⟩
  CNOT • SWAP • (T ↑ • CNOT) • SWAP • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (SWAP • T ↑) • CNOT • SWAP • CNOT
    ≈⟨ back _ (front _ SWAP-T↑) ⟩
  CNOT • (T • SWAP) • CNOT • SWAP • CNOT
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • (SWAP • CNOT • SWAP • CNOT)
    ≈⟨ back _ (back _ SCSC) ⟩
  CNOT • T • (CNOT • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  U • SWAP ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- The swaps carrying the bottom wires up, and back, cancel.
σ₂σ₂⁻¹ : (₃₊ n) ⊢ σ₂ • (SWAP • SWAP ↑) ≈ ε
σ₂σ₂⁻¹ {n} = begin
  σ₂ • (SWAP • SWAP ↑)                 ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • (SWAP • SWAP) • SWAP ↑      ≈⟨ back _ (front _ (ax swap-order)) ⟩
  SWAP ↑ • ε • SWAP ↑                  ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • SWAP ↑                      ≈⟨ SWAP²↑ ⟩
  ε ∎
  where open Tools ((₃₊ n) VRel,_===_)

σ₃⁻¹σ₃ : (₄₊ n) ⊢ (SWAP • SWAP ↑ • SWAP ↑ ↑) • σ₃ ≈ ε
σ₃⁻¹σ₃ {n} = begin
  (SWAP • SWAP ↑ • SWAP ↑ ↑) • σ₃
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP ↑ • (SWAP ↑ ↑ • SWAP ↑ ↑) • SWAP ↑ • SWAP
    ≈⟨ back _ (back _ (front _ SWAP²↑↑)) ⟩
  SWAP • SWAP ↑ • ε • SWAP ↑ • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • (SWAP ↑ • SWAP ↑) • SWAP
    ≈⟨ back _ (front _ SWAP²↑) ⟩
  SWAP • ε • SWAP
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP
    ≈⟨ ax swap-order ⟩
  ε ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- U as U ↑ conjugated by the swaps: naturality read backwards.
U-conj : (₃₊ n) ⊢ U ≈ SWAP ↑ • SWAP • U ↑ • SWAP • SWAP ↑
U-conj {n} = begin
  U                                    ≈⟨ sym right-unit ⟩
  U • ε                                ≈⟨ back _ (sym σ₂σ₂⁻¹) ⟩
  U • (σ₂ • (SWAP • SWAP ↑))           ≈⟨ sym assoc ⟩
  (U • σ₂) • (SWAP • SWAP ↑)           ≈⟨ front _ nat-U ⟩
  (σ₂ • U ↑) • (SWAP • SWAP ↑)         ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • SWAP • U ↑ • SWAP • SWAP ↑  ∎
  where open Tools ((₃₊ n) VRel,_===_)

SWAP↑-U : (₃₊ n) ⊢ SWAP ↑ • U ≈ U₀₂ • SWAP ↑
SWAP↑-U {n} = begin
  SWAP ↑ • U
    ≈⟨ back _ U-conj ⟩
  SWAP ↑ • (SWAP ↑ • SWAP • U ↑ • SWAP • SWAP ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP ↑ • SWAP ↑) • SWAP • U ↑ • SWAP • SWAP ↑
    ≈⟨ front _ SWAP²↑ ⟩
  ε • SWAP • U ↑ • SWAP • SWAP ↑
    ≈⟨ left-unit ⟩
  SWAP • U ↑ • SWAP • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  U₀₂ • SWAP ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

SWAP-U↑ : (₃₊ n) ⊢ SWAP • U ↑ ≈ U₀₂ • SWAP
SWAP-U↑ {n} = sym (begin
  U₀₂ • SWAP                          ≈⟨ by-assoc Eq.refl ⟩
  SWAP • U ↑ • (SWAP • SWAP)          ≈⟨ back _ (back _ (ax swap-order)) ⟩
  SWAP • U ↑ • ε                      ≈⟨ back _ right-unit ⟩
  SWAP • U ↑ ∎)
  where open Tools ((₃₊ n) VRel,_===_)

SWAP↑-U₀₂ : (₃₊ n) ⊢ SWAP ↑ • U₀₂ ≈ U • SWAP ↑
SWAP↑-U₀₂ {n} = begin
  SWAP ↑ • U₀₂
    ≈⟨ sym right-unit ⟩
  (SWAP ↑ • U₀₂) • ε
    ≈⟨ back _ (sym SWAP²↑) ⟩
  (SWAP ↑ • U₀₂) • (SWAP ↑ • SWAP ↑)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  SWAP ↑ • (U₀₂ • SWAP ↑) • SWAP ↑
    ≈⟨ mid _ _ (sym SWAP↑-U) ⟩
  SWAP ↑ • (SWAP ↑ • U) • SWAP ↑
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (SWAP ↑ • SWAP ↑) • U • SWAP ↑
    ≈⟨ front _ SWAP²↑ ⟩
  ε • U • SWAP ↑
    ≈⟨ left-unit ⟩
  U • SWAP ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- R₅ one wire up.
SWAP-CNOT↑ : (₃₊ n) ⊢ SWAP ↑ • CNOT ↑ ≈ CNOT ↑ • SWAP ↑ • CNOT ↑ • SWAP ↑
SWAP-CNOT↑ = lemma-cong↑ (SWAP • CNOT) (CNOT • SWAP • CNOT • SWAP) SWAP-CNOT

SCSC↑ : (₃₊ n) ⊢ SWAP ↑ • CNOT ↑ • SWAP ↑ • CNOT ↑ ≈ CNOT ↑ • SWAP ↑
SCSC↑ = lemma-cong↑ (SWAP • CNOT • SWAP • CNOT) (CNOT • SWAP) SCSC

-- V is symmetric in its upper two wires …
SWAP↑-V : (₃₊ n) ⊢ SWAP ↑ • V ≈ V • SWAP ↑
SWAP↑-V {n} = begin
  SWAP ↑ • V
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP ↑ • CNOT ↑) • U • CNOT ↑
    ≈⟨ front _ SWAP-CNOT↑ ⟩
  (CNOT ↑ • SWAP ↑ • CNOT ↑ • SWAP ↑) • U • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • CNOT ↑ • (SWAP ↑ • U) • CNOT ↑
    ≈⟨ back _ (back _ (back _ (front _ SWAP↑-U))) ⟩
  CNOT ↑ • SWAP ↑ • CNOT ↑ • (U₀₂ • SWAP ↑) • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • SWAP ↑ • (CNOT ↑ • U₀₂) • SWAP ↑ • CNOT ↑
    ≈⟨ back _ (back _ (front _ CNOT↑-U₀₂)) ⟩
  CNOT ↑ • SWAP ↑ • (U₀₂ • CNOT ↑) • SWAP ↑ • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (SWAP ↑ • U₀₂) • CNOT ↑ • SWAP ↑ • CNOT ↑
    ≈⟨ back _ (front _ SWAP↑-U₀₂) ⟩
  CNOT ↑ • (U • SWAP ↑) • CNOT ↑ • SWAP ↑ • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • U • (SWAP ↑ • CNOT ↑ • SWAP ↑ • CNOT ↑)
    ≈⟨ back _ (back _ SCSC↑) ⟩
  CNOT ↑ • U • (CNOT ↑ • SWAP ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  V • SWAP ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- … and in its lower two: conjugating U by CNOT₂₀ also gives V.
CNOT-U₀₂ : (₃₊ n) ⊢ CNOT • U₀₂ ≈ V • CNOT
CNOT-U₀₂ {n} = begin
  CNOT • U₀₂
    ≈⟨ sym right-unit ⟩
  (CNOT • U₀₂) • ε
    ≈⟨ back _ (sym (ax R₄)) ⟩
  (CNOT • U₀₂) • (CNOT • CNOT)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  CNOT • (U₀₂ • CNOT) • CNOT
    ≈⟨ mid _ _ (sym CNOT-V) ⟩
  CNOT • (CNOT • V) • CNOT
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (CNOT • CNOT) • V • CNOT
    ≈⟨ front _ (ax R₄) ⟩
  ε • V • CNOT
    ≈⟨ left-unit ⟩
  V • CNOT ∎
  where open Tools ((₃₊ n) VRel,_===_)

C₂₀UC₂₀ : (₃₊ n) ⊢ CNOT₂₀ • U • CNOT₂₀ ≈ V
C₂₀UC₂₀ {n} = begin
  CNOT₂₀ • U • CNOT₂₀
    ≈⟨ front _ (ax R₆) ⟩
  (CNOT • CNOT ↑ • CNOT • CNOT ↑) • U • CNOT₂₀
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CNOT ↑ • CNOT • (CNOT ↑ • U) • CNOT₂₀
    ≈⟨ back _ (back _ (back _ (front _ CNOT↑-U))) ⟩
  CNOT • CNOT ↑ • CNOT • (V • CNOT ↑) • CNOT₂₀
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CNOT ↑ • (CNOT • V) • CNOT ↑ • CNOT₂₀
    ≈⟨ back _ (back _ (front _ CNOT-V)) ⟩
  CNOT • CNOT ↑ • (U₀₂ • CNOT) • CNOT ↑ • CNOT₂₀
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (CNOT ↑ • U₀₂) • CNOT • CNOT ↑ • CNOT₂₀
    ≈⟨ back _ (front _ CNOT↑-U₀₂) ⟩
  CNOT • (U₀₂ • CNOT ↑) • CNOT • CNOT ↑ • CNOT₂₀
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT • U₀₂) • CNOT ↑ • CNOT • CNOT ↑ • CNOT₂₀
    ≈⟨ front _ CNOT-U₀₂ ⟩
  (V • CNOT) • CNOT ↑ • CNOT • CNOT ↑ • CNOT₂₀
    ≈⟨ by-assoc Eq.refl ⟩
  V • (CNOT • CNOT ↑ • CNOT • CNOT ↑) • CNOT₂₀
    ≈⟨ back _ (front _ (sym (ax R₆))) ⟩
  V • CNOT₂₀ • CNOT₂₀
    ≈⟨ back _ CNOT₂₀² ⟩
  V • ε
    ≈⟨ right-unit ⟩
  V ∎
  where open Tools ((₃₊ n) VRel,_===_)

SWAP-V : (₃₊ n) ⊢ SWAP • V ≈ V • SWAP
SWAP-V {n} = begin
  SWAP • V
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP • CNOT ↑) • U • CNOT ↑
    ≈⟨ front _ (sym CNOT₂₀-SWAP) ⟩
  (CNOT₂₀ • SWAP) • U • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT₂₀ • (SWAP • U) • CNOT ↑
    ≈⟨ mid _ _ SWAP-U ⟩
  CNOT₂₀ • (U • SWAP) • CNOT ↑
    ≈⟨ by-assoc Eq.refl ⟩
  CNOT₂₀ • U • (SWAP • CNOT ↑)
    ≈⟨ back _ (back _ (sym CNOT₂₀-SWAP)) ⟩
  CNOT₂₀ • U • (CNOT₂₀ • SWAP)
    ≈⟨ by-assoc Eq.refl ⟩
  (CNOT₂₀ • U • CNOT₂₀) • SWAP
    ≈⟨ front _ C₂₀UC₂₀ ⟩
  V • SWAP ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- V moved to wires 0, 1 and 3 is V conjugated by the top swap.
V↑-conj : (₄₊ n) ⊢ V ↑ ≈ SWAP • SWAP ↑ • SWAP ↑ ↑ • V • SWAP ↑ ↑ • SWAP ↑ • SWAP
V↑-conj {n} = begin
  V ↑
    ≈⟨ sym left-unit ⟩
  ε • V ↑
    ≈⟨ front _ (sym σ₃⁻¹σ₃) ⟩
  ((SWAP • SWAP ↑ • SWAP ↑ ↑) • σ₃) • V ↑
    ≈⟨ assoc ⟩
  (SWAP • SWAP ↑ • SWAP ↑ ↑) • (σ₃ • V ↑)
    ≈⟨ back _ (sym nat-V) ⟩
  (SWAP • SWAP ↑ • SWAP ↑ ↑) • (V • σ₃)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP ↑ • SWAP ↑ ↑ • V • SWAP ↑ ↑ • SWAP ↑ • SWAP ∎
  where open Tools ((₄₊ n) VRel,_===_)

V₀₁₃-conj : (₄₊ n) ⊢ V₀₁₃ ≈ SWAP ↑ ↑ • V • SWAP ↑ ↑
V₀₁₃-conj {n} = begin
  V₀₁₃
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • SWAP • V ↑ • (SWAP • SWAP ↑)
    ≈⟨ back _ (back _ (front _ V↑-conj)) ⟩
  SWAP ↑ • SWAP • (SWAP • SWAP ↑ • SWAP ↑ ↑ • V • SWAP ↑ ↑ • SWAP ↑ • SWAP) • (SWAP • SWAP ↑)
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ • (SWAP • SWAP) • SWAP ↑ • SWAP ↑ ↑ • V • SWAP ↑ ↑ • SWAP ↑ • (SWAP • SWAP) • SWAP ↑
    ≈⟨ back _ (front _ (ax swap-order)) ⟩
  SWAP ↑ • ε • SWAP ↑ • SWAP ↑ ↑ • V • SWAP ↑ ↑ • SWAP ↑ • (SWAP • SWAP) • SWAP ↑
    ≈⟨ back _ (back _ (back _ (back _ (back _ (back _ (back _ (front _ (ax swap-order)))))))) ⟩
  SWAP ↑ • ε • SWAP ↑ • SWAP ↑ ↑ • V • SWAP ↑ ↑ • SWAP ↑ • ε • SWAP ↑
    ≈⟨ by-assoc Eq.refl ⟩
  (SWAP ↑ • SWAP ↑) • SWAP ↑ ↑ • V • SWAP ↑ ↑ • (SWAP ↑ • SWAP ↑)
    ≈⟨ cong SWAP²↑ (back _ (back _ (back _ SWAP²↑))) ⟩
  ε • SWAP ↑ ↑ • V • SWAP ↑ ↑ • ε
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ ↑ • V • SWAP ↑ ↑ ∎
  where open Tools ((₄₊ n) VRel,_===_)

SWAP↑↑-V : (₄₊ n) ⊢ SWAP ↑ ↑ • V ≈ V₀₁₃ • SWAP ↑ ↑
SWAP↑↑-V {n} = sym (begin
  V₀₁₃ • SWAP ↑ ↑
    ≈⟨ front _ V₀₁₃-conj ⟩
  (SWAP ↑ ↑ • V • SWAP ↑ ↑) • SWAP ↑ ↑
    ≈⟨ by-assoc Eq.refl ⟩
  SWAP ↑ ↑ • V • (SWAP ↑ ↑ • SWAP ↑ ↑)
    ≈⟨ back _ (back _ SWAP²↑↑) ⟩
  SWAP ↑ ↑ • V • ε
    ≈⟨ back _ right-unit ⟩
  SWAP ↑ ↑ • V ∎)
  where open Tools ((₄₊ n) VRel,_===_)

SWAP-V↑ : (₄₊ n) ⊢ SWAP • V ↑ ≈ V₀₂₃ • SWAP
SWAP-V↑ {n} = sym (begin
  V₀₂₃ • SWAP                        ≈⟨ by-assoc Eq.refl ⟩
  SWAP • V ↑ • (SWAP • SWAP)         ≈⟨ back _ (back _ (ax swap-order)) ⟩
  SWAP • V ↑ • ε                     ≈⟨ back _ right-unit ⟩
  SWAP • V ↑ ∎)
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Lemma 5.2: diagonal gates commute

T↑-U : (₂₊ n) ⊢ T ↑ • U ≈ U • T ↑
T↑-U {n} = begin
  T ↑ • U                        ≈⟨ by-assoc Eq.refl ⟩
  (T ↑ • CNOT) • T • CNOT        ≈⟨ front _ (sym CNOT-T↑) ⟩
  (CNOT • T ↑) • T • CNOT        ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (T ↑ • T) • CNOT        ≈⟨ mid _ _ (PB.axiom (comm₁ T-gate T-gen)) ⟩
  CNOT • (T • T ↑) • CNOT        ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • (T ↑ • CNOT)        ≈⟨ back _ (back _ (sym CNOT-T↑)) ⟩
  CNOT • T • (CNOT • T ↑)        ≈⟨ by-assoc Eq.refl ⟩
  U • T ↑ ∎
  where open Tools ((₂₊ n) VRel,_===_)

T↑↑-U : (₃₊ n) ⊢ T ↑ ↑ • U ≈ U • T ↑ ↑
T↑↑-U {n} = begin
  T ↑ ↑ • U                      ≈⟨ by-assoc Eq.refl ⟩
  (T ↑ ↑ • CNOT) • T • CNOT      ≈⟨ front _ (PB.axiom (comm₂ CNOT-gate T-gen)) ⟩
  (CNOT • T ↑ ↑) • T • CNOT      ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (T ↑ ↑ • T) • CNOT      ≈⟨ mid _ _ (PB.axiom (comm₁ T-gate (T-gen ↥))) ⟩
  CNOT • (T • T ↑ ↑) • CNOT      ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • (T ↑ ↑ • CNOT)      ≈⟨ back _ (back _ (PB.axiom (comm₂ CNOT-gate T-gen))) ⟩
  CNOT • T • (CNOT • T ↑ ↑)      ≈⟨ by-assoc Eq.refl ⟩
  U • T ↑ ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

CNOT-T↑↑ : (₃₊ n) ⊢ CNOT ↑ • T ↑ ↑ ≈ T ↑ ↑ • CNOT ↑
CNOT-T↑↑ = lemma-cong↑ (CNOT • T ↑) (T ↑ • CNOT) CNOT-T↑

T↑↑-V : (₃₊ n) ⊢ T ↑ ↑ • V ≈ V • T ↑ ↑
T↑↑-V {n} = begin
  T ↑ ↑ • V                          ≈⟨ by-assoc Eq.refl ⟩
  (T ↑ ↑ • CNOT ↑) • U • CNOT ↑      ≈⟨ front _ (sym CNOT-T↑↑) ⟩
  (CNOT ↑ • T ↑ ↑) • U • CNOT ↑      ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (T ↑ ↑ • U) • CNOT ↑      ≈⟨ mid _ _ T↑↑-U ⟩
  CNOT ↑ • (U • T ↑ ↑) • CNOT ↑      ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • U • (T ↑ ↑ • CNOT ↑)      ≈⟨ back _ (back _ (sym CNOT-T↑↑)) ⟩
  CNOT ↑ • U • (CNOT ↑ • T ↑ ↑)      ≈⟨ by-assoc Eq.refl ⟩
  V • T ↑ ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

U↑-CNOT↑ : (₃₊ n) ⊢ U ↑ • CNOT ↑ ≈ CNOT ↑ • T ↑
U↑-CNOT↑ {n} = lemma-cong↑ (U • CNOT) (CNOT • T) (sym CNOT-T)
  where open Tools ((₂₊ n) VRel,_===_)

T↑-CNOT↑ : (₃₊ n) ⊢ T ↑ • CNOT ↑ ≈ CNOT ↑ • U ↑
T↑-CNOT↑ {n} = lemma-cong↑ (T • CNOT) (CNOT • U) (sym CNOT-U)
  where open Tools ((₂₊ n) VRel,_===_)

U↑-V : (₃₊ n) ⊢ U ↑ • V ≈ V • U ↑
U↑-V {n} = begin
  U ↑ • V                          ≈⟨ by-assoc Eq.refl ⟩
  (U ↑ • CNOT ↑) • U • CNOT ↑      ≈⟨ front _ U↑-CNOT↑ ⟩
  (CNOT ↑ • T ↑) • U • CNOT ↑      ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (T ↑ • U) • CNOT ↑      ≈⟨ mid _ _ T↑-U ⟩
  CNOT ↑ • (U • T ↑) • CNOT ↑      ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • U • (T ↑ • CNOT ↑)      ≈⟨ back _ (back _ T↑-CNOT↑) ⟩
  CNOT ↑ • U • (CNOT ↑ • U ↑)      ≈⟨ by-assoc Eq.refl ⟩
  V • U ↑ ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- U two wires up commutes with U (the bifunctorial law, letter by
-- letter) and with the upper CNOT (CNOT-U↑ shifted).
U↑↑-U : (₄₊ n) ⊢ U ↑ ↑ • U ≈ U • U ↑ ↑
U↑↑-U {n} = begin
  U ↑ ↑ • U                        ≈⟨ by-assoc Eq.refl ⟩
  (U ↑ ↑ • CNOT) • T • CNOT        ≈⟨ front _ (comm-gate₂-w↑↑ CNOT-gate U) ⟩
  (CNOT • U ↑ ↑) • T • CNOT        ≈⟨ by-assoc Eq.refl ⟩
  CNOT • (U ↑ ↑ • T) • CNOT        ≈⟨ mid _ _ (comm-gate₁-w↑ T-gate (U ↑)) ⟩
  CNOT • (T • U ↑ ↑) • CNOT        ≈⟨ by-assoc Eq.refl ⟩
  CNOT • T • (U ↑ ↑ • CNOT)        ≈⟨ back _ (back _ (comm-gate₂-w↑↑ CNOT-gate U)) ⟩
  CNOT • T • (CNOT • U ↑ ↑)        ≈⟨ by-assoc Eq.refl ⟩
  U • U ↑ ↑ ∎
  where open Tools ((₄₊ n) VRel,_===_)

CNOT↑-U↑↑ : (₄₊ n) ⊢ CNOT ↑ • U ↑ ↑ ≈ U ↑ ↑ • CNOT ↑
CNOT↑-U↑↑ = lemma-cong↑ (CNOT • U ↑) (U ↑ • CNOT) CNOT-U↑

U↑↑-V : (₄₊ n) ⊢ U ↑ ↑ • V ≈ V • U ↑ ↑
U↑↑-V {n} = begin
  U ↑ ↑ • V                          ≈⟨ by-assoc Eq.refl ⟩
  (U ↑ ↑ • CNOT ↑) • U • CNOT ↑      ≈⟨ front _ (sym CNOT↑-U↑↑) ⟩
  (CNOT ↑ • U ↑ ↑) • U • CNOT ↑      ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • (U ↑ ↑ • U) • CNOT ↑      ≈⟨ mid _ _ U↑↑-U ⟩
  CNOT ↑ • (U • U ↑ ↑) • CNOT ↑      ≈⟨ by-assoc Eq.refl ⟩
  CNOT ↑ • U • (U ↑ ↑ • CNOT ↑)      ≈⟨ back _ (back _ (sym CNOT↑-U↑↑)) ⟩
  CNOT ↑ • U • (CNOT ↑ • U ↑ ↑)      ≈⟨ by-assoc Eq.refl ⟩
  V • U ↑ ↑ ∎
  where open Tools ((₄₊ n) VRel,_===_)
