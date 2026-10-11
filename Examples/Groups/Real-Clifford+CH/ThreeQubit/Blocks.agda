------------------------------------------------------------------------
-- Presentations of groups
--
-- Three-wire derivations by two-wire blocks
--
-- A circuit on three wires is a product of circuits on two of them:
-- the lower pair (wires 0 and 1), the upper pair (1 and 2) and the
-- outer pair (0 and 2, through the swap of wires 0 and 1 — the shape
-- of CZ₂₀ and CH₂₀).  The paper rewrites such a block "by Lemma 7.6",
-- completeness on two qubits; here that is one evaluation
-- (SemanticSteps).  What the paper's string diagrams give for free —
-- gates on disjoint wires pass each other — is `L-comm` and the
-- one-wire lemmas below.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Soundness.Relators using (Same)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; ax ; Ex² ; comm-↓↑)

open Below 2 (s≤s (s≤s z≤n)) complete₂ public

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The three kinds of blocks

-- A two-wire circuit on the lower pair, on the upper pair, and on the
-- outer pair (its lower wire on wire 0, its upper wire on wire 2).
L U O : Circuit 2 → Circuit (₃₊ n)
L {n} u = u ↓ᵏ (₁₊ n)
U {n} u = (u ↓ᵏ n) ↑
O u     = Ex ↓ • U u • Ex ↓

-- A block is rewritten by evaluation.
L-sem : (u v : Circuit 2) → Same u v → (₃₊ n) ⊢ L u ≈ L v
L-sem {n} u v e = by-sem u v e {₁₊ n}

U-sem : (u v : Circuit 2) → Same u v → (₃₊ n) ⊢ U u ≈ U v
U-sem {n} u v e = by-sem↑ u v e {n}

O-sem : (u v : Circuit 2) → Same u v → (₃₊ n) ⊢ O u ≈ O v
O-sem {n} u v e = mid (Ex ↓) (Ex ↓) (U-sem u v e)
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Disjoint wires

-- A lower block passes anything on the wires from 2 up.
L-comm : (u : Circuit 2) (v : Circuit (₁₊ n)) → (₃₊ n) ⊢ L u • v ↑ ↑ ≈ v ↑ ↑ • L u
L-comm [ gate₀ () ]ʷ v
L-comm [ gate₀ () ↥ ]ʷ v
L-comm [ gate₀ () ↥ ↥ ]ʷ v
L-comm {n} [ gate₁ h ]ʷ v = sym (comm-gate₁-w↑ h (v ↑))
  where open Tools ((₃₊ n) VRel,_===_)
L-comm {n} [ gate₂ h ]ʷ v = sym (comm-gate₂-w↑↑ h v)
  where open Tools ((₃₊ n) VRel,_===_)
L-comm {n} [ gate₁ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ]ʷ • v ↑) (v ↑ • [ gate₁ h ]ʷ) (PB-sym (comm-gate₁-w↑ h v))
  where open Tools ((₂₊ n) VRel,_===_) renaming (sym to PB-sym)
L-comm {n} ε v = trans left-unit (sym right-unit)
  where open Tools ((₃₊ n) VRel,_===_)
L-comm {n} (u • t) v = begin
  (L u • L t) • v ↑ ↑   ≈⟨ assoc ⟩
  L u • (L t • v ↑ ↑)   ≈⟨ back _ (L-comm t v) ⟩
  L u • (v ↑ ↑ • L t)   ≈⟨ sym assoc ⟩
  (L u • v ↑ ↑) • L t   ≈⟨ front _ (L-comm u v) ⟩
  (v ↑ ↑ • L u) • L t   ≈⟨ assoc ⟩
  v ↑ ↑ • (L u • L t)   ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- An upper block passes a one-wire circuit on wire 0.
U-comm : (w : Circuit 1) (u : Circuit 2) → (₃₊ n) ⊢ (w ↓ᵏ (₂₊ n)) • U u ≈ U u • (w ↓ᵏ (₂₊ n))
U-comm {n} w u = comm-↓↑ w (u ↓ᵏ n)

------------------------------------------------------------------------
-- The outer pair

private
  Ex↓² : (₃₊ n) ⊢ Ex ↓ • Ex ↓ ≈ ε
  Ex↓² = Ex²

-- The outer embedding is multiplicative.
O-• : (u v : Circuit 2) → (₃₊ n) ⊢ O (u • v) ≈ O u • O v
O-• {n} u v = begin
  Ex ↓ • (U u • U v) • Ex ↓
    ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  Ex ↓ • U u • U v • Ex ↓
    ≈⟨ back _ (back _ (insertˡ _ Ex↓²)) ⟩
  Ex ↓ • U u • Ex ↓ • Ex ↓ • U v • Ex ↓
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (Ex ↓ • U u • Ex ↓) • (Ex ↓ • U v • Ex ↓) ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- An outer block is an involution when the circuit is.
O-invol : (u : Circuit 2) → 2 ⊢ u • u ≈ ε → (₃₊ n) ⊢ O u • O u ≈ ε
O-invol {n} u e = conj-invol Ex↓² (lemma-cong↑ ((u • u) ↓ᵏ n) ε (weak e))
  where
  open Tools ((₃₊ n) VRel,_===_)
  open import Examples.Groups.Real-Clifford+CH.Weakening using (weaken)
  weak : 2 ⊢ u • u ≈ ε → (₂₊ n) ⊢ (u • u) ↓ᵏ n ≈ ε
  weak = weaken n (s≤s (s≤s z≤n))

-- A lower block on the outer pair's far side: a circuit on wire 1 only
-- passes an outer block.  Stated for the three one-wire gates used.
private
  mid-O : (g : Circuit 1) →
          (∀ {k} → (₂₊ k) ⊢ (g ↓ᵏ k) ↑ • Ex ≈ Ex • (g ↓ᵏ (₁₊ k))) →
          (∀ {k} → (₂₊ k) ⊢ (g ↓ᵏ (₁₊ k)) • Ex ≈ Ex • (g ↓ᵏ k) ↑) →
          (u : Circuit 2) → (₃₊ n) ⊢ (g ↓ᵏ (₁₊ n)) ↑ • O u ≈ O u • (g ↓ᵏ (₁₊ n)) ↑
  mid-O {n} g up down u = begin
    g₁ • Ex ↓ • U u • Ex ↓
      ≈⟨ sym assoc ⟩
    (g₁ • Ex ↓) • U u • Ex ↓
      ≈⟨ front _ up ⟩
    (Ex ↓ • g₀) • U u • Ex ↓
      ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    Ex ↓ • (g₀ • U u) • Ex ↓
      ≈⟨ mid _ _ (U-comm g u) ⟩
    Ex ↓ • (U u • g₀) • Ex ↓
      ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
    Ex ↓ • U u • (g₀ • Ex ↓)
      ≈⟨ back _ (back _ down) ⟩
    Ex ↓ • U u • (Ex ↓ • g₁)
      ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (Ex ↓ • U u • Ex ↓) • g₁ ∎
    where
    open Tools ((₃₊ n) VRel,_===_)
    g₀ g₁ : Circuit (₃₊ n)
    g₀ = g ↓ᵏ (₂₊ n)
    g₁ = (g ↓ᵏ (₁₊ n)) ↑

Z↑-O : (u : Circuit 2) → (₃₊ n) ⊢ Z ↑ • O u ≈ O u • Z ↑
Z↑-O = mid-O Z (by-sem (Z ↑ • Ex) (Ex • Z ↓) Eq.refl) (by-sem (Z ↓ • Ex) (Ex • Z ↑) Eq.refl)

H↑-O : (u : Circuit 2) → (₃₊ n) ⊢ H ↑ • O u ≈ O u • H ↑
H↑-O = mid-O H (by-sem (H ↑ • Ex) (Ex • H ↓) Eq.refl) (by-sem (H ↓ • Ex) (Ex • H ↑) Eq.refl)

X↑-O : (u : Circuit 2) → (₃₊ n) ⊢ X ↑ • O u ≈ O u • X ↑
X↑-O = mid-O X (by-sem (X ↑ • Ex) (Ex • X ↓) Eq.refl) (by-sem (X ↓ • Ex) (Ex • X ↑) Eq.refl)

-- A one-wire circuit on the outer pair's lower wire is on wire 0, and
-- on its upper wire is on wire 2.
O-bot : (g : Circuit 1) →
        (∀ {k} → (₂₊ k) ⊢ Ex • (g ↓ᵏ k) ↑ • Ex ≈ g ↓ᵏ (₁₊ k)) →
        (₃₊ n) ⊢ O (g ↓ᵏ 1) ≈ g ↓ᵏ (₂₊ n)
O-bot {n} g e = Eq.subst (λ x → (₃₊ n) ⊢ Ex ↓ • x • Ex ↓ ≈ g ↓ᵏ (₂₊ n)) (lift-eq g) (e {₁₊ n})
  where
  -- (g ↓ᵏ 1) ↓ᵏ n shifted is g shifted, generator by generator.
  lift-eq : (g : Circuit 1) → (g ↓ᵏ (₁₊ n)) ↑ ≡ U {n} (g ↓ᵏ 1)
  lift-eq [ gate₀ () ]ʷ
  lift-eq [ gate₀ () ↥ ]ʷ
  lift-eq [ gate₁ h ]ʷ = Eq.refl
  lift-eq ε            = Eq.refl
  lift-eq (g • g′)     = Eq.cong₂ _•_ (lift-eq g) (lift-eq g′)

O-top : (v : Circuit 1) → (₃₊ n) ⊢ Ex ↓ • (v ↓ᵏ n) ↑ ↑ • Ex ↓ ≈ (v ↓ᵏ n) ↑ ↑
O-top {n} v = begin
  Ex ↓ • v₂ • Ex ↓     ≈⟨ sym assoc ⟩
  (Ex ↓ • v₂) • Ex ↓   ≈⟨ front _ (L-comm Ex (v ↓ᵏ n)) ⟩
  (v₂ • Ex ↓) • Ex ↓   ≈⟨ cancelʳ _ Ex↓² ⟩
  v₂ ∎
  where
  open Tools ((₃₊ n) VRel,_===_)
  v₂ : Circuit (₃₊ n)
  v₂ = (v ↓ᵏ n) ↑ ↑

-- The one-wire gates on the outer pair's lower wire.
O-Z↓ : (₃₊ n) ⊢ O (Z ↓) ≈ Z ↓
O-Z↓ = O-bot Z (by-sem (Ex • Z ↑ • Ex) (Z ↓) Eq.refl)

O-H↓ : (₃₊ n) ⊢ O (H ↓) ≈ H ↓
O-H↓ = O-bot H (by-sem (Ex • H ↑ • Ex) (H ↓) Eq.refl)

O-X↓ : (₃₊ n) ⊢ O (X ↓) ≈ X ↓
O-X↓ = O-bot X (by-sem (Ex • X ↑ • Ex) (X ↓) Eq.refl)

------------------------------------------------------------------------
-- The three embeddings and the swaps

-- The rules (f1)–(f4) for a whole block: a block on the upper pair
-- slides down through the two swaps.
private
  slide₀ : ∀ {g₁ g₀ : Circuit (₃₊ n)} →
           (₃₊ n) ⊢ g₁ • Ex ↓ ≈ Ex ↓ • g₀ → (₃₊ n) ⊢ g₀ • Ex ↑ ≈ Ex ↑ • g₀ →
           (₃₊ n) ⊢ g₁ • (Ex ↓ • Ex ↑) ≈ (Ex ↓ • Ex ↑) • g₀
  slide₀ {n} {g₁} {g₀} down pass = begin
    g₁ • (Ex ↓ • Ex ↑)   ≈⟨ sym assoc ⟩
    (g₁ • Ex ↓) • Ex ↑   ≈⟨ front _ down ⟩
    (Ex ↓ • g₀) • Ex ↑   ≈⟨ assoc ⟩
    Ex ↓ • (g₀ • Ex ↑)   ≈⟨ back _ pass ⟩
    Ex ↓ • (Ex ↑ • g₀)   ≈⟨ sym assoc ⟩
    (Ex ↓ • Ex ↑) • g₀ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  slide₁ : ∀ {g₂ g₁ : Circuit (₃₊ n)} →
           (₃₊ n) ⊢ g₂ • Ex ↓ ≈ Ex ↓ • g₂ → (₃₊ n) ⊢ g₂ • Ex ↑ ≈ Ex ↑ • g₁ →
           (₃₊ n) ⊢ g₂ • (Ex ↓ • Ex ↑) ≈ (Ex ↓ • Ex ↑) • g₁
  slide₁ {n} {g₂} {g₁} pass down = begin
    g₂ • (Ex ↓ • Ex ↑)   ≈⟨ sym assoc ⟩
    (g₂ • Ex ↓) • Ex ↑   ≈⟨ front _ pass ⟩
    (Ex ↓ • g₂) • Ex ↑   ≈⟨ assoc ⟩
    Ex ↓ • (g₂ • Ex ↑)   ≈⟨ back _ down ⟩
    Ex ↓ • (Ex ↑ • g₁)   ≈⟨ sym assoc ⟩
    (Ex ↓ • Ex ↑) • g₁ ∎
    where open Tools ((₃₊ n) VRel,_===_)

U-shift : (u : Circuit 2) → (₃₊ n) ⊢ U u • (Ex ↓ • Ex ↑) ≈ (Ex ↓ • Ex ↑) • L u
U-shift [ gate₀ () ]ʷ
U-shift [ gate₀ () ↥ ]ʷ
U-shift [ gate₀ () ↥ ↥ ]ʷ
U-shift [ H-gen ]ʷ = slide₀ (L-sem (H ↑ • Ex) (Ex • H ↓) Eq.refl) (U-comm H Ex)
U-shift [ Z-gen ]ʷ = slide₀ (L-sem (Z ↑ • Ex) (Ex • Z ↓) Eq.refl) (U-comm Z Ex)
U-shift {n} [ H-gen ↥ ]ʷ = slide₁ (sym (L-comm Ex H)) (U-sem (H ↑ • Ex) (Ex • H ↓) Eq.refl)
  where open Tools ((₃₊ n) VRel,_===_)
U-shift {n} [ Z-gen ↥ ]ʷ = slide₁ (sym (L-comm Ex Z)) (U-sem (Z ↑ • Ex) (Ex • Z ↓) Eq.refl)
  where open Tools ((₃₊ n) VRel,_===_)
U-shift {n} [ CZ-gen ]ʷ = trans (ax swap-CZ) (sym assoc)
  where open Tools ((₃₊ n) VRel,_===_)
U-shift {n} [ CH-gen ]ʷ = trans (ax swap-CH) (sym assoc)
  where open Tools ((₃₊ n) VRel,_===_)
U-shift {n} ε = trans left-unit (sym right-unit)
  where open Tools ((₃₊ n) VRel,_===_)
U-shift {n} (u • v) = begin
  (U u • U v) • (Ex ↓ • Ex ↑)   ≈⟨ assoc ⟩
  U u • (U v • (Ex ↓ • Ex ↑))   ≈⟨ back _ (U-shift v) ⟩
  U u • ((Ex ↓ • Ex ↑) • L v)   ≈⟨ sym assoc ⟩
  (U u • (Ex ↓ • Ex ↑)) • L v   ≈⟨ front _ (U-shift u) ⟩
  ((Ex ↓ • Ex ↑) • L u) • L v   ≈⟨ assoc ⟩
  (Ex ↓ • Ex ↑) • (L u • L v) ∎
  where open Tools ((₃₊ n) VRel,_===_)

-- So the outer block is also the lower block under the swap of the
-- upper pair.
O-L : (u : Circuit 2) → (₃₊ n) ⊢ Ex ↑ • L u • Ex ↑ ≈ O u
O-L {n} u = sym (trans (moveʳ Ex↑² pass) assoc)
  where
  open Tools ((₃₊ n) VRel,_===_)
  Ex↑² : (₃₊ n) ⊢ Ex ↑ • Ex ↑ ≈ ε
  Ex↑² = lemma-cong↑ (Ex • Ex) ε Ex²
  pass : (₃₊ n) ⊢ O u • Ex ↑ ≈ Ex ↑ • L u
  pass = begin
    (Ex ↓ • U u • Ex ↓) • Ex ↑     ≈⟨ by-passoc ((□ • □ • □) • □) (□ • (□ • (□ • □))) Eq.refl ⟩
    Ex ↓ • (U u • (Ex ↓ • Ex ↑))   ≈⟨ back _ (U-shift u) ⟩
    Ex ↓ • ((Ex ↓ • Ex ↑) • L u)   ≈⟨ by-passoc (□ • ((□ • □) • □)) (□ • □ • □ • □) Eq.refl ⟩
    Ex ↓ • Ex ↓ • Ex ↑ • L u       ≈⟨ cancelˡ _ Ex↓² ⟩
    Ex ↑ • L u ∎
