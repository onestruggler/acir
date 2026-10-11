------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire derivations by two- and three-wire blocks
--
-- On four wires the paper rewrites a block on three of them "by Lemma
-- D.3", completeness on three qubits — its induction hypothesis (Lemma
-- 5.1) one width down.  Here that is one evaluation on stored 8 × 8
-- tries (SemanticSteps), for each of the four triples of wires:
--
--   L₃  wires 0 1 2        U₃  wires 1 2 3
--   O₃  wires 0 2 3        M₃  wires 0 1 3
--
-- the last two through the swap of the lower and of the upper pair.  A
-- two-wire block sits on one of six pairs: L, U, O of ThreeQubit.Blocks
-- are the pairs 01, 12 and 02, and P₂₃, P₁₃, P₀₃ the other three.  The
-- coherence lemmas say which pair a block of a triple lands on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Blocks
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Soundness.Relators using (Same)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps
open import Examples.Groups.Real-Clifford+CH.Weakening using (↑-↓ᵏ)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ public

open Below 3 (s≤s (s≤s (s≤s z≤n))) complete₃ public
  renaming (by-sem₀ to by-sem₃₀ ; by-sem to by-sem₃ ; by-sem↑ to by-sem₃↑)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The three swaps, as conjugations

private
  Ex↑² : (₄₊ n) ⊢ Ex ↑ • Ex ↑ ≈ ε
  Ex↑² = lemma-cong↑ (Ex • Ex) ε Ex²

  Ex↑↑² : (₄₊ n) ⊢ Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
  Ex↑↑² = lemma-cong↑ (Ex ↑ • Ex ↑) ε (lemma-cong↑ (Ex • Ex) ε Ex²)

module S₀₁ {n : ℕ} = Conj {₄₊ n} (Ex ↓) Ex²
module S₁₂ {n : ℕ} = Conj {₄₊ n} (Ex ↑) Ex↑²
module S₂₃ {n : ℕ} = Conj {₄₊ n} (Ex ↑ ↑) Ex↑↑²

------------------------------------------------------------------------
-- Blocks

-- A two-wire circuit on the pairs 23, 13 and 03 (its lower wire on the
-- lower one).  The pairs 01, 12 and 02 are L, U and O.
P₂₃ P₁₃ P₀₃ : Circuit 2 → Circuit (₄₊ n)
P₂₃ {n} u = (u ↓ᵏ n) ↑ ↑
P₁₃ u     = Ex ↑ • P₂₃ u • Ex ↑
P₀₃ u     = Ex ↓ • P₁₃ u • Ex ↓

-- A three-wire circuit on each triple (its wires in order).
L₃ U₃ O₃ M₃ : Circuit 3 → Circuit (₄₊ n)
L₃ {n} u = u ↓ᵏ (₁₊ n)
U₃ {n} u = (u ↓ᵏ n) ↑
O₃ u     = Ex ↓ • U₃ u • Ex ↓
M₃ u     = Ex ↑ ↑ • L₃ u • Ex ↑ ↑

-- A block is rewritten by evaluation.
L₃-sem : (u v : Circuit 3) → Same u v → (₄₊ n) ⊢ L₃ u ≈ L₃ v
L₃-sem {n} u v e = by-sem₃ u v e {₁₊ n}

U₃-sem : (u v : Circuit 3) → Same u v → (₄₊ n) ⊢ U₃ u ≈ U₃ v
U₃-sem {n} u v e = by-sem₃↑ u v e {n}

O₃-sem : (u v : Circuit 3) → Same u v → (₄₊ n) ⊢ O₃ u ≈ O₃ v
O₃-sem u v e = S₀₁.⟪⟫-cong (U₃-sem u v e)

M₃-sem : (u v : Circuit 3) → Same u v → (₄₊ n) ⊢ M₃ u ≈ M₃ v
M₃-sem u v e = S₂₃.⟪⟫-cong (L₃-sem u v e)

-- So is a two-wire block on the pair 03.
P₀₃-sem : (u v : Circuit 2) → Same u v → (₄₊ n) ⊢ P₀₃ u ≈ P₀₃ v
P₀₃-sem {n} u v e =
  S₀₁.⟪⟫-cong (S₁₂.⟪⟫-cong (lemma-cong↑ ((u ↓ᵏ n) ↑) ((v ↓ᵏ n) ↑) (by-sem↑ u v e {n})))

-- Two blocks of one triple that commute there.
L₃-comm : (u v : Circuit 3) → Same (u • v) (v • u) → (₄₊ n) ⊢ L₃ u • L₃ v ≈ L₃ v • L₃ u
L₃-comm u v e = L₃-sem (u • v) (v • u) e

U₃-comm : (u v : Circuit 3) → Same (u • v) (v • u) → (₄₊ n) ⊢ U₃ u • U₃ v ≈ U₃ v • U₃ u
U₃-comm u v e = U₃-sem (u • v) (v • u) e

O₃-comm : (u v : Circuit 3) → Same (u • v) (v • u) → (₄₊ n) ⊢ O₃ u • O₃ v ≈ O₃ v • O₃ u
O₃-comm u v e =
  S₀₁.⟪⟫-≈ (U₃-sem (u • v) (v • u) e) (S₀₁.⟪⟫-• (U₃ u) (U₃ v)) (S₀₁.⟪⟫-• (U₃ v) (U₃ u))

M₃-comm : (u v : Circuit 3) → Same (u • v) (v • u) → (₄₊ n) ⊢ M₃ u • M₃ v ≈ M₃ v • M₃ u
M₃-comm u v e =
  S₂₃.⟪⟫-≈ (L₃-sem (u • v) (v • u) e) (S₂₃.⟪⟫-• (L₃ u) (L₃ v)) (S₂₃.⟪⟫-• (L₃ v) (L₃ u))

------------------------------------------------------------------------
-- Multiplicativity

P₁₃-• : (u v : Circuit 2) → (₄₊ n) ⊢ P₁₃ (u • v) ≈ P₁₃ u • P₁₃ v
P₁₃-• u v = S₁₂.⟪⟫-• (P₂₃ u) (P₂₃ v)

P₀₃-• : (u v : Circuit 2) → (₄₊ n) ⊢ P₀₃ (u • v) ≈ P₀₃ u • P₀₃ v
P₀₃-• {n} u v = trans (S₀₁.⟪⟫-cong (P₁₃-• u v)) (S₀₁.⟪⟫-• (P₁₃ u) (P₁₃ v))
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Coherence: the swaps and the blocks

-- The lower swap does not touch the pair 23, nor the upper swap the
-- pair 01.
P₂₃-S₀₁ : (w : Circuit (₂₊ n)) → (₄₊ n) ⊢ Ex ↓ • w ↑ ↑ • Ex ↓ ≈ w ↑ ↑
P₂₃-S₀₁ w = S₀₁.⟪⟫-fix (L-comm Ex w)

L-S₂₃ : (u : Circuit 2) → (₄₊ n) ⊢ Ex ↑ ↑ • L u • Ex ↑ ↑ ≈ L u
L-S₂₃ {n} u = S₂₃.⟪⟫-fix (sym (L-comm u Ex))
  where open Tools ((₄₊ n) VRel,_===_)

-- The upper swap carries the pair 12 to 13 and the pair 02 to 03.
U-S₂₃ : (u : Circuit 2) → (₄₊ n) ⊢ Ex ↑ ↑ • U u • Ex ↑ ↑ ≈ P₁₃ u
U-S₂₃ {n} u = lemma-cong↑ (Ex ↑ • L u • Ex ↑) (O u) (O-L u)

O-S₂₃ : (u : Circuit 2) → (₄₊ n) ⊢ Ex ↑ ↑ • O u • Ex ↑ ↑ ≈ P₀₃ u
O-S₂₃ {n} u = S₂₃.⟪⟫-•₃ (L-S₂₃ Ex) (U-S₂₃ u) (L-S₂₃ Ex)

-- The transposition of wires 0 and 2 carries the pair 23 to 03: the
-- spelling of Definition 2.4.
τ-P₀₃ : (u : Circuit 2) → (₄₊ n) ⊢ τ₀₂-conj (P₂₃ u) ≈ P₀₃ u
τ-P₀₃ {n} u = begin
  (Ex ↓ • Ex ↑ • Ex ↓) • P₂₃ u • (Ex ↓ • Ex ↑ • Ex ↓)
    ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
  Ex ↓ • Ex ↑ • (Ex ↓ • P₂₃ u • Ex ↓) • Ex ↑ • Ex ↓
    ≈⟨ back _ (back _ (front _ (P₂₃-S₀₁ (u ↓ᵏ n)))) ⟩
  Ex ↓ • Ex ↑ • P₂₃ u • Ex ↑ • Ex ↓
    ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  Ex ↓ • (Ex ↑ • P₂₃ u • Ex ↑) • Ex ↓ ∎
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Disjoint pairs

-- The pairs 23 and 01.
P₂₃-L : (u v : Circuit 2) → (₄₊ n) ⊢ P₂₃ u • L v ≈ L v • P₂₃ u
P₂₃-L {n} u v = sym (L-comm v (u ↓ᵏ n))
  where open Tools ((₄₊ n) VRel,_===_)

-- The interleaved pairs 13 and 02.
P₁₃-O : (u v : Circuit 2) → (₄₊ n) ⊢ P₁₃ u • O v ≈ O v • P₁₃ u
P₁₃-O {n} u v = S₁₂.⟪⟫-≈ (P₂₃-L u v) (S₁₂.⟪⟫-•₂ refl (O-L v)) (S₁₂.⟪⟫-•₂ (O-L v) refl)
  where open Tools ((₄₊ n) VRel,_===_)

-- The nested pairs 03 and 12.
P₀₃-U : (u v : Circuit 2) → (₄₊ n) ⊢ P₀₃ u • U v ≈ U v • P₀₃ u
P₀₃-U {n} u v =
  S₀₁.⟪⟫-≈ (P₁₃-O u v) (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ (U v))) (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ (U v)) refl)
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Blocks of blocks

-- Widening twice is widening once, generator by generator.
private
  fuse₀ : (g : Gen 2) (k : ℕ) → (g ↧ᵏ 0) ↧ᵏ k ≡ g ↧ᵏ k
  fuse₀ (gate₀ ()) k
  fuse₀ (gate₀ () ↥) k
  fuse₀ (gate₀ () ↥ ↥) k
  fuse₀ (gate₁ h) k   = Eq.refl
  fuse₀ (gate₁ h ↥) k = Eq.refl
  fuse₀ (gate₂ h) k   = Eq.refl

  fuse₁ : (g : Gen 2) (k : ℕ) → (g ↧ᵏ 1) ↧ᵏ k ≡ g ↧ᵏ (₁₊ k)
  fuse₁ (gate₀ ()) k
  fuse₁ (gate₀ () ↥) k
  fuse₁ (gate₀ () ↥ ↥) k
  fuse₁ (gate₁ h) k   = Eq.refl
  fuse₁ (gate₁ h ↥) k = Eq.refl
  fuse₁ (gate₂ h) k   = Eq.refl

  ↓-fuse₀ : (u : Circuit 2) (k : ℕ) → (u ↓ᵏ 0) ↓ᵏ k ≡ u ↓ᵏ k
  ↓-fuse₀ [ g ]ʷ  k = Eq.cong [_]ʷ (fuse₀ g k)
  ↓-fuse₀ ε       k = Eq.refl
  ↓-fuse₀ (u • v) k = Eq.cong₂ _•_ (↓-fuse₀ u k) (↓-fuse₀ v k)

  ↓-fuse₁ : (u : Circuit 2) (k : ℕ) → (u ↓ᵏ 1) ↓ᵏ k ≡ u ↓ᵏ (₁₊ k)
  ↓-fuse₁ [ g ]ʷ  k = Eq.cong [_]ʷ (fuse₁ g k)
  ↓-fuse₁ ε       k = Eq.refl
  ↓-fuse₁ (u • v) k = Eq.cong₂ _•_ (↓-fuse₁ u k) (↓-fuse₁ v k)

-- The pairs of a triple, as pairs of the four wires (L, U, O at width 3
-- are written L₀, U₀, O₀).
L₀ U₀ O₀ : Circuit 2 → Circuit 3
L₀ = L {0}
U₀ = U {0}
O₀ = O {0}

L₃-L : (u : Circuit 2) → L₃ {n} (L₀ u) ≡ L u
L₃-L {n} u = ↓-fuse₁ u (₁₊ n)

L₃-U : (u : Circuit 2) → L₃ {n} (U₀ u) ≡ U u
L₃-U {n} u = Eq.trans (↑-↓ᵏ (u ↓ᵏ 0) (₁₊ n)) (Eq.cong _↑ (↓-fuse₀ u (₁₊ n)))

L₃-O : (u : Circuit 2) → L₃ {n} (O₀ u) ≡ O u
L₃-O u = Eq.cong (λ x → Ex ↓ • x • Ex ↓) (L₃-U u)

U₃-L : (u : Circuit 2) → U₃ {n} (L₀ u) ≡ U u
U₃-L {n} u = Eq.cong _↑ (↓-fuse₁ u n)

U₃-U : (u : Circuit 2) → U₃ {n} (U₀ u) ≡ P₂₃ u
U₃-U {n} u = Eq.cong _↑ (Eq.trans (↑-↓ᵏ (u ↓ᵏ 0) n) (Eq.cong _↑ (↓-fuse₀ u n)))

U₃-O : (u : Circuit 2) → U₃ {n} (O₀ u) ≡ P₁₃ u
U₃-O u = Eq.cong (λ x → Ex ↑ • x • Ex ↑) (U₃-U u)

O₃-L : (u : Circuit 2) → O₃ {n} (L₀ u) ≡ O u
O₃-L u = Eq.cong (λ x → Ex ↓ • x • Ex ↓) (U₃-L u)

O₃-O : (u : Circuit 2) → O₃ {n} (O₀ u) ≡ P₀₃ u
O₃-O u = Eq.cong (λ x → Ex ↓ • x • Ex ↓) (U₃-O u)

M₃-L : (u : Circuit 2) → (₄₊ n) ⊢ M₃ (L₀ u) ≈ L u
M₃-L {n} u = Eq.subst (λ x → (₄₊ n) ⊢ Ex ↑ ↑ • x • Ex ↑ ↑ ≈ L u) (Eq.sym (L₃-L u)) (L-S₂₃ u)

M₃-U : (u : Circuit 2) → (₄₊ n) ⊢ M₃ (U₀ u) ≈ P₁₃ u
M₃-U {n} u = Eq.subst (λ x → (₄₊ n) ⊢ Ex ↑ ↑ • x • Ex ↑ ↑ ≈ P₁₃ u) (Eq.sym (L₃-U u)) (U-S₂₃ u)

M₃-O : (u : Circuit 2) → (₄₊ n) ⊢ M₃ (O₀ u) ≈ P₀₃ u
M₃-O {n} u = Eq.subst (λ x → (₄₊ n) ⊢ Ex ↑ ↑ • x • Ex ↑ ↑ ≈ P₀₃ u) (Eq.sym (L₃-O u)) (O-S₂₃ u)

------------------------------------------------------------------------
-- Two pairs sharing a wire commute when they do on their triple

-- The pairs 03 and 01, on the triple 0 1 3.
comm-03-01 : (u v : Circuit 2) → Evaluated (O₀ u • L₀ v) (L₀ v • O₀ u) →
             (₄₊ n) ⊢ P₀₃ u • L v ≈ L v • P₀₃ u
comm-03-01 {n} u v e = begin
  P₀₃ u • L v               ≈⟨ sym (cong (M₃-O u) (M₃-L v)) ⟩
  M₃ (O₀ u) • M₃ (L₀ v)     ≈⟨ M₃-comm (O₀ u) (L₀ v) (Evaluated.same e) ⟩
  M₃ (L₀ v) • M₃ (O₀ u)     ≈⟨ cong (M₃-L v) (M₃-O u) ⟩
  L v • P₀₃ u ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- The pairs 03 and 02, on the triple 0 2 3.
comm-03-02 : (u v : Circuit 2) → Evaluated (O₀ u • L₀ v) (L₀ v • O₀ u) →
             (₄₊ n) ⊢ P₀₃ u • O v ≈ O v • P₀₃ u
comm-03-02 {n} u v e =
  Eq.subst₂ (λ x y → (₄₊ n) ⊢ x • y ≈ y • x) (O₃-O u) (O₃-L v)
    (O₃-comm (O₀ u) (L₀ v) (Evaluated.same e))

------------------------------------------------------------------------
-- Every two pairs with a common wire: they commute when they do on
-- their triple

private
  ≡⇒≈ : ∀ {x y : Circuit (₄₊ n)} → x ≡ y → (₄₊ n) ⊢ x ≈ y
  ≡⇒≈ {n} Eq.refl = refl
    where open Tools ((₄₊ n) VRel,_===_)

  land : {E : Circuit 3 → Circuit (₄₊ n)} →
         ((u v : Circuit 3) → Same (u • v) (v • u) → (₄₊ n) ⊢ E u • E v ≈ E v • E u) →
         {p₀ q₀ : Circuit 2 → Circuit 3} {P Q : Circuit 2 → Circuit (₄₊ n)} →
         ((u : Circuit 2) → (₄₊ n) ⊢ E (p₀ u) ≈ P u) →
         ((v : Circuit 2) → (₄₊ n) ⊢ E (q₀ v) ≈ Q v) →
         (u v : Circuit 2) → Evaluated (p₀ u • q₀ v) (q₀ v • p₀ u) →
         (₄₊ n) ⊢ P u • Q v ≈ Q v • P u
  land {n} {E} E-comm {p₀} {q₀} {P} {Q} eP eQ u v e = begin
    P u • Q v               ≈⟨ sym (cong (eP u) (eQ v)) ⟩
    E (p₀ u) • E (q₀ v)     ≈⟨ E-comm (p₀ u) (q₀ v) (Evaluated.same e) ⟩
    E (q₀ v) • E (p₀ u)     ≈⟨ cong (eQ v) (eP u) ⟩
    Q v • P u ∎
    where open Tools ((₄₊ n) VRel,_===_)

  O₃-U : (u : Circuit 2) → (₄₊ n) ⊢ O₃ (U₀ u) ≈ P₂₃ u
  O₃-U {n} u = trans (S₀₁.⟪⟫-cong (≡⇒≈ (U₃-U u))) (P₂₃-S₀₁ (u ↓ᵏ n))
    where open Tools ((₄₊ n) VRel,_===_)

-- On the triple 0 1 2.
comm-01-12 : (u v : Circuit 2) → Evaluated (L₀ u • U₀ v) (U₀ v • L₀ u) → (₄₊ n) ⊢ L u • U v ≈ U v • L u
comm-01-12 = land L₃-comm (λ u → ≡⇒≈ (L₃-L u)) (λ v → ≡⇒≈ (L₃-U v))

comm-01-02 : (u v : Circuit 2) → Evaluated (L₀ u • O₀ v) (O₀ v • L₀ u) → (₄₊ n) ⊢ L u • O v ≈ O v • L u
comm-01-02 = land L₃-comm (λ u → ≡⇒≈ (L₃-L u)) (λ v → ≡⇒≈ (L₃-O v))

comm-12-02 : (u v : Circuit 2) → Evaluated (U₀ u • O₀ v) (O₀ v • U₀ u) → (₄₊ n) ⊢ U u • O v ≈ O v • U u
comm-12-02 = land L₃-comm (λ u → ≡⇒≈ (L₃-U u)) (λ v → ≡⇒≈ (L₃-O v))

-- On the triple 1 2 3.
comm-12-23 : (u v : Circuit 2) → Evaluated (L₀ u • U₀ v) (U₀ v • L₀ u) → (₄₊ n) ⊢ U u • P₂₃ v ≈ P₂₃ v • U u
comm-12-23 = land U₃-comm (λ u → ≡⇒≈ (U₃-L u)) (λ v → ≡⇒≈ (U₃-U v))

comm-12-13 : (u v : Circuit 2) → Evaluated (L₀ u • O₀ v) (O₀ v • L₀ u) → (₄₊ n) ⊢ U u • P₁₃ v ≈ P₁₃ v • U u
comm-12-13 = land U₃-comm (λ u → ≡⇒≈ (U₃-L u)) (λ v → ≡⇒≈ (U₃-O v))

comm-23-13 : (u v : Circuit 2) → Evaluated (U₀ u • O₀ v) (O₀ v • U₀ u) → (₄₊ n) ⊢ P₂₃ u • P₁₃ v ≈ P₁₃ v • P₂₃ u
comm-23-13 = land U₃-comm (λ u → ≡⇒≈ (U₃-U u)) (λ v → ≡⇒≈ (U₃-O v))

-- On the triple 0 2 3.
comm-02-23 : (u v : Circuit 2) → Evaluated (L₀ u • U₀ v) (U₀ v • L₀ u) → (₄₊ n) ⊢ O u • P₂₃ v ≈ P₂₃ v • O u
comm-02-23 = land O₃-comm (λ u → ≡⇒≈ (O₃-L u)) O₃-U

comm-02-03 : (u v : Circuit 2) → Evaluated (L₀ u • O₀ v) (O₀ v • L₀ u) → (₄₊ n) ⊢ O u • P₀₃ v ≈ P₀₃ v • O u
comm-02-03 = land O₃-comm (λ u → ≡⇒≈ (O₃-L u)) (λ v → ≡⇒≈ (O₃-O v))

comm-23-03 : (u v : Circuit 2) → Evaluated (U₀ u • O₀ v) (O₀ v • U₀ u) → (₄₊ n) ⊢ P₂₃ u • P₀₃ v ≈ P₀₃ v • P₂₃ u
comm-23-03 = land O₃-comm O₃-U (λ v → ≡⇒≈ (O₃-O v))

-- On the triple 0 1 3.
comm-01-13 : (u v : Circuit 2) → Evaluated (L₀ u • U₀ v) (U₀ v • L₀ u) → (₄₊ n) ⊢ L u • P₁₃ v ≈ P₁₃ v • L u
comm-01-13 = land M₃-comm M₃-L M₃-U

comm-01-03 : (u v : Circuit 2) → Evaluated (L₀ u • O₀ v) (O₀ v • L₀ u) → (₄₊ n) ⊢ L u • P₀₃ v ≈ P₀₃ v • L u
comm-01-03 = land M₃-comm M₃-L M₃-O

comm-13-03 : (u v : Circuit 2) → Evaluated (U₀ u • O₀ v) (O₀ v • U₀ u) → (₄₊ n) ⊢ P₁₃ u • P₀₃ v ≈ P₀₃ v • P₁₃ u
comm-13-03 = land M₃-comm M₃-U M₃-O
