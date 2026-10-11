------------------------------------------------------------------------
-- Presentations of groups
--
-- The box wire of the multi-controlled box is an identity wire, and
-- its two lowest controls can be exchanged (Clément, Lemma D.8,
-- Equations (274) and (275))
--
-- The box does not depend on which wire carries its box: the swap of
-- the box wire with an idle wire below it leaves the gate unchanged.
--
-- The proof is the five-qubit (251) at every width, and just as short,
-- because the swap IS a word in CZ and H — Equation (8) is how `Ex` is
-- spelled in `Syntactics`, so `Ex ↓` unfolds to
--
--     CZ ↓ • H ↓ • H ↑ • CZ ↓ • H ↓ • H ↑ • CZ ↓ • H ↓ • H ↑
--
-- definitionally.  The box one wire up passes each letter: the CZ by
-- (272), H on the idle wire 0 because it touches nothing of the gate,
-- and H on wire 1 — the box wire — by (285), H on the box wire passes
-- the box.  That last one is the keystone of Lemma D.8 and is not yet
-- available at every width, so it is a hypothesis here: at k = 0 it is
-- the four-qubit (155), and in the paper's induction on the width it
-- comes from the previous level, which is why the paper cites it as
-- (285)ₙ₋₁.
--
-- (275) is then the generalisation of the four-qubit (157): the box is
-- W B V B, the swap of the wires 1 2 fixes W and V by (127), and it
-- carries the letter B — the smaller box met between the transposition
-- of the wires 0 2 — to the same letter with its box wire moved, which
-- is (274) one size down.  The transport is the braid relation alone:
-- Ex ↑ • τ₀₂ ≈ τ₀₂ • Ex ↓, since τ₀₂ is Ex ↓ • Ex ↑ • Ex ↓.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxWire
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq124 ; eq127)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₁₂ ; U-sem)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq155 ; eq157)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (braid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃
  using (eq272 ; B□)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- (285) at the sizes where it is already known
--
-- H on the box wire passes the box: the four-qubit (155) is the box
-- with three controls, the first case of the schema.

Eq285 : ℕ → Set
Eq285 k = (₄₊ k) ⊢ H ↓ • Λ□ (₃₊ k) ≈ Λ□ (₃₊ k) • H ↓

eq285-0 : Eq285 0
eq285-0 = eq155

------------------------------------------------------------------------
-- The box passes the swap of its box wire with the idle wire below

box-Ex : ∀ k → Eq285 k → (₁₊ (₄₊ k)) ⊢ Ex ↓ • (Λ□ (₃₊ k) ↑) ≈ (Λ□ (₃₊ k) ↑) • Ex ↓
box-Ex k e285 = sym (comm-• c (comm-• h₀ (comm-• h₁ (comm-• c (comm-• h₀
                    (comm-• h₁ (comm-• c (comm-• h₀ h₁))))))))
  where
  open Tools ((₁₊ (₄₊ k)) VRel,_===_)
  open WordAlgebra ((₁₊ (₄₊ k)) VRel,_===_)

  box : Circuit (₁₊ (₄₊ k))
  box = Λ□ (₃₊ k) ↑

  c : box • CZ ↓ ≈ CZ ↓ • box
  c = sym (eq272 k)

  -- Wire 0 is idle for the shifted box.
  h₀ : box • H ↓ ≈ H ↓ • box
  h₀ = comm-gate₁-w↑ H-gate (Λ□ (₃₊ k))

  -- Wire 1 is the box wire.
  h₁ : box • H ↑ ≈ H ↑ • box
  h₁ = sym (lemma-cong↑ (H ↓ • Λ□ (₃₊ k)) (Λ□ (₃₊ k) • H ↓) e285)

------------------------------------------------------------------------
-- (274)

eq274 : ∀ k → Eq285 k →
        (₁₊ (₄₊ k)) ⊢ Ex ↓ • (Λ□ (₃₊ k) ↑) • Ex ↓ ≈ Λ□ (₃₊ k) ↑
eq274 k e285 = begin
  Ex ↓ • (Λ□ (₃₊ k) ↑) • Ex ↓       ≈⟨ sym assoc ⟩
  (Ex ↓ • Λ□ (₃₊ k) ↑) • Ex ↓       ≈⟨ front _ (box-Ex k e285) ⟩
  ((Λ□ (₃₊ k) ↑) • Ex ↓) • Ex ↓     ≈⟨ cancelʳ _ Ex² ⟩
  Λ□ (₃₊ k) ↑ ∎
  where open Tools ((₁₊ (₄₊ k)) VRel,_===_)

------------------------------------------------------------------------
-- (275): the controls on wires 1 and 2 can be exchanged

-- The four-qubit case, the box with three controls.
eq275-0 : 4 ⊢ Ex ↑ • Λ□ 3 • Ex ↑ ≈ Λ□ 3
eq275-0 = eq157

-- Moving the swap of the wires 1 2 across the transposition of the
-- wires 0 2: the braid relation, since τ₀₂ is Ex ↓ • Ex ↑ • Ex ↓.
private
  s-τ : (₃₊ n) ⊢ Ex ↑ • τ₀₂ ≈ τ₀₂ • Ex ↓
  s-τ {n} = begin
    Ex ↑ • (Ex ↓ • Ex ↑ • Ex ↓)     ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
    (Ex ↑ • Ex ↓ • Ex ↑) • Ex ↓     ≈⟨ front _ (sym braid) ⟩
    (Ex ↓ • Ex ↑ • Ex ↓) • Ex ↓ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  τ-s : (₃₊ n) ⊢ τ₀₂ • Ex ↑ ≈ Ex ↓ • τ₀₂
  τ-s {n} = begin
    (Ex ↓ • Ex ↑ • Ex ↓) • Ex ↑     ≈⟨ by-passoc ((□ • □ • □) • □) (□ • (□ • □ • □)) Eq.refl ⟩
    Ex ↓ • (Ex ↑ • Ex ↓ • Ex ↑)     ≈⟨ back _ (sym braid) ⟩
    Ex ↓ • (Ex ↓ • Ex ↑ • Ex ↓) ∎
    where open Tools ((₃₊ n) VRel,_===_)

eq275 : ∀ j → Eq285 j → (₁₊ (₄₊ j)) ⊢ Ex ↑ • Λ□ (₄₊ j) • Ex ↑ ≈ Λ□ (₄₊ j)
eq275 j e285 = S₁₂.⟪⟫-•₄ S-W S-B S-V S-B
  where
  open Tools ((₁₊ (₄₊ j)) VRel,_===_)

  S-W : S₁₂.⟪ CCZX ⟫ ≈ CCZX
  S-W = S₁₂.⟪⟫-fix (sym eq127)

  S-d : S₁₂.⟪ CZ ↑ ⟫ ≈ CZ ↑
  S-d = U-sem (Ex • CZ • Ex) CZ Eq.refl

  S-V : S₁₂.⟪ CCXZ ⟫ ≈ CCXZ
  S-V = begin
    S₁₂.⟪ CCXZ ⟫           ≈⟨ S₁₂.⟪⟫-cong (sym eq124) ⟩
    S₁₂.⟪ CCZX • CZ ↑ ⟫    ≈⟨ S₁₂.⟪⟫-•₂ S-W S-d ⟩
    CCZX • CZ ↑            ≈⟨ eq124 ⟩
    CCXZ ∎

  -- The swap of the wires 1 2 moves the smaller box's box wire, which
  -- (274) undoes.
  S-B : S₁₂.⟪ B□ (₁₊ j) ⟫ ≈ B□ (₁₊ j)
  S-B = begin
    Ex ↑ • (τ₀₂ • (Λ□ (₃₊ j) ↑) • τ₀₂) • Ex ↑
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (Ex ↑ • τ₀₂) • (Λ□ (₃₊ j) ↑) • (τ₀₂ • Ex ↑)
      ≈⟨ cong s-τ (back _ τ-s) ⟩
    (τ₀₂ • Ex ↓) • (Λ□ (₃₊ j) ↑) • (Ex ↓ • τ₀₂)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    τ₀₂ • (Ex ↓ • (Λ□ (₃₊ j) ↑) • Ex ↓) • τ₀₂
      ≈⟨ mid _ _ (eq274 j e285) ⟩
    τ₀₂ • (Λ□ (₃₊ j) ↑) • τ₀₂ ∎
