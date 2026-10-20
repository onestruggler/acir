------------------------------------------------------------------------
-- Presentations of groups
--
-- A decoded letter of P′ has the letter's matrix, decided by one boolean
-- (four wires)
--
-- The check compares the circuit's row-operation reading with the
-- letter's two-level word read at the Gray numbering, each scaled by
-- the other's power of γ, as DecodingChecks does; `chk-sem` turns a
-- successful check into the equation of scaled operators that
-- Lemma87.Decodes asks of a letter.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Lemma87.Chk where

open import Data.Bool using (T ; true)
open import Data.Fin using (Fin ; toℕ) renaming (_<_ to _<ᶠ_)
open import Data.Nat using (_<ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧M ; ⟦⟧-ix ; len)
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Clifford+CS.FastEval using (⟦_⟧Q ; nK ; Q-≡)
open import Examples.Groups.Clifford+CS.BridgeGray 4 using (⟦_⟧ʸ ; ⟦_⟧Y ; ⟦_⟧PY)
open import Examples.Groups.Clifford+CS.Decoding 0 using (d)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL

-- The stored reading of a two-level word at the Gray numbering.
⟦_⟧GM : Word (TL.Gen 16) → Mat 4
⟦ [ y ]ʷ ⟧GM = matOf (proj₂ ⟦ y ⟧ʸ)
⟦ ε ⟧GM      = idM
⟦ u • t ⟧GM  = mulM ⟦ u ⟧GM ⟦ t ⟧GM

GM-ix : ∀ (u : Word (TL.Gen 16)) → proj₂ ⟦ u ⟧Y ≐ ix ⟦ u ⟧GM
GM-ix [ y ]ʷ  = ≐-sym (ix-matOf (proj₂ ⟦ y ⟧ʸ))
GM-ix ε       = ≐-sym ix-id
GM-ix (u • t) = ≐-trans (⊙-cong (GM-ix u) (GM-ix t)) (≐-sym (ix-mul ⟦ u ⟧GM ⟦ t ⟧GM))

-- The check.
Chk : GenP 16 → Set
Chk x = eqM (scaleM (γ^ proj₁ ⟦ asG x ⟧Y) ⟦ d x ⟧Q) (scaleM (γ^ nK (d x)) ⟦ asG x ⟧GM) ≡ true

-- A successful check: the decoded letter has the letter's matrix.
chk-sem : ∀ (x : GenP 16) → Chk x → ⟦ d x ⟧ ~ ⟦ [ x ]ʷ ⟧PY
chk-sem x e =
  ≐-trans (·-cong Eq.refl (⟦⟧-ix (d x)))
    (≐-trans (≐-sym (ix-scaleM (γ^ ℓ) ⟦ d x ⟧M))
      (≐-trans (ix-≡ same)
        (≐-trans (ix-scaleM (γ^ len (d x)) ⟦ asG x ⟧GM)
          (·-cong Eq.refl (≐-sym (GM-ix (asG x)))))))
  where
  ℓ = proj₁ ⟦ asG x ⟧Y

  same : scaleM (γ^ ℓ) ⟦ d x ⟧M ≡ scaleM (γ^ len (d x)) ⟦ asG x ⟧GM
  same = Q-≡ (d x) ℓ ⟦ asG x ⟧GM e

-- An order of two literal indices.
lt : ∀ (a b : Fin 16) {p : T (toℕ a <ᵇ toℕ b)} → a <ᶠ b
lt a b {p} = <ᵇ⇒< (toℕ a) (toℕ b) p
