------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 3.5: an n×n matrix over 𝔻 = ℤ[1/2] is orthogonal if and
-- only if it is a product of generators.  The products of generators
-- are orthogonal (Orthogonal.Unitary-⟦⟧ᵐ); conversely, Algorithm 1
-- reduces an orthogonal M to I, ⟦ synth M ⟧ M = I, and the generators
-- being involutions, M is the matrix of the reversed word.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Generation where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (∃ ; _,_ ; proj₁)
open import Relation.Binary.PropositionalEquality

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Synthesis using (synth ; synth-correct)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Inverse words

-- The generators are involutions, so the inverse of a word is its
-- reversal.
inv : Word (Gen n) → Word (Gen n)
inv [ g ]ʷ  = [ g ]ʷ
inv ε       = ε
inv (u • v) = inv v • inv u

inv-left : (w : Word (Gen n)) → ⟦ inv w ⟧ᵐ ·*· ⟦ w ⟧ᵐ ≡ 𝕀
inv-left [ g ]ʷ = trans (cong₂ _·*·_ (⟦g⟧ᵐ≡ g) (⟦g⟧ᵐ≡ g)) (gmat-invol g)
inv-left ε = ·*·-identityˡ 𝕀
inv-left (u • v) = begin
  ⟦ inv v • inv u ⟧ᵐ ·*· ⟦ u • v ⟧ᵐ                      ≡⟨ cong₂ _·*·_ (⟦•⟧ᵐ (inv v) (inv u)) (⟦•⟧ᵐ u v) ⟩
  (⟦ inv v ⟧ᵐ ·*· ⟦ inv u ⟧ᵐ) ·*· (⟦ u ⟧ᵐ ·*· ⟦ v ⟧ᵐ)    ≡⟨ ·*·-assoc ⟦ inv v ⟧ᵐ ⟦ inv u ⟧ᵐ (⟦ u ⟧ᵐ ·*· ⟦ v ⟧ᵐ) ⟩
  ⟦ inv v ⟧ᵐ ·*· (⟦ inv u ⟧ᵐ ·*· (⟦ u ⟧ᵐ ·*· ⟦ v ⟧ᵐ))    ≡⟨ cong (⟦ inv v ⟧ᵐ ·*·_) (sym (·*·-assoc ⟦ inv u ⟧ᵐ ⟦ u ⟧ᵐ ⟦ v ⟧ᵐ)) ⟩
  ⟦ inv v ⟧ᵐ ·*· ((⟦ inv u ⟧ᵐ ·*· ⟦ u ⟧ᵐ) ·*· ⟦ v ⟧ᵐ)    ≡⟨ cong (λ z → ⟦ inv v ⟧ᵐ ·*· (z ·*· ⟦ v ⟧ᵐ)) (inv-left u) ⟩
  ⟦ inv v ⟧ᵐ ·*· (𝕀 ·*· ⟦ v ⟧ᵐ)                          ≡⟨ cong (⟦ inv v ⟧ᵐ ·*·_) (·*·-identityˡ ⟦ v ⟧ᵐ) ⟩
  ⟦ inv v ⟧ᵐ ·*· ⟦ v ⟧ᵐ                                  ≡⟨ inv-left v ⟩
  𝕀                                                      ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Theorem 3.5

-- Every orthogonal matrix is the matrix of a word.
generation : (M : Matrix n n D) → Unitary M → ∃ λ w → ⟦ w ⟧ᵐ ≡ M
generation M u = inv w , (begin
  ⟦ inv w ⟧ᵐ                            ≡⟨ sym (·*·-identityʳ ⟦ inv w ⟧ᵐ) ⟩
  ⟦ inv w ⟧ᵐ ·*· 𝕀                      ≡⟨ cong (⟦ inv w ⟧ᵐ ·*·_) (sym wM) ⟩
  ⟦ inv w ⟧ᵐ ·*· (⟦ w ⟧ᵐ ·*· M)         ≡⟨ sym (·*·-assoc ⟦ inv w ⟧ᵐ ⟦ w ⟧ᵐ M) ⟩
  (⟦ inv w ⟧ᵐ ·*· ⟦ w ⟧ᵐ) ·*· M         ≡⟨ cong (_·*· M) (inv-left w) ⟩
  𝕀 ·*· M                               ≡⟨ ·*·-identityˡ M ⟩
  M                                     ∎)
  where
  open ≡-Reasoning
  o : ColOrth M
  o = →ColOrth (proj₁ u)
  w = synth M o
  wM : ⟦ w ⟧ᵐ ·*· M ≡ 𝕀
  wM = trans (sym (actMʷ≡ w M)) (synth-correct M o)

-- And the matrix of every word is orthogonal.
words-orthogonal : (w : Word (Gen n)) → Unitary ⟦ w ⟧ᵐ
words-orthogonal = Unitary-⟦⟧ᵐ
