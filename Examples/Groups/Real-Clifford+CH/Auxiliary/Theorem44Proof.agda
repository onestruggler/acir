------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 4.4, proved
--
-- The paper imports Theorem 4.4 from Fang, Heunen and Kaarsgaard:
-- Figure 6 is complete for the proper words over the one- and
-- two-level generators.  Real-Clifford+CH-TwoLevel-Clement proves the
-- presentation of O_N(ℤ[1/√2]) by that figure in every dimension N,
-- by Clément's own proof (Thesis.MainLemma.completeness), and the
-- bridge carries it here.  A proper word u translates to φ u
-- (Bridge.Syntax), whose matrix is the reading Φ ⟦ u ⟧ of this
-- development's matrix as a matrix over ℤ[1/√2] (Bridge.Matrix).  Two
-- proper words with ⟦ u ⟧ ~ ⟦ t ⟧ then have φ u ≈ φ t by Hadamard-Pi's
-- Figure 6, so ψ (φ u) ≈ ψ (φ t) by this one, and u ≈ t (Complete).
--
-- Both readings of the development are covered: on four basis vectors,
-- numbered by TwoQubit's table (theorem-4-4₂), and on 2ⁿ for n ≥ 3,
-- numbered by the Gray code at the width of P (theorem-4-4ₙ).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem44Proof where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ ; _^_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; trans ; sym)

open import Quantum.Synthesis.Matrix using (_·*·_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Notations using (₃₊)

import Examples.Groups.Real-Clifford+CH.Semantics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (ProperG ; −1[_] ; X[_,_] ; H[_,_])
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1 using (Complete⁶)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (⟦_⟧ᴳ)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem44 as T44
import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray as Gray
import Examples.Groups.Real-Clifford+CH.TwoQubit as TwoQubit
import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410Proof as T410
import Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Matrix as Matrix
import Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Syntax as Syntax
import Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.TwoQubit as B₂
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (SemiRingD ; RingD ; AdjointD)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (𝕀 ; ⟦_⟧ᵐ)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.MainLemma as ML

------------------------------------------------------------------------
-- Completeness of Figure 6, for any reading through a numbering

module Complete
  (n : ℕ) (code : Fin (2 ^ n) → Bits n) (index : Bits n → Fin (2 ^ n))
  (code-index : ∀ g → code (index g) ≡ g) (index-code : ∀ a → index (code a) ≡ a)
  (⟦_⟧W : Word (G.Gen (2 ^ n)) → S.Scaled n)
  (let open Matrix n code index code-index index-code)
  (W-ε : Φ ⟦ ε ⟧W ≡ 𝕀)
  (W-• : ∀ u v → Φ ⟦ u • v ⟧W ≡ Φ ⟦ u ⟧W ·*· Φ ⟦ v ⟧W)
  (W-g : ∀ g → ProperG g → Φ ⟦ [ g ]ʷ ⟧W ≡ ⟦ φg g ⟧ᵐ)
  where

  open Words ⟦_⟧W W-ε W-• W-g using (sem)
  open Syntax (2 ^ n) using (ψ-≈ ; ψφ)

  complete : Complete⁶ ⟦_⟧W S._~_
  complete {u} {t} pu pt e =
    PB.trans (PB.sym (ψφ u pu))
      (PB.trans (ψ-≈ (ML.completeness (trans (sym (sem u pu)) (trans (Φ-~ {⟦ u ⟧W} {⟦ t ⟧W} e) (sem t pt)))))
                (ψφ t pt))

------------------------------------------------------------------------
-- On four basis vectors

theorem-4-4₂ : T44.Theorem-4-4₂
theorem-4-4₂ = C.complete
  where
  module C = Complete 2 TwoQubit.bits B₂.index B₂.code-index B₂.index-code TwoQubit.BF.⟦_⟧Y
    B₂.Φ-ε (λ u v → B₂.Φ-∙ (TwoQubit.BF.⟦ u ⟧Y) (TwoQubit.BF.⟦ v ⟧Y))
    (λ g pg → trans (B₂.Φ-agree g) (B₂.letter g pg))

------------------------------------------------------------------------
-- On 2ⁿ basis vectors, n = 3 + k

theorem-4-4ₙ : ∀ k → T44.Theorem-4-4ₙ k
theorem-4-4ₙ k = C.complete
  where
  n = ₃₊ k
  module M = Matrix n (Gray.code n) (Gray.index n) (Gray.code-index n) (Gray.index-code n)

  -- The development's matrices of the generators are those M reads.
  ᴳ≡c : ∀ g → ⟦ g ⟧ᴳ ≡ M.⟦ g ⟧c
  ᴳ≡c −1[ a ]    = refl
  ᴳ≡c X[ a , b ] = refl
  ᴳ≡c H[ a , b ] = refl

  module C = Complete n (Gray.code n) (Gray.index n) (Gray.code-index n) (Gray.index-code n) (T410.BG.⟦_⟧Y k)
    M.Φ-ε (λ u v → M.Φ-∙ (T410.BG.⟦_⟧Y k u) (T410.BG.⟦_⟧Y k v))
    (λ g pg → trans (cong M.Φ (ᴳ≡c g)) (M.letter g pg))
