------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the concrete two-qubit Schreier presentation.
-- The 33 table factorizations are checked by exact dyadic evaluation
-- inside Agda, then converted to auxiliary derivations by completeness.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.TwoQubit.Soundness where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (z≤n ; s≤s)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (recompute)
open import Notations using (₀ ; ₁ ; ₂ ; ₃)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH.Encoding using (encode)
open import Examples.Groups.CCX+HH.TwoQubit.Table
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as M
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open S using (actV ; set₁ ; set₂)

private
  k : T.Gen 4
  k = T.K-gen ₀ ₁ ₂ ₃ (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n)))

rep : Coset → Word (T.Gen 4)
rep c0 = ε
rep c1 = T.M ₀
rep c2 = T.M ₀ • [ k ]ʷ

private
  Checked : Coset → T.Gen 4 → Set
  Checked c g = S.⟦ rep c • [ g ]ʷ ⟧ᵐ ≡
                S.⟦ encode (emit c g) • rep (step c g) ⟧ᵐ

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  checked-M : ∀ c a → Checked c (T.M-gen a)
  checked-M c0 ₀ = refl
  checked-M c0 ₁ = refl
  checked-M c0 ₂ = refl
  checked-M c0 ₃ = refl
  checked-M c1 ₀ = refl
  checked-M c1 ₁ = refl
  checked-M c1 ₂ = refl
  checked-M c1 ₃ = refl
  checked-M c2 ₀ = refl
  checked-M c2 ₁ = refl
  checked-M c2 ₂ = refl
  checked-M c2 ₃ = refl

  checked-X : ∀ c a b (p : a < b) → Checked c (T.X-gen a b p)
  checked-X c ₀ ₀ ()
  checked-X c ₁ ₀ ()
  checked-X c ₁ ₁ (s≤s ())
  checked-X c ₂ ₀ ()
  checked-X c ₂ ₁ (s≤s ())
  checked-X c ₂ ₂ (s≤s (s≤s ()))
  checked-X c ₃ ₀ ()
  checked-X c ₃ ₁ (s≤s ())
  checked-X c ₃ ₂ (s≤s (s≤s ()))
  checked-X c ₃ ₃ (s≤s (s≤s (s≤s ())))
  checked-X c0 ₀ ₁ p = refl
  checked-X c0 ₀ ₂ p = refl
  checked-X c0 ₀ ₃ p = refl
  checked-X c0 ₁ ₂ p = refl
  checked-X c0 ₁ ₃ p = refl
  checked-X c0 ₂ ₃ p = refl
  checked-X c1 ₀ ₁ p = refl
  checked-X c1 ₀ ₂ p = refl
  checked-X c1 ₀ ₃ p = refl
  checked-X c1 ₁ ₂ p = refl
  checked-X c1 ₁ ₃ p = refl
  checked-X c1 ₂ ₃ p = refl
  checked-X c2 ₀ ₁ p = refl
  checked-X c2 ₀ ₂ p = refl
  checked-X c2 ₀ ₃ p = refl
  checked-X c2 ₁ ₂ p = refl
  checked-X c2 ₁ ₃ p = refl
  checked-X c2 ₂ ₃ p = refl

  checked-K-base : ∀ c → Checked c k
  checked-K-base c0 = refl
  checked-K-base c1 = refl
  checked-K-base c2 = refl

checked-K : ∀ s a b c d (p : a < b) (q : b < c) (r : c < d) →
  Checked s (T.K-gen a b c d p q r)
checked-K s a b c d p q r with full4 a b c d p q r
... | refl , refl , refl , refl = checked-K-base s

factor : ∀ c y → PB._≈_ (T._===_ {4})
  (rep c • [ y ]ʷ) (encode (emit c y) • rep (step c y))
factor c (T.M-gen a) = M.completeness (checked-M c a)
factor c (T.X-gen a b p) =
  M.completeness (checked-X c a b (recompute (a FP.<? b) p))
factor s (T.K-gen a b c d p q r) = M.completeness
  (checked-K s a b c d (recompute (a FP.<? b) p)
     (recompute (b FP.<? c) q) (recompute (c FP.<? d) r))

module Proven = Theory.Complete.Sound state-roundtrip state-relations rep PB.refl factor
open Proven public using (encoded-soundness)
