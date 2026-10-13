------------------------------------------------------------------------
-- Presentations of groups
--
-- Conjugation by a permutation matrix relabels finite matrix indices.
-- The proof uses the delta columns directly and never enumerates the
-- dimension.  Sign and K generators are natural under this relabeling.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.PermutationConjugation where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin ; _<_)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary.Decidable using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Instances using (_*_ ; -_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
  using (ent ; ent-·*· ; sum-cong-≗ ; sum-δˡ ; sum-δʳ ; δ ; δ-refl ; δ-≢
        ; mat-ext ; gmat ; ent-gmat ; coef ; coef-M-a ; coef-M-≢
        ; coef-K-a ; coef-K-b ; coef-K-c ; coef-K-d ; coef-K-≢
        ; rowA ; rowB ; rowC ; rowD ; 𝕀 ; ent-𝕀
        ; ·*·-assoc ; ·*·-identityˡ ; ·*·-identityʳ)

module Permutation {n : ℕ}
  (f g : Fin n → Fin n)
  (fg : ∀ i → f (g i) ≡ i) (gf : ∀ i → g (f i) ≡ i)
  (P Q : Matrix n n D)
  (p-entry : ∀ r c → ent P r c ≡ δ r (f c))
  (q-entry : ∀ r c → ent Q r c ≡ δ r (g c)) where

  injective : ∀ {i j} → f i ≡ f j → i ≡ j
  injective {i} {j} eq = trans (sym (gf i)) (trans (cong g eq) (gf j))

  δ-image : ∀ i j → δ (f i) (f j) ≡ δ i j
  δ-image i j = choose (i ≟ j)
    where
    choose : Dec (i ≡ j) → δ (f i) (f j) ≡ δ i j
    choose (yes refl) = trans (δ-refl (f i)) (sym (δ-refl i))
    choose (no ne) = trans (δ-≢ (λ eq → ne (injective eq))) (sym (δ-≢ ne))

  private
    p-row : ∀ r c → ent P r c ≡ δ (g r) c
    p-row r c = trans (p-entry r c)
      (trans (cong (λ i → δ i (f c)) (sym (fg r))) (δ-image (g r) c))

  left-entry : ∀ (A : Matrix n n D) r c → ent (P ·*· A) r c ≡ ent A (g r) c
  left-entry A r c = trans (ent-·*· P A r c)
    (trans (sum-cong-≗ (λ i → cong (_* ent A i c) (p-row r i)))
      (sum-δˡ (λ i → ent A i c) (g r)))

  right-entry : ∀ (A : Matrix n n D) r c → ent (A ·*· Q) r c ≡ ent A r (g c)
  right-entry A r c = trans (ent-·*· A Q r c)
    (trans (sum-cong-≗ (λ i → cong (ent A r i *_) (q-entry i c)))
      (sum-δʳ (λ i → ent A r i) (g c)))

  entry : ∀ (A : Matrix n n D) r c → ent (P ·*· A ·*· Q) r c ≡ ent A (g r) (g c)
  entry A r c = trans (right-entry (P ·*· A) r c) (left-entry A r (g c))

  conjugate : ∀ (A B : Matrix n n D) → (∀ r c → ent B (f r) (f c) ≡ ent A r c) →
    P ·*· A ·*· Q ≡ B
  conjugate A B image = mat-ext λ r c → trans (entry A r c)
    (trans (sym (image (g r) (g c))) (cong₂ (ent B) (fg r) (fg c)))

  inverse-left : Q ·*· P ≡ 𝕀
  inverse-left = mat-ext λ r c → trans (ent-·*· Q P r c)
    (trans (sum-cong-≗ (λ i → cong (ent Q r i *_) (p-entry i c)))
      (trans (sum-δʳ (ent Q r) (f c))
        (trans (q-entry r (f c))
          (trans (cong (δ r) (gf c)) (sym (ent-𝕀 r c))))))

  product : ∀ (A B : Matrix n n D) → P ·*· (A ·*· B) ·*· Q ≡
    (P ·*· A ·*· Q) ·*· (P ·*· B ·*· Q)
  product A B = sym (begin
    (P ·*· A ·*· Q) ·*· (P ·*· B ·*· Q)
      ≡⟨ ·*·-assoc (P ·*· A) Q (P ·*· B ·*· Q) ⟩
    (P ·*· A) ·*· (Q ·*· (P ·*· B ·*· Q))
      ≡⟨ cong ((P ·*· A) ·*·_) (trans
          (cong (Q ·*·_) (·*·-assoc P B Q))
          (sym (·*·-assoc Q P (B ·*· Q)))) ⟩
    (P ·*· A) ·*· ((Q ·*· P) ·*· (B ·*· Q))
      ≡⟨ cong ((P ·*· A) ·*·_) (trans (cong (_·*· (B ·*· Q)) inverse-left)
          (·*·-identityˡ (B ·*· Q))) ⟩
    (P ·*· A) ·*· (B ·*· Q)
      ≡⟨ trans (sym (·*·-assoc (P ·*· A) B Q))
          (cong (_·*· Q) (·*·-assoc P A B)) ⟩
    P ·*· (A ·*· B) ·*· Q ∎)
    where open ≡-Reasoning

  sign-coef : ∀ a r c → coef (M-gen (f a)) (f r) (f c) ≡ coef (M-gen a) r c
  sign-coef a r c = choose (r ≟ a)
    where
    choose : Dec (r ≡ a) → coef (M-gen (f a)) (f r) (f c) ≡ coef (M-gen a) r c
    choose (yes refl) = trans (coef-M-a (f a) (f c))
      (trans (cong -_ (δ-image a c)) (sym (coef-M-a a c)))
    choose (no ra) = trans (coef-M-≢ (f a) (λ eq → ra (injective eq)) (f c))
      (trans (δ-image r c) (sym (coef-M-≢ a ra c)))

  sign : ∀ a → P ·*· gmat (M-gen a) ·*· Q ≡ gmat (M-gen (f a))
  sign a = conjugate (gmat (M-gen a)) (gmat (M-gen (f a))) λ r c → trans (ent-gmat (M-gen (f a)) (f r) (f c))
    (trans (sign-coef a r c) (sym (ent-gmat (M-gen a) r c)))

  module Block (a b c d : Fin n)
    .(ab : a < b) .(bc : b < c) .(cd : c < d)
    .(fab : f a < f b) .(fbc : f b < f c) .(fcd : f c < f d) where

    private
      old = K-gen a b c d ab bc cd
      new = K-gen (f a) (f b) (f c) (f d) fab fbc fcd

      row-image : ∀ (row : D → D → D → D → D) x →
        row (δ (f a) (f x)) (δ (f b) (f x)) (δ (f c) (f x)) (δ (f d) (f x)) ≡
        row (δ a x) (δ b x) (δ c x) (δ d x)
      row-image row x rewrite δ-image a x | δ-image b x | δ-image c x | δ-image d x = refl

    coefficients : ∀ r x → coef new (f r) (f x) ≡ coef old r x
    coefficients r x = first (r ≟ a)
      where
      first : Dec (r ≡ a) → coef new (f r) (f x) ≡ coef old r x
      first (yes refl) = trans (coef-K-a fab fbc fcd (f x))
        (trans (row-image rowA x) (sym (coef-K-a ab bc cd x)))
      first (no ra) = second (r ≟ b)
        where
        second : Dec (r ≡ b) → coef new (f r) (f x) ≡ coef old r x
        second (yes refl) = trans (coef-K-b fab fbc fcd (f x))
          (trans (row-image rowB x) (sym (coef-K-b ab bc cd x)))
        second (no rb) = third (r ≟ c)
          where
          third : Dec (r ≡ c) → coef new (f r) (f x) ≡ coef old r x
          third (yes refl) = trans (coef-K-c fab fbc fcd (f x))
            (trans (row-image rowC x) (sym (coef-K-c ab bc cd x)))
          third (no rc) = fourth (r ≟ d)
            where
            fourth : Dec (r ≡ d) → coef new (f r) (f x) ≡ coef old r x
            fourth (yes refl) = trans (coef-K-d fab fbc fcd (f x))
              (trans (row-image rowD x) (sym (coef-K-d ab bc cd x)))
            fourth (no rd) = trans
              (coef-K-≢ fab fbc fcd (λ eq → ra (injective eq))
                (λ eq → rb (injective eq)) (λ eq → rc (injective eq))
                (λ eq → rd (injective eq)) (f x))
              (trans (δ-image r x) (sym (coef-K-≢ ab bc cd ra rb rc rd x)))

    block : P ·*· gmat old ·*· Q ≡ gmat new
    block = conjugate (gmat old) (gmat new) λ r c → trans (ent-gmat new (f r) (f c))
      (trans (coefficients r c) (sym (ent-gmat old r c)))
