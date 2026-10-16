------------------------------------------------------------------------
-- Presentations of groups
--
-- The control on the top wire, where it reads 1
--
-- `ctrl₁` reads an operator on m wires as the one on m + 1 wires that
-- applies it where the top wire reads 1 (the semantics of λ¹; Five.Sem.TL
-- has `ctrl`, where it reads 0): multiplicative (`ctrl₁-∙`, `ctrl₁-ε`)
-- and respecting the scaled equivalence (`ctrl₁-cong`).  The proofs are
-- TL's with the two projections exchanged.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Ctrl1 where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (P₀ ; P₁ ; γI)

private
  variable
    m n : ℕ

private
  Z₁ : Op 1
  Z₁ _ _ = 0#

  P00 : (P₀ ⊙ P₀) ≐ P₀
  P00 (false ∷ []) (false ∷ []) = refl
  P00 (false ∷ []) (true ∷ [])  = refl
  P00 (true ∷ [])  (false ∷ []) = refl
  P00 (true ∷ [])  (true ∷ [])  = refl

  P11 : (P₁ ⊙ P₁) ≐ P₁
  P11 (false ∷ []) (false ∷ []) = refl
  P11 (false ∷ []) (true ∷ [])  = refl
  P11 (true ∷ [])  (false ∷ []) = refl
  P11 (true ∷ [])  (true ∷ [])  = refl

  P01 : (P₀ ⊙ P₁) ≐ Z₁
  P01 (false ∷ []) (false ∷ []) = refl
  P01 (false ∷ []) (true ∷ [])  = refl
  P01 (true ∷ [])  (false ∷ []) = refl
  P01 (true ∷ [])  (true ∷ [])  = refl

  P10 : (P₁ ⊙ P₀) ≐ Z₁
  P10 (false ∷ []) (false ∷ []) = refl
  P10 (false ∷ []) (true ∷ [])  = refl
  P10 (true ∷ [])  (false ∷ []) = refl
  P10 (true ∷ [])  (true ∷ [])  = refl

  P0+P1 : (λ u v → P₀ u v + P₁ u v) ≐ Idₒ {1}
  P0+P1 (false ∷ []) (false ∷ []) = refl
  P0+P1 (false ∷ []) (true ∷ [])  = refl
  P0+P1 (true ∷ [])  (false ∷ []) = refl
  P0+P1 (true ∷ [])  (true ∷ [])  = refl

  tensor-zeroʳ : (M : Op m) → ∀ (x y : Bits (m +ℕ 1)) → tensor M Z₁ x y ≡ 0#
  tensor-zeroʳ {zero}  M x       y       = *-zeroʳ (M [] [])
  tensor-zeroʳ {suc m} M (a ∷ x) (b ∷ y) = tensor-zeroʳ {m} (λ u v → M (a ∷ u) (b ∷ v)) x y

  tensor-addʳ : (M : Op m) (N N′ : Op 1) → ∀ (x y : Bits (m +ℕ 1)) →
                tensor M (λ u v → N u v + N′ u v) x y ≡ tensor M N x y + tensor M N′ x y
  tensor-addʳ {zero}  M N N′ x       y       = *-distribˡ-+ (M [] []) (N x y) (N′ x y)
  tensor-addʳ {suc m} M N N′ (a ∷ x) (b ∷ y) =
    tensor-addʳ {m} (λ u v → M (a ∷ u) (b ∷ v)) N N′ x y

  -- The product distributes over the sum of operators.
  ⊙-+ˡ : (A B C : Op n) → ((λ x y → A x y + B x y) ⊙ C) ≐ (λ x y → (A ⊙ C) x y + (B ⊙ C) x y)
  ⊙-+ˡ A B C x y =
    Eq.trans (Σ-cong {f = λ z → (A x z + B x z) * C z y} {g = λ z → A x z * C z y + B x z * C z y}
                     (λ z → *-distribʳ-+ (C z y) (A x z) (B x z)))
             (Σ-add (λ z → A x z * C z y) (λ z → B x z * C z y))

  ⊙-+ʳ : (A B C : Op n) → (A ⊙ (λ x y → B x y + C x y)) ≐ (λ x y → (A ⊙ B) x y + (A ⊙ C) x y)
  ⊙-+ʳ A B C x y =
    Eq.trans (Σ-cong {f = λ z → A x z * (B z y + C z y)} {g = λ z → A x z * B z y + A x z * C z y}
                     (λ z → *-distribˡ-+ (A x z) (B z y) (C z y)))
             (Σ-add (λ z → A x z * B z y) (λ z → A x z * C z y))


private
  γI-⊙ : ∀ k l → (γI {n} k ⊙ γI l) ≐ γI (k +ℕ l)
  γI-⊙ k l = ≐-trans (·-⊙ (γ^ k) (γ^ l) Idₒ Idₒ)
               (·-cong (Eq.sym (γ^-+ k l)) (⊙-identityˡ Idₒ))

ctrl₁Op : ℕ → Op m → Op (m +ℕ 1)
ctrl₁Op {m} k M x y = tensor (γI {m} k) P₀ x y + tensor M P₁ x y

ctrl₁ : Scaled m → Scaled (m +ℕ 1)
ctrl₁ (k , M) = (k , ctrl₁Op k M)

private
  module Prod (k l : ℕ) (M N : Op m) where
    A B C D : Op (m +ℕ 1)
    A = tensor (γI {m} k) P₀
    B = tensor M P₁
    C = tensor (γI {m} l) P₀
    D = tensor N P₁

    AC : (A ⊙ C) ≐ tensor (γI {m} (k +ℕ l)) P₀
    AC = ≐-trans (tensor-⊙ (γI k) (γI l) P₀ P₀) (tensor-cong (γI-⊙ k l) P00)

    AD : ∀ x y → (A ⊙ D) x y ≡ 0#
    AD x y = Eq.trans (≐-trans (tensor-⊙ (γI k) N P₀ P₁) (tensor-cong (≐-refl (γI k ⊙ N)) P01) x y)
                      (tensor-zeroʳ (γI k ⊙ N) x y)

    BC : ∀ x y → (B ⊙ C) x y ≡ 0#
    BC x y = Eq.trans (≐-trans (tensor-⊙ M (γI l) P₁ P₀) (tensor-cong (≐-refl (M ⊙ γI l)) P10) x y)
                      (tensor-zeroʳ (M ⊙ γI l) x y)

    BD : (B ⊙ D) ≐ tensor (M ⊙ N) P₁
    BD = ≐-trans (tensor-⊙ M N P₁ P₁) (tensor-cong (≐-refl (M ⊙ N)) P11)

    prod : (ctrl₁Op k M ⊙ ctrl₁Op l N) ≐ ctrl₁Op (k +ℕ l) (M ⊙ N)
    prod x y =
      Eq.trans (⊙-+ˡ A B (λ x y → C x y + D x y) x y)
        (Eq.trans (Eq.cong₂ _+_ (⊙-+ʳ A C D x y) (⊙-+ʳ B C D x y))
          (Eq.trans (Eq.cong₂ _+_ (Eq.cong₂ _+_ (AC x y) (AD x y)) (Eq.cong₂ _+_ (BC x y) (BD x y)))
            (Eq.cong₂ _+_ (+-identityʳ _) (+-identityˡ _))))

ctrl₁-∙ : (s t : Scaled m) → ctrl₁ (s ∙ t) ~ (ctrl₁ s ∙ ctrl₁ t)
ctrl₁-∙ (k , M) (l , N) =
  ~-reflexive {l = k +ℕ l} {k +ℕ l} {M = ctrl₁Op (k +ℕ l) (M ⊙ N)} {ctrl₁Op k M ⊙ ctrl₁Op l N}
    refl (≐-sym (Prod.prod k l M N))

ctrl₁-ε : ctrl₁ (ε∙ {m}) ~ ε∙
ctrl₁-ε {m} = ~-reflexive {l = 0} {0} {M = ctrl₁Op {m} 0 Idₒ} {Idₒ} refl (λ x y →
  Eq.trans (Eq.cong (_+ tensor Idₒ P₁ x y)
                    (tensor-cong {M = γI {m} 0} {M' = Idₒ} (·-1 Idₒ) (≐-refl P₀) x y))
    (Eq.trans (Eq.sym (tensor-addʳ Idₒ P₀ P₁ x y))
      (Eq.trans (tensor-cong {M = Idₒ {m}} (≐-refl Idₒ) P0+P1 x y) (Eq.sym (tensor-Id {m} {1} x y)))))

private
  tensor-scale : (c : 𝔽) (M : Op m) (N : Op n) → ∀ x y → c * tensor M N x y ≡ tensor (c · M) N x y
  tensor-scale {zero}  c M N x       y       = Eq.sym (*-assoc c (M [] []) (N x y))
  tensor-scale {suc m} c M N (a ∷ x) (b ∷ y) =
    tensor-scale {m} c (λ u v → M (a ∷ u) (b ∷ v)) N x y

-- The control respects the scaled equivalence.
ctrl₁-cong : {s t : Scaled m} → s ~ t → ctrl₁ s ~ ctrl₁ t
ctrl₁-cong {m} {k , M} {l , N} e x y =
  Eq.trans (*-distribˡ-+ (γ^ l) (tensor (γI {m} k) P₀ x y) (tensor M P₁ x y))
    (Eq.trans (Eq.cong₂ _+_ A B)
      (Eq.sym (*-distribˡ-+ (γ^ k) (tensor (γI {m} l) P₀ x y) (tensor N P₁ x y))))
  where
  A : γ^ l * tensor (γI {m} k) P₀ x y ≡ γ^ k * tensor (γI {m} l) P₀ x y
  A = Eq.trans (tensor-scale (γ^ l) (γI k) P₀ x y)
        (Eq.trans (tensor-cong {M = γ^ l · γI {m} k} {M' = γ^ k · γI {m} l}
                     (·-comm (γ^ l) (γ^ k) Idₒ) (≐-refl P₀) x y)
          (Eq.sym (tensor-scale (γ^ k) (γI l) P₀ x y)))

  B : γ^ l * tensor M P₁ x y ≡ γ^ k * tensor N P₁ x y
  B = Eq.trans (tensor-scale (γ^ l) M P₁ x y)
        (Eq.trans (tensor-cong {M = γ^ l · M} {M' = γ^ k · N} e (≐-refl P₁) x y)
          (Eq.sym (tensor-scale (γ^ k) N P₁ x y)))

-- At one scale, pointwise equal operators.
ctrl₁-≐ : ∀ {k} {M M′ : Op m} → M ≐ M′ → ctrl₁ (k , M) ~ ctrl₁ (k , M′)
ctrl₁-≐ {m} {k} {M} {M′} e = ctrl₁-cong {m} {k , M} {k , M′} (·-cong refl e)
