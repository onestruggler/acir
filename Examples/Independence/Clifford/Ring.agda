------------------------------------------------------------------------
-- Presentations of groups
--
-- ℤ[ω] in 𝔻[ω]: the entries of Cliff₂'s matrices read in the ring of
-- Selinger's semantics
--
-- Cliff₂'s matrices have entries in ℤ[ω] as Examples.Independence.
-- Semantics.Quartic writes it, c₀ + c₁ x + c₂ x² + c₃ x³; EucDomain's
-- ℤ[ω] writes the same number aω³ + bω² + cω + d, and embeds in 𝔻[ω] =
-- ℤ[1/√2, i] (Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring.emb).  φ
-- is the composite, a ring homomorphism: the two products are the same
-- four polynomials, checked by the integer solver.  It sends x to ω and
-- √2 = x − x³ to the inverse of 1/√2.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford.Ring where

open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Integer.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Quantum.Synthesis.Ring using (Omega)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; Z ; emb ; emb-+ ; emb-* ; module ZR ; module DR ; ωᴰ ; √½ ; √2ᶻ ;
         _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)

open import Examples.Independence.Semantics.Qubit using (module ZΩ ; √2)

open +-*-Solver using (solve ; _:=_ ; _:+_ ; _:*_ ; _:-_ ; con)

private
  cong₄ : ∀ {A B C E F : Set} (f : A → B → C → E → F) {a a′ b b′ c c′ e e′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → f a b c e ≡ f a′ b′ c′ e′
  cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- ℤ[ω] to EucDomain's ℤ[ω]

ψ : ZΩ.Q → Z
ψ ZΩ.⟨ a₀ , a₁ , a₂ , a₃ ⟩ = Omega a₃ a₂ a₁ a₀

ψ-+ : ∀ a b → ψ (a ZΩ.+ b) ≡ ψ a ZR.+ ψ b
ψ-+ ZΩ.⟨ a₀ , a₁ , a₂ , a₃ ⟩ ZΩ.⟨ b₀ , b₁ , b₂ , b₃ ⟩ = refl

ψ-* : ∀ a b → ψ (a ZΩ.* b) ≡ ψ a ZR.* ψ b
ψ-* a@(ZΩ.⟨ a₀ , a₁ , a₂ , a₃ ⟩) b@(ZΩ.⟨ b₀ , b₁ , b₂ , b₃ ⟩) =
  Eq.trans (Eq.cong ψ (ZΩ.*≡*ₗ a b)) (cong₄ Omega e₃ e₂ e₁ e₀)
  where
  e₃ = solve 8 (λ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
         ((((a₀ :* b₃) :+ (a₁ :* b₂)) :+ (a₂ :* b₁)) :+ (a₃ :* b₀))
           :+ (con (+ 0) :* ((a₂ :* b₃) :+ (a₃ :* b₂)))
         := (((a₃ :* b₀) :+ (a₂ :* b₁)) :+ (a₁ :* b₂)) :+ (a₀ :* b₃))
         refl a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  e₂ = solve 8 (λ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
         ((((a₀ :* b₂) :+ (a₁ :* b₁)) :+ (a₂ :* b₀))
           :+ (con (+ 0) :* (((a₁ :* b₃) :+ (a₂ :* b₂)) :+ (a₃ :* b₁))))
           :+ (((con (+ 0) :* con (+ 0)) :+ con -[1+ 0 ]) :* (a₃ :* b₃))
         := (((a₂ :* b₀) :+ (a₁ :* b₁)) :+ (a₀ :* b₂)) :- (a₃ :* b₃))
         refl a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  e₁ = solve 8 (λ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
         ((a₀ :* b₁) :+ (a₁ :* b₀)) :+ (con -[1+ 0 ] :* ((a₂ :* b₃) :+ (a₃ :* b₂)))
         := (((a₁ :* b₀) :+ (a₀ :* b₁)) :- (a₃ :* b₂)) :- (a₂ :* b₃))
         refl a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  e₀ = solve 8 (λ a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ →
         ((a₀ :* b₀) :+ (con -[1+ 0 ] :* (((a₁ :* b₃) :+ (a₂ :* b₂)) :+ (a₃ :* b₁))))
           :+ ((con (+ 0) :* con -[1+ 0 ]) :* (a₃ :* b₃))
         := (((a₀ :* b₀) :- (a₃ :* b₁)) :- (a₂ :* b₂)) :- (a₁ :* b₃))
         refl a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃

------------------------------------------------------------------------
-- ℤ[ω] in 𝔻[ω]

φ : ZΩ.Q → D
φ a = emb (ψ a)

φ-+ : ∀ a b → φ (a ZΩ.+ b) ≡ φ a DR.+ φ b
φ-+ a b = Eq.trans (Eq.cong emb (ψ-+ a b)) (emb-+ (ψ a) (ψ b))

φ-* : ∀ a b → φ (a ZΩ.* b) ≡ φ a DR.* φ b
φ-* a b = Eq.trans (Eq.cong emb (ψ-* a b)) (emb-* (ψ a) (ψ b))

φ-0 : φ ZΩ.0q ≡ DR.0#
φ-0 = refl

φ-1 : φ ZΩ.1q ≡ DR.1#
φ-1 = refl

φ-x : φ ZΩ.x ≡ ωᴰ
φ-x = refl

φ-√2 : φ √2 ≡ emb √2ᶻ
φ-√2 = refl

opaque
  unfolding _*ᴰ_

  -- 1/√2 inverts √2.
  √½-√2 : √½ DR.* φ √2 ≡ DR.1#
  √½-√2 = refl
