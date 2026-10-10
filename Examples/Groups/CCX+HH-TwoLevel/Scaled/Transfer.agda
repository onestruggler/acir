------------------------------------------------------------------------
-- Presentations of groups
--
-- A ring homomorphism f : A → B that sends the scalar of K over A to
-- that over B commutes with the action of the generators of 𝒢ₙ
-- (Action at A and at B): so the matrix of a word over B is the image
-- of its matrix over A (⟦⟧-map).  Images of matrices also respect
-- products and adjoints, and are injective with f.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH-TwoLevel.Scaled.Transfer
  {A B : Set} {{RA : Ring A}} {{AdA : Adjoint A}} {{RB : Ring B}} {{AdB : Adjoint B}}
  (isCRA : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#) (adjA : IsInvolutiveRingEndo {A} adj) (hA : A)
  (isCRB : IsCommutativeRing (_≡_ {A = B}) _+_ _*_ -_ 0# 1#) (adjB : IsInvolutiveRingEndo {B} adj) (hB : B)
  (f : A → B)
  (f-+ : ∀ x y → f (x + y) ≡ f x + f y) (f-* : ∀ x y → f (x * y) ≡ f x * f y)
  (f-neg : ∀ x → f (- x) ≡ - f x) (f-0 : f 0# ≡ 0#) (f-1 : f 1# ≡ 1#) (f-h : f hA ≡ hB)
  (f-adj : ∀ x → f (adj x) ≡ adj (f x))
  where

open import Data.Fin.Base using (Fin ; zero ; suc)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; unMatrix ; _·*·_ ; adjoint)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen ; M-gen ; X-gen ; K-gen)
import Examples.Groups.CCX+HH-TwoLevel.Action as Action

private
  module CA = Action {A} ⦃ RA ⦄ ⦃ AdA ⦄ isCRA adjA hA
  module CB = Action {B} ⦃ RB ⦄ ⦃ AdB ⦄ isCRB adjB hB
  variable
    n m : ℕ

------------------------------------------------------------------------
-- Images of vectors and matrices

mapV : Vec A n → Vec B n
mapV = Vec.map f

mapM : Matrix n m A → Matrix n m B
mapM M = Matrix' (Vec.map mapV (unMatrix M))

!-mapV : (v : Vec A n) (x : Fin n) → mapV v CB.! x ≡ f (v CA.! x)
!-mapV v x = VecP.lookup-map x f v

col-mapM : (M : Matrix n m A) (c : Fin m) → CB.col (mapM M) c ≡ mapV (CA.col M c)
col-mapM M c = VecP.lookup-map c mapV (unMatrix M)

ent-mapM : (M : Matrix n m A) (r : Fin n) (c : Fin m) → CB.ent (mapM M) r c ≡ f (CA.ent M r c)
ent-mapM M r c = trans (cong (CB._! r) (col-mapM M c)) (!-mapV (CA.col M c) r)

------------------------------------------------------------------------
-- The scalars and rows

private
  f-δ : (x y : Fin n) → f (CA.δ x y) ≡ CB.δ x y
  f-δ x y = by (x FinP.≟ y)
    where
    by : Dec (x ≡ y) → f (CA.δ x y) ≡ CB.δ x y
    by (yes refl) = trans (cong f (CA.δ-refl x)) (trans f-1 (sym (CB.δ-refl x)))
    by (no ne) = trans (cong f (CA.δ-≢ ne)) (trans f-0 (sym (CB.δ-≢ ne)))

  f-m1 : f CA.m1 ≡ CB.m1
  f-m1 = trans (f-neg 1#) (cong -_ f-1)

  f-lin : ∀ s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ →
          f (CA.lin s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄) ≡ CB.lin (f s₁) (f s₂) (f s₃) (f s₄) (f x₁) (f x₂) (f x₃) (f x₄)
  f-lin s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ =
    trans (f-* hA _)
      (cong₂ _*_ f-h
        (trans (f-+ _ _)
          (cong₂ _+_ (trans (f-+ _ _) (cong₂ _+_ (trans (f-+ _ _) (cong₂ _+_ (f-* s₁ x₁) (f-* s₂ x₂))) (f-* s₃ x₃)))
                     (f-* s₄ x₄))))

  cong₄ : ∀ (F : B → B → B → B → B) {x x′ y y′ z z′ t t′} →
          x ≡ x′ → y ≡ y′ → z ≡ z′ → t ≡ t′ → F x y z t ≡ F x′ y′ z′ t′
  cong₄ F refl refl refl refl = refl

  f-rowA : ∀ x₁ x₂ x₃ x₄ → f (CA.rowA x₁ x₂ x₃ x₄) ≡ CB.rowA (f x₁) (f x₂) (f x₃) (f x₄)
  f-rowA x₁ x₂ x₃ x₄ = trans (f-lin _ _ _ _ x₁ x₂ x₃ x₄)
                         (cong₄ (λ a b c d → CB.lin a b c d (f x₁) (f x₂) (f x₃) (f x₄)) f-1 f-1 f-1 f-1)

  f-rowB : ∀ x₁ x₂ x₃ x₄ → f (CA.rowB x₁ x₂ x₃ x₄) ≡ CB.rowB (f x₁) (f x₂) (f x₃) (f x₄)
  f-rowB x₁ x₂ x₃ x₄ = trans (f-lin _ _ _ _ x₁ x₂ x₃ x₄)
                         (cong₄ (λ a b c d → CB.lin a b c d (f x₁) (f x₂) (f x₃) (f x₄)) f-1 f-m1 f-1 f-m1)

  f-rowC : ∀ x₁ x₂ x₃ x₄ → f (CA.rowC x₁ x₂ x₃ x₄) ≡ CB.rowC (f x₁) (f x₂) (f x₃) (f x₄)
  f-rowC x₁ x₂ x₃ x₄ = trans (f-lin _ _ _ _ x₁ x₂ x₃ x₄)
                         (cong₄ (λ a b c d → CB.lin a b c d (f x₁) (f x₂) (f x₃) (f x₄)) f-1 f-1 f-m1 f-m1)

  f-rowD : ∀ x₁ x₂ x₃ x₄ → f (CA.rowD x₁ x₂ x₃ x₄) ≡ CB.rowD (f x₁) (f x₂) (f x₃) (f x₄)
  f-rowD x₁ x₂ x₃ x₄ = trans (f-lin _ _ _ _ x₁ x₂ x₃ x₄)
                         (cong₄ (λ a b c d → CB.lin a b c d (f x₁) (f x₂) (f x₃) (f x₄)) f-1 f-m1 f-m1 f-1)

------------------------------------------------------------------------
-- The action commutes with f

actV-map : (g : Gen n) (v : Vec A n) → CB.actV g (mapV v) ≡ mapV (CA.actV g v)
actV-map (M-gen a) v = CB.vec-ext λ x → by x (x FinP.≟ a)
  where
  g = M-gen a
  by : ∀ x → Dec (x ≡ a) → CB.actV g (mapV v) CB.! x ≡ mapV (CA.actV g v) CB.! x
  by x (yes refl) = trans (CB.actV-Ma x (mapV v))
    (trans (cong -_ (!-mapV v x))
      (sym (trans (!-mapV (CA.actV g v) x) (trans (cong f (CA.actV-Ma x v)) (f-neg _)))))
  by x (no ne) = trans (CB.actV-M≢ a (mapV v) ne)
    (trans (!-mapV v x) (sym (trans (!-mapV (CA.actV g v) x) (cong f (CA.actV-M≢ a v ne)))))
actV-map (X-gen a b p) v = CB.vec-ext λ x → by x (x FinP.≟ a) (x FinP.≟ b)
  where
  g = X-gen a b p
  rhs : ∀ x → mapV (CA.actV g v) CB.! x ≡ f (CA.actV g v CA.! x)
  rhs x = !-mapV (CA.actV g v) x
  by : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → CB.actV g (mapV v) CB.! x ≡ mapV (CA.actV g v) CB.! x
  by x (yes refl) _ = trans (CB.actV-Xa p (mapV v)) (trans (!-mapV v b) (sym (trans (rhs x) (cong f (CA.actV-Xa p v)))))
  by x (no _) (yes refl) = trans (CB.actV-Xb p (mapV v)) (trans (!-mapV v a) (sym (trans (rhs x) (cong f (CA.actV-Xb p v)))))
  by x (no xa) (no xb) =
    trans (CB.actV-X≢ p (mapV v) xa xb) (trans (!-mapV v x) (sym (trans (rhs x) (cong f (CA.actV-X≢ p v xa xb)))))
actV-map (K-gen a b c d p q r) v = CB.vec-ext λ x → by x (x FinP.≟ a) (x FinP.≟ b) (x FinP.≟ c) (x FinP.≟ d)
  where
  g = K-gen a b c d p q r
  rhs : ∀ x → mapV (CA.actV g v) CB.! x ≡ f (CA.actV g v CA.! x)
  rhs x = !-mapV (CA.actV g v) x
  ents : ∀ (F : B → B → B → B → B) → F (mapV v CB.! a) (mapV v CB.! b) (mapV v CB.! c) (mapV v CB.! d) ≡
                                      F (f (v CA.! a)) (f (v CA.! b)) (f (v CA.! c)) (f (v CA.! d))
  ents F = cong₄ F (!-mapV v a) (!-mapV v b) (!-mapV v c) (!-mapV v d)
  by : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Dec (x ≡ c) → Dec (x ≡ d) →
       CB.actV g (mapV v) CB.! x ≡ mapV (CA.actV g v) CB.! x
  by x (yes refl) _ _ _ = trans (CB.actV-Ka p q r (mapV v))
    (trans (ents CB.rowA) (sym (trans (rhs x) (trans (cong f (CA.actV-Ka p q r v)) (f-rowA _ _ _ _)))))
  by x (no _) (yes refl) _ _ = trans (CB.actV-Kb p q r (mapV v))
    (trans (ents CB.rowB) (sym (trans (rhs x) (trans (cong f (CA.actV-Kb p q r v)) (f-rowB _ _ _ _)))))
  by x (no _) (no _) (yes refl) _ = trans (CB.actV-Kc p q r (mapV v))
    (trans (ents CB.rowC) (sym (trans (rhs x) (trans (cong f (CA.actV-Kc p q r v)) (f-rowC _ _ _ _)))))
  by x (no _) (no _) (no _) (yes refl) = trans (CB.actV-Kd p q r (mapV v))
    (trans (ents CB.rowD) (sym (trans (rhs x) (trans (cong f (CA.actV-Kd p q r v)) (f-rowD _ _ _ _)))))
  by x (no xa) (no xb) (no xc) (no xd) = trans (CB.actV-K≢ p q r (mapV v) xa xb xc xd)
    (trans (!-mapV v x) (sym (trans (rhs x) (cong f (CA.actV-K≢ p q r v xa xb xc xd)))))

actM-map : (g : Gen n) (M : Matrix n m A) → CB.actM g (mapM M) ≡ mapM (CA.actM g M)
actM-map g M = CB.col-ext λ c →
  trans (CB.col-actM g (mapM M) c)
    (trans (cong (CB.actV g) (col-mapM M c))
      (trans (actV-map g (CA.col M c))
        (sym (trans (col-mapM (CA.actM g M) c) (cong mapV (CA.col-actM g M c))))))

actMʷ-map : (w : Word (Gen n)) (M : Matrix n m A) → CB.actMʷ w (mapM M) ≡ mapM (CA.actMʷ w M)
actMʷ-map [ g ]ʷ M = actM-map g M
actMʷ-map ε M = refl
actMʷ-map (u • w) M = trans (cong (CB.actMʷ u) (actMʷ-map w M)) (actMʷ-map u (CA.actMʷ w M))

mapM-𝕀 : mapM (CA.𝕀 {n}) ≡ CB.𝕀
mapM-𝕀 = CB.mat-ext λ r c →
  trans (ent-mapM CA.𝕀 r c) (trans (cong f (CA.ent-𝕀 r c)) (trans (f-δ r c) (sym (CB.ent-𝕀 r c))))

-- The matrix of a word over B is the image of its matrix over A.
⟦⟧-map : (w : Word (Gen n)) → CB.⟦ w ⟧ᵐ ≡ mapM CA.⟦ w ⟧ᵐ
⟦⟧-map w = trans (cong (CB.actMʷ w) (sym mapM-𝕀)) (actMʷ-map w CA.𝕀)

------------------------------------------------------------------------
-- Products, adjoints, injectivity

private
  f-sum : (g : Fin n → A) → f (CA.sum g) ≡ CB.sum (f ∘ g)
  f-sum {zero} g = f-0
  f-sum {suc n} g = trans (f-+ (g zero) (CA.sum (g ∘ suc))) (cong (f (g zero) +_) (f-sum (g ∘ suc)))

mapM-·*· : ∀ {p} (M : Matrix n m A) (N : Matrix m p A) → mapM (M ·*· N) ≡ mapM M ·*· mapM N
mapM-·*· {n} {m} M N = CB.mat-ext λ r c → begin
  CB.ent (mapM (M ·*· N)) r c                                    ≡⟨ ent-mapM (M ·*· N) r c ⟩
  f (CA.ent (M ·*· N) r c)                                       ≡⟨ cong f (CA.ent-·*· M N r c) ⟩
  f (CA.sum (λ x → CA.ent M r x * CA.ent N x c))                 ≡⟨ f-sum {m} (λ x → CA.ent M r x * CA.ent N x c) ⟩
  CB.sum (λ x → f (CA.ent M r x * CA.ent N x c))                 ≡⟨ CB.sum-cong-≗ (λ x → trans (f-* _ _)
                                                                      (cong₂ _*_ (sym (ent-mapM M r x)) (sym (ent-mapM N x c)))) ⟩
  CB.sum (λ x → CB.ent (mapM M) r x * CB.ent (mapM N) x c)       ≡⟨ sym (CB.ent-·*· (mapM M) (mapM N) r c) ⟩
  CB.ent (mapM M ·*· mapM N) r c                                 ∎
  where open ≡-Reasoning

mapM-adjoint : (M : Matrix n m A) → mapM (adjoint M) ≡ adjoint (mapM M)
mapM-adjoint M = CB.mat-ext λ r c →
  trans (ent-mapM (adjoint M) r c)
    (trans (cong f (CA.ent-adjoint M r c))
      (trans (f-adj _) (trans (cong adj (sym (ent-mapM M c r))) (sym (CB.ent-adjoint (mapM M) r c)))))

mapM-injective : (∀ {x y} → f x ≡ f y → x ≡ y) → {M N : Matrix n m A} → mapM M ≡ mapM N → M ≡ N
mapM-injective inj {M} {N} eq = CA.mat-ext λ r c →
  inj (trans (sym (ent-mapM M r c)) (trans (cong (λ P → CB.ent P r c) eq) (ent-mapM N r c)))
