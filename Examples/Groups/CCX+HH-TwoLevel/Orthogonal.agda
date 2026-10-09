------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators are involutions that keep inner products, given
-- adj h = h and 4h² = 1; so the matrices of words are unitary
-- (orthogonal, over a ring whose involution is trivial), and a word
-- keeps the orthonormality of the columns of a matrix (ColOrth).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; _-_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH-TwoLevel.Orthogonal
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h : A)
  (h-self : adj h ≡ h)
  (h-quarter : h * h + h * h + h * h + h * h ≡ 1#)
  where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
import Data.Integer.Base as ℤ
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true ; dec-false)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)
import Quantum.Synthesis.Ring.Properties.Common as Common

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
import Examples.Groups.CCX+HH-TwoLevel.Action as Action

open Action isCR adjI h public

private
  module S = Common.ZSolver R
  variable
    n m : ℕ

  -- (h h + h h + h h + h h) x = x.
  quarter : ∀ x → (h * h + h * h + h * h + h * h) * x ≡ x
  quarter x = trans (cong (_* x) h-quarter) (AR.*-identityˡ x)

------------------------------------------------------------------------
-- The ring identities behind K: K is an involution, and keeps inner
-- products

private
  KA : ∀ x₁ x₂ x₃ x₄ → rowA (rowA x₁ x₂ x₃ x₄) (rowB x₁ x₂ x₃ x₄) (rowC x₁ x₂ x₃ x₄) (rowD x₁ x₂ x₃ x₄) ≡ x₁
  KA x₁ x₂ x₃ x₄ = trans (S.solve 5 (λ h a b c d → (h S.:* (((S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ S.con (ℤ.+ 1) S.:* b) S.:+ S.con (ℤ.+ 1) S.:* c) S.:+ S.con (ℤ.+ 1) S.:* d)) S.:+ S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ (S.:- S.con (ℤ.+ 1)) S.:* b) S.:+ S.con (ℤ.+ 1) S.:* c) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* d))) S.:+ S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ S.con (ℤ.+ 1) S.:* b) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* c) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* d))) S.:+ S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ (S.:- S.con (ℤ.+ 1)) S.:* b) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* c) S.:+ S.con (ℤ.+ 1) S.:* d)))) S.:= (((h S.:* h S.:+ h S.:* h) S.:+ h S.:* h) S.:+ h S.:* h) S.:* a) AR.refl h x₁ x₂ x₃ x₄) (quarter x₁)

  KB : ∀ x₁ x₂ x₃ x₄ → rowB (rowA x₁ x₂ x₃ x₄) (rowB x₁ x₂ x₃ x₄) (rowC x₁ x₂ x₃ x₄) (rowD x₁ x₂ x₃ x₄) ≡ x₂
  KB x₁ x₂ x₃ x₄ = trans (S.solve 5 (λ h a b c d → (h S.:* (((S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ S.con (ℤ.+ 1) S.:* b) S.:+ S.con (ℤ.+ 1) S.:* c) S.:+ S.con (ℤ.+ 1) S.:* d)) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ (S.:- S.con (ℤ.+ 1)) S.:* b) S.:+ S.con (ℤ.+ 1) S.:* c) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* d))) S.:+ S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ S.con (ℤ.+ 1) S.:* b) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* c) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* d))) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ (S.:- S.con (ℤ.+ 1)) S.:* b) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* c) S.:+ S.con (ℤ.+ 1) S.:* d)))) S.:= (((h S.:* h S.:+ h S.:* h) S.:+ h S.:* h) S.:+ h S.:* h) S.:* b) AR.refl h x₁ x₂ x₃ x₄) (quarter x₂)

  KC : ∀ x₁ x₂ x₃ x₄ → rowC (rowA x₁ x₂ x₃ x₄) (rowB x₁ x₂ x₃ x₄) (rowC x₁ x₂ x₃ x₄) (rowD x₁ x₂ x₃ x₄) ≡ x₃
  KC x₁ x₂ x₃ x₄ = trans (S.solve 5 (λ h a b c d → (h S.:* (((S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ S.con (ℤ.+ 1) S.:* b) S.:+ S.con (ℤ.+ 1) S.:* c) S.:+ S.con (ℤ.+ 1) S.:* d)) S.:+ S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ (S.:- S.con (ℤ.+ 1)) S.:* b) S.:+ S.con (ℤ.+ 1) S.:* c) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* d))) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ S.con (ℤ.+ 1) S.:* b) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* c) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* d))) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ (S.:- S.con (ℤ.+ 1)) S.:* b) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* c) S.:+ S.con (ℤ.+ 1) S.:* d)))) S.:= (((h S.:* h S.:+ h S.:* h) S.:+ h S.:* h) S.:+ h S.:* h) S.:* c) AR.refl h x₁ x₂ x₃ x₄) (quarter x₃)

  KD : ∀ x₁ x₂ x₃ x₄ → rowD (rowA x₁ x₂ x₃ x₄) (rowB x₁ x₂ x₃ x₄) (rowC x₁ x₂ x₃ x₄) (rowD x₁ x₂ x₃ x₄) ≡ x₄
  KD x₁ x₂ x₃ x₄ = trans (S.solve 5 (λ h a b c d → (h S.:* (((S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ S.con (ℤ.+ 1) S.:* b) S.:+ S.con (ℤ.+ 1) S.:* c) S.:+ S.con (ℤ.+ 1) S.:* d)) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ (S.:- S.con (ℤ.+ 1)) S.:* b) S.:+ S.con (ℤ.+ 1) S.:* c) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* d))) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ S.con (ℤ.+ 1) S.:* b) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* c) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* d))) S.:+ S.con (ℤ.+ 1) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* a S.:+ (S.:- S.con (ℤ.+ 1)) S.:* b) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* c) S.:+ S.con (ℤ.+ 1) S.:* d)))) S.:= (((h S.:* h S.:+ h S.:* h) S.:+ h S.:* h) S.:+ h S.:* h) S.:* d) AR.refl h x₁ x₂ x₃ x₄) (quarter x₄)

  ipK : ∀ u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄ →
        ((rowA u₁ u₂ u₃ u₄ * rowA w₁ w₂ w₃ w₄ + rowB u₁ u₂ u₃ u₄ * rowB w₁ w₂ w₃ w₄) + rowC u₁ u₂ u₃ u₄ * rowC w₁ w₂ w₃ w₄)
          + rowD u₁ u₂ u₃ u₄ * rowD w₁ w₂ w₃ w₄ ≡ ((u₁ * w₁ + u₂ * w₂) + u₃ * w₃) + u₄ * w₄
  ipK u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄ = trans (S.solve 9 (λ h u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄ → ((((h S.:* (((S.con (ℤ.+ 1) S.:* u₁ S.:+ S.con (ℤ.+ 1) S.:* u₂) S.:+ S.con (ℤ.+ 1) S.:* u₃) S.:+ S.con (ℤ.+ 1) S.:* u₄)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* w₁ S.:+ S.con (ℤ.+ 1) S.:* w₂) S.:+ S.con (ℤ.+ 1) S.:* w₃) S.:+ S.con (ℤ.+ 1) S.:* w₄)) S.:+ (h S.:* (((S.con (ℤ.+ 1) S.:* u₁ S.:+ (S.:- S.con (ℤ.+ 1)) S.:* u₂) S.:+ S.con (ℤ.+ 1) S.:* u₃) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* u₄)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* w₁ S.:+ (S.:- S.con (ℤ.+ 1)) S.:* w₂) S.:+ S.con (ℤ.+ 1) S.:* w₃) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* w₄))) S.:+ (h S.:* (((S.con (ℤ.+ 1) S.:* u₁ S.:+ S.con (ℤ.+ 1) S.:* u₂) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* u₃) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* u₄)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* w₁ S.:+ S.con (ℤ.+ 1) S.:* w₂) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* w₃) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* w₄))) S.:+ (h S.:* (((S.con (ℤ.+ 1) S.:* u₁ S.:+ (S.:- S.con (ℤ.+ 1)) S.:* u₂) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* u₃) S.:+ S.con (ℤ.+ 1) S.:* u₄)) S.:* (h S.:* (((S.con (ℤ.+ 1) S.:* w₁ S.:+ (S.:- S.con (ℤ.+ 1)) S.:* w₂) S.:+ (S.:- S.con (ℤ.+ 1)) S.:* w₃) S.:+ S.con (ℤ.+ 1) S.:* w₄))) S.:= (((h S.:* h S.:+ h S.:* h) S.:+ h S.:* h) S.:+ h S.:* h) S.:* (((u₁ S.:* w₁ S.:+ u₂ S.:* w₂) S.:+ u₃ S.:* w₃) S.:+ u₄ S.:* w₄)) AR.refl h u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄) (quarter _)

------------------------------------------------------------------------
-- The generators are involutions

private
  cong₄ : ∀ (f : A → A → A → A → A) {x x′ y y′ z z′ t t′} →
          x ≡ x′ → y ≡ y′ → z ≡ z′ → t ≡ t′ → f x y z t ≡ f x′ y′ z′ t′
  cong₄ f refl refl refl refl = refl

  neg-neg : ∀ y → - (- y) ≡ y
  neg-neg = S.solve 1 (λ y → S.:- (S.:- y) S.:= y) AR.refl

actV-invol : (g : Gen n) (v : Vec A n) → actV g (actV g v) ≡ v
actV-invol (M-gen a) v = vec-ext λ x → at x (x FinP.≟ a)
  where
  at : ∀ x → Dec (x ≡ a) → actV (M-gen a) (actV (M-gen a) v) ! x ≡ v ! x
  at x (yes refl) = trans (actV-Ma x (actV (M-gen x) v)) (trans (cong -_ (actV-Ma x v)) (neg-neg (v ! x)))
  at x (no x≢a) = trans (actV-M≢ a _ x≢a) (actV-M≢ a v x≢a)
actV-invol (X-gen a b p) v = vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b)
  where
  g = X-gen a b p
  at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → actV g (actV g v) ! x ≡ v ! x
  at x (yes refl) _ = trans (actV-Xa p (actV g v)) (actV-Xb p v)
  at x (no _) (yes refl) = trans (actV-Xb p (actV g v)) (actV-Xa p v)
  at x (no x≢a) (no x≢b) = trans (actV-X≢ p (actV g v) x≢a x≢b) (actV-X≢ p v x≢a x≢b)
actV-invol (K-gen a b c d p q r) v =
  vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b) (x FinP.≟ c) (x FinP.≟ d)
  where
  g = K-gen a b c d p q r
  w = actV g v
  ent4 : ∀ (f : A → A → A → A → A) → f (w ! a) (w ! b) (w ! c) (w ! d) ≡
         f (rowA (v ! a) (v ! b) (v ! c) (v ! d)) (rowB (v ! a) (v ! b) (v ! c) (v ! d))
           (rowC (v ! a) (v ! b) (v ! c) (v ! d)) (rowD (v ! a) (v ! b) (v ! c) (v ! d))
  ent4 f = cong₄ f (actV-Ka p q r v) (actV-Kb p q r v) (actV-Kc p q r v) (actV-Kd p q r v)
  at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Dec (x ≡ c) → Dec (x ≡ d) → actV g w ! x ≡ v ! x
  at x (yes refl) _ _ _ =
    trans (actV-Ka p q r w) (trans (ent4 rowA) (KA (v ! a) (v ! b) (v ! c) (v ! d)))
  at x (no _) (yes refl) _ _ =
    trans (actV-Kb p q r w) (trans (ent4 rowB) (KB (v ! a) (v ! b) (v ! c) (v ! d)))
  at x (no _) (no _) (yes refl) _ =
    trans (actV-Kc p q r w) (trans (ent4 rowC) (KC (v ! a) (v ! b) (v ! c) (v ! d)))
  at x (no _) (no _) (no _) (yes refl) =
    trans (actV-Kd p q r w) (trans (ent4 rowD) (KD (v ! a) (v ! b) (v ! c) (v ! d)))
  at x (no xa) (no xb) (no xc) (no xd) =
    trans (actV-K≢ p q r w xa xb xc xd) (actV-K≢ p q r v xa xb xc xd)

------------------------------------------------------------------------
-- Inner products are kept

private
  if-t : ∀ {t : Bool} {x y : A} → t ≡ true → (if t then x else y) ≡ x
  if-t refl = refl

  if-f : ∀ {t : Bool} {x y : A} → t ≡ false → (if t then x else y) ≡ y
  if-f refl = refl

  -- A sum over a function that vanishes off four points.
  sum-four : (f : Fin n → A) {a b c d : Fin n} → Distinct₄ a b c d →
             (∀ x → x ≢ a → x ≢ b → x ≢ c → x ≢ d → f x ≡ 0#) → sum f ≡ ((f a + f b) + f c) + f d
  sum-four f {a} {b} {c} {d} D off = begin
    sum f                                     ≡⟨ sum-cong-≗ split ⟩
    sum (λ x → ((fa x + fb x) + fc x) + fd x) ≡⟨ ∑-distrib-+ (λ x → (fa x + fb x) + fc x) fd ⟩
    sum (λ x → (fa x + fb x) + fc x) + sum fd ≡⟨ cong (_+ sum fd) (∑-distrib-+ (λ x → fa x + fb x) fc) ⟩
    (sum (λ x → fa x + fb x) + sum fc) + sum fd
      ≡⟨ cong (λ z → (z + sum fc) + sum fd) (∑-distrib-+ fa fb) ⟩
    ((sum fa + sum fb) + sum fc) + sum fd
      ≡⟨ cong₄ (λ s t u v → ((s + t) + u) + v) (one a) (one b) (one c) (one d) ⟩
    ((f a + f b) + f c) + f d ∎
    where
    open ≡-Reasoning
    open Distinct₄ D
    at : Fin _ → Fin _ → A
    at p x = if does (x FinP.≟ p) then f x else 0#
    fa fb fc fd : Fin _ → A
    fa = at a
    fb = at b
    fc = at c
    fd = at d
    here : ∀ p → at p p ≡ f p
    here p = if-t (dec-true (p FinP.≟ p) refl)
    away : ∀ {p x} → x ≢ p → at p x ≡ 0#
    away {p} {x} ne = if-f (dec-false (x FinP.≟ p) ne)
    one : ∀ p → sum (at p) ≡ f p
    one p = trans (sum-single (at p) p (λ x x≢p → away x≢p)) (here p)
    z : A
    z = 0#
    four : ∀ {x α β γ δ′} → fa x ≡ α → fb x ≡ β → fc x ≡ γ → fd x ≡ δ′ →
           ((fa x + fb x) + fc x) + fd x ≡ ((α + β) + γ) + δ′
    four = cong₄ (λ s t u v → ((s + t) + u) + v)
    s0 : ((f a + z) + z) + z ≡ f a
    s0 = S.solve 1 (λ y → ((y S.:+ S.con (ℤ.+ 0)) S.:+ S.con (ℤ.+ 0)) S.:+ S.con (ℤ.+ 0) S.:= y) AR.refl (f a)
    s1 : ((z + f b) + z) + z ≡ f b
    s1 = S.solve 1 (λ y → ((S.con (ℤ.+ 0) S.:+ y) S.:+ S.con (ℤ.+ 0)) S.:+ S.con (ℤ.+ 0) S.:= y) AR.refl (f b)
    s2 : ((z + z) + f c) + z ≡ f c
    s2 = S.solve 1 (λ y → ((S.con (ℤ.+ 0) S.:+ S.con (ℤ.+ 0)) S.:+ y) S.:+ S.con (ℤ.+ 0) S.:= y) AR.refl (f c)
    s3 : ((z + z) + z) + f d ≡ f d
    s3 = S.solve 1 (λ y → ((S.con (ℤ.+ 0) S.:+ S.con (ℤ.+ 0)) S.:+ S.con (ℤ.+ 0)) S.:+ y S.:= y) AR.refl (f d)
    s4 : ((z + z) + z) + z ≡ 0#
    s4 = S.solve 0 (((S.con (ℤ.+ 0) S.:+ S.con (ℤ.+ 0)) S.:+ S.con (ℤ.+ 0)) S.:+ S.con (ℤ.+ 0) S.:= S.con (ℤ.+ 0)) AR.refl
    split : ∀ x → f x ≡ ((fa x + fb x) + fc x) + fd x
    split x = by (x FinP.≟ a) (x FinP.≟ b) (x FinP.≟ c) (x FinP.≟ d)
      where
      by : Dec (x ≡ a) → Dec (x ≡ b) → Dec (x ≡ c) → Dec (x ≡ d) → f x ≡ ((fa x + fb x) + fc x) + fd x
      by (yes refl) _ _ _ = sym (trans (four (here a) (away ab) (away ac) (away ad)) s0)
      by (no xa) (yes refl) _ _ = sym (trans (four (away xa) (here b) (away bc) (away bd)) s1)
      by (no xa) (no xb) (yes refl) _ = sym (trans (four (away xa) (away xb) (here c) (away cd)) s2)
      by (no xa) (no xb) (no xc) (yes refl) = sym (trans (four (away xa) (away xb) (away xc) (here d)) s3)
      by (no xa) (no xb) (no xc) (no xd) =
        trans (off x xa xb xc xd) (sym (trans (four (away xa) (away xb) (away xc) (away xd)) s4))

  -- If g and f agree off four points, and their sums there agree, then
  -- their sums agree.
  sum-update₄ : (f g : Fin n → A) {a b c d : Fin n} → Distinct₄ a b c d →
                (∀ x → x ≢ a → x ≢ b → x ≢ c → x ≢ d → g x ≡ f x) →
                ((g a + g b) + g c) + g d ≡ ((f a + f b) + f c) + f d → sum g ≡ sum f
  sum-update₄ f g {a} {b} {c} {d} D agree tot = begin
    sum g                                ≡⟨ sum-cong-≗ (λ x → S.solve 2 (λ g f → g S.:= (g S.:+ S.:- f) S.:+ f) AR.refl (g x) (f x)) ⟩
    sum (λ x → (g x + - f x) + f x)      ≡⟨ ∑-distrib-+ (λ x → g x + - f x) f ⟩
    sum (λ x → g x + - f x) + sum f      ≡⟨ cong (_+ sum f) (sum-four (λ x → g x + - f x) D
                                              (λ x xa xb xc xd → trans (cong (λ y → y + - f x) (agree x xa xb xc xd))
                                                                       (AR.-‿inverseʳ (f x)))) ⟩
    (((g a + - f a) + (g b + - f b)) + (g c + - f c)) + (g d + - f d) + sum f
      ≡⟨ cong (_+ sum f) (trans (S.solve 8 (λ ga gb gc gd fa fb fc fd →
              (((ga S.:+ S.:- fa) S.:+ (gb S.:+ S.:- fb)) S.:+ (gc S.:+ S.:- fc)) S.:+ (gd S.:+ S.:- fd)
              S.:= (((ga S.:+ gb) S.:+ gc) S.:+ gd) S.:+ S.:- (((fa S.:+ fb) S.:+ fc) S.:+ fd))
              AR.refl (g a) (g b) (g c) (g d) (f a) (f b) (f c) (f d))
            (trans (cong (λ y → y + - (((f a + f b) + f c) + f d)) tot) (AR.-‿inverseʳ _))) ⟩
    0# + sum f                           ≡⟨ AR.+-identityˡ (sum f) ⟩
    sum f                                ∎
    where open ≡-Reasoning

private
  adj-m1 : adj m1 ≡ m1
  adj-m1 = trans (adj-neg 1#) (cong -_ adj-1)

  adj-lin : ∀ s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ → adj s₁ ≡ s₁ → adj s₂ ≡ s₂ → adj s₃ ≡ s₃ → adj s₄ ≡ s₄ →
            adj (lin s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄) ≡ lin s₁ s₂ s₃ s₄ (adj x₁) (adj x₂) (adj x₃) (adj x₄)
  adj-lin s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ e₁ e₂ e₃ e₄ =
    trans (adj-* h _) (cong₂ _*_ h-self
      (trans (adj-+ _ _) (cong₂ _+_ (trans (adj-+ _ _) (cong₂ _+_ (trans (adj-+ _ _) (cong₂ _+_ (term e₁) (term e₂))) (term e₃)))
                                    (term e₄))))
    where
    term : ∀ {s x} → adj s ≡ s → adj (s * x) ≡ s * adj x
    term {s} {x} e = trans (adj-* s x) (cong (_* adj x) e)

ip-actV : (g : Gen n) (u u' : Vec A n) → ⟨ actV g u , actV g u' ⟩ ≡ ⟨ u , u' ⟩
ip-actV (M-gen a) u u' = sum-update₁ F G a off
  (trans (cong₂ (λ y z → adj y * z) (actV-Ma a u) (actV-Ma a u'))
     (trans (cong (_* (- (u' ! a))) (adj-neg (u ! a)))
       (S.solve 2 (λ x y → (S.:- x) S.:* (S.:- y) S.:= x S.:* y) AR.refl (adj (u ! a)) (u' ! a))))
  where
  F G : Fin _ → A
  F x = adj (u ! x) * u' ! x
  G x = adj (actV (M-gen a) u ! x) * actV (M-gen a) u' ! x
  off : ∀ x → x ≢ a → G x ≡ F x
  off x xa = cong₂ (λ y z → adj y * z) (actV-M≢ a u xa) (actV-M≢ a u' xa)
ip-actV (X-gen a b p) u u' = sum-update F G a b (<⇒≢ p) off
  (trans (cong₂ _+_ (cong₂ (λ y z → adj y * z) (actV-Xa p u) (actV-Xa p u'))
                    (cong₂ (λ y z → adj y * z) (actV-Xb p u) (actV-Xb p u')))
         (AR.+-comm (F b) (F a)))
  where
  F G : Fin _ → A
  F x = adj (u ! x) * u' ! x
  G x = adj (actV (X-gen a b p) u ! x) * actV (X-gen a b p) u' ! x
  off : ∀ x → x ≢ a → x ≢ b → G x ≡ F x
  off x xa xb = cong₂ (λ y z → adj y * z) (actV-X≢ p u xa xb) (actV-X≢ p u' xa xb)
ip-actV (K-gen a b c d p q r) u u' = sum-update₄ F G (distinct₄ p q r) off tot
  where
  g = K-gen a b c d p q r
  F G : Fin _ → A
  F x = adj (u ! x) * u' ! x
  G x = adj (actV g u ! x) * actV g u' ! x
  off : ∀ x → x ≢ a → x ≢ b → x ≢ c → x ≢ d → G x ≡ F x
  off x xa xb xc xd = cong₂ (λ y z → adj y * z) (actV-K≢ p q r u xa xb xc xd) (actV-K≢ p q r u' xa xb xc xd)
  ā = adj (u ! a)
  b̄ = adj (u ! b)
  c̄ = adj (u ! c)
  d̄ = adj (u ! d)
  ua = u' ! a
  ub = u' ! b
  uc = u' ! c
  ud = u' ! d
  e1 : adj 1# ≡ 1#
  e1 = adj-1
  tot : ((G a + G b) + G c) + G d ≡ ((F a + F b) + F c) + F d
  tot = begin
    ((G a + G b) + G c) + G d
      ≡⟨ cong₂ _+_ (cong₂ _+_ (cong₂ _+_
            (cong₂ (λ y z → adj y * z) (actV-Ka p q r u) (actV-Ka p q r u'))
            (cong₂ (λ y z → adj y * z) (actV-Kb p q r u) (actV-Kb p q r u')))
            (cong₂ (λ y z → adj y * z) (actV-Kc p q r u) (actV-Kc p q r u')))
            (cong₂ (λ y z → adj y * z) (actV-Kd p q r u) (actV-Kd p q r u')) ⟩
    ((adj (rowA (u ! a) (u ! b) (u ! c) (u ! d)) * rowA ua ub uc ud
      + adj (rowB (u ! a) (u ! b) (u ! c) (u ! d)) * rowB ua ub uc ud)
      + adj (rowC (u ! a) (u ! b) (u ! c) (u ! d)) * rowC ua ub uc ud)
      + adj (rowD (u ! a) (u ! b) (u ! c) (u ! d)) * rowD ua ub uc ud
      ≡⟨ cong₂ _+_ (cong₂ _+_ (cong₂ _+_
            (cong (_* rowA ua ub uc ud) (adj-lin 1# 1# 1# 1# (u ! a) (u ! b) (u ! c) (u ! d) e1 e1 e1 e1))
            (cong (_* rowB ua ub uc ud) (adj-lin 1# m1 1# m1 (u ! a) (u ! b) (u ! c) (u ! d) e1 adj-m1 e1 adj-m1)))
            (cong (_* rowC ua ub uc ud) (adj-lin 1# 1# m1 m1 (u ! a) (u ! b) (u ! c) (u ! d) e1 e1 adj-m1 adj-m1)))
            (cong (_* rowD ua ub uc ud) (adj-lin 1# m1 m1 1# (u ! a) (u ! b) (u ! c) (u ! d) e1 adj-m1 adj-m1 e1)) ⟩
    ((rowA ā b̄ c̄ d̄ * rowA ua ub uc ud + rowB ā b̄ c̄ d̄ * rowB ua ub uc ud) + rowC ā b̄ c̄ d̄ * rowC ua ub uc ud)
      + rowD ā b̄ c̄ d̄ * rowD ua ub uc ud
      ≡⟨ ipK ā b̄ c̄ d̄ ua ub uc ud ⟩
    ((F a + F b) + F c) + F d ∎
    where open ≡-Reasoning

ip-actVʷ : (w : Word (Gen n)) (u u' : Vec A n) → ⟨ actVʷ w u , actVʷ w u' ⟩ ≡ ⟨ u , u' ⟩
ip-actVʷ [ g ]ʷ u u' = ip-actV g u u'
ip-actVʷ ε u u' = refl
ip-actVʷ (v • w) u u' = trans (ip-actVʷ v (actVʷ w u) (actVʷ w u')) (ip-actVʷ w u u')

------------------------------------------------------------------------
-- Orthonormal columns

opaque
  ColOrth : Matrix n m A → Set
  ColOrth M = adjoint M ·*· M ≡ 𝕀

  ColOrth→ : {M : Matrix n m A} → ColOrth M → adjoint M ·*· M ≡ 𝕀
  ColOrth→ o = o

  →ColOrth : {M : Matrix n m A} → adjoint M ·*· M ≡ 𝕀 → ColOrth M
  →ColOrth e = e

  ColOrth-ip : {M : Matrix n m A} → ColOrth M → ∀ r c → ⟨ col M r , col M c ⟩ ≡ δ r c
  ColOrth-ip {M = M} o r c = trans (sym (ent-†·*· M M r c)) (trans (cong (λ N → ent N r c) o) (ent-𝕀 r c))

  ip⇒ColOrth : {M : Matrix n m A} → (∀ r c → ⟨ col M r , col M c ⟩ ≡ δ r c) → ColOrth M
  ip⇒ColOrth {M = M} ip = mat-ext λ r c → trans (ent-†·*· M M r c) (trans (ip r c) (sym (ent-𝕀 r c)))

ColOrth-actMʷ : (w : Word (Gen n)) {M : Matrix n m A} → ColOrth M → ColOrth (actMʷ w M)
ColOrth-actMʷ w {M} o = ip⇒ColOrth λ r c → begin
  ⟨ col (actMʷ w M) r , col (actMʷ w M) c ⟩     ≡⟨ cong₂ ⟨_,_⟩ (col-actMʷ w M r) (col-actMʷ w M c) ⟩
  ⟨ actVʷ w (col M r) , actVʷ w (col M c) ⟩     ≡⟨ ip-actVʷ w (col M r) (col M c) ⟩
  ⟨ col M r , col M c ⟩                         ≡⟨ ColOrth-ip o r c ⟩
  δ r c                                         ∎
  where open ≡-Reasoning

ColOrth-𝕀 : ColOrth (𝕀 {n})
ColOrth-𝕀 = →ColOrth (trans (cong (_·*· 𝕀) adjoint-𝕀) (·*·-identityˡ 𝕀))

------------------------------------------------------------------------
-- Unitary matrices

Unitary : Matrix n n A → Set
Unitary M = (adjoint M ·*· M ≡ 𝕀) × (M ·*· adjoint M ≡ 𝕀)

Unitary-𝕀 : Unitary (𝕀 {n})
Unitary-𝕀 = ColOrth→ ColOrth-𝕀 , trans (cong (𝕀 ·*·_) adjoint-𝕀) (·*·-identityˡ 𝕀)

Unitary-·*· : {M N : Matrix n n A} → Unitary M → Unitary N → Unitary (M ·*· N)
Unitary-·*· {M = M} {N} (m₁ , m₂) (n₁ , n₂) = u₁ , u₂
  where
  open ≡-Reasoning
  u₁ : adjoint (M ·*· N) ·*· (M ·*· N) ≡ 𝕀
  u₁ = begin
    adjoint (M ·*· N) ·*· (M ·*· N)               ≡⟨ cong (_·*· (M ·*· N)) (adjoint-·*· M N) ⟩
    (adjoint N ·*· adjoint M) ·*· (M ·*· N)       ≡⟨ ·*·-assoc (adjoint N) (adjoint M) (M ·*· N) ⟩
    adjoint N ·*· (adjoint M ·*· (M ·*· N))       ≡⟨ cong (adjoint N ·*·_) (sym (·*·-assoc (adjoint M) M N)) ⟩
    adjoint N ·*· ((adjoint M ·*· M) ·*· N)       ≡⟨ cong (λ z → adjoint N ·*· (z ·*· N)) m₁ ⟩
    adjoint N ·*· (𝕀 ·*· N)                       ≡⟨ cong (adjoint N ·*·_) (·*·-identityˡ N) ⟩
    adjoint N ·*· N                               ≡⟨ n₁ ⟩
    𝕀                                             ∎
  u₂ : (M ·*· N) ·*· adjoint (M ·*· N) ≡ 𝕀
  u₂ = begin
    (M ·*· N) ·*· adjoint (M ·*· N)               ≡⟨ cong ((M ·*· N) ·*·_) (adjoint-·*· M N) ⟩
    (M ·*· N) ·*· (adjoint N ·*· adjoint M)       ≡⟨ ·*·-assoc M N (adjoint N ·*· adjoint M) ⟩
    M ·*· (N ·*· (adjoint N ·*· adjoint M))       ≡⟨ cong (M ·*·_) (sym (·*·-assoc N (adjoint N) (adjoint M))) ⟩
    M ·*· ((N ·*· adjoint N) ·*· adjoint M)       ≡⟨ cong (λ z → M ·*· (z ·*· adjoint M)) n₂ ⟩
    M ·*· (𝕀 ·*· adjoint M)                       ≡⟨ cong (M ·*·_) (·*·-identityˡ (adjoint M)) ⟩
    M ·*· adjoint M                               ≡⟨ m₂ ⟩
    𝕀                                             ∎

Unitary-adjoint : {M : Matrix n n A} → Unitary M → Unitary (adjoint M)
Unitary-adjoint {M = M} (m₁ , m₂) =
  trans (cong (_·*· adjoint M) (adjoint-involutive M)) m₂ ,
  trans (cong (adjoint M ·*·_) (adjoint-involutive M)) m₁

-- The matrix of a generator is its own inverse, and orthogonal, hence
-- self-adjoint and unitary.
gmat-invol : (g : Gen n) → gmat g ·*· gmat g ≡ 𝕀
gmat-invol g = begin
  gmat g ·*· gmat g               ≡⟨ sym (actM≡ g (gmat g)) ⟩
  actM g (gmat g)                 ≡⟨ cong (actM g) (sym (⟦g⟧ᵐ≡ g)) ⟩
  actM g (actM g 𝕀)               ≡⟨ col-ext (λ c → trans (col-actM g (actM g 𝕀) c)
                                                     (trans (cong (actV g) (col-actM g 𝕀 c)) (actV-invol g (col 𝕀 c)))) ⟩
  𝕀                               ∎
  where open ≡-Reasoning

Unitary-gmat : (g : Gen n) → Unitary (gmat g)
Unitary-gmat g = o , trans (cong (G ·*·_) self) (gmat-invol g)
  where
  G = gmat g
  o : adjoint G ·*· G ≡ 𝕀
  o = ColOrth→ (subst ColOrth (⟦g⟧ᵐ≡ g) (ColOrth-actMʷ [ g ]ʷ ColOrth-𝕀))
  self : adjoint G ≡ G
  self = begin
    adjoint G                          ≡⟨ sym (·*·-identityʳ (adjoint G)) ⟩
    adjoint G ·*· 𝕀                    ≡⟨ cong (adjoint G ·*·_) (sym (gmat-invol g)) ⟩
    adjoint G ·*· (G ·*· G)            ≡⟨ sym (·*·-assoc (adjoint G) G G) ⟩
    (adjoint G ·*· G) ·*· G            ≡⟨ cong (_·*· G) o ⟩
    𝕀 ·*· G                            ≡⟨ ·*·-identityˡ G ⟩
    G                                  ∎
    where open ≡-Reasoning

Unitary-⟦⟧ᵐ : (w : Word (Gen n)) → Unitary ⟦ w ⟧ᵐ
Unitary-⟦⟧ᵐ [ g ]ʷ = subst Unitary (sym (⟦g⟧ᵐ≡ g)) (Unitary-gmat g)
Unitary-⟦⟧ᵐ ε = Unitary-𝕀
Unitary-⟦⟧ᵐ (u • w) = subst Unitary (sym (⟦•⟧ᵐ u w)) (Unitary-·*· (Unitary-⟦⟧ᵐ u) (Unitary-⟦⟧ᵐ w))

------------------------------------------------------------------------
-- Columns of matrices with orthonormal columns

private
  adj-δ′ : (x y : Fin n) → adj (δ x y) ≡ δ x y
  adj-δ′ x y with x FinP.≟ y
  ... | yes _ = adj-1
  ... | no  _ = adj-0

ip-e : (x : Fin n) (v : Vec A n) → ⟨ col 𝕀 x , v ⟩ ≡ v ! x
ip-e x v = begin
  sum (λ y → adj (col 𝕀 x ! y) * (v ! y))     ≡⟨ sum-cong-≗ (λ y → cong (λ a → adj a * (v ! y))
                                                                 (trans (ent-𝕀 y x) (δ-sym y x))) ⟩
  sum (λ y → adj (δ x y) * (v ! y))            ≡⟨ sum-cong-≗ (λ y → cong (_* (v ! y)) (adj-δ′ x y)) ⟩
  sum (λ y → δ x y * (v ! y))                  ≡⟨ sum-δˡ (v !_) x ⟩
  v ! x                                        ∎
  where open ≡-Reasoning

col-vanish : {M : Matrix n n A} → ColOrth M → ∀ {x p} → col M x ≡ col 𝕀 x → x ≢ p → col M p ! x ≡ 0#
col-vanish {M = M} o {x} {p} Mx x≢p = begin
  col M p ! x                    ≡⟨ sym (ip-e x (col M p)) ⟩
  ⟨ col 𝕀 x , col M p ⟩          ≡⟨ cong (λ u → ⟨ u , col M p ⟩) (sym Mx) ⟩
  ⟨ col M x , col M p ⟩          ≡⟨ ColOrth-ip o x p ⟩
  δ x p                          ≡⟨ δ-≢ x≢p ⟩
  0#                             ∎
  where open ≡-Reasoning

col-unit : {M : Matrix n n A} → ColOrth M → ∀ p → ⟨ col M p , col M p ⟩ ≡ 1#
col-unit o p = trans (ColOrth-ip o p p) (δ-refl p)
