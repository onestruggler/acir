------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators acting on vectors and matrices, over any commutative
-- ring with an involution and a self-adjoint scalar h with 4h² = 1
-- (h = 1/2 for Oₙ(ℤ[1/2])):
--
--   (-1)_[a] negates entry a, X_[a,b] swaps entries a and b, and
--   K_[a,b,c,d] replaces the entries a, b, c, d by h times
--     v_a + v_b + v_c + v_d,  v_a - v_b + v_c - v_d,
--     v_a + v_b - v_c - v_d,  v_a - v_b - v_c + v_d
--   (K = H ⊗ H, Definition 2.4).
--
-- The matrix of a word is its action on I, and the action of a word on
-- a matrix is multiplication by its matrix (actMʷ≡), so ⟦_⟧ᵐ is a
-- homomorphism.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; _-_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH-TwoLevel.Action
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h : A)
  where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Fin.Base as Fin using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Vec.Base as Vec using (Vec ; tabulate)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_ ; id)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; recompute ; dec-true ; dec-false)

open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; unMatrix ; _·*·_ ; adjoint)
import Quantum.Synthesis.Ring.Properties.Common as Common

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra as MatrixAlgebra

open MatrixAlgebra isCR adjI public

private
  module S = Common.ZSolver R
  variable
    n m : ℕ

<⇒≢ : {a b : Fin n} → .(a < b) → a ≢ b
<⇒≢ {a = a} {b} p a≡b = FinP.<-irrefl a≡b (recompute (a FinP.<? b) p)

------------------------------------------------------------------------
-- The rows of K

-- h (s₁ x₁ + s₂ x₂ + s₃ x₃ + s₄ x₄).
lin : (s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ : A) → A
lin s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ = h * (s₁ * x₁ + s₂ * x₂ + s₃ * x₃ + s₄ * x₄)

m1 : A
m1 = - 1#

rowA rowB rowC rowD : (x₁ x₂ x₃ x₄ : A) → A
rowA = lin 1# 1# 1# 1#
rowB = lin 1# m1 1# m1
rowC = lin 1# 1# m1 m1
rowD = lin 1# m1 m1 1#

------------------------------------------------------------------------
-- Updating four entries

set₄ : {B : Set} → Fin n → Fin n → Fin n → Fin n → B → B → B → B → Vec B n → Vec B n
set₄ a b c d α β γ δ′ v = set₂ a b α β (set₂ c d γ δ′ v)

-- Four distinct indices.
record Distinct₄ {n : ℕ} (a b c d : Fin n) : Set where
  field
    ab : a ≢ b
    ac : a ≢ c
    ad : a ≢ d
    bc : b ≢ c
    bd : b ≢ d
    cd : c ≢ d

private
  rcp : ∀ {k} {x y : Fin k} → .(x < y) → x < y
  rcp {x = x} {y} lt = recompute (x FinP.<? y) lt

distinct₄ : {a b c d : Fin n} → .(a < b) → .(b < c) → .(c < d) → Distinct₄ a b c d
distinct₄ p q r = record
  { ab = <⇒≢ p ; ac = <⇒≢ (FinP.<-trans (rcp p) (rcp q)) ; ad = <⇒≢ (FinP.<-trans (FinP.<-trans (rcp p) (rcp q)) (rcp r))
  ; bc = <⇒≢ q ; bd = <⇒≢ (FinP.<-trans (rcp q) (rcp r)) ; cd = <⇒≢ r }

module _ {B : Set} {a b c d : Fin n} (D : Distinct₄ a b c d) (α β γ δ′ : B) (v : Vec B n) where

  open Distinct₄ D

  private
    sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
    sym≢ ne e = ne (sym e)

  set₄-a : set₄ a b c d α β γ δ′ v ! a ≡ α
  set₄-a = set₂-a a b α β _

  set₄-b : set₄ a b c d α β γ δ′ v ! b ≡ β
  set₄-b = set₂-b a b α β _ ab

  set₄-c : set₄ a b c d α β γ δ′ v ! c ≡ γ
  set₄-c = trans (set₂-≢ a b α β _ (sym≢ ac) (sym≢ bc)) (set₂-a c d γ δ′ v)

  set₄-d : set₄ a b c d α β γ δ′ v ! d ≡ δ′
  set₄-d = trans (set₂-≢ a b α β _ (sym≢ ad) (sym≢ bd)) (set₂-b c d γ δ′ v cd)

  set₄-≢ : ∀ {x} → x ≢ a → x ≢ b → x ≢ c → x ≢ d → set₄ a b c d α β γ δ′ v ! x ≡ v ! x
  set₄-≢ xa xb xc xd = trans (set₂-≢ a b α β _ xa xb) (set₂-≢ c d γ δ′ v xc xd)

------------------------------------------------------------------------
-- The action on vectors

opaque
  actV : Gen n → Vec A n → Vec A n
  actV (M-gen a) v = set₁ a (- (v ! a)) v
  actV (X-gen a b _) v = set₂ a b (v ! b) (v ! a) v
  actV (K-gen a b c d _ _ _) v =
    set₄ a b c d (rowA (v ! a) (v ! b) (v ! c) (v ! d)) (rowB (v ! a) (v ! b) (v ! c) (v ! d))
                 (rowC (v ! a) (v ! b) (v ! c) (v ! d)) (rowD (v ! a) (v ! b) (v ! c) (v ! d)) v

  actV-M≡ : (a : Fin n) (v : Vec A n) → actV (M-gen a) v ≡ set₁ a (- (v ! a)) v
  actV-M≡ a v = refl

  actV-X≡ : {a b : Fin n} .(p : a < b) (v : Vec A n) → actV (X-gen a b p) v ≡ set₂ a b (v ! b) (v ! a) v
  actV-X≡ p v = refl

  actV-K≡ : {a b c d : Fin n} .(p : a < b) .(q : b < c) .(r : c < d) (v : Vec A n) →
            actV (K-gen a b c d p q r) v ≡
            set₄ a b c d (rowA (v ! a) (v ! b) (v ! c) (v ! d)) (rowB (v ! a) (v ! b) (v ! c) (v ! d))
                         (rowC (v ! a) (v ! b) (v ! c) (v ! d)) (rowD (v ! a) (v ! b) (v ! c) (v ! d)) v
  actV-K≡ p q r v = refl

actV-Ma : (a : Fin n) (v : Vec A n) → actV (M-gen a) v ! a ≡ - (v ! a)
actV-Ma a v = trans (cong (_! a) (actV-M≡ a v)) (set₁-a a (- (v ! a)) v)

actV-M≢ : (a : Fin n) (v : Vec A n) {x : Fin n} → x ≢ a → actV (M-gen a) v ! x ≡ v ! x
actV-M≢ a v {x} xa = trans (cong (_! x) (actV-M≡ a v)) (set₁-≢ a (- (v ! a)) v xa)

module _ {a b : Fin n} .(p : a < b) (v : Vec A n) where

  actV-Xa : actV (X-gen a b p) v ! a ≡ v ! b
  actV-Xa = trans (cong (_! a) (actV-X≡ p v)) (set₂-a a b (v ! b) (v ! a) v)

  actV-Xb : actV (X-gen a b p) v ! b ≡ v ! a
  actV-Xb = trans (cong (_! b) (actV-X≡ p v)) (set₂-b a b (v ! b) (v ! a) v (<⇒≢ p))

  actV-X≢ : ∀ {x} → x ≢ a → x ≢ b → actV (X-gen a b p) v ! x ≡ v ! x
  actV-X≢ {x} xa xb = trans (cong (_! x) (actV-X≡ p v)) (set₂-≢ a b (v ! b) (v ! a) v xa xb)

module _ {a b c d : Fin n} .(p : a < b) .(q : b < c) .(r : c < d) (v : Vec A n) where

  private
    D = distinct₄ p q r
    va = v ! a
    vb = v ! b
    vc = v ! c
    vd = v ! d
    g = K-gen a b c d p q r

  actV-Ka : actV g v ! a ≡ rowA va vb vc vd
  actV-Ka = trans (cong (_! a) (actV-K≡ p q r v)) (set₄-a D _ _ _ _ v)

  actV-Kb : actV g v ! b ≡ rowB va vb vc vd
  actV-Kb = trans (cong (_! b) (actV-K≡ p q r v)) (set₄-b D _ _ _ _ v)

  actV-Kc : actV g v ! c ≡ rowC va vb vc vd
  actV-Kc = trans (cong (_! c) (actV-K≡ p q r v)) (set₄-c D _ _ _ _ v)

  actV-Kd : actV g v ! d ≡ rowD va vb vc vd
  actV-Kd = trans (cong (_! d) (actV-K≡ p q r v)) (set₄-d D _ _ _ _ v)

  actV-K≢ : ∀ {x} → x ≢ a → x ≢ b → x ≢ c → x ≢ d → actV g v ! x ≡ v ! x
  actV-K≢ {x} xa xb xc xd = trans (cong (_! x) (actV-K≡ p q r v)) (set₄-≢ D _ _ _ _ v xa xb xc xd)

actVʷ : Word (Gen n) → Vec A n → Vec A n
actVʷ [ g ]ʷ   = actV g
actVʷ ε        = id
actVʷ (u • w)  = actVʷ u ∘ actVʷ w

------------------------------------------------------------------------
-- The action on matrices, column by column

actM : Gen n → Matrix n m A → Matrix n m A
actM g M = Matrix' (Vec.map (actV g) (unMatrix M))

actMʷ : Word (Gen n) → Matrix n m A → Matrix n m A
actMʷ [ g ]ʷ  = actM g
actMʷ ε       = id
actMʷ (u • w) = actMʷ u ∘ actMʷ w

col-actM : (g : Gen n) (M : Matrix n m A) (c : Fin m) → col (actM g M) c ≡ actV g (col M c)
col-actM g M c = VecP.lookup-map c (actV g) (unMatrix M)

col-actMʷ : (w : Word (Gen n)) (M : Matrix n m A) (c : Fin m) → col (actMʷ w M) c ≡ actVʷ w (col M c)
col-actMʷ [ g ]ʷ M c = col-actM g M c
col-actMʷ ε M c = refl
col-actMʷ (u • w) M c = trans (col-actMʷ u (actMʷ w M) c) (cong (actVʷ u) (col-actMʷ w M c))

------------------------------------------------------------------------
-- The matrices of the generators

private
  if-t : ∀ {B : Set} {b : Bool} {x y : B} → b ≡ true → (if b then x else y) ≡ x
  if-t refl = refl

  if-f : ∀ {B : Set} {b : Bool} {x y : B} → b ≡ false → (if b then x else y) ≡ y
  if-f refl = refl

  is : ∀ {x y : Fin n} → x ≡ y → does (x FinP.≟ y) ≡ true
  is {x = x} {y} e = dec-true (x FinP.≟ y) e

  isn't : ∀ {x y : Fin n} → x ≢ y → does (x FinP.≟ y) ≡ false
  isn't {x = x} {y} ne = dec-false (x FinP.≟ y) ne

  sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
  sym≢ ne e = ne (sym e)

coef : Gen n → Fin n → Fin n → A
coef (M-gen a) r x = if does (r FinP.≟ a) then - δ r x else δ r x
coef (X-gen a b _) r x =
  if does (r FinP.≟ a) then δ b x else if does (r FinP.≟ b) then δ a x else δ r x
coef (K-gen a b c d _ _ _) r x =
  if does (r FinP.≟ a) then rowA (δ a x) (δ b x) (δ c x) (δ d x)
  else if does (r FinP.≟ b) then rowB (δ a x) (δ b x) (δ c x) (δ d x)
  else if does (r FinP.≟ c) then rowC (δ a x) (δ b x) (δ c x) (δ d x)
  else if does (r FinP.≟ d) then rowD (δ a x) (δ b x) (δ c x) (δ d x)
  else δ r x

private
  -- Sums against the δ's.
  sum-sδ : (s : A) (y : Fin n) (v : Vec A n) → sum (λ x → s * (δ y x * v ! x)) ≡ s * v ! y
  sum-sδ s y v = trans (sym (*-distribˡ-sum s (λ x → δ y x * v ! x))) (cong (s *_) (sum-δˡ (v !_) y))

  sum-lin : (s₁ s₂ s₃ s₄ : A) (a b c d : Fin n) (v : Vec A n) →
            sum (λ x → lin s₁ s₂ s₃ s₄ (δ a x) (δ b x) (δ c x) (δ d x) * v ! x)
            ≡ lin s₁ s₂ s₃ s₄ (v ! a) (v ! b) (v ! c) (v ! d)
  sum-lin s₁ s₂ s₃ s₄ a b c d v = begin
    sum (λ x → lin s₁ s₂ s₃ s₄ (δ a x) (δ b x) (δ c x) (δ d x) * v ! x)
      ≡⟨ sum-cong-≗ (λ x → split x) ⟩
    sum (λ x → (((h * s₁) * (δ a x * v ! x) + (h * s₂) * (δ b x * v ! x)) + (h * s₃) * (δ c x * v ! x))
               + (h * s₄) * (δ d x * v ! x))
      ≡⟨ ∑-distrib-+ (λ x → ((h * s₁) * (δ a x * v ! x) + (h * s₂) * (δ b x * v ! x)) + (h * s₃) * (δ c x * v ! x))
                     (λ x → (h * s₄) * (δ d x * v ! x)) ⟩
    sum (λ x → ((h * s₁) * (δ a x * v ! x) + (h * s₂) * (δ b x * v ! x)) + (h * s₃) * (δ c x * v ! x))
      + sum (λ x → (h * s₄) * (δ d x * v ! x))
      ≡⟨ cong₂ _+_ (trans (∑-distrib-+ (λ x → (h * s₁) * (δ a x * v ! x) + (h * s₂) * (δ b x * v ! x))
                                       (λ x → (h * s₃) * (δ c x * v ! x)))
                          (cong₂ _+_ (trans (∑-distrib-+ (λ x → (h * s₁) * (δ a x * v ! x)) (λ x → (h * s₂) * (δ b x * v ! x)))
                                            (cong₂ _+_ (sum-sδ (h * s₁) a v) (sum-sδ (h * s₂) b v)))
                                     (sum-sδ (h * s₃) c v)))
                   (sum-sδ (h * s₄) d v) ⟩
    (((h * s₁) * v ! a + (h * s₂) * v ! b) + (h * s₃) * v ! c) + (h * s₄) * v ! d
      ≡⟨ S.solve 9 (λ h s₁ s₂ s₃ s₄ x₁ x₂ x₃ x₄ →
             (((h S.:* s₁) S.:* x₁ S.:+ (h S.:* s₂) S.:* x₂) S.:+ (h S.:* s₃) S.:* x₃) S.:+ (h S.:* s₄) S.:* x₄
             S.:= h S.:* (((s₁ S.:* x₁ S.:+ s₂ S.:* x₂) S.:+ s₃ S.:* x₃) S.:+ s₄ S.:* x₄))
           AR.refl h s₁ s₂ s₃ s₄ (v ! a) (v ! b) (v ! c) (v ! d) ⟩
    lin s₁ s₂ s₃ s₄ (v ! a) (v ! b) (v ! c) (v ! d) ∎
    where
    open ≡-Reasoning
    split : ∀ x → lin s₁ s₂ s₃ s₄ (δ a x) (δ b x) (δ c x) (δ d x) * v ! x ≡
                  (((h * s₁) * (δ a x * v ! x) + (h * s₂) * (δ b x * v ! x)) + (h * s₃) * (δ c x * v ! x))
                  + (h * s₄) * (δ d x * v ! x)
    split x = S.solve 10 (λ h s₁ s₂ s₃ s₄ d₁ d₂ d₃ d₄ w →
                (h S.:* (((s₁ S.:* d₁ S.:+ s₂ S.:* d₂) S.:+ s₃ S.:* d₃) S.:+ s₄ S.:* d₄)) S.:* w
                S.:= (((h S.:* s₁) S.:* (d₁ S.:* w) S.:+ (h S.:* s₂) S.:* (d₂ S.:* w)) S.:+ (h S.:* s₃) S.:* (d₃ S.:* w))
                     S.:+ (h S.:* s₄) S.:* (d₄ S.:* w))
                AR.refl h s₁ s₂ s₃ s₄ (δ a x) (δ b x) (δ c x) (δ d x) (v ! x)

  sum-negδ : (a : Fin n) (v : Vec A n) → sum (λ x → (- δ a x) * v ! x) ≡ - (v ! a)
  sum-negδ a v = begin
    sum (λ x → (- δ a x) * v ! x)      ≡⟨ sum-cong-≗ (λ x → S.solve 2 (λ d w → (S.:- d) S.:* w S.:= (S.:- S.con (Data.Integer.Base.+ 1)) S.:* (d S.:* w)) AR.refl (δ a x) (v ! x)) ⟩
    sum (λ x → (- 1#) * (δ a x * v ! x)) ≡⟨ sum-sδ (- 1#) a v ⟩
    (- 1#) * v ! a                     ≡⟨ S.solve 1 (λ w → (S.:- S.con (Data.Integer.Base.+ 1)) S.:* w S.:= S.:- w) AR.refl (v ! a) ⟩
    - (v ! a)                          ∎
    where
    open ≡-Reasoning
    import Data.Integer.Base

-- The coefficients, row by row.
coef-M-a : (a x : Fin n) → coef (M-gen a) a x ≡ - δ a x
coef-M-a a x = if-t (is {x = a} {a} refl)

coef-M-≢ : (a : Fin n) {r : Fin n} → r ≢ a → ∀ x → coef (M-gen a) r x ≡ δ r x
coef-M-≢ a {r} ra x = if-f (isn't {x = r} {a} ra)

module _ {a b : Fin n} .(p : a < b) where

  coef-X-a : ∀ x → coef (X-gen a b p) a x ≡ δ b x
  coef-X-a x = if-t (is {x = a} {a} refl)

  coef-X-b : ∀ x → coef (X-gen a b p) b x ≡ δ a x
  coef-X-b x = trans (if-f (isn't {x = b} {a} (sym≢ (<⇒≢ p)))) (if-t (is {x = b} {b} refl))

  coef-X-≢ : ∀ {r} → r ≢ a → r ≢ b → ∀ x → coef (X-gen a b p) r x ≡ δ r x
  coef-X-≢ {r} ra rb x = trans (if-f (isn't {x = r} {a} ra)) (if-f (isn't {x = r} {b} rb))

module _ {a b c d : Fin n} .(p : a < b) .(q : b < c) .(s : c < d) where

  private
    g = K-gen a b c d p q s
    D = distinct₄ p q s
    open Distinct₄ D

  coef-K-a : ∀ x → coef g a x ≡ rowA (δ a x) (δ b x) (δ c x) (δ d x)
  coef-K-a x = if-t (is {x = a} {a} refl)

  coef-K-b : ∀ x → coef g b x ≡ rowB (δ a x) (δ b x) (δ c x) (δ d x)
  coef-K-b x = trans (if-f (isn't {x = b} {a} (sym≢ ab))) (if-t (is {x = b} {b} refl))

  coef-K-c : ∀ x → coef g c x ≡ rowC (δ a x) (δ b x) (δ c x) (δ d x)
  coef-K-c x = trans (if-f (isn't {x = c} {a} (sym≢ ac))) (trans (if-f (isn't {x = c} {b} (sym≢ bc))) (if-t (is {x = c} {c} refl)))

  coef-K-d : ∀ x → coef g d x ≡ rowD (δ a x) (δ b x) (δ c x) (δ d x)
  coef-K-d x = trans (if-f (isn't {x = d} {a} (sym≢ ad)))
                 (trans (if-f (isn't {x = d} {b} (sym≢ bd))) (trans (if-f (isn't {x = d} {c} (sym≢ cd))) (if-t (is {x = d} {d} refl))))

  coef-K-≢ : ∀ {r} → r ≢ a → r ≢ b → r ≢ c → r ≢ d → ∀ x → coef g r x ≡ δ r x
  coef-K-≢ {r} ra rb rc rd x =
    trans (if-f (isn't {x = r} {a} ra)) (trans (if-f (isn't {x = r} {b} rb)) (trans (if-f (isn't {x = r} {c} rc)) (if-f (isn't {x = r} {d} rd))))

actV-row : (g : Gen n) (v : Vec A n) (r : Fin n) → actV g v ! r ≡ sum (λ x → coef g r x * v ! x)
actV-row (M-gen a) v r = by (r FinP.≟ a)
  where
  by : Dec (r ≡ a) → actV (M-gen a) v ! r ≡ sum (λ x → coef (M-gen a) r x * v ! x)
  by (yes refl) = trans (actV-Ma r v) (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-M-a r x))) (sum-negδ r v)))
  by (no r≢a) = trans (actV-M≢ a v r≢a)
                  (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-M-≢ a r≢a x))) (sum-δˡ (v !_) r)))
actV-row (X-gen a b p) v r = by (r FinP.≟ a) (r FinP.≟ b)
  where
  g = X-gen a b p
  by : Dec (r ≡ a) → Dec (r ≡ b) → actV g v ! r ≡ sum (λ x → coef g r x * v ! x)
  by (yes refl) _ = trans (actV-Xa p v) (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-X-a p x))) (sum-δˡ (v !_) b)))
  by (no r≢a) (yes refl) =
    trans (actV-Xb p v) (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-X-b p x))) (sum-δˡ (v !_) a)))
  by (no r≢a) (no r≢b) =
    trans (actV-X≢ p v r≢a r≢b) (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-X-≢ p r≢a r≢b x))) (sum-δˡ (v !_) r)))
actV-row (K-gen a b c d p q s) v r = by (r FinP.≟ a) (r FinP.≟ b) (r FinP.≟ c) (r FinP.≟ d)
  where
  g = K-gen a b c d p q s
  by : Dec (r ≡ a) → Dec (r ≡ b) → Dec (r ≡ c) → Dec (r ≡ d) → actV g v ! r ≡ sum (λ x → coef g r x * v ! x)
  by (yes refl) _ _ _ =
    trans (actV-Ka p q s v) (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-K-a p q s x))) (sum-lin 1# 1# 1# 1# a b c d v)))
  by (no ra) (yes refl) _ _ =
    trans (actV-Kb p q s v) (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-K-b p q s x))) (sum-lin 1# m1 1# m1 a b c d v)))
  by (no ra) (no rb) (yes refl) _ =
    trans (actV-Kc p q s v) (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-K-c p q s x))) (sum-lin 1# 1# m1 m1 a b c d v)))
  by (no ra) (no rb) (no rc) (yes refl) =
    trans (actV-Kd p q s v) (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-K-d p q s x))) (sum-lin 1# m1 m1 1# a b c d v)))
  by (no ra) (no rb) (no rc) (no rd) =
    trans (actV-K≢ p q s v ra rb rc rd)
      (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-K-≢ p q s ra rb rc rd x))) (sum-δˡ (v !_) r)))

gmat : Gen n → Matrix n n A
gmat g = mk (coef g)

ent-gmat : (g : Gen n) (r c : Fin n) → ent (gmat g) r c ≡ coef g r c
ent-gmat g = ent-mk (coef g)

actM≡ : (g : Gen n) (M : Matrix n m A) → actM g M ≡ gmat g ·*· M
actM≡ g M = mat-ext λ r c → begin
  ent (actM g M) r c                           ≡⟨ cong (_! r) (col-actM g M c) ⟩
  actV g (col M c) ! r                         ≡⟨ actV-row g (col M c) r ⟩
  sum (λ x → coef g r x * ent M x c)           ≡⟨ sum-cong-≗ (λ x → cong (_* ent M x c) (sym (ent-gmat g r x))) ⟩
  sum (λ x → ent (gmat g) r x * ent M x c)     ≡⟨ sym (ent-·*· (gmat g) M r c) ⟩
  ent (gmat g ·*· M) r c                       ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The matrices of words

⟦_⟧ᵐ : Word (Gen n) → Matrix n n A
⟦ w ⟧ᵐ = actMʷ w 𝕀

⟦g⟧ᵐ≡ : (g : Gen n) → ⟦ [ g ]ʷ ⟧ᵐ ≡ gmat g
⟦g⟧ᵐ≡ g = trans (actM≡ g 𝕀) (·*·-identityʳ (gmat g))

actMʷ≡ : (w : Word (Gen n)) (M : Matrix n m A) → actMʷ w M ≡ ⟦ w ⟧ᵐ ·*· M
actMʷ≡ [ g ]ʷ M = trans (actM≡ g M) (cong (_·*· M) (sym (⟦g⟧ᵐ≡ g)))
actMʷ≡ ε M = sym (·*·-identityˡ M)
actMʷ≡ (u • w) M = begin
  actMʷ u (actMʷ w M)            ≡⟨ actMʷ≡ u (actMʷ w M) ⟩
  ⟦ u ⟧ᵐ ·*· actMʷ w M           ≡⟨ cong (⟦ u ⟧ᵐ ·*·_) (actMʷ≡ w M) ⟩
  ⟦ u ⟧ᵐ ·*· (⟦ w ⟧ᵐ ·*· M)      ≡⟨ sym (·*·-assoc ⟦ u ⟧ᵐ ⟦ w ⟧ᵐ M) ⟩
  (⟦ u ⟧ᵐ ·*· ⟦ w ⟧ᵐ) ·*· M      ≡⟨ cong (_·*· M) (sym (actMʷ≡ u ⟦ w ⟧ᵐ)) ⟩
  ⟦ u • w ⟧ᵐ ·*· M               ∎
  where open ≡-Reasoning

⟦•⟧ᵐ : (u w : Word (Gen n)) → ⟦ u • w ⟧ᵐ ≡ ⟦ u ⟧ᵐ ·*· ⟦ w ⟧ᵐ
⟦•⟧ᵐ u w = actMʷ≡ u ⟦ w ⟧ᵐ

⟦ε⟧ᵐ : ⟦ ε ⟧ᵐ ≡ 𝕀 {n}
⟦ε⟧ᵐ = refl
