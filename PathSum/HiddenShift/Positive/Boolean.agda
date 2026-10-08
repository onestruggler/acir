------------------------------------------------------------------------
-- Presentations of groups
--
-- Boolean functions of degree at most one and two, on bit vectors
--
-- PathSum.HiddenShift.Positive proves that a class of reduction
-- strategies always completes the hidden shift path-sum.  Its
-- invariant is about the phase of a path-sum read as a Boolean
-- function F of the path variables (the phase is ½F modulo 1), and it
-- needs the two lowest degrees of such functions: affine ones (degree
-- at most one) and quadratic ones (at most two).  This module defines
-- them by finite differences, without polynomials:
--
--   Aff f  : f x ⊕ f (x⊕u) ⊕ f (x⊕w) ⊕ f (x⊕u⊕w) = 0 for all x, u, w,
--   Quad f : the same second difference vanishes after one more
--            difference, along any third direction v,
--
-- and proves what the invariant uses: both are closed under ⊕ and
-- under composition with affine maps of the bit vectors (AffMap), the
-- derivative of a quadratic function along any direction is affine,
-- the product of two affine functions is quadratic, and an affine
-- function is a constant plus a sum of coordinates (aff-expand).
--
-- The derivative of f in a coordinate v is ∂ˢ f v; f is Clifford in v
-- (Cl) when that derivative is affine, and independent of v (Indep)
-- when it vanishes.  The last section shows how both survive the
-- maps the rules read a path-sum's values through: renumbering (unfr),
-- clearing the head ([Elim]) and the substitution of an [HH] (Cl-hh,
-- Indep-hh-off, Indep-hh-out), where a coordinate that moves with the
-- substituted one stays Clifford when that one is Clifford too.
--
-- Points are vectors (Pt n = Vec Bool n) rather than functions Fin n →
-- Bool, so that two points are equal when they agree everywhere and a
-- Boolean function of a point needs no proof that it respects
-- pointwise equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.HiddenShift.Positive.Boolean where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_)
open import Data.Bool.Properties using
  (xor-assoc; xor-comm; xor-identityˡ; xor-identityʳ; xor-same)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; insertAt; removeAt)
open import Data.Vec.Properties using (insertAt-lookup; insertAt-punchIn)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

private
  variable
    n m k : ℕ


------------------------------------------------------------------------
-- Bits

-- Rearrangements of exclusive ors, each proved by cases.

xor-medial : ∀ a b c d → (a xor b) xor (c xor d) ≡ (a xor c) xor (b xor d)
xor-medial false false false false = refl
xor-medial false false false true  = refl
xor-medial false false true  false = refl
xor-medial false false true  true  = refl
xor-medial false true  false false = refl
xor-medial false true  false true  = refl
xor-medial false true  true  false = refl
xor-medial false true  true  true  = refl
xor-medial true  false false false = refl
xor-medial true  false false true  = refl
xor-medial true  false true  false = refl
xor-medial true  false true  true  = refl
xor-medial true  true  false false = refl
xor-medial true  true  false true  = refl
xor-medial true  true  true  false = refl
xor-medial true  true  true  true  = refl

xor-cancelˡ : ∀ a b → a xor (a xor b) ≡ b
xor-cancelˡ false b = refl
xor-cancelˡ true  false = refl
xor-cancelˡ true  true  = refl

xor-false : ∀ {a b} → a xor b ≡ false → a ≡ b
xor-false {false} {false} _ = refl
xor-false {true}  {true}  _ = refl

xor-eq : ∀ {a b} → a ≡ b → a xor b ≡ false
xor-eq {false} refl = refl
xor-eq {true}  refl = refl

cong₃ : ∀ {A B C D : Set} (h : A → B → C → D) {a a′ b b′ c c′} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ → h a b c ≡ h a′ b′ c′
cong₃ h refl refl refl = refl


------------------------------------------------------------------------
-- Points

Pt : ℕ → Set
Pt = Vec Bool

infixl 6 _⊕_

_⊕_ : Pt n → Pt n → Pt n
[]      ⊕ []      = []
(a ∷ x) ⊕ (b ∷ y) = (a xor b) ∷ (x ⊕ y)

0ᵖ : Pt n
0ᵖ {zero}  = []
0ᵖ {suc n} = false ∷ 0ᵖ

-- Two points that agree at every coordinate are equal.

vext : {x y : Pt n} → (∀ i → lookup x i ≡ lookup y i) → x ≡ y
vext {x = []}    {[]}    h = refl
vext {x = a ∷ x} {b ∷ y} h =
  cong₂ _∷_ (h zero) (vext (λ i → h (suc i)))

lookup-⊕ : (x y : Pt n) (i : Fin n) →
           lookup (x ⊕ y) i ≡ lookup x i xor lookup y i
lookup-⊕ (a ∷ x) (b ∷ y) zero    = refl
lookup-⊕ (a ∷ x) (b ∷ y) (suc i) = lookup-⊕ x y i

lookup-0ᵖ : (i : Fin n) → lookup (0ᵖ {n}) i ≡ false
lookup-0ᵖ zero    = refl
lookup-0ᵖ (suc i) = lookup-0ᵖ i

-- The group laws.

⊕-assoc : (x y z : Pt n) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
⊕-assoc []      []      []      = refl
⊕-assoc (a ∷ x) (b ∷ y) (c ∷ z) = cong₂ _∷_ (xor-assoc a b c) (⊕-assoc x y z)

⊕-comm : (x y : Pt n) → x ⊕ y ≡ y ⊕ x
⊕-comm []      []      = refl
⊕-comm (a ∷ x) (b ∷ y) = cong₂ _∷_ (xor-comm a b) (⊕-comm x y)

⊕-identityˡ : (x : Pt n) → 0ᵖ ⊕ x ≡ x
⊕-identityˡ []      = refl
⊕-identityˡ (a ∷ x) = cong (a ∷_) (⊕-identityˡ x)

⊕-identityʳ : (x : Pt n) → x ⊕ 0ᵖ ≡ x
⊕-identityʳ []      = refl
⊕-identityʳ (a ∷ x) = cong₂ _∷_ (xor-identityʳ a) (⊕-identityʳ x)

⊕-self : (x : Pt n) → x ⊕ x ≡ 0ᵖ
⊕-self []      = refl
⊕-self (a ∷ x) = cong₂ _∷_ (xor-same a) (⊕-self x)

-- Derived rearrangements.

⊕-medial : (x y z w : Pt n) → (x ⊕ y) ⊕ (z ⊕ w) ≡ (x ⊕ z) ⊕ (y ⊕ w)
⊕-medial x y z w = vext λ i → trans (lookup-⊕ (x ⊕ y) (z ⊕ w) i)
  (trans (cong₂ _xor_ (lookup-⊕ x y i) (lookup-⊕ z w i))
    (trans (xor-medial (lookup x i) (lookup y i) (lookup z i) (lookup w i))
      (sym (trans (lookup-⊕ (x ⊕ z) (y ⊕ w) i)
                  (cong₂ _xor_ (lookup-⊕ x z i) (lookup-⊕ y w i))))))

⊕-cancelˡ : (x y : Pt n) → x ⊕ (x ⊕ y) ≡ y
⊕-cancelˡ x y = trans (sym (⊕-assoc x x y))
  (trans (cong (_⊕ y) (⊕-self x)) (⊕-identityˡ y))

⊕-swap : (x u w : Pt n) → (x ⊕ u) ⊕ w ≡ (x ⊕ w) ⊕ u
⊕-swap x u w = trans (⊕-assoc x u w)
  (trans (cong (x ⊕_) (⊕-comm u w)) (sym (⊕-assoc x w u)))

-- A vector whose sum with another is 0 is that other.

⊕-unique : {x y : Pt n} → x ⊕ y ≡ 0ᵖ → x ≡ y
⊕-unique {x = x} {y} e = trans (sym (⊕-identityʳ x))
  (trans (cong (x ⊕_) (sym (⊕-self y)))
    (trans (sym (⊕-assoc x y y))
      (trans (cong (_⊕ y) e) (⊕-identityˡ y))))


------------------------------------------------------------------------
-- Differences

-- The second difference of f at x along u and w, and the third along
-- one more direction v.

D2 : (Pt n → Bool) → Pt n → Pt n → Pt n → Bool
D2 f x u w = ((f x xor f (x ⊕ u)) xor f (x ⊕ w)) xor f ((x ⊕ u) ⊕ w)

D3 : (Pt n → Bool) → Pt n → Pt n → Pt n → Pt n → Bool
D3 f x u v w = D2 f x u w xor D2 f (x ⊕ v) u w

-- Degree at most one, and at most two.

-- (Records, so that the function is recovered from the type.)

record Aff (f : Pt n → Bool) : Set where
  constructor aff
  field
    d2 : ∀ x u w → D2 f x u w ≡ false

open Aff public

record Quad (f : Pt n → Bool) : Set where
  constructor quad
  field
    d3 : ∀ x u v w → D3 f x u v w ≡ false

open Quad public

-- Affine maps of points: every coordinate is an affine function.

record AffMap (φ : Pt n → Pt m) : Set where
  constructor affmap
  field
    sq : ∀ x u w →
         ((φ x ⊕ φ (x ⊕ u)) ⊕ φ (x ⊕ w)) ⊕ φ ((x ⊕ u) ⊕ w) ≡ 0ᵖ

open AffMap public

-- The derivative of f along v.

∂ : (Pt n → Bool) → Pt n → Pt n → Bool
∂ f v x = f x xor f (x ⊕ v)

-- Respecting equality of values.

D2-cong : {f g : Pt n → Bool} → (∀ x → f x ≡ g x) → ∀ y u w →
          D2 f y u w ≡ D2 g y u w
D2-cong h y u w =
  cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_ (h y) (h (y ⊕ u))) (h (y ⊕ w)))
              (h ((y ⊕ u) ⊕ w))

Aff-cong : {f g : Pt n → Bool} → (∀ x → f x ≡ g x) → Aff f → Aff g
Aff-cong h a = aff λ x u w → trans (sym (D2-cong h x u w)) (d2 a x u w)

Quad-cong : {f g : Pt n → Bool} → (∀ x → f x ≡ g x) → Quad f → Quad g
Quad-cong h q = quad λ x u v w → trans
  (sym (cong₂ _xor_ (D2-cong h x u w) (D2-cong h (x ⊕ v) u w)))
  (d3 q x u v w)


------------------------------------------------------------------------
-- Closure

-- Constants, coordinates and sums are affine.

Aff-const : (b : Bool) → Aff {n} (λ _ → b)
Aff-const false = aff λ _ _ _ → refl
Aff-const true  = aff λ _ _ _ → refl

Aff-lookup : (i : Fin n) → Aff (λ x → lookup x i)
Aff-lookup i = aff λ x u w → trans
  (cong₂ _xor_ (cong₂ _xor_ (cong (lookup x i xor_) (lookup-⊕ x u i))
                           (lookup-⊕ x w i))
               (trans (lookup-⊕ (x ⊕ u) w i)
                      (cong (_xor lookup w i) (lookup-⊕ x u i))))
  (lookup-bits (lookup x i) (lookup u i) (lookup w i))
  where
  lookup-bits : ∀ a b c →
                ((a xor (a xor b)) xor (a xor c)) xor ((a xor b) xor c) ≡ false
  lookup-bits false false false = refl
  lookup-bits false false true  = refl
  lookup-bits false true  false = refl
  lookup-bits false true  true  = refl
  lookup-bits true  false false = refl
  lookup-bits true  false true  = refl
  lookup-bits true  true  false = refl
  lookup-bits true  true  true  = refl

private
  four : ∀ a b c d a′ b′ c′ d′ →
         (((a xor a′) xor (b xor b′)) xor (c xor c′)) xor (d xor d′) ≡
         (((a xor b) xor c) xor d) xor (((a′ xor b′) xor c′) xor d′)
  four a b c d a′ b′ c′ d′ = trans
    (cong (_xor (d xor d′))
      (trans (cong (_xor (c xor c′)) (xor-medial a a′ b b′))
             (xor-medial (a xor b) (a′ xor b′) c c′)))
    (xor-medial ((a xor b) xor c) ((a′ xor b′) xor c′) d d′)

D2-xor : (f g : Pt n → Bool) → ∀ x u w →
         D2 (λ y → f y xor g y) x u w ≡ D2 f x u w xor D2 g x u w
D2-xor f g x u w = four (f x) (f (x ⊕ u)) (f (x ⊕ w)) (f ((x ⊕ u) ⊕ w))
                        (g x) (g (x ⊕ u)) (g (x ⊕ w)) (g ((x ⊕ u) ⊕ w))

Aff-xor : {f g : Pt n → Bool} → Aff f → Aff g → Aff (λ y → f y xor g y)
Aff-xor {f = f} {g} af ag = aff λ x u w →
  trans (D2-xor f g x u w) (cong₂ _xor_ (d2 af x u w) (d2 ag x u w))

Quad-xor : {f g : Pt n → Bool} → Quad f → Quad g → Quad (λ y → f y xor g y)
Quad-xor {f = f} {g} qf qg = quad λ x u v w → trans
  (cong₂ _xor_ (D2-xor f g x u w) (D2-xor f g (x ⊕ v) u w))
  (trans (xor-medial (D2 f x u w) (D2 g x u w)
                     (D2 f (x ⊕ v) u w) (D2 g (x ⊕ v) u w))
         (cong₂ _xor_ (d3 qf x u v w) (d3 qg x u v w)))

-- Affine functions are quadratic.

Aff⇒Quad : {f : Pt n → Bool} → Aff f → Quad f
Aff⇒Quad af = quad λ x u v w → cong₂ _xor_ (d2 af x u w) (d2 af (x ⊕ v) u w)

-- An affine function at the far corner of a square is the sum of its
-- values at the other three.

aff-val : {f : Pt n → Bool} → Aff f → ∀ x u w →
          f ((x ⊕ u) ⊕ w) ≡ (f x xor f (x ⊕ u)) xor f (x ⊕ w)
aff-val af x u w = sym (xor-false (d2 af x u w))


------------------------------------------------------------------------
-- Affine maps

-- An affine map takes a square to a square.

affmap-val : {φ : Pt n → Pt m} → AffMap φ → ∀ x u w →
             φ ((x ⊕ u) ⊕ w) ≡ (φ x ⊕ φ (x ⊕ u)) ⊕ φ (x ⊕ w)
affmap-val am x u w = sym (⊕-unique (sq am x u w))

private
  -- (a ⊕ (a ⊕ b)) ⊕ (a ⊕ c) is (a ⊕ b) ⊕ c.
  tri : (a b c : Pt n) → (a ⊕ (a ⊕ b)) ⊕ (a ⊕ c) ≡ (a ⊕ b) ⊕ c
  tri a b c = trans (cong (_⊕ (a ⊕ c)) (⊕-cancelˡ a b))
    (trans (sym (⊕-assoc b a c)) (cong (_⊕ c) (⊕-comm b a)))

-- So the second difference of f ∘ φ is one of f, along the images of
-- the two directions.

D2-∘ : (f : Pt m → Bool) {φ : Pt n → Pt m} → AffMap φ → ∀ x u w →
       D2 (λ y → f (φ y)) x u w ≡
       D2 f (φ x) (φ x ⊕ φ (x ⊕ u)) (φ x ⊕ φ (x ⊕ w))
D2-∘ f {φ} am x u w = cong₂ _xor_
  (cong₂ _xor_
   (cong (f (φ x) xor_) (cong f (sym (⊕-cancelˡ (φ x) (φ (x ⊕ u))))))
               (cong f (sym (⊕-cancelˡ (φ x) (φ (x ⊕ w))))))
  (cong f (trans (affmap-val am x u w)
                 (sym (tri (φ x) (φ (x ⊕ u)) (φ (x ⊕ w))))))

Aff-∘ : {f : Pt m → Bool} {φ : Pt n → Pt m} → Aff f → AffMap φ →
        Aff (λ y → f (φ y))
Aff-∘ {f = f} {φ} af am = aff λ x u w → trans (D2-∘ f am x u w) (d2 af _ _ _)

-- The image of a direction under an affine map does not depend on the
-- base point.

affmap-side : {φ : Pt n → Pt m} → AffMap φ → ∀ x v t →
              φ (x ⊕ v) ⊕ φ ((x ⊕ v) ⊕ t) ≡ φ x ⊕ φ (x ⊕ t)
affmap-side {φ = φ} am x v t = trans (cong (φ (x ⊕ v) ⊕_) (affmap-val am x v t))
  (trans (cong (φ (x ⊕ v) ⊕_) (⊕-swap (φ x) (φ (x ⊕ v)) (φ (x ⊕ t))))
    (trans (cong (φ (x ⊕ v) ⊕_) (⊕-comm (φ x ⊕ φ (x ⊕ t)) (φ (x ⊕ v))))
           (⊕-cancelˡ (φ (x ⊕ v)) (φ x ⊕ φ (x ⊕ t)))))

Quad-∘ : {f : Pt m → Bool} {φ : Pt n → Pt m} → Quad f → AffMap φ →
         Quad (λ y → f (φ y))
Quad-∘ {f = f} {φ} qf am = quad λ x u v w → trans
  (cong₂ _xor_ (D2-∘ f am x u w)
    (trans (D2-∘ f am (x ⊕ v) u w)
      (cong₃ (D2 f) (sym (⊕-cancelˡ (φ x) (φ (x ⊕ v))))
                    (affmap-side am x v u) (affmap-side am x v w))))
  (d3 qf (φ x) (φ x ⊕ φ (x ⊕ u)) (φ x ⊕ φ (x ⊕ v)) (φ x ⊕ φ (x ⊕ w)))

-- A map is affine exactly when each of its coordinates is.

private
  lookup-sq : (a b c d : Pt m) (i : Fin m) →
              lookup (((a ⊕ b) ⊕ c) ⊕ d) i ≡
              ((lookup a i xor lookup b i) xor lookup c i) xor lookup d i
  lookup-sq a b c d i = trans (lookup-⊕ ((a ⊕ b) ⊕ c) d i)
    (cong (_xor lookup d i) (trans (lookup-⊕ (a ⊕ b) c i)
                                   (cong (_xor lookup c i) (lookup-⊕ a b i))))

AffMap-coords : {φ : Pt n → Pt m} → (∀ i → Aff (λ x → lookup (φ x) i)) →
                AffMap φ
AffMap-coords {φ = φ} h = affmap λ x u w → vext λ i →
  trans (lookup-sq (φ x) (φ (x ⊕ u)) (φ (x ⊕ w)) (φ ((x ⊕ u) ⊕ w)) i)
        (trans (d2 (h i) x u w) (sym (lookup-0ᵖ i)))

AffMap-lookup : {φ : Pt n → Pt m} → AffMap φ → ∀ i →
                Aff (λ y → lookup (φ y) i)
AffMap-lookup {φ = φ} am i = aff λ x u w → trans
  (sym (lookup-sq (φ x) (φ (x ⊕ u)) (φ (x ⊕ w)) (φ ((x ⊕ u) ⊕ w)) i))
  (trans (cong (λ p → lookup p i) (sq am x u w)) (lookup-0ᵖ i))

-- Composites of affine maps are affine.

AffMap-∘ : {φ : Pt m → Pt k} {ψ : Pt n → Pt m} → AffMap φ → AffMap ψ →
           AffMap (λ x → φ (ψ x))
AffMap-∘ {φ = φ} {ψ} aφ aψ = AffMap-coords λ i →
  Aff-∘ {f = λ y → lookup (φ y) i} (AffMap-lookup aφ i) aψ


------------------------------------------------------------------------
-- Derivatives and products

private
  -- The four corners of a square moved along v.
  corner : (x u v w : Pt n) → ((x ⊕ u) ⊕ w) ⊕ v ≡ ((x ⊕ v) ⊕ u) ⊕ w
  corner x u v w = trans (⊕-swap (x ⊕ u) w v)
    (cong (_⊕ w) (⊕-swap x u v))

-- The derivative of a quadratic function along any direction is
-- affine: its second difference is the third difference of f.

Quad⇒Aff-∂ : {f : Pt n → Bool} → Quad f → ∀ v → Aff (∂ f v)
Quad⇒Aff-∂ {f = f} qf v = aff λ x u w → trans
  (D2-xor f (λ y → f (y ⊕ v)) x u w)
  (trans (cong (D2 f x u w xor_) (moved x u w)) (d3 qf x u v w))
  where
  moved : ∀ x u w → D2 (λ y → f (y ⊕ v)) x u w ≡ D2 f (x ⊕ v) u w
  moved x u w = cong₂ _xor_
    (cong₂ _xor_ (cong (f (x ⊕ v) xor_) (cong f (⊕-swap x u v)))
                 (cong f (⊕-swap x w v)))
    (cong f (corner x u v w))

-- The product of two affine functions is quadratic: at the eight
-- corners of a cube both are determined by their values at four, and
-- the third difference of the product of the two determinations
-- vanishes identically.

private
  prod8 : ∀ a b c d a′ b′ c′ d′ →
          ((((a ∧ a′) xor (b ∧ b′)) xor (d ∧ d′)) xor
            ((((a xor b) xor d)) ∧ (((a′ xor b′) xor d′)))) xor
          ((((c ∧ c′) xor (((a xor c) xor b) ∧ ((a′ xor c′) xor b′))) xor
            (((a xor c) xor d) ∧ ((a′ xor c′) xor d′))) xor
           (((c xor ((a xor c) xor b)) xor ((a xor c) xor d)) ∧
            ((c′ xor ((a′ xor c′) xor b′)) xor ((a′ xor c′) xor d′))))
          ≡ false
  prod8 false false false false false false false false = refl
  prod8 false false false false false false false true  = refl
  prod8 false false false false false false true  false = refl
  prod8 false false false false false false true  true  = refl
  prod8 false false false false false true  false false = refl
  prod8 false false false false false true  false true  = refl
  prod8 false false false false false true  true  false = refl
  prod8 false false false false false true  true  true  = refl
  prod8 false false false false true  false false false = refl
  prod8 false false false false true  false false true  = refl
  prod8 false false false false true  false true  false = refl
  prod8 false false false false true  false true  true  = refl
  prod8 false false false false true  true  false false = refl
  prod8 false false false false true  true  false true  = refl
  prod8 false false false false true  true  true  false = refl
  prod8 false false false false true  true  true  true  = refl
  prod8 false false false true  false false false false = refl
  prod8 false false false true  false false false true  = refl
  prod8 false false false true  false false true  false = refl
  prod8 false false false true  false false true  true  = refl
  prod8 false false false true  false true  false false = refl
  prod8 false false false true  false true  false true  = refl
  prod8 false false false true  false true  true  false = refl
  prod8 false false false true  false true  true  true  = refl
  prod8 false false false true  true  false false false = refl
  prod8 false false false true  true  false false true  = refl
  prod8 false false false true  true  false true  false = refl
  prod8 false false false true  true  false true  true  = refl
  prod8 false false false true  true  true  false false = refl
  prod8 false false false true  true  true  false true  = refl
  prod8 false false false true  true  true  true  false = refl
  prod8 false false false true  true  true  true  true  = refl
  prod8 false false true  false false false false false = refl
  prod8 false false true  false false false false true  = refl
  prod8 false false true  false false false true  false = refl
  prod8 false false true  false false false true  true  = refl
  prod8 false false true  false false true  false false = refl
  prod8 false false true  false false true  false true  = refl
  prod8 false false true  false false true  true  false = refl
  prod8 false false true  false false true  true  true  = refl
  prod8 false false true  false true  false false false = refl
  prod8 false false true  false true  false false true  = refl
  prod8 false false true  false true  false true  false = refl
  prod8 false false true  false true  false true  true  = refl
  prod8 false false true  false true  true  false false = refl
  prod8 false false true  false true  true  false true  = refl
  prod8 false false true  false true  true  true  false = refl
  prod8 false false true  false true  true  true  true  = refl
  prod8 false false true  true  false false false false = refl
  prod8 false false true  true  false false false true  = refl
  prod8 false false true  true  false false true  false = refl
  prod8 false false true  true  false false true  true  = refl
  prod8 false false true  true  false true  false false = refl
  prod8 false false true  true  false true  false true  = refl
  prod8 false false true  true  false true  true  false = refl
  prod8 false false true  true  false true  true  true  = refl
  prod8 false false true  true  true  false false false = refl
  prod8 false false true  true  true  false false true  = refl
  prod8 false false true  true  true  false true  false = refl
  prod8 false false true  true  true  false true  true  = refl
  prod8 false false true  true  true  true  false false = refl
  prod8 false false true  true  true  true  false true  = refl
  prod8 false false true  true  true  true  true  false = refl
  prod8 false false true  true  true  true  true  true  = refl
  prod8 false true  false false false false false false = refl
  prod8 false true  false false false false false true  = refl
  prod8 false true  false false false false true  false = refl
  prod8 false true  false false false false true  true  = refl
  prod8 false true  false false false true  false false = refl
  prod8 false true  false false false true  false true  = refl
  prod8 false true  false false false true  true  false = refl
  prod8 false true  false false false true  true  true  = refl
  prod8 false true  false false true  false false false = refl
  prod8 false true  false false true  false false true  = refl
  prod8 false true  false false true  false true  false = refl
  prod8 false true  false false true  false true  true  = refl
  prod8 false true  false false true  true  false false = refl
  prod8 false true  false false true  true  false true  = refl
  prod8 false true  false false true  true  true  false = refl
  prod8 false true  false false true  true  true  true  = refl
  prod8 false true  false true  false false false false = refl
  prod8 false true  false true  false false false true  = refl
  prod8 false true  false true  false false true  false = refl
  prod8 false true  false true  false false true  true  = refl
  prod8 false true  false true  false true  false false = refl
  prod8 false true  false true  false true  false true  = refl
  prod8 false true  false true  false true  true  false = refl
  prod8 false true  false true  false true  true  true  = refl
  prod8 false true  false true  true  false false false = refl
  prod8 false true  false true  true  false false true  = refl
  prod8 false true  false true  true  false true  false = refl
  prod8 false true  false true  true  false true  true  = refl
  prod8 false true  false true  true  true  false false = refl
  prod8 false true  false true  true  true  false true  = refl
  prod8 false true  false true  true  true  true  false = refl
  prod8 false true  false true  true  true  true  true  = refl
  prod8 false true  true  false false false false false = refl
  prod8 false true  true  false false false false true  = refl
  prod8 false true  true  false false false true  false = refl
  prod8 false true  true  false false false true  true  = refl
  prod8 false true  true  false false true  false false = refl
  prod8 false true  true  false false true  false true  = refl
  prod8 false true  true  false false true  true  false = refl
  prod8 false true  true  false false true  true  true  = refl
  prod8 false true  true  false true  false false false = refl
  prod8 false true  true  false true  false false true  = refl
  prod8 false true  true  false true  false true  false = refl
  prod8 false true  true  false true  false true  true  = refl
  prod8 false true  true  false true  true  false false = refl
  prod8 false true  true  false true  true  false true  = refl
  prod8 false true  true  false true  true  true  false = refl
  prod8 false true  true  false true  true  true  true  = refl
  prod8 false true  true  true  false false false false = refl
  prod8 false true  true  true  false false false true  = refl
  prod8 false true  true  true  false false true  false = refl
  prod8 false true  true  true  false false true  true  = refl
  prod8 false true  true  true  false true  false false = refl
  prod8 false true  true  true  false true  false true  = refl
  prod8 false true  true  true  false true  true  false = refl
  prod8 false true  true  true  false true  true  true  = refl
  prod8 false true  true  true  true  false false false = refl
  prod8 false true  true  true  true  false false true  = refl
  prod8 false true  true  true  true  false true  false = refl
  prod8 false true  true  true  true  false true  true  = refl
  prod8 false true  true  true  true  true  false false = refl
  prod8 false true  true  true  true  true  false true  = refl
  prod8 false true  true  true  true  true  true  false = refl
  prod8 false true  true  true  true  true  true  true  = refl
  prod8 true  false false false false false false false = refl
  prod8 true  false false false false false false true  = refl
  prod8 true  false false false false false true  false = refl
  prod8 true  false false false false false true  true  = refl
  prod8 true  false false false false true  false false = refl
  prod8 true  false false false false true  false true  = refl
  prod8 true  false false false false true  true  false = refl
  prod8 true  false false false false true  true  true  = refl
  prod8 true  false false false true  false false false = refl
  prod8 true  false false false true  false false true  = refl
  prod8 true  false false false true  false true  false = refl
  prod8 true  false false false true  false true  true  = refl
  prod8 true  false false false true  true  false false = refl
  prod8 true  false false false true  true  false true  = refl
  prod8 true  false false false true  true  true  false = refl
  prod8 true  false false false true  true  true  true  = refl
  prod8 true  false false true  false false false false = refl
  prod8 true  false false true  false false false true  = refl
  prod8 true  false false true  false false true  false = refl
  prod8 true  false false true  false false true  true  = refl
  prod8 true  false false true  false true  false false = refl
  prod8 true  false false true  false true  false true  = refl
  prod8 true  false false true  false true  true  false = refl
  prod8 true  false false true  false true  true  true  = refl
  prod8 true  false false true  true  false false false = refl
  prod8 true  false false true  true  false false true  = refl
  prod8 true  false false true  true  false true  false = refl
  prod8 true  false false true  true  false true  true  = refl
  prod8 true  false false true  true  true  false false = refl
  prod8 true  false false true  true  true  false true  = refl
  prod8 true  false false true  true  true  true  false = refl
  prod8 true  false false true  true  true  true  true  = refl
  prod8 true  false true  false false false false false = refl
  prod8 true  false true  false false false false true  = refl
  prod8 true  false true  false false false true  false = refl
  prod8 true  false true  false false false true  true  = refl
  prod8 true  false true  false false true  false false = refl
  prod8 true  false true  false false true  false true  = refl
  prod8 true  false true  false false true  true  false = refl
  prod8 true  false true  false false true  true  true  = refl
  prod8 true  false true  false true  false false false = refl
  prod8 true  false true  false true  false false true  = refl
  prod8 true  false true  false true  false true  false = refl
  prod8 true  false true  false true  false true  true  = refl
  prod8 true  false true  false true  true  false false = refl
  prod8 true  false true  false true  true  false true  = refl
  prod8 true  false true  false true  true  true  false = refl
  prod8 true  false true  false true  true  true  true  = refl
  prod8 true  false true  true  false false false false = refl
  prod8 true  false true  true  false false false true  = refl
  prod8 true  false true  true  false false true  false = refl
  prod8 true  false true  true  false false true  true  = refl
  prod8 true  false true  true  false true  false false = refl
  prod8 true  false true  true  false true  false true  = refl
  prod8 true  false true  true  false true  true  false = refl
  prod8 true  false true  true  false true  true  true  = refl
  prod8 true  false true  true  true  false false false = refl
  prod8 true  false true  true  true  false false true  = refl
  prod8 true  false true  true  true  false true  false = refl
  prod8 true  false true  true  true  false true  true  = refl
  prod8 true  false true  true  true  true  false false = refl
  prod8 true  false true  true  true  true  false true  = refl
  prod8 true  false true  true  true  true  true  false = refl
  prod8 true  false true  true  true  true  true  true  = refl
  prod8 true  true  false false false false false false = refl
  prod8 true  true  false false false false false true  = refl
  prod8 true  true  false false false false true  false = refl
  prod8 true  true  false false false false true  true  = refl
  prod8 true  true  false false false true  false false = refl
  prod8 true  true  false false false true  false true  = refl
  prod8 true  true  false false false true  true  false = refl
  prod8 true  true  false false false true  true  true  = refl
  prod8 true  true  false false true  false false false = refl
  prod8 true  true  false false true  false false true  = refl
  prod8 true  true  false false true  false true  false = refl
  prod8 true  true  false false true  false true  true  = refl
  prod8 true  true  false false true  true  false false = refl
  prod8 true  true  false false true  true  false true  = refl
  prod8 true  true  false false true  true  true  false = refl
  prod8 true  true  false false true  true  true  true  = refl
  prod8 true  true  false true  false false false false = refl
  prod8 true  true  false true  false false false true  = refl
  prod8 true  true  false true  false false true  false = refl
  prod8 true  true  false true  false false true  true  = refl
  prod8 true  true  false true  false true  false false = refl
  prod8 true  true  false true  false true  false true  = refl
  prod8 true  true  false true  false true  true  false = refl
  prod8 true  true  false true  false true  true  true  = refl
  prod8 true  true  false true  true  false false false = refl
  prod8 true  true  false true  true  false false true  = refl
  prod8 true  true  false true  true  false true  false = refl
  prod8 true  true  false true  true  false true  true  = refl
  prod8 true  true  false true  true  true  false false = refl
  prod8 true  true  false true  true  true  false true  = refl
  prod8 true  true  false true  true  true  true  false = refl
  prod8 true  true  false true  true  true  true  true  = refl
  prod8 true  true  true  false false false false false = refl
  prod8 true  true  true  false false false false true  = refl
  prod8 true  true  true  false false false true  false = refl
  prod8 true  true  true  false false false true  true  = refl
  prod8 true  true  true  false false true  false false = refl
  prod8 true  true  true  false false true  false true  = refl
  prod8 true  true  true  false false true  true  false = refl
  prod8 true  true  true  false false true  true  true  = refl
  prod8 true  true  true  false true  false false false = refl
  prod8 true  true  true  false true  false false true  = refl
  prod8 true  true  true  false true  false true  false = refl
  prod8 true  true  true  false true  false true  true  = refl
  prod8 true  true  true  false true  true  false false = refl
  prod8 true  true  true  false true  true  false true  = refl
  prod8 true  true  true  false true  true  true  false = refl
  prod8 true  true  true  false true  true  true  true  = refl
  prod8 true  true  true  true  false false false false = refl
  prod8 true  true  true  true  false false false true  = refl
  prod8 true  true  true  true  false false true  false = refl
  prod8 true  true  true  true  false false true  true  = refl
  prod8 true  true  true  true  false true  false false = refl
  prod8 true  true  true  true  false true  false true  = refl
  prod8 true  true  true  true  false true  true  false = refl
  prod8 true  true  true  true  false true  true  true  = refl
  prod8 true  true  true  true  true  false false false = refl
  prod8 true  true  true  true  true  false false true  = refl
  prod8 true  true  true  true  true  false true  false = refl
  prod8 true  true  true  true  true  false true  true  = refl
  prod8 true  true  true  true  true  true  false false = refl
  prod8 true  true  true  true  true  true  false true  = refl
  prod8 true  true  true  true  true  true  true  false = refl
  prod8 true  true  true  true  true  true  true  true  = refl

Quad-∧ : {f g : Pt n → Bool} → Aff f → Aff g → Quad (λ y → f y ∧ g y)
Quad-∧ {f = f} {g} af ag = quad λ x u v w → trans
  (cong₂ _xor_
    (cong (λ t → (((f x ∧ g x) xor (f (x ⊕ u) ∧ g (x ⊕ u))) xor
                   (f (x ⊕ w) ∧ g (x ⊕ w))) xor t)
          (cong₂ _∧_ (aff-val af x u w) (aff-val ag x u w)))
    (cong₃ (λ p q r → (((f (x ⊕ v) ∧ g (x ⊕ v)) xor p) xor q) xor r)
           (cong₂ _∧_ (aff-val af x v u) (aff-val ag x v u))
           (cong₂ _∧_ (aff-val af x v w) (aff-val ag x v w))
           (cong₂ _∧_ (far af x u v w) (far ag x u v w))))
  (prod8 (f x) (f (x ⊕ u)) (f (x ⊕ v)) (f (x ⊕ w))
         (g x) (g (x ⊕ u)) (g (x ⊕ v)) (g (x ⊕ w)))
  where
  far : {h : Pt _ → Bool} → Aff h → ∀ x u v w →
        h (((x ⊕ v) ⊕ u) ⊕ w) ≡
        (h (x ⊕ v) xor ((h x xor h (x ⊕ v)) xor h (x ⊕ u))) xor
        ((h x xor h (x ⊕ v)) xor h (x ⊕ w))
  far {h} ah x u v w = trans (aff-val ah (x ⊕ v) u w)
    (cong₂ _xor_ (cong (h (x ⊕ v) xor_) (aff-val ah x v u))
                 (aff-val ah x v w))


------------------------------------------------------------------------
-- Inner products and the shape of an affine function

-- The inner product of two points.

dotᵥ : Pt n → Pt n → Bool
dotᵥ []      []      = false
dotᵥ (a ∷ s) (b ∷ x) = (a ∧ b) xor dotᵥ s x

dotᵥ-⊕ : (s x y : Pt n) → dotᵥ s (x ⊕ y) ≡ dotᵥ s x xor dotᵥ s y
dotᵥ-⊕ []      []      []      = refl
dotᵥ-⊕ (a ∷ s) (b ∷ x) (c ∷ y) = trans
  (cong₂ _xor_ (distrib a b c) (dotᵥ-⊕ s x y))
  (xor-medial (a ∧ b) (a ∧ c) (dotᵥ s x) (dotᵥ s y))
  where
  distrib : ∀ a b c → a ∧ (b xor c) ≡ (a ∧ b) xor (a ∧ c)
  distrib false b c = refl
  distrib true  b c = refl

dotᵥ-0ᵖ : (s : Pt n) → dotᵥ s 0ᵖ ≡ false
dotᵥ-0ᵖ []      = refl
dotᵥ-0ᵖ (a ∷ s) = trans (cong (_xor dotᵥ s 0ᵖ) (∧-false a)) (dotᵥ-0ᵖ s)
  where
  ∧-false : ∀ a → a ∧ false ≡ false
  ∧-false false = refl
  ∧-false true  = refl

-- A constant plus an inner product is affine ...

Aff-dot : (c : Bool) (s : Pt n) → Aff (λ x → c xor dotᵥ s x)
Aff-dot c s = aff λ x u w → trans
  (cong₂ _xor_ (cong₂ _xor_ (cong ((c xor dotᵥ s x) xor_)
                                  (cong (c xor_) (dotᵥ-⊕ s x u)))
                            (cong (c xor_) (dotᵥ-⊕ s x w)))
               (cong (c xor_) (trans (dotᵥ-⊕ s (x ⊕ u) w)
                                     (cong (_xor dotᵥ s w) (dotᵥ-⊕ s x u)))))
  (bits c (dotᵥ s x) (dotᵥ s u) (dotᵥ s w))
  where
  bits : ∀ c a b d →
         (((c xor a) xor (c xor (a xor b))) xor (c xor (a xor d))) xor
         (c xor ((a xor b) xor d)) ≡ false
  bits false false false false = refl
  bits false false false true  = refl
  bits false false true  false = refl
  bits false false true  true  = refl
  bits false true  false false = refl
  bits false true  false true  = refl
  bits false true  true  false = refl
  bits false true  true  true  = refl
  bits true  false false false = refl
  bits true  false false true  = refl
  bits true  false true  false = refl
  bits true  false true  true  = refl
  bits true  true  false false = refl
  bits true  true  false true  = refl
  bits true  true  true  false = refl
  bits true  true  true  true  = refl

-- ... and every affine function is one: a constant plus the inner
-- product with the vector of its slopes.  The slope along u is the
-- same at every point.

aff-slope : {f : Pt n → Bool} → Aff f → ∀ y u →
            f (y ⊕ u) xor f y ≡ f u xor f 0ᵖ
aff-slope {f = f} af y u = bits {f 0ᵖ} {f u} {f y} {f (y ⊕ u)} (trans
  (cong₂ _xor_ (cong₂ _xor_ (cong (f 0ᵖ xor_) (cong f (sym (⊕-identityˡ u))))
                            (cong f (sym (⊕-identityˡ y))))
               (cong f (trans (⊕-comm y u)
                              (cong (_⊕ y) (sym (⊕-identityˡ u))))))
  (d2 af 0ᵖ u y))
  where
  bits : ∀ {a b c d} → ((a xor b) xor c) xor d ≡ false → d xor c ≡ b xor a
  bits {false} {false} {false} {false} _ = refl
  bits {false} {false} {true}  {true}  _ = refl
  bits {false} {true}  {false} {true}  _ = refl
  bits {false} {true}  {true}  {false} _ = refl
  bits {true}  {false} {false} {true}  _ = refl
  bits {true}  {false} {true}  {false} _ = refl
  bits {true}  {true}  {false} {false} _ = refl
  bits {true}  {true}  {true}  {true}  _ = refl

aff-expand : {f : Pt n → Bool} → Aff f →
             Σ Bool (λ c → Σ (Pt n) (λ s → ∀ x → f x ≡ c xor dotᵥ s x))
aff-expand {n = zero}  {f} af = f [] , [] , λ
  { [] → sym (xor-identityʳ (f [])) }
aff-expand {n = suc n} {f} af =
  c′ , (slope ∷ s′) , value
  where
  f′ : Pt n → Bool
  f′ x = f (false ∷ x)

  af′ : Aff f′
  af′ = aff λ x u w → d2 af (false ∷ x) (false ∷ u) (false ∷ w)

  rec = aff-expand af′
  c′  = proj₁ rec
  s′  = proj₁ (proj₂ rec)
  eq′ = proj₂ (proj₂ rec)

  slope : Bool
  slope = f (true ∷ 0ᵖ) xor f (false ∷ 0ᵖ)

  -- f (b ∷ x) is f (0 ∷ x) plus b times the slope at the head.
  head : ∀ b x → f (b ∷ x) ≡ f (false ∷ x) xor (b ∧ slope)
  head false x = sym (xor-identityʳ (f (false ∷ x)))
  head true  x = trans (sym (xor-cancelˡ (f (false ∷ x)) (f (true ∷ x))))
    (cong (f (false ∷ x) xor_)
      (trans (xor-comm (f (false ∷ x)) (f (true ∷ x)))
        (trans (cong (λ t → f (true ∷ t) xor f (false ∷ x))
                     (sym (⊕-identityʳ x)))
               (aff-slope af (false ∷ x) (true ∷ 0ᵖ)))))

  value : ∀ x → f x ≡ c′ xor dotᵥ (slope ∷ s′) x
  value (b ∷ x) = trans (head b x)
    (trans (cong (_xor (b ∧ slope)) (eq′ x))
      (trans (xor-assoc c′ (dotᵥ s′ x) (b ∧ slope))
        (cong (c′ xor_) (trans (xor-comm (dotᵥ s′ x) (b ∧ slope))
                               (cong (_xor dotᵥ s′ x) (∧-comm b slope))))))
    where
    ∧-comm : ∀ a b → a ∧ b ≡ b ∧ a
    ∧-comm false false = refl
    ∧-comm false true  = refl
    ∧-comm true  false = refl
    ∧-comm true  true  = refl


------------------------------------------------------------------------
-- Setting and inserting a coordinate

-- x with coordinate i set to b; the unit vector at i.

set : Pt n → Fin n → Bool → Pt n
set (a ∷ x) zero    b = b ∷ x
set (a ∷ x) (suc i) b = a ∷ set x i b

unit : Fin n → Pt n
unit i = set 0ᵖ i true

lookup-set-here : (x : Pt n) (i : Fin n) (b : Bool) → lookup (set x i b) i ≡ b
lookup-set-here (a ∷ x) zero    b = refl
lookup-set-here (a ∷ x) (suc i) b = lookup-set-here x i b

lookup-set-there : (x : Pt n) {i j : Fin n} (b : Bool) → j ≢ i →
                   lookup (set x i b) j ≡ lookup x j
lookup-set-there (a ∷ x) {zero}  {zero}  b j≢i = ⊥-elim (j≢i refl)
lookup-set-there (a ∷ x) {zero}  {suc j} b j≢i = refl
lookup-set-there (a ∷ x) {suc i} {zero}  b j≢i = refl
lookup-set-there (a ∷ x) {suc i} {suc j} b j≢i =
  lookup-set-there x b (λ e → j≢i (cong suc e))

set-set : (x : Pt n) (i : Fin n) (b c : Bool) → set (set x i b) i c ≡ set x i c
set-set (a ∷ x) zero    b c = refl
set-set (a ∷ x) (suc i) b c = cong (a ∷_) (set-set x i b c)

set-lookup : (x : Pt n) (i : Fin n) → set x i (lookup x i) ≡ x
set-lookup (a ∷ x) zero    = refl
set-lookup (a ∷ x) (suc i) = cong (a ∷_) (set-lookup x i)

set-comm : (x : Pt n) {i j : Fin n} (b c : Bool) → i ≢ j →
           set (set x i b) j c ≡ set (set x j c) i b
set-comm (a ∷ x) {zero}  {zero}  b c i≢j = ⊥-elim (i≢j refl)
set-comm (a ∷ x) {zero}  {suc j} b c i≢j = refl
set-comm (a ∷ x) {suc i} {zero}  b c i≢j = refl
set-comm (a ∷ x) {suc i} {suc j} b c i≢j =
  cong (a ∷_) (set-comm x b c (λ e → i≢j (cong suc e)))

set-⊕ : (x y : Pt n) (i : Fin n) (a b : Bool) →
        set x i a ⊕ set y i b ≡ set (x ⊕ y) i (a xor b)
set-⊕ (c ∷ x) (d ∷ y) zero    a b = refl
set-⊕ (c ∷ x) (d ∷ y) (suc i) a b = cong ((c xor d) ∷_) (set-⊕ x y i a b)

set-0ᵖ : (i : Fin n) → set (0ᵖ {n}) i false ≡ 0ᵖ
set-0ᵖ zero    = refl
set-0ᵖ (suc i) = cong (false ∷_) (set-0ᵖ i)

-- Setting a coordinate to 1 is adding the unit vector to the point
-- with that coordinate 0.

set-unit : (x : Pt n) (i : Fin n) → set x i true ≡ set x i false ⊕ unit i
set-unit x i = sym (trans (set-⊕ x 0ᵖ i false true)
                          (cong (λ y → set y i true) (⊕-identityʳ x)))

insertAt-⊕ : (x y : Pt n) (j : Fin (suc n)) (a b : Bool) →
             insertAt x j a ⊕ insertAt y j b ≡ insertAt (x ⊕ y) j (a xor b)
insertAt-⊕ x       y       zero    a b = refl
insertAt-⊕ (c ∷ x) (d ∷ y) (suc j) a b = cong ((c xor d) ∷_)
  (insertAt-⊕ x y j a b)

insertAt-0ᵖ : (j : Fin (suc n)) → insertAt (0ᵖ {n}) j false ≡ 0ᵖ
insertAt-0ᵖ {n = n}     zero    = refl
insertAt-0ᵖ {n = suc n} (suc j) = cong (false ∷_) (insertAt-0ᵖ j)

-- The square of the identity vanishes.

sq-id : (x u w : Pt n) → ((x ⊕ (x ⊕ u)) ⊕ (x ⊕ w)) ⊕ ((x ⊕ u) ⊕ w) ≡ 0ᵖ
sq-id x u w = vext λ i → trans (lookup-sq x (x ⊕ u) (x ⊕ w) ((x ⊕ u) ⊕ w) i)
  (trans (d2 (Aff-lookup i) x u w) (sym (lookup-0ᵖ i)))

AffMap-id : AffMap {n} (λ x → x)
AffMap-id = affmap sq-id

-- Setting a coordinate to an affine function of the point, and
-- inserting a constant coordinate, are affine maps.

AffMap-set : {h : Pt n → Bool} → Aff h → (i : Fin n) →
             AffMap (λ x → set x i (h x))
AffMap-set {h = h} ah i = affmap λ x u w → trans
  (cong (_⊕ set ((x ⊕ u) ⊕ w) i (h ((x ⊕ u) ⊕ w)))
    (trans (cong (_⊕ set (x ⊕ w) i (h (x ⊕ w))) (set-⊕ x (x ⊕ u) i _ _))
           (set-⊕ (x ⊕ (x ⊕ u)) (x ⊕ w) i _ _)))
  (trans (set-⊕ ((x ⊕ (x ⊕ u)) ⊕ (x ⊕ w)) ((x ⊕ u) ⊕ w) i _ _)
    (trans (cong₂ (λ p b → set p i b) (sq-id x u w) (d2 ah x u w))
           (set-0ᵖ i)))

AffMap-insertAt : (j : Fin (suc n)) (b : Bool) →
                  AffMap (λ (x : Pt n) → insertAt x j b)
AffMap-insertAt j b = affmap λ x u w → trans
  (cong (_⊕ insertAt ((x ⊕ u) ⊕ w) j b)
    (trans (cong (_⊕ insertAt (x ⊕ w) j b) (insertAt-⊕ x (x ⊕ u) j b b))
           (insertAt-⊕ (x ⊕ (x ⊕ u)) (x ⊕ w) j _ b)))
  (trans (insertAt-⊕ ((x ⊕ (x ⊕ u)) ⊕ (x ⊕ w)) ((x ⊕ u) ⊕ w) j _ b)
    (trans (cong₂ (λ p c → insertAt p j c) (sq-id x u w) (bits b))
           (insertAt-0ᵖ j)))
  where
  bits : ∀ b → ((b xor b) xor b) xor b ≡ false
  bits false = refl
  bits true  = refl

-- An affine function changes by a constant when one coordinate flips.

κˢ : Fin n → (Pt n → Bool) → Bool
κˢ i e = e (unit i) xor e 0ᵖ

aff-flip : {e : Pt n → Bool} → Aff e → ∀ x i →
           e (set x i true) ≡ e (set x i false) xor κˢ i e
aff-flip {e = e} ae x i = bits (trans (cong (λ p → e p xor e (set x i false))
                                            (set-unit x i))
                                      (aff-slope ae (set x i false) (unit i)))
  where
  bits : ∀ {a b k} → a xor b ≡ k → a ≡ b xor k
  bits {false} {false} refl = refl
  bits {false} {true}  refl = refl
  bits {true}  {false} refl = refl
  bits {true}  {true}  refl = refl


------------------------------------------------------------------------
-- Affine from coordinate second differences

-- Functions of at most one coordinate are affine.

Aff-0 : (ℓ : Pt 0 → Bool) → Aff ℓ
Aff-0 ℓ = aff λ { [] [] [] → bits (ℓ []) }
  where
  bits : ∀ a → ((a xor a) xor a) xor a ≡ false
  bits false = refl
  bits true  = refl

Aff-1 : (ℓ : Pt 1 → Bool) → Aff ℓ
Aff-1 ℓ = Aff-cong value (Aff-dot (ℓ (false ∷ [])) (slope ∷ []))
  where
  slope : Bool
  slope = ℓ (true ∷ []) xor ℓ (false ∷ [])

  value : ∀ x → ℓ (false ∷ []) xor dotᵥ (slope ∷ []) x ≡ ℓ x
  value (false ∷ []) = trans (cong (ℓ (false ∷ []) xor_) (bits slope))
                             (xor-identityʳ (ℓ (false ∷ [])))
    where
    bits : ∀ s → (s ∧ false) xor false ≡ false
    bits false = refl
    bits true  = refl
  value (true ∷ []) = trans
    (cong (ℓ (false ∷ []) xor_) (xor-identityʳ (slope ∧ true)))
    (trans (cong (ℓ (false ∷ []) xor_) (∧-true slope))
      (trans
       (cong (ℓ (false ∷ []) xor_) (xor-comm (ℓ (true ∷ [])) (ℓ (false ∷ []))))
             (xor-cancelˡ (ℓ (false ∷ [])) (ℓ (true ∷ [])))))
    where
    ∧-true : ∀ s → s ∧ true ≡ s
    ∧-true false = refl
    ∧-true true  = refl

-- The coordinate second differences: at a pair of coordinates, the
-- second one numbered without the first, both inserted.

CSD : (Pt (suc (suc n)) → Bool) → Set
CSD {n} ℓ = ∀ (a : Fin (suc (suc n))) (b : Fin (suc n)) (z : Pt n) →
  ((ℓ (insertAt (insertAt z b true) a true) xor
    ℓ (insertAt (insertAt z b true) a false)) xor
   ℓ (insertAt (insertAt z b false) a true)) xor
  ℓ (insertAt (insertAt z b false) a false) ≡ false

-- A function that no coordinate flip changes is constant.

flip-const : (δ : Pt (suc n) → Bool) →
             (∀ b z → δ (insertAt z b true) ≡ δ (insertAt z b false)) →
             ∀ y → δ y ≡ δ 0ᵖ
flip-const {n = zero}  δ h (false ∷ []) = refl
flip-const {n = zero}  δ h (true  ∷ []) = h zero []
flip-const {n = suc n} δ h (c ∷ y) =
  trans (head c) (flip-const (λ z → δ (false ∷ z))
                             (λ b z → h (suc b) (false ∷ z)) y)
  where
  head : ∀ c → δ (c ∷ y) ≡ δ (false ∷ y)
  head false = refl
  head true  = h zero y

-- Vanishing coordinate second differences make a function affine: its
-- restriction to a 0 at the head is (by induction), and its slope at
-- the head does not depend on the other coordinates.

CSD-shape : (ℓ : Pt (suc (suc n)) → Bool) → CSD ℓ →
            Aff (λ z → ℓ (false ∷ z)) →
            Σ Bool (λ c → Σ (Pt (suc (suc n))) (λ s →
              ∀ x → c xor dotᵥ s x ≡ ℓ x))
CSD-shape {n} ℓ csd aff₀ = c₀ , (δ₀ ∷ s₀) , value
  where
  rec = aff-expand aff₀
  c₀  = proj₁ rec
  s₀  = proj₁ (proj₂ rec)
  eq₀ = proj₂ (proj₂ rec)

  δ : Pt (suc n) → Bool
  δ z = ℓ (true ∷ z) xor ℓ (false ∷ z)

  δ-flip : ∀ b z → δ (insertAt z b true) ≡ δ (insertAt z b false)
  δ-flip b z = bits {ℓ (true ∷ insertAt z b true)}
    {ℓ (false ∷ insertAt z b true)}
                    {ℓ (true ∷ insertAt z b false)}
                      {ℓ (false ∷ insertAt z b false)}
                    (csd zero b z)
    where
    bits : ∀ {p q r s} → ((p xor q) xor r) xor s ≡ false →
           p xor q ≡ r xor s
    bits {false} {false} {false} {false} _ = refl
    bits {false} {false} {true}  {true}  _ = refl
    bits {false} {true}  {false} {true}  _ = refl
    bits {false} {true}  {true}  {false} _ = refl
    bits {true}  {false} {false} {true}  _ = refl
    bits {true}  {false} {true}  {false} _ = refl
    bits {true}  {true}  {false} {false} _ = refl
    bits {true}  {true}  {true}  {true}  _ = refl

  δ₀ : Bool
  δ₀ = δ 0ᵖ

  ∧-false : ∀ s → s ∧ false ≡ false
  ∧-false false = refl
  ∧-false true  = refl

  ∧-true : ∀ s → s ∧ true ≡ s
  ∧-true false = refl
  ∧-true true  = refl

  value : ∀ x → c₀ xor dotᵥ (δ₀ ∷ s₀) x ≡ ℓ x
  value (false ∷ z) = trans (cong (λ t → c₀ xor (t xor dotᵥ s₀ z)) (∧-false δ₀))
                            (sym (eq₀ z))
  value (true ∷ z) = trans
    (cong (c₀ xor_) (cong (_xor dotᵥ s₀ z) (∧-true δ₀)))
    (trans (sym (xor-assoc c₀ δ₀ (dotᵥ s₀ z)))
      (trans (cong (_xor dotᵥ s₀ z) (xor-comm c₀ δ₀))
        (trans (xor-assoc δ₀ c₀ (dotᵥ s₀ z))
          (trans (cong (δ₀ xor_) (sym (eq₀ z)))
            (trans (cong (_xor ℓ (false ∷ z)) (sym (flip-const δ δ-flip z)))
              (trans (xor-assoc (ℓ (true ∷ z)) (ℓ (false ∷ z)) (ℓ (false ∷ z)))
                (trans (cong (ℓ (true ∷ z) xor_) (xor-same (ℓ (false ∷ z))))
                       (xor-identityʳ (ℓ (true ∷ z))))))))))

mutual
  CSD⇒Aff : (ℓ : Pt (suc (suc n)) → Bool) → CSD ℓ → Aff ℓ
  CSD⇒Aff {n} ℓ csd =
    Aff-cong (proj₂ (proj₂ shape)) (Aff-dot (proj₁ shape) (proj₁ (proj₂ shape)))
    where
    shape = CSD-shape ℓ csd (restrict-aff n ℓ csd)

  restrict-aff : (n : ℕ) (ℓ : Pt (suc (suc n)) → Bool) → CSD ℓ →
                 Aff (λ z → ℓ (false ∷ z))
  restrict-aff zero    ℓ csd = Aff-1 _
  restrict-aff (suc n) ℓ csd =
    CSD⇒Aff (λ z → ℓ (false ∷ z)) (λ a b z → csd (suc a) (suc b) (false ∷ z))


------------------------------------------------------------------------
-- Inserting, removing and moving coordinates

-- Setting an inserted coordinate is inserting the new value; setting
-- another coordinate commutes with the insertion.

set-insertAt : (z : Pt n) (v : Fin (suc n)) (a b : Bool) →
               set (insertAt z v a) v b ≡ insertAt z v b
set-insertAt z       zero    a b = refl
set-insertAt (c ∷ z) (suc v) a b = cong (c ∷_) (set-insertAt z v a b)

insertAt-set : (y : Pt n) (j : Fin (suc n)) (l : Fin n) (b c : Bool) →
               insertAt (set y l b) j c ≡ set (insertAt y j c) (punchIn j l) b
insertAt-set y       zero    l       b c = refl
insertAt-set (a ∷ y) (suc j) zero    b c = refl
insertAt-set (a ∷ y) (suc j) (suc l) b c = cong (a ∷_) (insertAt-set y j l b c)

-- Removing a coordinate is linear.

removeAt-⊕ : (x y : Pt (suc n)) (i : Fin (suc n)) →
             removeAt (x ⊕ y) i ≡ removeAt x i ⊕ removeAt y i
removeAt-⊕ (a ∷ x)     (b ∷ y)     zero    = refl
removeAt-⊕ (a ∷ c ∷ x) (b ∷ d ∷ y) (suc i) =
  cong ((a xor b) ∷_) (removeAt-⊕ (c ∷ x) (d ∷ y) i)

removeAt-0ᵖ : (i : Fin (suc n)) → removeAt (0ᵖ {suc n}) i ≡ 0ᵖ
removeAt-0ᵖ {n = n}     zero    = refl
removeAt-0ᵖ {n = suc n} (suc i) = cong (false ∷_) (removeAt-0ᵖ i)

-- A map that respects sums and keeps 0 is affine.

AffMap-linear : {φ : Pt n → Pt m} → (∀ x y → φ (x ⊕ y) ≡ φ x ⊕ φ y) →
                φ 0ᵖ ≡ 0ᵖ → AffMap φ
AffMap-linear {φ = φ} lin zero₀ = affmap λ x u w → trans
  (sym (trans (lin ((x ⊕ (x ⊕ u)) ⊕ (x ⊕ w)) ((x ⊕ u) ⊕ w))
         (cong (_⊕ φ ((x ⊕ u) ⊕ w))
           (trans (lin (x ⊕ (x ⊕ u)) (x ⊕ w))
                  (cong (_⊕ φ (x ⊕ w)) (lin x (x ⊕ u)))))))
  (trans (cong φ (sq-id x u w)) zero₀)

AffMap-removeAt : (i : Fin (suc n)) →
                  AffMap (λ (x : Pt (suc n)) → removeAt x i)
AffMap-removeAt i = AffMap-linear (λ x y → removeAt-⊕ x y i) (removeAt-0ᵖ i)

-- Every point is its coordinate v inserted into the others.

set-as-insertAt : (p : Pt (suc n)) (v : Fin (suc n)) (b : Bool) →
                  set p v b ≡ insertAt (removeAt p v) v b
set-as-insertAt (a ∷ p)     zero    b = refl
set-as-insertAt (a ∷ c ∷ p) (suc v) b =
  cong (a ∷_) (set-as-insertAt (c ∷ p) v b)

-- Moving the head coordinate to position j: the point a path-sum with
-- y_j renumbered to the front stands for.  Coordinate u of the moved
-- point is coordinate πᶠ j u of the original.

unfr : Fin (suc n) → Pt (suc n) → Pt (suc n)
unfr j (b ∷ y) = insertAt y j b

πᶠ : Fin (suc n) → Fin (suc n) → Fin (suc n)
πᶠ j zero    = j
πᶠ j (suc l) = punchIn j l

lookup-unfr : (j : Fin (suc n)) (p : Pt (suc n)) (u : Fin (suc n)) →
              lookup (unfr j p) (πᶠ j u) ≡ lookup p u
lookup-unfr j (b ∷ y) zero    = insertAt-lookup y j b
lookup-unfr j (b ∷ y) (suc l) = insertAt-punchIn y j b l

unfr-set : (j : Fin (suc n)) (p : Pt (suc n)) (u : Fin (suc n)) (b : Bool) →
           unfr j (set p u b) ≡ set (unfr j p) (πᶠ j u) b
unfr-set j (c ∷ y) zero    b = sym (set-insertAt y j c b)
unfr-set j (c ∷ y) (suc l) b = insertAt-set y j l b c

unfr-⊕ : (j : Fin (suc n)) (x y : Pt (suc n)) →
         unfr j (x ⊕ y) ≡ unfr j x ⊕ unfr j y
unfr-⊕ j (a ∷ x) (b ∷ y) = sym (insertAt-⊕ x y j a b)

AffMap-unfr : (j : Fin (suc n)) → AffMap (unfr j)
AffMap-unfr j = AffMap-linear (unfr-⊕ j) (insertAt-0ᵖ j)

-- Translation is affine.

AffMap-⊕const : {φ : Pt n → Pt m} → AffMap φ → (u : Pt m) →
                AffMap (λ x → φ x ⊕ u)
AffMap-⊕const {φ = φ} am u = affmap λ x a b → trans
  (⊕-assoc ((φ x ⊕ u) ⊕ (φ (x ⊕ a) ⊕ u)) (φ (x ⊕ b) ⊕ u)
           (φ ((x ⊕ a) ⊕ b) ⊕ u))
  (trans
   (cong₂ _⊕_ (pair (φ x) (φ (x ⊕ a))) (pair (φ (x ⊕ b)) (φ ((x ⊕ a) ⊕ b))))
    (trans (sym (⊕-assoc (φ x ⊕ φ (x ⊕ a)) (φ (x ⊕ b)) (φ ((x ⊕ a) ⊕ b))))
           (sq am x a b)))
  where
  pair : ∀ c d → (c ⊕ u) ⊕ (d ⊕ u) ≡ c ⊕ d
  pair c d = trans (⊕-medial c u d u)
    (trans (cong ((c ⊕ d) ⊕_) (⊕-self u)) (⊕-identityʳ (c ⊕ d)))

-- An affine map shifts by a constant when its argument does.

affmap-shift : {φ : Pt n → Pt m} → AffMap φ → ∀ x u →
               φ (x ⊕ u) ≡ φ x ⊕ (φ u ⊕ φ 0ᵖ)
affmap-shift {φ = φ} am x u = trans
  (cong φ (cong₂ _⊕_ (sym (⊕-identityˡ x)) refl))
  (trans (affmap-val am 0ᵖ x u)
    (trans (cong₂ (λ a b → (φ 0ᵖ ⊕ φ a) ⊕ φ b) (⊕-identityˡ x) (⊕-identityˡ u))
      (trans (cong (_⊕ φ u) (⊕-comm (φ 0ᵖ) (φ x)))
        (trans (⊕-assoc (φ x) (φ 0ᵖ) (φ u))
               (cong (φ x ⊕_) (⊕-comm (φ 0ᵖ) (φ u)))))))


------------------------------------------------------------------------
-- Derivatives along coordinates

-- The derivative of f in coordinate v, read at every point (it does
-- not depend on the point's own coordinate v); f is Clifford in v when
-- that derivative is affine, and independent of v when it vanishes.

∂ˢ : (Pt n → Bool) → Fin n → Pt n → Bool
∂ˢ f v p = f (set p v true) xor f (set p v false)

Cl : (Pt n → Bool) → Fin n → Set
Cl f v = Aff (∂ˢ f v)

Indep : (Pt n → Bool) → Fin n → Set
Indep f v = ∀ p → f (set p v true) ≡ f (set p v false)

-- An independent coordinate can be set to anything.

indep-any : {f : Pt n → Bool} {v : Fin n} → Indep f v →
            ∀ p b c → f (set p v b) ≡ f (set p v c)
indep-any h p false false = refl
indep-any h p false true  = sym (h p)
indep-any h p true  false = h p
indep-any h p true  true  = refl

indep-set : {f : Pt n → Bool} {v : Fin n} → Indep f v →
            ∀ p b → f (set p v b) ≡ f p
indep-set {f = f} {v} h p b =
  trans (indep-any {f = f} {v} h p b (lookup p v)) (cong f (set-lookup p v))

-- Adding the unit vector at v flips coordinate v ...

⊕-unit : (x : Pt n) (v : Fin n) → x ⊕ unit v ≡ set x v (not (lookup x v))
⊕-unit (a ∷ x) zero    = cong₂ _∷_ (xor-true a) (⊕-identityʳ x)
  where
  xor-true : ∀ a → a xor true ≡ not a
  xor-true false = refl
  xor-true true  = refl
⊕-unit (a ∷ x) (suc v) = cong₂ _∷_ (xor-identityʳ a) (⊕-unit x v)

-- ... so the derivative along it is the coordinate derivative.

∂-unit : (f : Pt n → Bool) (v : Fin n) (x : Pt n) → ∂ f (unit v) x ≡ ∂ˢ f v x
∂-unit f v x = go (lookup x v) refl
  where
  at : ∀ b → lookup x v ≡ b → x ≡ set x v b
  at b e = sym (trans (cong (set x v) (sym e)) (set-lookup x v))

  flip : ∀ b → lookup x v ≡ b → x ⊕ unit v ≡ set x v (not b)
  flip b e = trans (⊕-unit x v) (cong (λ c → set x v (not c)) e)

  go : ∀ b → lookup x v ≡ b → f x xor f (x ⊕ unit v) ≡ ∂ˢ f v x
  go false e = trans (cong₂ (λ p q → f p xor f q) (at false e) (flip false e))
                     (xor-comm (f (set x v false)) (f (set x v true)))
  go true  e = cong₂ (λ p q → f p xor f q) (at true e) (flip true e)

Cl⇒∂ : {f : Pt n → Bool} {v : Fin n} → Cl f v → Aff (∂ f (unit v))
Cl⇒∂ {f = f} {v} c = Aff-cong (λ x → sym (∂-unit f v x)) c

∂⇒Cl : {f : Pt n → Bool} {v : Fin n} → Aff (∂ f (unit v)) → Cl f v
∂⇒Cl {f = f} {v} a = Aff-cong (∂-unit f v) a

-- The derivative along a sum of two directions is affine when both
-- are.

∂-⊕ : (f : Pt n → Bool) (u w x : Pt n) →
      ∂ f (u ⊕ w) x ≡ ∂ f u x xor ∂ f w (x ⊕ u)
∂-⊕ f u w x = trans (cong (λ p → f x xor f p) (sym (⊕-assoc x u w)))
  (sym (trans (xor-assoc (f x) (f (x ⊕ u)) (f (x ⊕ u) xor f ((x ⊕ u) ⊕ w)))
              (cong (f x xor_) (xor-cancelˡ (f (x ⊕ u)) (f ((x ⊕ u) ⊕ w))))))

Aff-∂-⊕ : {f : Pt n → Bool} {u w : Pt n} → Aff (∂ f u) → Aff (∂ f w) →
          Aff (∂ f (u ⊕ w))
Aff-∂-⊕ {f = f} {u} {w} au aw = Aff-cong (λ x → sym (∂-⊕ f u w x))
  (Aff-xor au (Aff-∘ aw (AffMap-⊕const AffMap-id u)))

-- Through an affine map ψ, the derivative in v is the derivative along
-- the constant ψ (unit v) ⊕ ψ 0, read at ψ of the point with v cleared.

Cl-∘ : {f : Pt m → Bool} {ψ : Pt n → Pt m} → AffMap ψ → (v : Fin n) →
       Aff (∂ f (ψ (unit v) ⊕ ψ 0ᵖ)) → Cl (λ p → f (ψ p)) v
Cl-∘ {f = f} {ψ} am v a =
  Aff-cong eq (Aff-∘ a (AffMap-∘ am (AffMap-set (Aff-const false) v)))
  where
  eq : ∀ p → ∂ f (ψ (unit v) ⊕ ψ 0ᵖ) (ψ (set p v false)) ≡
             f (ψ (set p v true)) xor f (ψ (set p v false))
  eq p = trans (xor-comm (f (ψ (set p v false)))
                         (f (ψ (set p v false) ⊕ (ψ (unit v) ⊕ ψ 0ᵖ))))
    (cong (λ q → f q xor f (ψ (set p v false)))
          (sym (trans (cong ψ (set-unit p v))
                      (affmap-shift am (set p v false) (unit v)))))

-- Renumbering, clearing the head, and the substitution of an [HH]
-- (clear the head, set coordinate i to an affine q of the rest that
-- does not read i) keep coordinates Clifford and independent.  A
-- coordinate v that q reads moves together with i, so it stays
-- Clifford when i is Clifford too.

Cl-unfr : {f : Pt (suc n) → Bool} (j v : Fin (suc n)) →
          Cl f (πᶠ j v) → Cl (λ p → f (unfr j p)) v
Cl-unfr {f = f} j v c = Aff-cong
  (λ p → sym (cong₂ (λ a b → f a xor f b) (unfr-set j p v true)
                                          (unfr-set j p v false)))
  (Aff-∘ c (AffMap-unfr j))

Indep-unfr : {f : Pt (suc n) → Bool} (j v : Fin (suc n)) →
             Indep f (πᶠ j v) → Indep (λ p → f (unfr j p)) v
Indep-unfr {f = f} j v h p = trans (cong f (unfr-set j p v true))
  (trans (h (unfr j p)) (cong f (sym (unfr-set j p v false))))

Cl-tail : {f : Pt (suc n) → Bool} (v : Fin n) →
          Cl f (suc v) → Cl (λ p → f (false ∷ p)) v
Cl-tail v c = Aff-∘ c (AffMap-insertAt zero false)

Cl-hh-self : {f : Pt (suc n) → Bool} {q : Pt n → Bool} (i : Fin n) →
             Indep q i → Cl (λ p → f (false ∷ set p i (q p))) i
Cl-hh-self {f = f} {q} i hq = Aff-cong (λ p → sym (trans
  (cong₂ (λ a b → f (false ∷ a) xor f (false ∷ b))
         (trans (set-set p i true (q (set p i true)))
                (cong (set p i) (indep-set {f = q} {i} hq p true)))
         (trans (set-set p i false (q (set p i false)))
                (cong (set p i) (indep-set {f = q} {i} hq p false))))
  (xor-same (f (false ∷ set p i (q p))))))
  (Aff-const false)

Cl-hh : {f : Pt (suc n) → Bool} {q : Pt n → Bool} → Aff q →
        (i v : Fin n) → v ≢ i → Cl f (suc v) →
        (κˢ v q ≡ true → Cl f (suc i)) →
        Cl (λ p → f (false ∷ set p i (q p))) v
Cl-hh {n = n} {f = f} {q} aq i v v≢i cv ci =
  Cl-∘ {f = f} {ψ} am v (go (κˢ v q) refl)
  where
  ψ : Pt n → Pt (suc n)
  ψ p = false ∷ set p i (q p)

  am : AffMap ψ
  am = AffMap-∘ (AffMap-insertAt zero false) (AffMap-set aq i)

  Δ≡ : ψ (unit v) ⊕ ψ 0ᵖ ≡ false ∷ set (unit v) i (κˢ v q)
  Δ≡ = cong (false ∷_) (trans (set-⊕ (unit v) 0ᵖ i (q (unit v)) (q 0ᵖ))
                              (cong (λ t → set t i (κˢ v q))
                               (⊕-identityʳ (unit v))))

  unit-off : set (unit v) i false ≡ unit v
  unit-off = trans (set-comm 0ᵖ true false (λ e → v≢i e))
                   (cong (λ t → set t v true) (set-0ᵖ i))

  go : ∀ b → κˢ v q ≡ b → Aff (∂ f (ψ (unit v) ⊕ ψ 0ᵖ))
  go false e = subst (λ d → Aff (∂ f d))
    (sym
     (trans Δ≡ (cong (false ∷_) (trans (cong (set (unit v) i) e) unit-off))))
    (Cl⇒∂ {f = f} {suc v} cv)
  go true  e = subst (λ d → Aff (∂ f d))
    (sym (trans Δ≡ (cong (false ∷_)
      (trans (cong (set (unit v) i) e)
        (trans (set-unit (unit v) i) (cong (_⊕ unit i) unit-off))))))
    (Aff-∂-⊕ {f = f} {unit (suc v)} {unit (suc i)} (Cl⇒∂ {f = f} {suc v} cv)
     (Cl⇒∂ {f = f} {suc i} (ci e)))

Indep-tail : {f : Pt (suc n) → Bool} (v : Fin n) →
             Indep f (suc v) → Indep (λ p → f (false ∷ p)) v
Indep-tail v h p = h (false ∷ p)

Indep-hh-self : {f : Pt (suc n) → Bool} {q : Pt n → Bool} (i : Fin n) →
                Indep q i → Indep (λ p → f (false ∷ set p i (q p))) i
Indep-hh-self {f = f} {q} i hq p = cong (λ a → f (false ∷ a))
  (trans (trans (set-set p i true (q (set p i true)))
                (cong (set p i) (indep-set {f = q} {i} hq p true)))
         (sym (trans (set-set p i false (q (set p i false)))
                     (cong (set p i) (indep-set {f = q} {i} hq p false)))))

Indep-hh-off : {f : Pt (suc n) → Bool} {q : Pt n → Bool} (i v : Fin n) →
               v ≢ i → Indep q v → Indep f (suc v) →
               Indep (λ p → f (false ∷ set p i (q p))) v
Indep-hh-off {f = f} {q} i v v≢i hq hf p = trans (at true) (trans
  (hf (false ∷ set p i (q p))) (sym (at false)))
  where
  at : ∀ b → f (false ∷ set (set p v b) i (q (set p v b))) ≡
             f (false ∷ set (set p i (q p)) v b)
  at b = cong (λ a → f (false ∷ a))
    (trans (cong (set (set p v b) i) (indep-set {f = q} {v} hq p b))
           (set-comm p b (q p) v≢i))

Indep-hh-out : {f : Pt (suc n) → Bool} {q : Pt n → Bool} (i v : Fin n) →
               Indep f (suc i) → Indep f (suc v) →
               Indep (λ p → f (false ∷ set p i (q p))) v
Indep-hh-out {f = f} {q} i v hi hv p = trans
  (indep-set {f = f} {v = suc i} hi (false ∷ set p v true) (q (set p v true)))
  (trans (hv (false ∷ p))
    (sym (indep-set {f = f} {v = suc i} hi (false ∷ set p v false)
                    (q (set p v false)))))

-- An inner product with one coordinate of the left vector split off.

dotᵥ-set : (s x : Pt n) (i : Fin n) →
           dotᵥ s x ≡ dotᵥ (set s i false) x xor (lookup s i ∧ lookup x i)
dotᵥ-set (a ∷ s) (b ∷ x) zero    = xor-comm (a ∧ b) (dotᵥ s x)
dotᵥ-set (a ∷ s) (b ∷ x) (suc i) = trans (cong ((a ∧ b) xor_) (dotᵥ-set s x i))
  (sym (xor-assoc (a ∧ b) (dotᵥ (set s i false) x) (lookup s i ∧ lookup x i)))

dotᵥ-null : (s x : Pt n) → (∀ i → lookup s i ≡ false) → dotᵥ s x ≡ false
dotᵥ-null []      []      h = refl
dotᵥ-null (a ∷ s) (b ∷ x) h =
  trans (cong (λ t → (t ∧ b) xor dotᵥ s x) (h zero))
        (dotᵥ-null s x (λ i → h (suc i)))
