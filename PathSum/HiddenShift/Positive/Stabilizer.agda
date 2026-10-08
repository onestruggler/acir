------------------------------------------------------------------------
-- Presentations of groups
--
-- Stabilizer-like functions and their partial sums
--
-- Summing (-1)^F(x) over some of the coordinates of x is how a path-sum
-- with phase ½F loses path variables: [HH] and [Elim] are such sums,
-- carried out symbolically.  PathSum.HiddenShift.Positive's invariant
-- is that one particular partial sum of (-1)^F has the shape of a
-- stabilizer amplitude:
--
--   2^d · A(x) = c · [e₁(x) = 0, …, e_r(x) = 0] · (-1)^R(x)
--
-- with every e_t affine and R quadratic (PathSum.HiddenShift.Positive.
-- Boolean) -- a quadratic phase on an affine subspace, up to a scalar
-- (SL).  The power of 2 on the left makes halving free (SL-half).
--
-- The facts used: SL is closed under composition with affine maps
-- (SL-∘) and under summing over one more coordinate (SL-σ), the
-- Gaussian elimination of stabilizer theory.  If some equation e
-- involves the coordinate i, exactly one value of x_i satisfies it and
-- substituting that value keeps everything affine and quadratic;
-- otherwise the sum of (-1)^R over x_i is twice an indicator of the
-- affine function R(x_i = 1) ⊕ R(x_i = 0), which joins the equations.
--
-- The partial sums are over a set T of coordinates, given as a
-- predicate (Σ[ T ]), defined by recursion on the head coordinate; the
-- lemmas move one coordinate in or out of the sum (Σ-pull, Σ-comm) and
-- read a sum at a point with one coordinate inserted (Σ-ins-in,
-- Σ-ins-out), which is how a reduct's sums relate to its path-sum's.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.HiddenShift.Positive.Stabilizer where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-identityʳ; xor-comm)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Fin.Properties using (_≟_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using (pos-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_^_ to _ℕ^_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; insertAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)

import Data.Nat.Properties as ℕ

open import PathSum.HiddenShift.Positive.Boolean
open import PathSum.Polynomial using (sgn)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Signs

sgn-xor : ∀ a b → sgn (a xor b) ≡ sgn a * sgn b
sgn-xor false false = refl
sgn-xor false true  = refl
sgn-xor true  false = refl
sgn-xor true  true  = refl

-- The indicator of b = 0.

zero? : Bool → ℤ
zero? false = 1ℤ
zero? true  = 0ℤ

-- 1 + (-1)^b is twice the indicator of b = 0.

1+sgn : ∀ b → 1ℤ + sgn b ≡ (+ 2) * zero? b
1+sgn false = refl
1+sgn true  = refl


------------------------------------------------------------------------
-- Stabilizer-like functions

-- The sum over coordinate i.

σ : Fin n → (Pt n → ℤ) → Pt n → ℤ
σ i f x = f (set x i false) + f (set x i true)

-- The indicator that every equation holds.

ind : List (Pt n → Bool) → Pt n → ℤ
ind []       x = 1ℤ
ind (e ∷ es) x = zero? (e x) * ind es x

Form : ℤ → List (Pt n → Bool) → (Pt n → Bool) → Pt n → ℤ
Form c es R x = c * (ind es x * sgn (R x))

record SL (A : Pt n → ℤ) : Set where
  constructor sl
  field
    d     : ℕ
    c     : ℤ
    es    : List (Pt n → Bool)
    R     : Pt n → Bool
    affs  : All Aff es
    quadR : Quad R
    form  : ∀ x → (+ (2 ℕ^ d)) * A x ≡ Form c es R x

open SL public

-- Equal values, equal shape.

SL-cong : {A B : Pt n → ℤ} → (∀ x → A x ≡ B x) → SL A → SL B
SL-cong h (sl d c es R a q f) =
  sl d c es R a q (λ x → trans (cong ((+ (2 ℕ^ d)) *_) (sym (h x))) (f x))


------------------------------------------------------------------------
-- Composition with an affine map

private
  ind-map : (es : List (Pt m → Bool)) (φ : Pt n → Pt m) (x : Pt n) →
            ind (map (λ e y → e (φ y)) es) x ≡ ind es (φ x)
  ind-map []       φ x = refl
  ind-map (e ∷ es) φ x = cong (zero? (e (φ x)) *_) (ind-map es φ x)

  All-map : {es : List (Pt m → Bool)} {φ : Pt n → Pt m} → AffMap φ →
            All Aff es → All Aff (map (λ e y → e (φ y)) es)
  All-map am []       = []
  All-map am (a ∷ as) = Aff-∘ a am ∷ All-map am as

SL-∘ : {A : Pt m → ℤ} {φ : Pt n → Pt m} → SL A → AffMap φ →
       SL (λ y → A (φ y))
SL-∘ {φ = φ} (sl d c es R a q f) am =
  sl d c (map (λ e y → e (φ y)) es) (λ y → R (φ y))
     (All-map am a) (Quad-∘ q am)
     (λ y → trans (f (φ y))
                  (cong (λ t → c * (t * sgn (R (φ y)))) (sym (ind-map es φ y))))


------------------------------------------------------------------------
-- Halving

SL-half : {A : Pt n → ℤ} → SL (λ x → A x + A x) → SL A
SL-half {A = A} (sl d c es R a q f) = sl (suc d) c es R a q λ x →
  trans (shape d (A x)) (f x)
  where
  shape : ∀ k t → (+ (2 ℕ^ suc k)) * t ≡ (+ (2 ℕ^ k)) * (t + t)
  shape k t = trans (cong (_* t) (trans (cong +_ (ℕ.*-comm 2 (2 ℕ^ k)))
                                        (pos-* (2 ℕ^ k) 2)))
    (solve 2 (λ p t → (p :* con (+ 2)) :* t := p :* (t :+ t)) refl
       (+ (2 ℕ^ k)) t)


------------------------------------------------------------------------
-- Summing over one more coordinate

private
  ind-same : {es : List (Pt n → Bool)} (i : Fin n) → All Aff es →
             All (λ e → κˢ i e ≡ false) es →
             ∀ x → ind es (set x i true) ≡ ind es (set x i false)
  ind-same i []       []       x = refl
  ind-same {es = e ∷ es} i (a ∷ as) (k ∷ ks) x = cong₂ _*_
    (cong zero? (trans (aff-flip a x i)
                       (trans (cong (e (set x i false) xor_) k)
                              (xor-identityʳ (e (set x i false))))))
    (ind-same i as ks x)

  ind-pivot : (pre : List (Pt n → Bool)) (e : Pt n → Bool)
              (post : List (Pt n → Bool)) (x : Pt n) →
              ind (pre ++ e ∷ post) x ≡ zero? (e x) * ind (pre ++ post) x
  ind-pivot []         e post x = refl
  ind-pivot (e′ ∷ pre) e post x = trans
    (cong (zero? (e′ x) *_) (ind-pivot pre e post x))
    (solve 3 (λ a b t → a :* (b :* t) := b :* (a :* t)) refl
           (zero? (e′ x)) (zero? (e x)) (ind (pre ++ post) x))

  All-pick : ∀ {P : (Pt n → Bool) → Set} (pre : List (Pt n → Bool)) {e}
             (post : List (Pt n → Bool)) →
             All P (pre ++ e ∷ post) → P e × All P (pre ++ post)
  All-pick []         post (p ∷ ps) = p , ps
  All-pick (e′ ∷ pre) post (p ∷ ps) =
    proj₁ (All-pick pre post ps) , p ∷ proj₂ (All-pick pre post ps)

  zero-set : (i : Fin n) → AffMap (λ (y : Pt n) → set y i false)
  zero-set i = AffMap-set (Aff-const false) i

-- Whether some equation involves coordinate i.

data Pivot (i : Fin n) : List (Pt n → Bool) → Set where
  none : ∀ {es} → All (λ e → κˢ i e ≡ false) es → Pivot i es
  some : ∀ pre e post → κˢ i e ≡ true → Pivot i (pre ++ e ∷ post)

pivot? : (i : Fin n) (es : List (Pt n → Bool)) → Pivot i es
pivot? i []       = none []
pivot? i (e ∷ es) = go (κˢ i e) refl (pivot? i es)
  where
  go : ∀ {es} b → κˢ i e ≡ b → Pivot i es → Pivot i (e ∷ es)
  go true  k _                     = some [] e _ k
  go false k (none ks)             = none (k ∷ ks)
  go false k (some pre e′ post k′) = some (e ∷ pre) e′ post k′

private
  -- No equation involves i: the sum over x_i of (-1)^R is twice the
  -- indicator of the affine function R(x_i = 1) ⊕ R(x_i = 0).
  σ-none : (i : Fin n) {A : Pt n → ℤ} (d : ℕ) (c : ℤ)
           {es : List (Pt n → Bool)} (R : Pt n → Bool) →
           All Aff es → Quad R →
           (∀ x → (+ (2 ℕ^ d)) * A x ≡ Form c es R x) →
           All (λ e → κˢ i e ≡ false) es → SL (σ i A)
  σ-none i {A} d c {es} R a q f ks =
    sl d ((+ 2) * c) (ℓ ∷ map (λ e y → e (set y i false)) es)
       (λ y → R (set y i false))
       (aff-ℓ ∷ All-map (zero-set i) a) (Quad-∘ q (zero-set i)) value
    where
    ℓ : Pt _ → Bool
    ℓ y = R (set y i true) xor R (set y i false)

    aff-ℓ : Aff ℓ
    aff-ℓ = Aff-cong
      (λ y → trans (xor-comm (R (set y i false)) (R (set y i false ⊕ unit i)))
                   (cong (λ p → R p xor R (set y i false))
                    (sym (set-unit y i))))
      (Aff-∘ (Quad⇒Aff-∂ q (unit i)) (zero-set i))

    flip : ∀ x → sgn (R (set x i true)) ≡ sgn (R (set x i false)) * sgn (ℓ x)
    flip x = trans (cong sgn (bits (R (set x i true)) (R (set x i false))))
                   (sgn-xor (R (set x i false)) (ℓ x))
      where
      bits : ∀ a b → a ≡ b xor (a xor b)
      bits false false = refl
      bits false true  = refl
      bits true  false = refl
      bits true  true  = refl

    value : ∀ x → (+ (2 ℕ^ d)) * σ i A x ≡
                  Form ((+ 2) * c) (ℓ ∷ map (λ e y → e (set y i false)) es)
                       (λ y → R (set y i false)) x
    value x = trans (solve 3 (λ p a b → p :* (a :+ b) := p :* a :+ p :* b)
                             refl (+ (2 ℕ^ d)) (A (set x i false))
                             (A (set x i true)))
      (trans (cong₂ _+_ (f (set x i false)) (f (set x i true)))
        (trans
         (cong (λ t → c * (ind es (set x i false) * sgn (R (set x i false)))
                            + c * t)
                     (cong₂ _*_ (ind-same i a ks x) (flip x)))
          (trans (solve 4 (λ c I s t → c :* (I :* s) :+ c :* (I :* (s :* t)) :=
                                       c :* I :* s :* (con 1ℤ :+ t)) refl
                        c (ind es (set x i false)) (sgn (R (set x i false)))
                        (sgn (ℓ x)))
            (trans (cong (λ t → c * ind es (set x i false) *
                                sgn (R (set x i false)) * t) (1+sgn (ℓ x)))
              (trans (solve 5 (λ c I s two z → c :* I :* s :* (two :* z) :=
                                   (two :* c) :* ((z :* I) :* s)) refl
                            c (ind es (set x i false)) (sgn (R (set x i false)))
                            (+ 2) (zero? (ℓ x)))
                     (cong (λ t → ((+ 2) * c) * ((zero? (ℓ x) * t) *
                                                 sgn (R (set x i false))))
                           (sym (ind-map es (λ y → set y i false) x))))))))

  -- Some equation e involves i: exactly one value of x_i solves it,
  -- and substituting that value keeps the shape.
  σ-some : (i : Fin n) {A : Pt n → ℤ} (d : ℕ) (c : ℤ)
           (pre : List (Pt n → Bool)) (e : Pt n → Bool)
           (post : List (Pt n → Bool)) (R : Pt n → Bool) →
           All Aff (pre ++ e ∷ post) → Quad R →
           (∀ x → (+ (2 ℕ^ d)) * A x ≡ Form c (pre ++ e ∷ post) R x) →
           κˢ i e ≡ true → SL (σ i A)
  σ-some i {A} d c pre e post R a q f k =
    sl d c (map (λ e′ y → e′ (sub y)) (pre ++ post)) (λ y → R (sub y))
       (All-map am (proj₂ picked)) (Quad-∘ q am) value
    where
    picked = All-pick pre post a
    ae : Aff e
    ae = proj₁ picked

    sub : Pt _ → Pt _
    sub y = set y i (e (set y i false))

    am : AffMap sub
    am = AffMap-set (Aff-∘ ae (zero-set i)) i

    J : Pt _ → ℤ
    J = ind (pre ++ post)

    other : ∀ x → e (set x i true) ≡ e (set x i false) xor true
    other x = trans (aff-flip ae x i) (cong (e (set x i false) xor_) k)

    at : ∀ x b → e (set x i false) ≡ b →
         (+ (2 ℕ^ d)) * σ i A x ≡ c * (J (set x i b) * sgn (R (set x i b)))
    at x false eb = trans (solve 3 (λ p a b → p :* (a :+ b) := p :* a :+ p :* b)
                                   refl (+ (2 ℕ^ d)) (A (set x i false))
                                   (A (set x i true)))
      (trans (cong₂ _+_ (f (set x i false)) (f (set x i true)))
        (trans (cong₂ (λ s t → c * (s * sgn (R (set x i false))) +
                               c * (t * sgn (R (set x i true))))
                      (trans (ind-pivot pre e post (set x i false))
                             (cong (λ b → zero? b * J (set x i false)) eb))
                      (trans (ind-pivot pre e post (set x i true))
                             (cong (λ b → zero? b * J (set x i true))
                                   (trans (other x) (cong (_xor true) eb)))))
          (solve 4 (λ c J₀ s₀ r → c :* ((con 1ℤ :* J₀) :* s₀) :+
                                  c :* ((con 0ℤ :* r)) := c :* (J₀ :* s₀))
                 refl c (J (set x i false)) (sgn (R (set x i false)))
                 (J (set x i true) * sgn (R (set x i true))))))
    at x true eb = trans (solve 3 (λ p a b → p :* (a :+ b) := p :* a :+ p :* b)
                                  refl (+ (2 ℕ^ d)) (A (set x i false))
                                  (A (set x i true)))
      (trans (cong₂ _+_ (f (set x i false)) (f (set x i true)))
        (trans (cong₂ (λ s t → c * (s * sgn (R (set x i false))) +
                               c * (t * sgn (R (set x i true))))
                      (trans (ind-pivot pre e post (set x i false))
                             (cong (λ b → zero? b * J (set x i false)) eb))
                      (trans (ind-pivot pre e post (set x i true))
                             (cong (λ b → zero? b * J (set x i true))
                                   (trans (other x) (cong (_xor true) eb)))))
          (solve 4 (λ c r J₁ s₁ → c :* ((con 0ℤ :* r)) :+
                                  c :* ((con 1ℤ :* J₁) :* s₁) := c :*
                                    (J₁ :* s₁))
                 refl c (J (set x i false) * sgn (R (set x i false)))
                 (J (set x i true)) (sgn (R (set x i true))))))

    value : ∀ x → (+ (2 ℕ^ d)) * σ i A x ≡
                  Form c (map (λ e′ y → e′ (sub y)) (pre ++ post))
                       (λ y → R (sub y)) x
    value x = trans (at x (e (set x i false)) refl)
      (cong (λ t → c * (t * sgn (R (sub x))))
            (sym (ind-map (pre ++ post) sub x)))

  σ-by : (i : Fin n) {A : Pt n → ℤ} (d : ℕ) (c : ℤ)
         {es : List (Pt n → Bool)} (R : Pt n → Bool) →
         All Aff es → Quad R →
         (∀ x → (+ (2 ℕ^ d)) * A x ≡ Form c es R x) →
         Pivot i es → SL (σ i A)
  σ-by i d c R a q f (none ks)           = σ-none i d c R a q f ks
  σ-by i d c R a q f (some pre e post k) = σ-some i d c pre e post R a q f k

SL-σ : {A : Pt n → ℤ} (i : Fin n) → SL A → SL (σ i A)
SL-σ i (sl d c es R a q f) = σ-by i d c R a q f (pivot? i es)


------------------------------------------------------------------------
-- Sums over a set of coordinates

-- Σ[ T ] f x sums f over the coordinates in T, the others read off x.

mutual
  Σ[_] : (Fin n → Bool) → (Pt n → ℤ) → Pt n → ℤ
  Σ[_] {zero}  T f []      = f []
  Σ[_] {suc n} T f (b ∷ x) = Σstep (T zero) (λ i → T (suc i)) f b x

  Σstep : Bool → (Fin n → Bool) → (Pt (suc n) → ℤ) → Bool → Pt n → ℤ
  Σstep true  T f b x = Σ[ T ] (λ y → f (false ∷ y) + f (true ∷ y)) x
  Σstep false T f b x = Σ[ T ] (λ y → f (b ∷ y)) x

-- A set with one coordinate changed.

setᵀ : (Fin n → Bool) → Fin n → Bool → Fin n → Bool
setᵀ T zero    b zero    = b
setᵀ T zero    b (suc j) = T (suc j)
setᵀ T (suc i) b zero    = T zero
setᵀ T (suc i) b (suc j) = setᵀ (λ k → T (suc k)) i b j

setᵀ-here : (T : Fin n → Bool) (i : Fin n) (b : Bool) → setᵀ T i b i ≡ b
setᵀ-here T zero    b = refl
setᵀ-here T (suc i) b = setᵀ-here (λ k → T (suc k)) i b

setᵀ-there : (T : Fin n → Bool) {i j : Fin n} (b : Bool) → j ≢ i →
             setᵀ T i b j ≡ T j
setᵀ-there T {zero}  {zero}  b j≢i = ⊥-elim (j≢i refl)
setᵀ-there T {zero}  {suc j} b j≢i = refl
setᵀ-there T {suc i} {zero}  b j≢i = refl
setᵀ-there T {suc i} {suc j} b j≢i =
  setᵀ-there (λ k → T (suc k)) b (λ e → j≢i (cong suc e))

-- Congruence, in the summand and in the set.

Σ-cong : (T : Fin n → Bool) {f g : Pt n → ℤ} → (∀ y → f y ≡ g y) →
         ∀ x → Σ[ T ] f x ≡ Σ[ T ] g x
Σ-cong {zero}  T h []      = h []
Σ-cong {suc n} T h (b ∷ x) = go (T zero)
  where
  go : ∀ t → Σstep t (λ i → T (suc i)) _ b x ≡ Σstep t (λ i → T (suc i)) _ b x
  go true  = Σ-cong (λ i → T (suc i))
                    (λ y → cong₂ _+_ (h (false ∷ y)) (h (true ∷ y))) x
  go false = Σ-cong (λ i → T (suc i)) (λ y → h (b ∷ y)) x

Σ-congᵀ : {T T′ : Fin n → Bool} → (∀ i → T i ≡ T′ i) →
          ∀ (f : Pt n → ℤ) x → Σ[ T ] f x ≡ Σ[ T′ ] f x
Σ-congᵀ {zero}  h f []      = refl
Σ-congᵀ {suc n} {T} {T′} h f (b ∷ x) =
  trans (cong (λ t → Σstep t (λ i → T (suc i)) f b x) (h zero))
        (go (T′ zero))
  where
  go : ∀ t → Σstep t (λ i → T (suc i)) f b x ≡ Σstep t (λ i → T′ (suc i)) f b x
  go true  = Σ-congᵀ (λ i → h (suc i)) _ x
  go false = Σ-congᵀ (λ i → h (suc i)) _ x

-- Sums add.

Σ-+ : (T : Fin n → Bool) (f g : Pt n → ℤ) →
      ∀ x → Σ[ T ] (λ y → f y + g y) x ≡ Σ[ T ] f x + Σ[ T ] g x
Σ-+ {zero}  T f g []      = refl
Σ-+ {suc n} T f g (b ∷ x) = go (T zero)
  where
  T′ = λ i → T (suc i)
  go : ∀ t → Σstep t T′ (λ y → f y + g y) b x ≡
             Σstep t T′ f b x + Σstep t T′ g b x
  go true  = trans (Σ-cong T′ (λ y → solve 4 (λ a b c d →
                     (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl
                     (f (false ∷ y)) (g (false ∷ y)) (f (true ∷ y))
                     (g (true ∷ y))) x)
                   (Σ-+ T′ (λ y → f (false ∷ y) + f (true ∷ y))
                           (λ y → g (false ∷ y) + g (true ∷ y)) x)
  go false = Σ-+ T′ (λ y → f (b ∷ y)) (λ y → g (b ∷ y)) x

-- The sum over coordinate i commutes with the head coordinate.

private
  σ-+ : (i : Fin n) (f g : Pt n → ℤ) → ∀ y →
        σ i (λ z → f z + g z) y ≡ σ i f y + σ i g y
  σ-+ i f g y = solve 4
    (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d))
                        refl (f (set y i false)) (g (set y i false))
                        (f (set y i true)) (g (set y i true))

-- A coordinate in the set can be summed first ...

Σ-pull : (T : Fin n → Bool) (i : Fin n) → T i ≡ true →
         ∀ (f : Pt n → ℤ) x → Σ[ T ] f x ≡ Σ[ setᵀ T i false ] (σ i f) x
Σ-pull {suc n} T zero    Ti f (b ∷ x) =
  trans (cong (λ t → Σstep t (λ k → T (suc k)) f b x) Ti) refl
Σ-pull {suc n} T (suc i) Ti f (b ∷ x) = go (T zero)
  where
  T′ = λ k → T (suc k)
  go : ∀ t → Σstep t T′ f b x ≡ Σstep t (setᵀ T′ i false) (σ (suc i) f) b x
  go true  = trans (Σ-pull T′ i Ti (λ y → f (false ∷ y) + f (true ∷ y)) x)
    (Σ-cong (setᵀ T′ i false)
            (λ y → σ-+ i (λ z → f (false ∷ z)) (λ z → f (true ∷ z)) y) x)
  go false = Σ-pull T′ i Ti (λ y → f (b ∷ y)) x

-- ... and a coordinate outside it commutes with the sum.

Σ-comm : (T : Fin n → Bool) (i : Fin n) → T i ≡ false →
         ∀ (f : Pt n → ℤ) x → Σ[ T ] (σ i f) x ≡ σ i (Σ[ T ] f) x
Σ-comm {suc n} T zero    Ti f (b ∷ x) =
  trans (cong (λ t → Σstep t (λ k → T (suc k)) (σ zero f) b x) Ti)
    (trans (Σ-+ (λ k → T (suc k)) (λ y → f (false ∷ y)) (λ y → f (true ∷ y)) x)
           (sym (cong₂ _+_ (cong (λ t → Σstep t (λ k → T (suc k)) f false x) Ti)
                           (cong
                            (λ t → Σstep t (λ k → T (suc k)) f true x) Ti))))
Σ-comm {suc n} T (suc i) Ti f (b ∷ x) = go (T zero)
  where
  T′ = λ k → T (suc k)
  go : ∀ t → Σstep t T′ (σ (suc i) f) b x ≡
             Σstep t T′ f b (set x i false) + Σstep t T′ f b (set x i true)
  go true  = trans
    (Σ-cong T′
     (λ y → sym (σ-+ i (λ z → f (false ∷ z)) (λ z → f (true ∷ z)) y)) x)
    (Σ-comm T′ i Ti (λ y → f (false ∷ y) + f (true ∷ y)) x)
  go false = Σ-comm T′ i Ti (λ y → f (b ∷ y)) x

-- Reading a sum at a point with coordinate j inserted: outside the
-- set, j keeps the inserted value; inside, it is summed.

Σ-ins-out : (T : Fin (suc n) → Bool) (j : Fin (suc n)) → T j ≡ false →
            ∀ (f : Pt (suc n) → ℤ) (b : Bool) y →
            Σ[ T ] f (insertAt y j b) ≡
            Σ[ (λ k → T (punchIn j k)) ] (λ z → f (insertAt z j b)) y
Σ-ins-out T zero Tj f b y =
  cong (λ t → Σstep t (λ k → T (suc k)) f b y) Tj
Σ-ins-out {suc n} T (suc j) Tj f b (c ∷ y) = go (T zero)
  where
  T′ = λ k → T (suc k)
  go : ∀ t → Σstep t T′ f c (insertAt y j b) ≡
             Σstep t (λ k → T (punchIn (suc j) (suc k)))
                   (λ z → f (insertAt z (suc j) b)) c y
  go true  = Σ-ins-out T′ j Tj (λ z → f (false ∷ z) + f (true ∷ z)) b y
  go false = Σ-ins-out T′ j Tj (λ z → f (c ∷ z)) b y

Σ-ins-in : (T : Fin (suc n) → Bool) (j : Fin (suc n)) → T j ≡ true →
           ∀ (f : Pt (suc n) → ℤ) (b : Bool) y →
           Σ[ T ] f (insertAt y j b) ≡
           Σ[ (λ k → T (punchIn j k)) ]
             (λ z → f (insertAt z j false) + f (insertAt z j true)) y
Σ-ins-in T zero Tj f b y =
  cong (λ t → Σstep t (λ k → T (suc k)) f b y) Tj
Σ-ins-in {suc n} T (suc j) Tj f b (c ∷ y) = go (T zero)
  where
  T′ = λ k → T (suc k)
  go : ∀ t → Σstep t T′ f c (insertAt y j b) ≡
             Σstep t (λ k → T (punchIn (suc j) (suc k)))
                   (λ z → f (insertAt z (suc j) false) + f
                    (insertAt z (suc j) true))
                   c y
  go true  = trans (Σ-ins-in T′ j Tj (λ z → f (false ∷ z) + f (true ∷ z)) b y)
    (Σ-cong (λ k → T′ (punchIn j k))
            (λ z → solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) :=
                                        (a :+ c) :+ (b :+ d)) refl
                   (f (false ∷ insertAt z j false))
                     (f (true ∷ insertAt z j false))
                   (f (false ∷ insertAt z j true))
                     (f (true ∷ insertAt z j true)))
            y)
  go false = Σ-ins-in T′ j Tj (λ z → f (c ∷ z)) b y

-- Summing over a coordinate a function does not read doubles it.

σ-indep : (i : Fin n) (f : Pt n → ℤ) → (∀ y b → f (set y i b) ≡ f y) →
          ∀ y → σ i f y ≡ f y + f y
σ-indep i f h y = cong₂ _+_ (h y false) (h y true)


------------------------------------------------------------------------
-- The empty set, a larger set, and renumbering

-- Over the empty set the sum is the summand.

Σ-none : (T : Fin n → Bool) → (∀ i → T i ≡ false) →
         ∀ (f : Pt n → ℤ) x → Σ[ T ] f x ≡ f x
Σ-none {zero}  T h f []      = refl
Σ-none {suc n} T h f (b ∷ x) =
  trans (cong (λ t → Σstep t (λ i → T (suc i)) f b x) (h zero))
        (Σ-none (λ i → T (suc i)) (λ i → h (suc i)) (λ y → f (b ∷ y)) x)

-- A set agreeing with T off j, and with b at j, is setᵀ T j b.

setᵀ-agree : (T T′ : Fin n → Bool) (j : Fin n) (b : Bool) → T′ j ≡ b →
             (∀ l → l ≢ j → T′ l ≡ T l) → ∀ l → setᵀ T j b l ≡ T′ l
setᵀ-agree T T′ j b e h l with l ≟ j
... | yes refl = trans (setᵀ-here T j b) (sym e)
... | no  l≢j  = trans (setᵀ-there T b l≢j) (sym (h l l≢j))

-- Summing over one more coordinate is summing the sum over it ...

Σ-grow : (T : Fin n → Bool) (j : Fin n) → T j ≡ false →
         ∀ (f : Pt n → ℤ) x → Σ[ setᵀ T j true ] f x ≡ σ j (Σ[ T ] f) x
Σ-grow T j e f x = trans (Σ-pull (setᵀ T j true) j (setᵀ-here T j true) f x)
  (trans (Σ-congᵀ (setᵀ-agree (setᵀ T j true) T j false e
                     (λ l l≢j → sym (setᵀ-there T true l≢j)))
                  (σ j f) x)
         (Σ-comm T j e f x))

-- ... so it keeps a sum stabilizer-like.

SL-grow : (T : Fin n → Bool) (j : Fin n) {f : Pt n → ℤ} →
          SL (Σ[ T ] f) → SL (Σ[ setᵀ T j true ] f)
SL-grow T j {f} s = go (T j) refl
  where
  go : ∀ b → T j ≡ b → SL (Σ[ setᵀ T j true ] f)
  go true  e = SL-cong (λ x → Σ-congᵀ
    (λ l → sym (setᵀ-agree T T j true e (λ _ _ → refl) l)) f x) s
  go false e = SL-cong (λ x → sym (Σ-grow T j e f x)) (SL-σ j s)

-- Renumbering y_j to the front renumbers the set.

Σ-unfr : (T : Fin (suc n) → Bool) (j : Fin (suc n)) (f : Pt (suc n) → ℤ)
         (p : Pt (suc n)) →
         Σ[ (λ u → T (πᶠ j u)) ] (λ y → f (unfr j y)) p ≡ Σ[ T ] f (unfr j p)
Σ-unfr T j f (b ∷ y) = go (T j) refl
  where
  go : ∀ t → T j ≡ t →
       Σstep t (λ l → T (punchIn j l)) (λ z → f (unfr j z)) b y ≡
       Σ[ T ] f (insertAt y j b)
  go false e = sym (Σ-ins-out T j e f b y)
  go true  e = sym (Σ-ins-in T j e f b y)
