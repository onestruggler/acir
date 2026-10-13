------------------------------------------------------------------------
-- Presentations of groups
--
-- Operators on n qudits of dimension d, over a commutative ring
--
-- A basis vector is a vector of n digits in Fin d, wire 0 first, and
-- an operator is a function from pairs of basis vectors to the ring:
-- its matrix.  Products, the identity, scalars, the Kronecker product
-- and its laws, after Examples.Groups.Real-Clifford.Semantics.Laws
-- (which has them for d = 2): sums over vectors of digits are sums
-- over the first digit of sums over the rest, and the digit sums Σ₁
-- obey the laws the vector sums need.  Operators are compared
-- pointwise (_≐_).  Tries (Mat) store an operator as data, so that a
-- long product is computed once when a relation is checked.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Examples.Independence.Semantics.Operators
  (d : ℕ) {A : Set} {_⊕_ _⊛_ : A → A → A} {⊖_ : A → A} {0r 1r : A}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _⊕_ _⊛_ ⊖_ 0r 1r)
  where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality as Eq using (refl)

R : CommutativeRing _ _
R = record { isCommutativeRing = isCR }

open CommutativeRing R public
  using (_+_ ; _*_ ; -_ ; 0# ; 1#)
open CommutativeRing R
  using (+-assoc ; +-comm ; *-assoc ; *-comm ; +-identityˡ ; +-identityʳ
        ; *-identityˡ ; *-identityʳ ; zeroˡ ; zeroʳ ; distribˡ ; distribʳ)

private
  variable
    k l m n : ℕ

  open Eq.≡-Reasoning

  shuffle : (a b c e : A) → (a + b) + (c + e) ≡ (a + c) + (b + e)
  shuffle a b c e = begin
    (a + b) + (c + e)   ≡⟨ +-assoc a b (c + e) ⟩
    a + (b + (c + e))   ≡⟨ Eq.cong (a +_) (Eq.sym (+-assoc b c e)) ⟩
    a + ((b + c) + e)   ≡⟨ Eq.cong (λ u → a + (u + e)) (+-comm b c) ⟩
    a + ((c + b) + e)   ≡⟨ Eq.cong (a +_) (+-assoc c b e) ⟩
    a + (c + (b + e))   ≡⟨ Eq.sym (+-assoc a c (b + e)) ⟩
    (a + c) + (b + e)   ∎

  cross : (a b c e : A) → (a * b) * (c * e) ≡ (a * c) * (b * e)
  cross a b c e = begin
    (a * b) * (c * e)   ≡⟨ *-assoc a b (c * e) ⟩
    a * (b * (c * e))   ≡⟨ Eq.cong (a *_) (Eq.sym (*-assoc b c e)) ⟩
    a * ((b * c) * e)   ≡⟨ Eq.cong (λ u → a * (u * e)) (*-comm b c) ⟩
    a * ((c * b) * e)   ≡⟨ Eq.cong (a *_) (*-assoc c b e) ⟩
    a * (c * (b * e))   ≡⟨ Eq.sym (*-assoc a c (b * e)) ⟩
    (a * c) * (b * e)   ∎

  -- (a b) c = (a c) b.
  swap-r : (a b c : A) → (a * b) * c ≡ (a * c) * b
  swap-r a b c = begin
    (a * b) * c   ≡⟨ *-assoc a b c ⟩
    a * (b * c)   ≡⟨ Eq.cong (a *_) (*-comm b c) ⟩
    a * (c * b)   ≡⟨ Eq.sym (*-assoc a c b) ⟩
    (a * c) * b   ∎

------------------------------------------------------------------------
-- Digits, and sums over them

Digits : ℕ → Set
Digits n = Vec (Fin d) n

δ₁ : Fin m → Fin m → A
δ₁ zero    zero    = 1#
δ₁ zero    (suc _) = 0#
δ₁ (suc _) zero    = 0#
δ₁ (suc i) (suc j) = δ₁ i j

Σ₁ : (Fin m → A) → A
Σ₁ {zero}  f = 0#
Σ₁ {suc m} f = f zero + Σ₁ (λ i → f (suc i))

δv : Digits n → Digits n → A
δv []      []      = 1#
δv (a ∷ x) (b ∷ y) = δ₁ a b * δv x y

-- Sum over all dⁿ basis vectors.
Σv : (Digits n → A) → A
Σv {zero}  f = f []
Σv {suc n} f = Σ₁ (λ a → Σv (λ xs → f (a ∷ xs)))

------------------------------------------------------------------------
-- Operators

infixl 7 _⊙_
infix  4 _≐_

Op : ℕ → Set
Op n = Digits n → Digits n → A

_⊙_ : Op n → Op n → Op n
(M ⊙ N) x y = Σv (λ z → M x z * N z y)

Idₒ : Op n
Idₒ = δv

scal : A → Op n
scal c x y = c * δv x y

scale : A → Op n → Op n
scale c M x y = c * M x y

-- M acts on the first m wires, N on the rest.
tensor : Op m → Op n → Op (m +ℕ n)
tensor {zero}  M N x       y       = M [] [] * N x y
tensor {suc m} M N (a ∷ x) (b ∷ y) = tensor (λ u v → M (a ∷ u) (b ∷ v)) N x y

_≐_ : Op n → Op n → Set
M ≐ N = ∀ x y → M x y ≡ N x y

------------------------------------------------------------------------
-- Tries

Tab : ℕ → Set → Set
Tab zero    B = B
Tab (suc k) B = Vec (Tab k B) d

tab : (k : ℕ) {B : Set} → (Digits k → B) → Tab k B
tab zero    f = f []
tab (suc k) f = tabulate (λ a → tab k (λ xs → f (a ∷ xs)))

get : {B : Set} → Tab k B → Digits k → B
get {zero}  t []       = t
get {suc k} t (a ∷ xs) = get (lookup t a) xs

get-tab : (k : ℕ) {B : Set} (f : Digits k → B) (x : Digits k) →
          get (tab k f) x ≡ f x
get-tab zero    f []       = refl
get-tab (suc k) f (a ∷ xs) =
  Eq.trans (Eq.cong (λ t → get t xs)
                    (lookup∘tabulate (λ b → tab k (λ ys → f (b ∷ ys))) a))
           (get-tab k (λ ys → f (a ∷ ys)) xs)

-- Wrapped in a record so that the width is inferable.
record Mat (k : ℕ) : Set where
  constructor mat
  field entries : Tab k (Tab k A)

open Mat public

ix : Mat k → Op k
ix M x y = get (get (entries M) x) y

matOf : Op k → Mat k
matOf {k} M = mat (tab k (λ x → tab k (λ y → M x y)))

ix-matOf : (M : Op k) → ix (matOf M) ≐ M
ix-matOf {k} M x y =
  Eq.trans (Eq.cong (λ t → get t y) (get-tab k (λ u → tab k (λ v → M u v)) x))
           (get-tab k (λ v → M x v) y)

mulM : Mat k → Mat k → Mat k
mulM M N = matOf (ix M ⊙ ix N)

idM : Mat k
idM = matOf Idₒ

tenM : Mat k → Mat l → Mat (k +ℕ l)
tenM M N = matOf (tensor (ix M) (ix N))

scalM : A → Mat k
scalM c = matOf (scal c)

------------------------------------------------------------------------
-- The laws of Σ₁

Σ₁-cong : {f g : Fin m → A} → (∀ i → f i ≡ g i) → Σ₁ f ≡ Σ₁ g
Σ₁-cong {zero}  e = refl
Σ₁-cong {suc m} e = Eq.cong₂ _+_ (e zero) (Σ₁-cong (λ i → e (suc i)))

Σ₁-zero : Σ₁ {m} (λ _ → 0#) ≡ 0#
Σ₁-zero {zero}  = refl
Σ₁-zero {suc m} = Eq.trans (Eq.cong (0# +_) (Σ₁-zero {m})) (+-identityʳ 0#)

Σ₁-scaleˡ : (c : A) (f : Fin m → A) → Σ₁ (λ i → c * f i) ≡ c * Σ₁ f
Σ₁-scaleˡ {zero}  c f = Eq.sym (zeroʳ c)
Σ₁-scaleˡ {suc m} c f =
  Eq.trans (Eq.cong (c * f zero +_) (Σ₁-scaleˡ c (λ i → f (suc i))))
           (Eq.sym (distribˡ c (f zero) (Σ₁ (λ i → f (suc i)))))

Σ₁-scaleʳ : (c : A) (f : Fin m → A) → Σ₁ (λ i → f i * c) ≡ Σ₁ f * c
Σ₁-scaleʳ {zero}  c f = Eq.sym (zeroˡ c)
Σ₁-scaleʳ {suc m} c f =
  Eq.trans (Eq.cong (f zero * c +_) (Σ₁-scaleʳ c (λ i → f (suc i))))
           (Eq.sym (distribʳ c (f zero) (Σ₁ (λ i → f (suc i)))))

Σ₁-add : (f g : Fin m → A) → Σ₁ (λ i → f i + g i) ≡ Σ₁ f + Σ₁ g
Σ₁-add {zero}  f g = Eq.sym (+-identityˡ 0#)
Σ₁-add {suc m} f g =
  Eq.trans (Eq.cong (f zero + g zero +_) (Σ₁-add (λ i → f (suc i)) (λ i → g (suc i))))
           (shuffle (f zero) (g zero) (Σ₁ (λ i → f (suc i))) (Σ₁ (λ i → g (suc i))))

Σ₁-δˡ : (a : Fin m) (f : Fin m → A) → Σ₁ (λ i → δ₁ a i * f i) ≡ f a
Σ₁-δˡ {suc m} zero f =
  Eq.trans (Eq.cong₂ _+_ (*-identityˡ (f zero))
             (Eq.trans (Σ₁-cong (λ i → zeroˡ (f (suc i)))) (Σ₁-zero {m})))
           (+-identityʳ (f zero))
Σ₁-δˡ (suc a) f =
  Eq.trans (Eq.cong₂ _+_ (zeroˡ (f zero)) (Σ₁-δˡ a (λ i → f (suc i))))
           (+-identityˡ (f (suc a)))

Σ₁-δʳ : (b : Fin m) (f : Fin m → A) → Σ₁ (λ i → f i * δ₁ i b) ≡ f b
Σ₁-δʳ {suc m} zero f =
  Eq.trans (Eq.cong₂ _+_ (*-identityʳ (f zero))
             (Eq.trans (Σ₁-cong (λ i → zeroʳ (f (suc i)))) (Σ₁-zero {m})))
           (+-identityʳ (f zero))
Σ₁-δʳ (suc b) f =
  Eq.trans (Eq.cong₂ _+_ (zeroʳ (f zero)) (Σ₁-δʳ b (λ i → f (suc i))))
           (+-identityˡ (f (suc b)))

------------------------------------------------------------------------
-- The laws of Σv

Σ-cong : {f g : Digits n → A} → (∀ x → f x ≡ g x) → Σv f ≡ Σv g
Σ-cong {zero}  e = e []
Σ-cong {suc n} e = Σ₁-cong (λ a → Σ-cong (λ xs → e (a ∷ xs)))

Σ-zero : Σv {n} (λ _ → 0#) ≡ 0#
Σ-zero {zero}  = refl
Σ-zero {suc n} = Eq.trans (Σ₁-cong {d} (λ _ → Σ-zero {n})) (Σ₁-zero {d})

Σ-scaleˡ : (c : A) (f : Digits n → A) → Σv (λ z → c * f z) ≡ c * Σv f
Σ-scaleˡ {zero}  c f = refl
Σ-scaleˡ {suc n} c f =
  Eq.trans (Σ₁-cong (λ a → Σ-scaleˡ c (λ xs → f (a ∷ xs))))
           (Σ₁-scaleˡ c (λ a → Σv (λ xs → f (a ∷ xs))))

Σ-scaleʳ : (c : A) (f : Digits n → A) → Σv (λ z → f z * c) ≡ Σv f * c
Σ-scaleʳ {zero}  c f = refl
Σ-scaleʳ {suc n} c f =
  Eq.trans (Σ₁-cong (λ a → Σ-scaleʳ c (λ xs → f (a ∷ xs))))
           (Σ₁-scaleʳ c (λ a → Σv (λ xs → f (a ∷ xs))))

Σ-add : (f g : Digits n → A) → Σv (λ z → f z + g z) ≡ Σv f + Σv g
Σ-add {zero}  f g = refl
Σ-add {suc n} f g =
  Eq.trans (Σ₁-cong (λ a → Σ-add (λ xs → f (a ∷ xs)) (λ xs → g (a ∷ xs))))
           (Σ₁-add (λ a → Σv (λ xs → f (a ∷ xs))) (λ a → Σv (λ xs → g (a ∷ xs))))

-- A digit sum and a vector sum commute.
Σ₁-Σ : (G : Fin m → Digits n → A) →
       Σ₁ (λ a → Σv (G a)) ≡ Σv (λ y → Σ₁ (λ a → G a y))
Σ₁-Σ {zero} {n} G = Eq.sym (Σ-zero {n})
Σ₁-Σ {suc m} G =
  Eq.trans (Eq.cong (Σv (G zero) +_) (Σ₁-Σ (λ a → G (suc a))))
           (Eq.sym (Σ-add (G zero) (λ y → Σ₁ (λ a → G (suc a) y))))

Σ-swap : (F : Digits m → Digits n → A) →
         Σv (λ x → Σv (λ y → F x y)) ≡ Σv (λ y → Σv (λ x → F x y))
Σ-swap {zero}  F = refl
Σ-swap {suc m} F =
  Eq.trans (Σ₁-cong (λ a → Σ-swap (λ xs → F (a ∷ xs))))
           (Σ₁-Σ (λ a y → Σv (λ xs → F (a ∷ xs) y)))

Σ-δˡ : (x : Digits n) (f : Digits n → A) → Σv (λ z → δv x z * f z) ≡ f x
Σ-δˡ []       f = *-identityˡ (f [])
Σ-δˡ (a ∷ x) f = begin
  Σ₁ (λ c → Σv (λ zs → (δ₁ a c * δv x zs) * f (c ∷ zs)))
    ≡⟨ Σ₁-cong (λ c → Eq.trans (Σ-cong (λ zs → *-assoc (δ₁ a c) (δv x zs) (f (c ∷ zs))))
                                (Σ-scaleˡ (δ₁ a c) (λ zs → δv x zs * f (c ∷ zs)))) ⟩
  Σ₁ (λ c → δ₁ a c * Σv (λ zs → δv x zs * f (c ∷ zs)))
    ≡⟨ Σ₁-cong (λ c → Eq.cong (δ₁ a c *_) (Σ-δˡ x (λ zs → f (c ∷ zs)))) ⟩
  Σ₁ (λ c → δ₁ a c * f (c ∷ x))
    ≡⟨ Σ₁-δˡ a (λ c → f (c ∷ x)) ⟩
  f (a ∷ x) ∎

Σ-δʳ : (y : Digits n) (f : Digits n → A) → Σv (λ z → f z * δv z y) ≡ f y
Σ-δʳ []       f = *-identityʳ (f [])
Σ-δʳ (b ∷ y) f = begin
  Σ₁ (λ c → Σv (λ zs → f (c ∷ zs) * (δ₁ c b * δv zs y)))
    ≡⟨ Σ₁-cong (λ c → Σ-cong (λ zs → regroup (f (c ∷ zs)) (δ₁ c b) (δv zs y))) ⟩
  Σ₁ (λ c → Σv (λ zs → (f (c ∷ zs) * δv zs y) * δ₁ c b))
    ≡⟨ Σ₁-cong (λ c → Σ-scaleʳ (δ₁ c b) (λ zs → f (c ∷ zs) * δv zs y)) ⟩
  Σ₁ (λ c → Σv (λ zs → f (c ∷ zs) * δv zs y) * δ₁ c b)
    ≡⟨ Σ₁-cong (λ c → Eq.cong (_* δ₁ c b) (Σ-δʳ y (λ zs → f (c ∷ zs)))) ⟩
  Σ₁ (λ c → f (c ∷ y) * δ₁ c b)
    ≡⟨ Σ₁-δʳ b (λ c → f (c ∷ y)) ⟩
  f (b ∷ y) ∎
  where
  regroup : (u v w : A) → u * (v * w) ≡ (u * w) * v
  regroup u v w = Eq.trans (Eq.cong (u *_) (*-comm v w)) (Eq.sym (*-assoc u w v))

------------------------------------------------------------------------
-- Operators, up to pointwise equality

≐-refl : (M : Op n) → M ≐ M
≐-refl M x y = refl

≐-sym : {M N : Op n} → M ≐ N → N ≐ M
≐-sym e x y = Eq.sym (e x y)

≐-trans : {M N P : Op n} → M ≐ N → N ≐ P → M ≐ P
≐-trans e f x y = Eq.trans (e x y) (f x y)

⊙-cong : {M M' N N' : Op n} → M ≐ M' → N ≐ N' → (M ⊙ N) ≐ (M' ⊙ N')
⊙-cong e f x y = Σ-cong (λ z → Eq.cong₂ _*_ (e x z) (f z y))

⊙-assoc : (M N P : Op n) → ((M ⊙ N) ⊙ P) ≐ (M ⊙ (N ⊙ P))
⊙-assoc M N P x y = begin
  Σv (λ w → Σv (λ z → M x z * N z w) * P w y)
    ≡⟨ Σ-cong (λ w → Eq.sym (Σ-scaleʳ (P w y) (λ z → M x z * N z w))) ⟩
  Σv (λ w → Σv (λ z → (M x z * N z w) * P w y))
    ≡⟨ Σ-swap (λ w z → (M x z * N z w) * P w y) ⟩
  Σv (λ z → Σv (λ w → (M x z * N z w) * P w y))
    ≡⟨ Σ-cong (λ z → Eq.trans
         (Σ-cong (λ w → *-assoc (M x z) (N z w) (P w y)))
         (Σ-scaleˡ (M x z) (λ w → N z w * P w y))) ⟩
  Σv (λ z → M x z * Σv (λ w → N z w * P w y)) ∎

⊙-identityˡ : (M : Op n) → (Idₒ ⊙ M) ≐ M
⊙-identityˡ M x y = Σ-δˡ x (λ z → M z y)

⊙-identityʳ : (M : Op n) → (M ⊙ Idₒ) ≐ M
⊙-identityʳ M x y = Σ-δʳ y (λ z → M x z)

------------------------------------------------------------------------
-- Scaling

scale-cong : {c : A} {M N : Op n} → M ≐ N → scale c M ≐ scale c N
scale-cong e x y = Eq.cong (_ *_) (e x y)

scale-1 : (M : Op n) → scale 1# M ≐ M
scale-1 M x y = *-identityˡ (M x y)

scale-scale : (a b : A) (M : Op n) → scale a (scale b M) ≐ scale (a * b) M
scale-scale a b M x y = Eq.sym (*-assoc a b (M x y))

scale-⊙ˡ : (c : A) (M N : Op n) → (scale c M ⊙ N) ≐ scale c (M ⊙ N)
scale-⊙ˡ c M N x y =
  Eq.trans (Σ-cong (λ z → *-assoc c (M x z) (N z y)))
           (Σ-scaleˡ c (λ z → M x z * N z y))

scale-⊙ʳ : (c : A) (M N : Op n) → (M ⊙ scale c N) ≐ scale c (M ⊙ N)
scale-⊙ʳ c M N x y =
  Eq.trans (Σ-cong (λ z → Eq.trans (Eq.sym (*-assoc (M x z) c (N z y)))
                    (Eq.trans (Eq.cong (_* N z y) (*-comm (M x z) c))
                              (*-assoc c (M x z) (N z y)))))
           (Σ-scaleˡ c (λ z → M x z * N z y))

------------------------------------------------------------------------
-- The Kronecker product

tensor-cong : {M M' : Op m} {N N' : Op n} → M ≐ M' → N ≐ N' →
              tensor M N ≐ tensor M' N'
tensor-cong {zero}  e f x       y       = Eq.cong₂ _*_ (e [] []) (f x y)
tensor-cong {suc m} e f (a ∷ x) (b ∷ y) =
  tensor-cong {m} (λ u v → e (a ∷ u) (b ∷ v)) f x y

tensor-zeroˡ : (N : Op n) → ∀ (x y : Digits (m +ℕ n)) →
               tensor {m} (λ _ _ → 0#) N x y ≡ 0#
tensor-zeroˡ {m = zero}  N x       y       = zeroˡ (N x y)
tensor-zeroˡ {m = suc m} N (a ∷ x) (b ∷ y) = tensor-zeroˡ {m = m} N x y

tensor-addˡ : (P Q : Op m) (N : Op n) → ∀ x y →
              tensor (λ u v → P u v + Q u v) N x y ≡ tensor P N x y + tensor Q N x y
tensor-addˡ {zero}  P Q N x       y       = distribʳ (N x y) (P [] []) (Q [] [])
tensor-addˡ {suc m} P Q N (a ∷ x) (b ∷ y) =
  tensor-addˡ {m} (λ u v → P (a ∷ u) (b ∷ v)) (λ u v → Q (a ∷ u) (b ∷ v)) N x y

-- tensor is additive in its first factor over a digit sum.
tensor-Σ₁ : (F : Fin k → Op m) (N : Op n) → ∀ x y →
            tensor (λ u v → Σ₁ (λ c → F c u v)) N x y ≡ Σ₁ (λ c → tensor (F c) N x y)
tensor-Σ₁ {zero}  F N x y = tensor-zeroˡ N x y
tensor-Σ₁ {suc k} F N x y =
  Eq.trans (tensor-addˡ (F zero) (λ u v → Σ₁ (λ c → F (suc c) u v)) N x y)
           (Eq.cong (tensor (F zero) N x y +_) (tensor-Σ₁ (λ c → F (suc c)) N x y))

-- The mixed product law.
tensor-⊙ : (M P : Op m) (N Q : Op n) →
           (tensor M N ⊙ tensor P Q) ≐ tensor (M ⊙ P) (N ⊙ Q)
tensor-⊙ {zero} M P N Q x y =
  Eq.trans (Σ-cong (λ z → cross (M [] []) (N x z) (P [] []) (Q z y)))
           (Σ-scaleˡ (M [] [] * P [] []) (λ z → N x z * Q z y))
tensor-⊙ {suc m} {n} M P N Q (a ∷ x) (b ∷ y) =
  Eq.trans (Σ₁-cong (λ c →
             tensor-⊙ {m} {n} (λ u v → M (a ∷ u) (c ∷ v))
                              (λ u v → P (c ∷ u) (b ∷ v)) N Q x y))
           (Eq.sym (tensor-Σ₁ (λ c u v → Σv (λ w → M (a ∷ u) (c ∷ w) * P (c ∷ w) (b ∷ v)))
                              (N ⊙ Q) x y))

tensor-scaleˡ : (c : A) (B : Op m) (C : Op n) → ∀ x y →
                tensor (λ u v → c * B u v) C x y ≡ c * tensor B C x y
tensor-scaleˡ {zero}  c B C x       y       = *-assoc c (B [] []) (C x y)
tensor-scaleˡ {suc m} c B C (a ∷ x) (b ∷ y) =
  tensor-scaleˡ {m} c (λ u v → B (a ∷ u) (b ∷ v)) C x y

tensor-scaleʳ : (c : A) (B : Op m) (C : Op n) → ∀ x y →
                tensor B (λ u v → c * C u v) x y ≡ c * tensor B C x y
tensor-scaleʳ {zero}  c B C x       y       =
  Eq.trans (Eq.sym (*-assoc (B [] []) c (C x y)))
    (Eq.trans (Eq.cong (_* C x y) (*-comm (B [] []) c)) (*-assoc c (B [] []) (C x y)))
tensor-scaleʳ {suc m} c B C (a ∷ x) (b ∷ y) =
  tensor-scaleʳ {m} c (λ u v → B (a ∷ u) (b ∷ v)) C x y

tensor-Id : Idₒ {m +ℕ n} ≐ tensor (Idₒ {m}) (Idₒ {n})
tensor-Id {zero}  x       y       = Eq.sym (*-identityˡ (δv x y))
tensor-Id {suc m} {n} (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong (δ₁ a b *_) (tensor-Id {m} {n} x y))
           (Eq.sym (tensor-scaleˡ {m} {n} (δ₁ a b) Idₒ Idₒ x y))

tensor-scal : (c : A) → tensor (scal {m} c) (Idₒ {n}) ≐ scal {m +ℕ n} c
tensor-scal {zero}  c x y = Eq.cong (_* δv x y) (*-identityʳ c)
tensor-scal {suc m} {n} c (a ∷ x) (b ∷ y) = begin
  tensor {m} {n} (λ u v → c * (δ₁ a b * δv u v)) Idₒ x y
    ≡⟨ tensor-cong {m} {n} (λ u v → Eq.sym (*-assoc c (δ₁ a b) (δv u v)))
                   (≐-refl Idₒ) x y ⟩
  tensor {m} {n} (scal (c * δ₁ a b)) Idₒ x y
    ≡⟨ tensor-scal {m} {n} (c * δ₁ a b) x y ⟩
  (c * δ₁ a b) * δv x y
    ≡⟨ *-assoc c (δ₁ a b) (δv x y) ⟩
  c * (δ₁ a b * δv x y) ∎

tensor-assoc₁ : (P : Op 1) (B : Op m) (C : Op n) →
                tensor (tensor P B) C ≐ tensor P (tensor B C)
tensor-assoc₁ P B C (a ∷ x) (b ∷ y) = tensor-scaleˡ (P (a ∷ []) (b ∷ [])) B C x y

tensor-assoc₂ : (P : Op 2) (B : Op m) (C : Op n) →
                tensor (tensor P B) C ≐ tensor P (tensor B C)
tensor-assoc₂ P B C (a ∷ a' ∷ x) (b ∷ b' ∷ y) =
  tensor-scaleˡ (P (a ∷ a' ∷ []) (b ∷ b' ∷ [])) B C x y

tensor-assoc₃ : (P : Op 3) (B : Op m) (C : Op n) →
                tensor (tensor P B) C ≐ tensor P (tensor B C)
tensor-assoc₃ P B C (a ∷ a' ∷ a'' ∷ x) (b ∷ b' ∷ b'' ∷ y) =
  tensor-scaleˡ (P (a ∷ a' ∷ a'' ∷ []) (b ∷ b' ∷ b'' ∷ [])) B C x y

------------------------------------------------------------------------
-- Tries

ix-mul : (M N : Mat k) → ix (mulM M N) ≐ (ix M ⊙ ix N)
ix-mul M N = ix-matOf (ix M ⊙ ix N)

ix-id : ix (idM {k}) ≐ Idₒ
ix-id = ix-matOf Idₒ

ix-tenM : (M : Mat k) (N : Mat l) → ix (tenM M N) ≐ tensor (ix M) (ix N)
ix-tenM M N = ix-matOf (tensor (ix M) (ix N))

ix-scalM : (c : A) → ix (scalM {k} c) ≐ scal c
ix-scalM c = ix-matOf (scal c)

------------------------------------------------------------------------
-- Gates on the bottom wires, and operators moved up

-- A k-wire operator on the bottom k wires of k + n.
emb : Op k → Op (k +ℕ n)
emb M = tensor M Idₒ

up : Op n → Op (suc n)
up M = tensor (Idₒ {1}) M

upk : (k : ℕ) → Op n → Op (k +ℕ n)
upk k M = tensor (Idₒ {k}) M

emb-cong : {M N : Op k} → M ≐ N → emb {k} {n} M ≐ emb N
emb-cong e = tensor-cong e (≐-refl Idₒ)

up-cong : {M N : Op n} → M ≐ N → up M ≐ up N
up-cong e = tensor-cong (≐-refl Idₒ) e

emb-⊙ : (M N : Op k) → (emb {k} {n} M ⊙ emb N) ≐ emb (M ⊙ N)
emb-⊙ M N = ≐-trans (tensor-⊙ M N Idₒ Idₒ) (tensor-cong (≐-refl (M ⊙ N)) (⊙-identityˡ Idₒ))

emb-id : emb {k} {n} Idₒ ≐ Idₒ
emb-id {k} {n} = ≐-sym (tensor-Id {m = k} {n = n})

emb-scale : (c : A) (M : Op k) → emb {k} {n} (scale c M) ≐ scale c (emb M)
emb-scale c M = tensor-scaleˡ c M Idₒ

up-⊙ : (M N : Op n) → (up M ⊙ up N) ≐ up (M ⊙ N)
up-⊙ M N = ≐-trans (tensor-⊙ Idₒ Idₒ M N) (tensor-cong (⊙-identityˡ Idₒ) (≐-refl (M ⊙ N)))

up-Id : up (Idₒ {n}) ≐ Idₒ
up-Id {n} = ≐-sym (tensor-Id {m = 1} {n = n})

up-scale : (c : A) (M : Op n) → up (scale c M) ≐ scale c (up M)
up-scale c M = tensor-scaleʳ c Idₒ M

-- A gate on the bottom k wires commutes with an operator shifted past
-- them.
emb-up-comm : (M : Op k) (N : Op n) → (emb {k} {n} M ⊙ upk k N) ≐ (upk k N ⊙ emb M)
emb-up-comm M N =
  ≐-trans (tensor-⊙ M Idₒ Idₒ N)
    (≐-trans (tensor-cong (⊙-identityʳ M) (⊙-identityˡ N))
      (≐-trans (tensor-cong (≐-sym (⊙-identityˡ M)) (≐-sym (⊙-identityʳ N)))
               (≐-sym (tensor-⊙ Idₒ M N Idₒ))))

up-up : (M : Op n) → up (up M) ≐ upk 2 M
up-up M (a ∷ b ∷ x) (a' ∷ b' ∷ y) = begin
  (δ₁ a a' * 1#) * ((δ₁ b b' * 1#) * M x y)
    ≡⟨ Eq.sym (*-assoc (δ₁ a a' * 1#) (δ₁ b b' * 1#) (M x y)) ⟩
  ((δ₁ a a' * 1#) * (δ₁ b b' * 1#)) * M x y
    ≡⟨ Eq.cong (_* M x y) (Eq.trans (*-assoc (δ₁ a a') 1# (δ₁ b b' * 1#))
                                    (Eq.cong (δ₁ a a' *_) (*-identityˡ (δ₁ b b' * 1#)))) ⟩
  (δ₁ a a' * (δ₁ b b' * 1#)) * M x y ∎

-- One more wire below an operator shifted past k of them.
up-upk : (k : ℕ) (M : Op n) → up (upk k M) ≐ upk (suc k) M
up-upk k M (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong (_* tensor (Idₒ {k}) M x y) (*-identityʳ (δ₁ a b)))
           (Eq.sym (tensor-scaleˡ {k} (δ₁ a b) Idₒ M x y))

-- Scalars are local, and the same on every wire.
up-scal : (c : A) → up (scal {n} c) ≐ scal c
up-scal c (a ∷ x) (b ∷ y) = begin
  (δ₁ a b * 1#) * (c * δv x y)   ≡⟨ Eq.cong (_* (c * δv x y)) (*-identityʳ (δ₁ a b)) ⟩
  δ₁ a b * (c * δv x y)          ≡⟨ Eq.sym (*-assoc (δ₁ a b) c (δv x y)) ⟩
  (δ₁ a b * c) * δv x y          ≡⟨ Eq.cong (_* δv x y) (*-comm (δ₁ a b) c) ⟩
  (c * δ₁ a b) * δv x y          ≡⟨ *-assoc c (δ₁ a b) (δv x y) ⟩
  c * (δ₁ a b * δv x y)          ∎

-- A gate read on a wider block.
emb-pad₁ : (M : Op 1) → emb {1} {m +ℕ n} M ≐ emb {suc m} {n} (tensor M (Idₒ {m}))
emb-pad₁ {m} {n} M =
  ≐-trans (tensor-cong {m = 1} {n = m +ℕ n} (≐-refl M) (tensor-Id {m} {n}))
          (≐-sym (tensor-assoc₁ M (Idₒ {m}) (Idₒ {n})))

emb-pad₂ : (M : Op 2) → emb {2} {m +ℕ n} M ≐ emb {suc (suc m)} {n} (tensor M (Idₒ {m}))
emb-pad₂ {m} {n} M =
  ≐-trans (tensor-cong {m = 2} {n = m +ℕ n} (≐-refl M) (tensor-Id {m} {n}))
          (≐-sym (tensor-assoc₂ M (Idₒ {m}) (Idₒ {n})))

emb-pad₃ : (M : Op 3) →
           emb {3} {m +ℕ n} M ≐ emb {suc (suc (suc m))} {n} (tensor M (Idₒ {m}))
emb-pad₃ {m} {n} M =
  ≐-trans (tensor-cong {m = 3} {n = m +ℕ n} (≐-refl M) (tensor-Id {m} {n}))
          (≐-sym (tensor-assoc₃ M (Idₒ {m}) (Idₒ {n})))

up-emb : (M : Op k) → up (emb {k} {n} M) ≐ emb {suc k} {n} (tensor (Idₒ {1}) M)
up-emb {k} {n} M = ≐-sym (tensor-assoc₁ (Idₒ {1}) M (Idₒ {n}))

scal-emb : (c : A) → scal {k +ℕ n} c ≐ emb {k} {n} (scal c)
scal-emb {k} {n} c = ≐-sym (tensor-scal {k} {n} c)
