------------------------------------------------------------------------
-- Presentations of groups
--
-- The laws of operators over a commutative ring: sums, products, the
-- Kronecker product and its mixed product law, gates on the bottom
-- wires (emb) and operators moved up (up)
--
-- A port of Clifford.Qubit.Model.Algebra and Model.Local from ℤ/17ℤ to
-- any commutative ring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Real-Clifford.Semantics.Laws
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Real-Clifford.Semantics.Ops A _+_ _*_ 0# 1# public

R : CommutativeRing _ _
R = record { isCommutativeRing = isCR }

module AR = CommutativeRing R
open AR using (+-assoc ; +-comm ; *-assoc ; *-comm ; +-identityˡ ; +-identityʳ
              ; *-identityˡ ; *-identityʳ ; zeroˡ ; zeroʳ ; distribˡ ; distribʳ)

private
  variable
    k l m n : ℕ

  shuffle : (a b c d : A) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  shuffle a b c d = begin
    (a + b) + (c + d)   ≡⟨ +-assoc a b (c + d) ⟩
    a + (b + (c + d))   ≡⟨ Eq.cong (a +_) (Eq.sym (+-assoc b c d)) ⟩
    a + ((b + c) + d)   ≡⟨ Eq.cong (λ x → a + (x + d)) (+-comm b c) ⟩
    a + ((c + b) + d)   ≡⟨ Eq.cong (a +_) (+-assoc c b d) ⟩
    a + (c + (b + d))   ≡⟨ Eq.sym (+-assoc a c (b + d)) ⟩
    (a + c) + (b + d)   ∎
    where open Eq.≡-Reasoning

  cross : (a b c d : A) → (a * b) * (c * d) ≡ (a * c) * (b * d)
  cross a b c d = begin
    (a * b) * (c * d)   ≡⟨ *-assoc a b (c * d) ⟩
    a * (b * (c * d))   ≡⟨ Eq.cong (a *_) (Eq.sym (*-assoc b c d)) ⟩
    a * ((b * c) * d)   ≡⟨ Eq.cong (λ x → a * (x * d)) (*-comm b c) ⟩
    a * ((c * b) * d)   ≡⟨ Eq.cong (a *_) (*-assoc c b d) ⟩
    a * (c * (b * d))   ≡⟨ Eq.sym (*-assoc a c (b * d)) ⟩
    (a * c) * (b * d)   ∎
    where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The laws of Σb

Σ-cong : {f g : Bits n → A} → (∀ x → f x ≡ g x) → Σb f ≡ Σb g
Σ-cong {zero}          e = e []
Σ-cong {suc n} {f} {g} e =
  Eq.cong₂ _+_
    (Σ-cong {n} {λ bs → f (false ∷ bs)} {λ bs → g (false ∷ bs)} (λ bs → e (false ∷ bs)))
    (Σ-cong {n} {λ bs → f (true ∷ bs)} {λ bs → g (true ∷ bs)} (λ bs → e (true ∷ bs)))

Σ-zero : Σb {n} (λ _ → 0#) ≡ 0#
Σ-zero {zero}  = Eq.refl
Σ-zero {suc n} = Eq.trans (Eq.cong₂ _+_ (Σ-zero {n}) (Σ-zero {n})) (+-identityʳ 0#)

Σ-scaleˡ : (c : A) (f : Bits n → A) → Σb (λ z → c * f z) ≡ c * Σb f
Σ-scaleˡ {zero}  c f = Eq.refl
Σ-scaleˡ {suc n} c f =
  Eq.trans (Eq.cong₂ _+_ (Σ-scaleˡ {n} c (λ bs → f (false ∷ bs)))
                         (Σ-scaleˡ {n} c (λ bs → f (true ∷ bs))))
           (Eq.sym (distribˡ c (Σb (λ bs → f (false ∷ bs))) (Σb (λ bs → f (true ∷ bs)))))

Σ-scaleʳ : (c : A) (f : Bits n → A) → Σb (λ z → f z * c) ≡ Σb f * c
Σ-scaleʳ {zero}  c f = Eq.refl
Σ-scaleʳ {suc n} c f =
  Eq.trans (Eq.cong₂ _+_ (Σ-scaleʳ {n} c (λ bs → f (false ∷ bs)))
                         (Σ-scaleʳ {n} c (λ bs → f (true ∷ bs))))
           (Eq.sym (distribʳ c (Σb (λ bs → f (false ∷ bs))) (Σb (λ bs → f (true ∷ bs)))))

Σ-add : (f g : Bits n → A) → Σb (λ z → f z + g z) ≡ Σb f + Σb g
Σ-add {zero}  f g = Eq.refl
Σ-add {suc n} f g =
  Eq.trans (Eq.cong₂ _+_
             (Σ-add {n} (λ bs → f (false ∷ bs)) (λ bs → g (false ∷ bs)))
             (Σ-add {n} (λ bs → f (true ∷ bs)) (λ bs → g (true ∷ bs))))
           (shuffle (Σb (λ bs → f (false ∷ bs))) (Σb (λ bs → g (false ∷ bs)))
                    (Σb (λ bs → f (true ∷ bs)))  (Σb (λ bs → g (true ∷ bs))))

Σ-swap : (F : Bits m → Bits n → A) →
         Σb (λ x → Σb (λ y → F x y)) ≡ Σb (λ y → Σb (λ x → F x y))
Σ-swap {zero}  F = Eq.refl
Σ-swap {suc m} F =
  Eq.trans (Eq.cong₂ _+_ (Σ-swap {m} (λ xs → F (false ∷ xs)))
                         (Σ-swap {m} (λ xs → F (true ∷ xs))))
           (Eq.sym (Σ-add (λ y → Σb (λ xs → F (false ∷ xs) y))
                          (λ y → Σb (λ xs → F (true ∷ xs) y))))

Σ-δˡ : (x : Bits n) (f : Bits n → A) → Σb (λ z → δb x z * f z) ≡ f x
Σ-δˡ []                 f = *-identityˡ (f [])
Σ-δˡ {suc n} (false ∷ xs) f =
  Eq.trans (Eq.cong₂ _+_
             (Σ-δˡ xs (λ zs → f (false ∷ zs)))
             (Eq.trans (Σ-cong {n} {λ zs → 0# * f (true ∷ zs)} {λ _ → 0#} (λ zs → zeroˡ (f (true ∷ zs))))
                       (Σ-zero {n})))
           (+-identityʳ (f (false ∷ xs)))
Σ-δˡ {suc n} (true ∷ xs)  f =
  Eq.trans (Eq.cong₂ _+_
             (Eq.trans (Σ-cong {n} {λ zs → 0# * f (false ∷ zs)} {λ _ → 0#} (λ zs → zeroˡ (f (false ∷ zs))))
                       (Σ-zero {n}))
             (Σ-δˡ xs (λ zs → f (true ∷ zs))))
           (+-identityˡ (f (true ∷ xs)))

Σ-δʳ : (y : Bits n) (f : Bits n → A) → Σb (λ z → f z * δb z y) ≡ f y
Σ-δʳ []                 f = *-identityʳ (f [])
Σ-δʳ {suc n} (false ∷ ys) f =
  Eq.trans (Eq.cong₂ _+_
             (Σ-δʳ ys (λ zs → f (false ∷ zs)))
             (Eq.trans (Σ-cong {n} {λ zs → f (true ∷ zs) * 0#} {λ _ → 0#} (λ zs → zeroʳ (f (true ∷ zs))))
                       (Σ-zero {n})))
           (+-identityʳ (f (false ∷ ys)))
Σ-δʳ {suc n} (true ∷ ys)  f =
  Eq.trans (Eq.cong₂ _+_
             (Eq.trans (Σ-cong {n} {λ zs → f (false ∷ zs) * 0#} {λ _ → 0#} (λ zs → zeroʳ (f (false ∷ zs))))
                       (Σ-zero {n}))
             (Σ-δʳ ys (λ zs → f (true ∷ zs))))
           (+-identityˡ (f (true ∷ ys)))

------------------------------------------------------------------------
-- Operators, up to pointwise equality

infix 4 _≐_

_≐_ : Op n → Op n → Set
M ≐ N = ∀ x y → M x y ≡ N x y

≐-refl : (M : Op n) → M ≐ M
≐-refl M x y = Eq.refl

≐-sym : {M N : Op n} → M ≐ N → N ≐ M
≐-sym e x y = Eq.sym (e x y)

≐-trans : {M N P : Op n} → M ≐ N → N ≐ P → M ≐ P
≐-trans e f x y = Eq.trans (e x y) (f x y)

⊙-cong : {M M' N N' : Op n} → M ≐ M' → N ≐ N' → (M ⊙ N) ≐ (M' ⊙ N')
⊙-cong {M = M} {M'} {N} {N'} e f x y =
  Σ-cong {f = λ z → M x z * N z y} {g = λ z → M' x z * N' z y}
         (λ z → Eq.cong₂ _*_ (e x z) (f z y))

⊙-assoc : (M N P : Op n) → ((M ⊙ N) ⊙ P) ≐ (M ⊙ (N ⊙ P))
⊙-assoc M N P x y = begin
  Σb (λ w → Σb (λ z → M x z * N z w) * P w y)
    ≡⟨ Σ-cong {f = λ w → Σb (λ z → M x z * N z w) * P w y}
               {g = λ w → Σb (λ z → (M x z * N z w) * P w y)}
               (λ w → Eq.sym (Σ-scaleʳ (P w y) (λ z → M x z * N z w))) ⟩
  Σb (λ w → Σb (λ z → (M x z * N z w) * P w y))
    ≡⟨ Σ-swap (λ w z → (M x z * N z w) * P w y) ⟩
  Σb (λ z → Σb (λ w → (M x z * N z w) * P w y))
    ≡⟨ Σ-cong {f = λ z → Σb (λ w → (M x z * N z w) * P w y)}
               {g = λ z → M x z * Σb (λ w → N z w * P w y)}
               (λ z → Eq.trans
                 (Σ-cong {f = λ w → (M x z * N z w) * P w y}
                          {g = λ w → M x z * (N z w * P w y)}
                          (λ w → *-assoc (M x z) (N z w) (P w y)))
                 (Σ-scaleˡ (M x z) (λ w → N z w * P w y))) ⟩
  Σb (λ z → M x z * Σb (λ w → N z w * P w y)) ∎
  where open Eq.≡-Reasoning

⊙-identityˡ : (M : Op n) → (Idₒ ⊙ M) ≐ M
⊙-identityˡ M x y = Σ-δˡ x (λ z → M z y)

⊙-identityʳ : (M : Op n) → (M ⊙ Idₒ) ≐ M
⊙-identityʳ M x y = Σ-δʳ y (λ z → M x z)

------------------------------------------------------------------------
-- Scalars

scal-⊙ : (a b : A) → (scal {n} a ⊙ scal b) ≐ scal (a * b)
scal-⊙ a b x y =
  Eq.trans (Σ-cong {f = λ z → (a * δb x z) * (b * δb z y)}
                    {g = λ z → (a * b) * (δb x z * δb z y)}
                    (λ z → cross a (δb x z) b (δb z y)))
    (Eq.trans (Σ-scaleˡ (a * b) (λ z → δb x z * δb z y))
              (Eq.cong ((a * b) *_) (Σ-δˡ x (λ z → δb z y))))

scal-1 : scal {n} 1# ≐ Idₒ
scal-1 x y = *-identityˡ (δb x y)

scal-⊙ˡ : (c : A) (M : Op n) → (scal c ⊙ M) ≐ (λ x y → c * M x y)
scal-⊙ˡ c M x y =
  Eq.trans (Σ-cong {f = λ z → (c * δb x z) * M z y}
                    {g = λ z → c * (δb x z * M z y)}
                    (λ z → *-assoc c (δb x z) (M z y)))
    (Eq.trans (Σ-scaleˡ c (λ z → δb x z * M z y))
      (Eq.cong (c *_) (Σ-δˡ x (λ z → M z y))))

scal-⊙ʳ : (c : A) (M : Op n) → (M ⊙ scal c) ≐ (λ x y → c * M x y)
scal-⊙ʳ c M x y =
  Eq.trans (Σ-cong {f = λ z → M x z * (c * δb z y)}
                    {g = λ z → (M x z * δb z y) * c}
                    (λ z → Eq.trans (Eq.cong (M x z *_) (*-comm c (δb z y)))
                                    (Eq.sym (*-assoc (M x z) (δb z y) c))))
    (Eq.trans (Σ-scaleʳ c (λ z → M x z * δb z y))
      (Eq.trans (Eq.cong (_* c) (Σ-δʳ y (λ z → M x z))) (*-comm (M x y) c)))

scal-central : (c : A) (M : Op n) → (scal c ⊙ M) ≐ (M ⊙ scal c)
scal-central c M = ≐-trans (scal-⊙ˡ c M) (≐-sym (scal-⊙ʳ c M))

------------------------------------------------------------------------
-- The Kronecker product

tensor-cong : {M M' : Op m} {N N' : Op n} → M ≐ M' → N ≐ N' → tensor M N ≐ tensor M' N'
tensor-cong {zero}  e f x       y       = Eq.cong₂ _*_ (e [] []) (f x y)
tensor-cong {suc m} {n} {M} {M'} e f (a ∷ x) (b ∷ y) =
  tensor-cong {m} {n} {λ u v → M (a ∷ u) (b ∷ v)} {λ u v → M' (a ∷ u) (b ∷ v)}
              (λ u v → e (a ∷ u) (b ∷ v)) f x y

tensor-addˡ : (P Q : Op m) (N : Op n) → ∀ x y →
              tensor (λ u v → P u v + Q u v) N x y ≡ tensor P N x y + tensor Q N x y
tensor-addˡ {zero}  P Q N x       y       = distribʳ (N x y) (P [] []) (Q [] [])
tensor-addˡ {suc m} P Q N (a ∷ x) (b ∷ y) =
  tensor-addˡ {m} (λ u v → P (a ∷ u) (b ∷ v)) (λ u v → Q (a ∷ u) (b ∷ v)) N x y

-- The mixed product law.
tensor-⊙ : (M P : Op m) (N Q : Op n) → (tensor M N ⊙ tensor P Q) ≐ tensor (M ⊙ P) (N ⊙ Q)
tensor-⊙ {zero} M P N Q x y =
  Eq.trans (Σ-cong {f = λ z → (M [] [] * N x z) * (P [] [] * Q z y)}
                    {g = λ z → (M [] [] * P [] []) * (N x z * Q z y)}
                    (λ z → cross (M [] []) (N x z) (P [] []) (Q z y)))
           (Σ-scaleˡ (M [] [] * P [] []) (λ z → N x z * Q z y))
tensor-⊙ {suc m} {n} M P N Q (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong₂ _+_
             (tensor-⊙ {m} {n} (λ u v → M (a ∷ u) (false ∷ v)) (λ u v → P (false ∷ u) (b ∷ v)) N Q x y)
             (tensor-⊙ {m} {n} (λ u v → M (a ∷ u) (true ∷ v)) (λ u v → P (true ∷ u) (b ∷ v)) N Q x y))
           (Eq.sym (tensor-addˡ {m}
                      (λ u v → Σb (λ w → M (a ∷ u) (false ∷ w) * P (false ∷ w) (b ∷ v)))
                      (λ u v → Σb (λ w → M (a ∷ u) (true ∷ w) * P (true ∷ w) (b ∷ v)))
                      (N ⊙ Q) x y))

tensor-zeroˡ : (N : Op n) → ∀ (x y : Bits (m +ℕ n)) → tensor {m} (λ _ _ → 0#) N x y ≡ 0#
tensor-zeroˡ {m = zero}  N x       y       = zeroˡ (N x y)
tensor-zeroˡ {m = suc m} N (a ∷ x) (b ∷ y) = tensor-zeroˡ {m = m} N x y

tensor-Id : Idₒ {m +ℕ n} ≐ tensor (Idₒ {m}) (Idₒ {n})
tensor-Id {zero}                    x           y           = Eq.sym (*-identityˡ (δb x y))
tensor-Id {suc m}       (true ∷ x)  (true ∷ y)  = tensor-Id {m} x y
tensor-Id {suc m}       (false ∷ x) (false ∷ y) = tensor-Id {m} x y
tensor-Id {suc m} {n}   (true ∷ x)  (false ∷ y) = Eq.sym (tensor-zeroˡ {n} {m} Idₒ x y)
tensor-Id {suc m} {n}   (false ∷ x) (true ∷ y)  = Eq.sym (tensor-zeroˡ {n} {m} Idₒ x y)

tensor-scaleˡ : (c : A) (B : Op m) (C : Op n) → ∀ x y →
                tensor (λ u v → c * B u v) C x y ≡ c * tensor B C x y
tensor-scaleˡ {zero}  c B C x       y       = *-assoc c (B [] []) (C x y)
tensor-scaleˡ {suc m} c B C (a ∷ x) (b ∷ y) = tensor-scaleˡ {m} c (λ u v → B (a ∷ u) (b ∷ v)) C x y

tensor-scaleʳ : (c : A) (B : Op m) (C : Op n) → ∀ x y →
                tensor B (λ u v → c * C u v) x y ≡ c * tensor B C x y
tensor-scaleʳ {zero}  c B C x       y       =
  Eq.trans (Eq.sym (*-assoc (B [] []) c (C x y)))
    (Eq.trans (Eq.cong (_* C x y) (*-comm (B [] []) c)) (*-assoc c (B [] []) (C x y)))
tensor-scaleʳ {suc m} c B C (a ∷ x) (b ∷ y) = tensor-scaleʳ {m} c (λ u v → B (a ∷ u) (b ∷ v)) C x y

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
emb-⊙ {k} {n} M N = ≐-trans (tensor-⊙ M N Idₒ Idₒ) (tensor-cong (≐-refl (M ⊙ N)) (⊙-identityˡ Idₒ))

emb-id : emb {k} {n} Idₒ ≐ Idₒ
emb-id {k} {n} = ≐-sym (tensor-Id {m = k} {n = n})

up-⊙ : (M N : Op n) → (up M ⊙ up N) ≐ up (M ⊙ N)
up-⊙ M N = ≐-trans (tensor-⊙ Idₒ Idₒ M N) (tensor-cong (⊙-identityˡ Idₒ) (≐-refl (M ⊙ N)))

up-Id : up (Idₒ {n}) ≐ Idₒ
up-Id {n} = ≐-sym (tensor-Id {m = 1} {n = n})

-- A gate on the bottom k wires commutes with an operator shifted past
-- them.
emb-up-comm : (M : Op k) (N : Op n) → (emb {k} {n} M ⊙ upk k N) ≐ (upk k N ⊙ emb M)
emb-up-comm {k} {n} M N =
  ≐-trans (tensor-⊙ M Idₒ Idₒ N)
    (≐-trans (tensor-cong (⊙-identityʳ M) (⊙-identityˡ N))
      (≐-trans (tensor-cong (≐-sym (⊙-identityˡ M)) (≐-sym (⊙-identityʳ N)))
               (≐-sym (tensor-⊙ Idₒ M N Idₒ))))

up-up : (M : Op n) → up (up M) ≐ upk 2 M
up-up M (a ∷ b ∷ x) (a' ∷ b' ∷ y) =
  Eq.sym (Eq.trans (Eq.cong (_* M x y) (tensor-Id {1} {1} (a ∷ b ∷ []) (a' ∷ b' ∷ [])))
                   (*-assoc (δb (a ∷ []) (a' ∷ [])) (δb (b ∷ []) (b' ∷ [])) (M x y)))

-- Scalars are local, and the same on every wire.
tensor-scal : (c : A) → tensor (scal {m} c) (Idₒ {n}) ≐ scal {m +ℕ n} c
tensor-scal {zero} c x y = Eq.cong (_* δb x y) (*-identityʳ c)
tensor-scal {suc m} c (true ∷ x)  (true ∷ y)  = tensor-scal {m} c x y
tensor-scal {suc m} c (false ∷ x) (false ∷ y) = tensor-scal {m} c x y
tensor-scal {suc m} {n} c (true ∷ x) (false ∷ y) =
  Eq.trans (tensor-cong {m = m} {n = n} {M = λ u v → c * δb (true ∷ u) (false ∷ v)} {M' = λ _ _ → 0#}
                        (λ u v → zeroʳ c) (≐-refl Idₒ) x y)
    (Eq.trans (tensor-zeroˡ {n = n} {m = m} Idₒ x y) (Eq.sym (zeroʳ c)))
tensor-scal {suc m} {n} c (false ∷ x) (true ∷ y) =
  Eq.trans (tensor-cong {m = m} {n = n} {M = λ u v → c * δb (false ∷ u) (true ∷ v)} {M' = λ _ _ → 0#}
                        (λ u v → zeroʳ c) (≐-refl Idₒ) x y)
    (Eq.trans (tensor-zeroˡ {n = n} {m = m} Idₒ x y) (Eq.sym (zeroʳ c)))

up-scal : (c : A) → up (scal {n} c) ≐ scal c
up-scal c (true ∷ x)  (true ∷ y)  = *-identityˡ (c * δb x y)
up-scal c (false ∷ x) (false ∷ y) = *-identityˡ (c * δb x y)
up-scal c (true ∷ x)  (false ∷ y) = Eq.trans (zeroˡ (c * δb x y)) (Eq.sym (zeroʳ c))
up-scal c (false ∷ x) (true ∷ y)  = Eq.trans (zeroˡ (c * δb x y)) (Eq.sym (zeroʳ c))

tensor-assoc₁ : (P : Op 1) (B : Op m) (C : Op n) → tensor (tensor P B) C ≐ tensor P (tensor B C)
tensor-assoc₁ P B C (a ∷ x) (b ∷ y) = tensor-scaleˡ (P (a ∷ []) (b ∷ [])) B C x y

tensor-assoc₂ : (P : Op 2) (B : Op m) (C : Op n) → tensor (tensor P B) C ≐ tensor P (tensor B C)
tensor-assoc₂ P B C (a ∷ a' ∷ x) (b ∷ b' ∷ y) = tensor-scaleˡ (P (a ∷ a' ∷ []) (b ∷ b' ∷ [])) B C x y

-- A gate read on a wider block.
emb-pad₁ : (M : Op 1) → emb {1} {m +ℕ n} M ≐ emb {suc m} {n} (tensor M (Idₒ {m}))
emb-pad₁ {m} {n} M =
  ≐-trans (tensor-cong {m = 1} {n = m +ℕ n} (≐-refl M) (tensor-Id {m} {n}))
          (≐-sym (tensor-assoc₁ M (Idₒ {m}) (Idₒ {n})))

emb-pad₂ : (M : Op 2) → emb {2} {m +ℕ n} M ≐ emb {suc (suc m)} {n} (tensor M (Idₒ {m}))
emb-pad₂ {m} {n} M =
  ≐-trans (tensor-cong {m = 2} {n = m +ℕ n} (≐-refl M) (tensor-Id {m} {n}))
          (≐-sym (tensor-assoc₂ M (Idₒ {m}) (Idₒ {n})))

up-emb : (M : Op k) → up (emb {k} {n} M) ≐ emb {suc k} {n} (tensor (Idₒ {1}) M)
up-emb {k} {n} M = ≐-sym (tensor-assoc₁ (Idₒ {1}) M (Idₒ {n}))

scal-emb : (c : A) → scal {k +ℕ n} c ≐ emb {k} {n} (scal c)
scal-emb {k} {n} c = ≐-sym (tensor-scal {k} {n} c)
