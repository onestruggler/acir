------------------------------------------------------------------------
-- Presentations of groups
--
-- Operators on n qubits over ℤ[√2]: sums, matrices, Kronecker products
--
-- The algebra behind the matrix semantics of real-Clifford+CH circuits.
-- It is Examples.Groups.Clifford.Qubit.Model.Algebra with the
-- coefficient field ℤ/17ℤ replaced by the ring ℤ[√2] (Semantics.Ring):
-- that development models a FINITE group, for which a finite field that
-- happens to contain 1/√2 is a faithful model, whereas the group
-- presented here is infinite, and the entries have to be read where
-- they live.  Nothing else changes, and the layering is the same:
--
--   Σb          finite sums over Bits n, with the linearity, exchange
--               and delta-collapse laws that everything else rests on;
--   Op / _⊙_    the operator monoid, uniform in n, with POINTWISE
--               equality _≐_;
--   Mat / ix    tries, where the concrete relations are computed and
--               compared by `refl`.
--
-- An operator on n wires is a matrix indexed by bit vectors,
--
--     Op n = Bits n → Bits n → 𝔽,
--
-- wire 0 first, with the usual product ∑ M x z · N z y.  Indexing by
-- bit vectors keeps the tensor structure free: the Kronecker product
-- splits a bit vector by peeling bits, so it needs no index arithmetic.
--
-- Operators are functions, which is right for the structural lemmas
-- but wrong for computing, so the concrete gates are stored as tries
-- (Tab / Mat), where a product is built once as data.  `ix` bridges
-- the two, `ix-mul` says the bridge respects products, and `mat-ext`
-- says a trie is determined by its entries — which is what turns a
-- pointwise equality of operators back into a `refl`-checkable one.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Semantics.Algebra where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable using (yes ; no)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford+CH.Semantics.Ring public

private
  variable
    k l m n : ℕ

------------------------------------------------------------------------
-- The coefficients and the index type

𝔽 : Set
𝔽 = ℤ√2

Bits : ℕ → Set
Bits n = Vec Bool n

δ₁ : Bool → Bool → 𝔽
δ₁ true  true  = 1#
δ₁ false false = 1#
δ₁ _     _     = 0#

δb : Bits n → Bits n → 𝔽
δb []           []           = 1#
δb (true  ∷ xs) (true  ∷ ys) = δb xs ys
δb (false ∷ xs) (false ∷ ys) = δb xs ys
δb (_ ∷ _)      (_ ∷ _)      = 0#

-- Sum over all 2ⁿ bit vectors.
Σb : (Bits n → 𝔽) → 𝔽
Σb {₀}    f = f []
Σb {₁₊ n} f = Σb (λ bs → f (false ∷ bs)) + Σb (λ bs → f (true ∷ bs))

------------------------------------------------------------------------
-- The laws of Σb

Σ-cong : {f g : Bits n → 𝔽} → (∀ x → f x ≡ g x) → Σb f ≡ Σb g
Σ-cong {₀}          e = e []
Σ-cong {₁₊ n} {f} {g} e =
  Eq.cong₂ _+_
    (Σ-cong {n} {λ bs → f (false ∷ bs)} {λ bs → g (false ∷ bs)}
            (λ bs → e (false ∷ bs)))
    (Σ-cong {n} {λ bs → f (true ∷ bs)} {λ bs → g (true ∷ bs)}
            (λ bs → e (true ∷ bs)))

Σ-zero : Σb {n} (λ _ → 0#) ≡ 0#
Σ-zero {₀}    = Eq.refl
Σ-zero {₁₊ n} = Eq.trans (Eq.cong₂ _+_ (Σ-zero {n}) (Σ-zero {n})) (+-identityʳ 0#)

Σ-scaleˡ : (c : 𝔽) (f : Bits n → 𝔽) → Σb (λ z → c * f z) ≡ c * Σb f
Σ-scaleˡ {₀}    c f = Eq.refl
Σ-scaleˡ {₁₊ n} c f =
  Eq.trans (Eq.cong₂ _+_ (Σ-scaleˡ {n} c (λ bs → f (false ∷ bs)))
                         (Σ-scaleˡ {n} c (λ bs → f (true ∷ bs))))
           (Eq.sym (*-distribˡ-+ c (Σb (λ bs → f (false ∷ bs)))
                                   (Σb (λ bs → f (true ∷ bs)))))

Σ-scaleʳ : (c : 𝔽) (f : Bits n → 𝔽) → Σb (λ z → f z * c) ≡ Σb f * c
Σ-scaleʳ {₀}    c f = Eq.refl
Σ-scaleʳ {₁₊ n} c f =
  Eq.trans (Eq.cong₂ _+_ (Σ-scaleʳ {n} c (λ bs → f (false ∷ bs)))
                         (Σ-scaleʳ {n} c (λ bs → f (true ∷ bs))))
           (Eq.sym (*-distribʳ-+ c (Σb (λ bs → f (false ∷ bs)))
                                   (Σb (λ bs → f (true ∷ bs)))))

Σ-add : (f g : Bits n → 𝔽) → Σb (λ z → f z + g z) ≡ Σb f + Σb g
Σ-add {₀}    f g = Eq.refl
Σ-add {₁₊ n} f g =
  Eq.trans (Eq.cong₂ _+_
             (Σ-add {n} (λ bs → f (false ∷ bs)) (λ bs → g (false ∷ bs)))
             (Σ-add {n} (λ bs → f (true ∷ bs)) (λ bs → g (true ∷ bs))))
           (+-shuffle (Σb (λ bs → f (false ∷ bs))) (Σb (λ bs → g (false ∷ bs)))
                      (Σb (λ bs → f (true ∷ bs)))  (Σb (λ bs → g (true ∷ bs))))

Σ-swap : (F : Bits m → Bits n → 𝔽) →
         Σb (λ x → Σb (λ y → F x y)) ≡ Σb (λ y → Σb (λ x → F x y))
Σ-swap {₀}    F = Eq.refl
Σ-swap {₁₊ m} F =
  Eq.trans (Eq.cong₂ _+_ (Σ-swap {m} (λ xs → F (false ∷ xs)))
                         (Σ-swap {m} (λ xs → F (true ∷ xs))))
           (Eq.sym (Σ-add (λ y → Σb (λ xs → F (false ∷ xs) y))
                          (λ y → Σb (λ xs → F (true ∷ xs) y))))

-- The delta collapses a sum, on either side.  These are what make a
-- gate's idle wires disappear.
Σ-δˡ : (x : Bits n) (f : Bits n → 𝔽) → Σb (λ z → δb x z * f z) ≡ f x
Σ-δˡ []                 f = *-identityˡ (f [])
Σ-δˡ {₁₊ n} (false ∷ xs) f =
  Eq.trans (Eq.cong₂ _+_
             (Σ-δˡ xs (λ zs → f (false ∷ zs)))
             (Eq.trans (Σ-cong {n} {λ zs → 0# * f (true ∷ zs)} {λ _ → 0#}
                               (λ zs → *-zeroˡ (f (true ∷ zs))))
                       (Σ-zero {n})))
           (+-identityʳ (f (false ∷ xs)))
Σ-δˡ {₁₊ n} (true ∷ xs)  f =
  Eq.trans (Eq.cong₂ _+_
             (Eq.trans (Σ-cong {n} {λ zs → 0# * f (false ∷ zs)} {λ _ → 0#}
                               (λ zs → *-zeroˡ (f (false ∷ zs))))
                       (Σ-zero {n}))
             (Σ-δˡ xs (λ zs → f (true ∷ zs))))
           (+-identityˡ (f (true ∷ xs)))

Σ-δʳ : (y : Bits n) (f : Bits n → 𝔽) → Σb (λ z → f z * δb z y) ≡ f y
Σ-δʳ []                 f = *-identityʳ (f [])
Σ-δʳ {₁₊ n} (false ∷ ys) f =
  Eq.trans (Eq.cong₂ _+_
             (Σ-δʳ ys (λ zs → f (false ∷ zs)))
             (Eq.trans (Σ-cong {n} {λ zs → f (true ∷ zs) * 0#} {λ _ → 0#}
                               (λ zs → *-zeroʳ (f (true ∷ zs))))
                       (Σ-zero {n})))
           (+-identityʳ (f (false ∷ ys)))
Σ-δʳ {₁₊ n} (true ∷ ys)  f =
  Eq.trans (Eq.cong₂ _+_
             (Eq.trans (Σ-cong {n} {λ zs → f (false ∷ zs) * 0#} {λ _ → 0#}
                               (λ zs → *-zeroʳ (f (false ∷ zs))))
                       (Σ-zero {n}))
             (Σ-δʳ ys (λ zs → f (true ∷ zs))))
           (+-identityˡ (f (true ∷ ys)))

-- The delta is symmetric.
δb-sym : (x y : Bits n) → δb x y ≡ δb y x
δb-sym []           []           = Eq.refl
δb-sym (true ∷ xs)  (true ∷ ys)  = δb-sym xs ys
δb-sym (false ∷ xs) (false ∷ ys) = δb-sym xs ys
δb-sym (true ∷ xs)  (false ∷ ys) = Eq.refl
δb-sym (false ∷ xs) (true ∷ ys)  = Eq.refl

δb-refl : (x : Bits n) → δb x x ≡ 1#
δb-refl []           = Eq.refl
δb-refl (true ∷ xs)  = δb-refl xs
δb-refl (false ∷ xs) = δb-refl xs

------------------------------------------------------------------------
-- Operators
--
-- Equality is pointwise: the model is a setoid, which costs nothing —
-- soundness is proved by hand, not through a bundle — and saves
-- extensionality.

infixl 7 _⊙_
infix 4 _≐_

Op : ℕ → Set
Op n = Bits n → Bits n → 𝔽

_≐_ : Op n → Op n → Set
M ≐ N = ∀ x y → M x y ≡ N x y

_⊙_ : Op n → Op n → Op n
(M ⊙ N) x y = Σb (λ z → M x z * N z y)

Idₒ : Op n
Idₒ = δb

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

-- The two Σ-congs name their target functions: the endpoints are sums of
-- sums, and Agda will not guess them from a proof term.
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

scal : 𝔽 → Op n
scal c x y = c * δb x y

scal-⊙ : (a b : 𝔽) → (scal {n} a ⊙ scal b) ≐ scal (a * b)
scal-⊙ a b x y =
  Eq.trans (Σ-cong {f = λ z → (a * δb x z) * (b * δb z y)}
                    {g = λ z → (a * b) * (δb x z * δb z y)}
                    (λ z → *-cross a (δb x z) b (δb z y)))
    (Eq.trans (Σ-scaleˡ (a * b) (λ z → δb x z * δb z y))
              (Eq.cong ((a * b) *_) (Σ-δˡ x (λ z → δb z y))))

scal-1 : scal {n} 1# ≐ Idₒ
scal-1 x y = *-identityˡ (δb x y)

scal-central : (c : 𝔽) (M : Op n) → (scal c ⊙ M) ≐ (M ⊙ scal c)
scal-central c M x y =
  Eq.trans (Σ-cong {f = λ z → (c * δb x z) * M z y}
                    {g = λ z → c * (δb x z * M z y)}
                    (λ z → *-assoc c (δb x z) (M z y)))
    (Eq.trans (Σ-scaleˡ c (λ z → δb x z * M z y))
      (Eq.trans (Eq.cong (c *_) (Σ-δˡ x (λ z → M z y)))
        (Eq.trans (*-comm c (M x y))
          (Eq.trans (Eq.cong (_* c) (Eq.sym (Σ-δʳ y (λ z → M x z))))
            (Eq.trans (Eq.sym (Σ-scaleʳ c (λ z → M x z * δb z y)))
              (Σ-cong {f = λ z → (M x z * δb z y) * c}
                       {g = λ z → M x z * (c * δb z y)}
                       (λ z → Eq.trans (*-assoc (M x z) (δb z y) c)
                                (Eq.cong (M x z *_) (*-comm (δb z y) c)))))))))

------------------------------------------------------------------------
-- The Kronecker product
--
-- tensor M N acts on the first m wires by M and on the rest by N.  It is
-- defined by peeling bits, so it computes with no index arithmetic.

tensor : Op m → Op n → Op (m +ℕ n)
tensor {₀}    M N x       y       = M [] [] * N x y
tensor {₁₊ m} M N (a ∷ x) (b ∷ y) = tensor (λ u v → M (a ∷ u) (b ∷ v)) N x y

tensor-cong : {M M' : Op m} {N N' : Op n} →
              M ≐ M' → N ≐ N' → tensor M N ≐ tensor M' N'
tensor-cong {₀}    e f x       y       = Eq.cong₂ _*_ (e [] []) (f x y)
tensor-cong {₁₊ m} {n} {M} {M'} e f (a ∷ x) (b ∷ y) =
  tensor-cong {m} {n} {λ u v → M (a ∷ u) (b ∷ v)} {λ u v → M' (a ∷ u) (b ∷ v)}
              (λ u v → e (a ∷ u) (b ∷ v)) f x y

-- The first factor is additive, which is the step case of the mixed
-- product law: a product of operators is a sum over the wire it acts on.
tensor-addˡ : (A B : Op m) (N : Op n) → ∀ x y →
              tensor (λ u v → A u v + B u v) N x y ≡
              tensor A N x y + tensor B N x y
tensor-addˡ {₀}    A B N x       y       = *-distribʳ-+ (N x y) (A [] []) (B [] [])
tensor-addˡ {₁₊ m} A B N (a ∷ x) (b ∷ y) =
  tensor-addˡ {m} (λ u v → A (a ∷ u) (b ∷ v)) (λ u v → B (a ∷ u) (b ∷ v)) N x y

-- The mixed product law.  Everything about disjoint wires follows from
-- it: with N = Id or M = Id it says that a gate and a shifted operator
-- commute, both products being M ⊗ N.
tensor-⊙ : (M P : Op m) (N Q : Op n) →
           (tensor M N ⊙ tensor P Q) ≐ tensor (M ⊙ P) (N ⊙ Q)
tensor-⊙ {₀} M P N Q x y =
  Eq.trans (Σ-cong {f = λ z → (M [] [] * N x z) * (P [] [] * Q z y)}
                    {g = λ z → (M [] [] * P [] []) * (N x z * Q z y)}
                    (λ z → *-cross (M [] []) (N x z) (P [] []) (Q z y)))
           (Σ-scaleˡ (M [] [] * P [] []) (λ z → N x z * Q z y))
tensor-⊙ {₁₊ m} {n} M P N Q (a ∷ x) (b ∷ y) =
  Eq.trans (Eq.cong₂ _+_
             (tensor-⊙ {m} {n} (λ u v → M (a ∷ u) (false ∷ v))
                               (λ u v → P (false ∷ u) (b ∷ v)) N Q x y)
             (tensor-⊙ {m} {n} (λ u v → M (a ∷ u) (true ∷ v))
                               (λ u v → P (true ∷ u) (b ∷ v)) N Q x y))
           (Eq.sym (tensor-addˡ {m}
                      (λ u v → Σb (λ w → M (a ∷ u) (false ∷ w) * P (false ∷ w) (b ∷ v)))
                      (λ u v → Σb (λ w → M (a ∷ u) (true ∷ w) * P (true ∷ w) (b ∷ v)))
                      (N ⊙ Q) x y))

-- A zero block stays zero, which is the off-diagonal half of tensor-Id.
tensor-zeroˡ : (N : Op n) → ∀ (x y : Bits (m +ℕ n)) →
               tensor {m} (λ _ _ → 0#) N x y ≡ 0#
tensor-zeroˡ {m = ₀}    N x       y       = *-zeroˡ (N x y)
tensor-zeroˡ {m = ₁₊ m} N (a ∷ x) (b ∷ y) = tensor-zeroˡ {m = m} N x y

tensor-Id : Idₒ {m +ℕ n} ≐ tensor (Idₒ {m}) (Idₒ {n})
tensor-Id {₀}                x           y           = Eq.sym (*-identityˡ (δb x y))
tensor-Id {₁₊ m} (true ∷ x)  (true ∷ y)  = tensor-Id {m} x y
tensor-Id {₁₊ m} (false ∷ x) (false ∷ y) = tensor-Id {m} x y
tensor-Id {₁₊ m} {n} (true ∷ x)  (false ∷ y) =
  Eq.sym (tensor-zeroˡ {n} {m} Idₒ x y)
tensor-Id {₁₊ m} {n} (false ∷ x) (true ∷ y)  =
  Eq.sym (tensor-zeroˡ {n} {m} Idₒ x y)

------------------------------------------------------------------------
-- Matrices as tries
--
-- Storage for the concrete gates.  A Tab of depth k is a complete binary
-- tree of 2ᵏ leaves, indexed by Bits k; a Mat is a Tab of Tabs.  Because
-- a product is built as DATA, an entry of a long product is computed
-- once rather than once per demand.

Tab : ℕ → Set → Set
Tab ₀      A = A
Tab (₁₊ k) A = Tab k A × Tab k A

tab : (k : ℕ) {A : Set} → (Bits k → A) → Tab k A
tab ₀      f = f []
tab (₁₊ k) f = tab k (λ bs → f (false ∷ bs)) , tab k (λ bs → f (true ∷ bs))

get : {A : Set} → Tab k A → Bits k → A
get {k = ₀}    t       []           = t
get {k = ₁₊ k} (l , r) (false ∷ bs) = get l bs
get {k = ₁₊ k} (l , r) (true  ∷ bs) = get r bs

get-tab : (k : ℕ) {A : Set} (f : Bits k → A) (x : Bits k) → get (tab k f) x ≡ f x
get-tab ₀      f []           = Eq.refl
get-tab (₁₊ k) f (false ∷ bs) = get-tab k (λ cs → f (false ∷ cs)) bs
get-tab (₁₊ k) f (true  ∷ bs) = get-tab k (λ cs → f (true ∷ cs)) bs

-- A trie is determined by its entries.
tab-ext : (k : ℕ) {A : Set} (s t : Tab k A) →
          (∀ x → get {k} {A} s x ≡ get {k} {A} t x) → s ≡ t
tab-ext ₀      s       t         e = e []
tab-ext (₁₊ k) {A} (l , r) (l' , r') e =
  Eq.cong₂ _,_ (tab-ext k {A} l l' (λ x → e (false ∷ x)))
               (tab-ext k {A} r r' (λ x → e (true ∷ x)))

-- Tries over a set with decidable equality have decidable equality.
tab-dec : (k : ℕ) {A : Set} → DecidableEquality A → DecidableEquality (Tab k A)
tab-dec ₀      _≟A_ s       t         = s ≟A t
tab-dec (₁₊ k) _≟A_ (l , r) (l' , r') with tab-dec k _≟A_ l l' | tab-dec k _≟A_ r r'
... | yes Eq.refl | yes Eq.refl = yes Eq.refl
... | no  l≢l'    | _           = no (λ e → l≢l' (Eq.cong proj₁ e))
... | _           | no  r≢r'    = no (λ e → r≢r' (Eq.cong proj₂ e))

-- Wrapped in a record so that the width is inferable: Tab is a
-- type-level function and its index cannot be read back off the type.
record Mat (k : ℕ) : Set where
  constructor mat
  field entries : Tab k (Tab k 𝔽)

open Mat public

ix : Mat k → Op k
ix M x y = get (get (entries M) x) y

-- Every stored entry is forced to literals (Ring.strict), so that a
-- product of stored matrices holds numbers, not the sums that produced
-- them.
matOf : Op k → Mat k
matOf {k} M = mat (tab k (λ x → tab k (λ y → strict (M x y))))

ix-matOf : (M : Op k) → ix (matOf M) ≐ M
ix-matOf {k} M x y =
  Eq.trans (Eq.cong (λ t → get t y) (get-tab k (λ u → tab k (λ v → strict (M u v))) x))
           (Eq.trans (get-tab k (λ v → strict (M x v)) y) (strict-id (M x y)))

-- Two stored matrices with the same entries are the same trie.
mat-ext : {M N : Mat k} → ix M ≐ ix N → M ≡ N
mat-ext {k} {mat s} {mat t} e =
  Eq.cong mat (tab-ext k {Tab k 𝔽} s t
    (λ x → tab-ext k {𝔽} (get {k} {Tab k 𝔽} s x) (get {k} {Tab k 𝔽} t x) (λ y → e x y)))

mat-dec : DecidableEquality (Mat k)
mat-dec {k} (mat s) (mat t) with tab-dec k (tab-dec k _≟_) s t
... | yes Eq.refl = yes Eq.refl
... | no  s≢t     = no (λ e → s≢t (Eq.cong entries e))

-- Product and identity, as tries.
mulM : Mat k → Mat k → Mat k
mulM M N = matOf (ix M ⊙ ix N)

idM : Mat k
idM = matOf Idₒ

ix-mul : (M N : Mat k) → ix (mulM M N) ≐ (ix M ⊙ ix N)
ix-mul M N = ix-matOf (ix M ⊙ ix N)

ix-id : ix (idM {k}) ≐ Idₒ
ix-id = ix-matOf Idₒ

-- The Kronecker product of two stored matrices.
tenM : Mat k → Mat l → Mat (k +ℕ l)
tenM M N = matOf (tensor (ix M) (ix N))

ix-tenM : (M : Mat k) (N : Mat l) → ix (tenM M N) ≐ tensor (ix M) (ix N)
ix-tenM M N = ix-matOf (tensor (ix M) (ix N))
