------------------------------------------------------------------------
-- Presentations of groups
--
-- EucDomain's matrices (Quantum.Synthesis.Matrix) over a commutative
-- ring A with an involutive conjugation adj: entries, the product as a
-- sum, and the laws that make the square matrices a monoid with an
-- anti-involution (the adjoint).
--
-- Everything is proved for an abstract A and instantiated at 𝔻[i]
-- (see Semantics), so that no proof has to unfold 𝔻[i]'s arithmetic.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_ ; lookup ; tabulate)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Decidable using (does)

open import Quantum.Synthesis.Matrix
  using (Matrix ; Matrix' ; unMatrix ; _·*·_ ; adjoint ; vector-transpose ; vector-repeat
        ; vector-zipwith ; vector-map ; SemiRingMatrix)
import Quantum.Synthesis.Ring.Properties.Hom as Hom
import Quantum.Synthesis.Ring.Properties.Common as Common

R : CommutativeRing _ _
R = record { isCommutativeRing = isCR }

module AR = CommutativeRing R

open import Algebra.Properties.Semiring.Sum AR.semiring public
  using (sum ; ∑-distrib-+ ; ∑-comm ; *-distribˡ-sum ; *-distribʳ-sum ; sum-cong-≗)

private
  module AdjL = Hom.Laws isCR (IsInvolutiveRingEndo.isRingEndo adjI)
  module S = Common.ZSolver R
  variable
    m n p : ℕ

open IsInvolutiveRingEndo adjI public
  using () renaming (f-+ to adj-+ ; f-* to adj-* ; f-1 to adj-1 ; involutive to adj-adj)
open AdjL public using () renaming (f-0 to adj-0 ; f-neg to adj-neg)

------------------------------------------------------------------------
-- Vectors

infixl 10 _!_

_!_ : {B : Set} → Vec B n → Fin n → B
_!_ = lookup

vec-ext : {B : Set} {u v : Vec B n} → (∀ x → u ! x ≡ v ! x) → u ≡ v
vec-ext {u = u} {v} eq =
  trans (sym (VecP.tabulate∘lookup u))
        (trans (VecP.tabulate-cong eq) (VecP.tabulate∘lookup v))

!-tabulate : {B : Set} (f : Fin n → B) (x : Fin n) → tabulate f ! x ≡ f x
!-tabulate f x = VecP.lookup∘tabulate f x

------------------------------------------------------------------------
-- Sums

sum-zero : (f : Fin n → A) → (∀ x → f x ≡ 0#) → sum f ≡ 0#
sum-zero {zero}  f z = refl
sum-zero {suc n} f z = begin
  f zero + sum (f ∘ suc)   ≡⟨ cong₂ _+_ (z zero) (sum-zero (f ∘ suc) (z ∘ suc)) ⟩
  0# + 0#                  ≡⟨ AR.+-identityˡ 0# ⟩
  0#                       ∎
  where open ≡-Reasoning

-- A sum over a function supported at a single point.
sum-single : (f : Fin n → A) (a : Fin n) → (∀ x → x ≢ a → f x ≡ 0#) → sum f ≡ f a
sum-single {suc n} f zero z = begin
  f zero + sum (f ∘ suc)   ≡⟨ cong (f zero +_) (sum-zero (f ∘ suc) (λ x → z (suc x) λ ())) ⟩
  f zero + 0#              ≡⟨ AR.+-identityʳ (f zero) ⟩
  f zero                   ∎
  where open ≡-Reasoning
sum-single {suc n} f (suc a) z = begin
  f zero + sum (f ∘ suc)   ≡⟨ cong₂ _+_ (z zero λ ()) (sum-single (f ∘ suc) a (λ x x≢a → z (suc x) (x≢a ∘ FinP.suc-injective))) ⟩
  0# + f (suc a)           ≡⟨ AR.+-identityˡ (f (suc a)) ⟩
  f (suc a)                ∎
  where open ≡-Reasoning

-- Kronecker's delta.
δ : Fin n → Fin n → A
δ x y with x FinP.≟ y
... | yes _ = 1#
... | no  _ = 0#

δ-refl : (x : Fin n) → δ x x ≡ 1#
δ-refl x with x FinP.≟ x
... | yes _ = refl
... | no  x≢x = contradiction refl x≢x
  where open import Relation.Nullary.Negation using (contradiction)

δ-≢ : {x y : Fin n} → x ≢ y → δ x y ≡ 0#
δ-≢ {x = x} {y} x≢y with x FinP.≟ y
... | yes x≡y = contradiction x≡y x≢y
  where open import Relation.Nullary.Negation using (contradiction)
... | no  _ = refl

δ-sym : (x y : Fin n) → δ x y ≡ δ y x
δ-sym x y with x FinP.≟ y | y FinP.≟ x
... | yes _ | yes _ = refl
... | no  _ | no  _ = refl
... | yes x≡y | no y≢x = contradiction (sym x≡y) y≢x
  where open import Relation.Nullary.Negation using (contradiction)
... | no x≢y | yes y≡x = contradiction (sym y≡x) x≢y
  where open import Relation.Nullary.Negation using (contradiction)

-- Summing against δ picks out one term.
sum-δˡ : (f : Fin n → A) (y : Fin n) → sum (λ x → δ y x * f x) ≡ f y
sum-δˡ f y = begin
  sum (λ x → δ y x * f x)   ≡⟨ sum-single (λ x → δ y x * f x) y
                                 (λ x x≢y → trans (cong (_* f x) (δ-≢ (x≢y ∘ sym))) (AR.zeroˡ (f x))) ⟩
  δ y y * f y               ≡⟨ cong (_* f y) (δ-refl y) ⟩
  1# * f y                  ≡⟨ AR.*-identityˡ (f y) ⟩
  f y                       ∎
  where open ≡-Reasoning

sum-δʳ : (f : Fin n → A) (y : Fin n) → sum (λ x → f x * δ x y) ≡ f y
sum-δʳ f y = trans (sum-cong-≗ (λ x → trans (AR.*-comm (f x) (δ x y)) (cong (_* f x) (δ-sym x y))))
                   (sum-δˡ f y)

-- Conjugation commutes with sums.
adj-sum : (f : Fin n → A) → adj (sum f) ≡ sum (adj ∘ f)
adj-sum {zero} f = adj-0
adj-sum {suc n} f = trans (adj-+ (f zero) (sum (f ∘ suc))) (cong (adj (f zero) +_) (adj-sum (f ∘ suc)))

------------------------------------------------------------------------
-- Matrices: columns and entries
--
-- EucDomain stores a matrix as its vector of columns.

col : Matrix m n A → Fin n → Vec A m
col M c = unMatrix M ! c

ent : Matrix m n A → Fin m → Fin n → A
ent M r c = col M c ! r

mat-ext : {M N : Matrix m n A} → (∀ r c → ent M r c ≡ ent N r c) → M ≡ N
mat-ext {M = Matrix' a} {Matrix' b} eq =
  cong Matrix' (vec-ext (λ c → vec-ext (λ r → eq r c)))

col-ext : {M N : Matrix m n A} → (∀ c → col M c ≡ col N c) → M ≡ N
col-ext {M = Matrix' a} {Matrix' b} eq = cong Matrix' (vec-ext eq)

-- The matrix with given entries.
mk : (Fin m → Fin n → A) → Matrix m n A
mk f = Matrix' (tabulate (λ c → tabulate (λ r → f r c)))

ent-mk : (f : Fin m → Fin n → A) (r : Fin m) (c : Fin n) → ent (mk f) r c ≡ f r c
ent-mk f r c = trans (cong (_! r) (!-tabulate (λ c → tabulate (λ r → f r c)) c))
                     (!-tabulate (λ r → f r c) r)

------------------------------------------------------------------------
-- The product
--
-- EucDomain's _·*·_ multiplies by columns with a helper local to its
-- definition.  Its value on one column, mv a v below, is that helper
-- definitionally, which is how the lemmas below get at it.

private
  mv : Vec (Vec A m) n → Vec A n → Vec A m
  mv a v = Vec.head (unMatrix (Matrix' a ·*· Matrix' (v ∷ [])))

  -- mv computes Σₓ vₓ · aₓ.
  mv-sum : (a : Vec (Vec A m) n) (v : Vec A n) (r : Fin m) →
           mv a v ! r ≡ sum (λ x → (v ! x) * (a ! x ! r))
  mv-sum [] [] r = VecP.lookup-replicate r 0#
  mv-sum (h ∷ []) (k ∷ []) r = begin
    Vec.map (k *_) h ! r          ≡⟨ VecP.lookup-map r (k *_) h ⟩
    k * (h ! r)                   ≡⟨ sym (AR.+-identityʳ _) ⟩
    k * (h ! r) + 0#              ∎
    where open ≡-Reasoning
  mv-sum (h ∷ t@(_ ∷ _)) (k ∷ s) r = begin
    Vec.zipWith _+_ (Vec.map (k *_) h) (mv t s) ! r
      ≡⟨ VecP.lookup-zipWith _+_ r (Vec.map (k *_) h) (mv t s) ⟩
    (Vec.map (k *_) h ! r) + (mv t s ! r)
      ≡⟨ cong₂ _+_ (VecP.lookup-map r (k *_) h) (mv-sum t s r) ⟩
    k * (h ! r) + sum (λ x → (s ! x) * (t ! x ! r))
      ∎
    where open ≡-Reasoning

  -- The columns of a product.
  col-·*· : (a : Vec (Vec A m) n) (b : Vec (Vec A n) p) (c : Fin p) →
            col (Matrix' a ·*· Matrix' b) c ≡ mv a (b ! c)
  col-·*· a (v ∷ b) zero = refl
  col-·*· a (v ∷ b) (suc c) = col-·*· a b c

-- The entries of a product.
ent-·*· : (M : Matrix m n A) (N : Matrix n p A) (r : Fin m) (c : Fin p) →
          ent (M ·*· N) r c ≡ sum (λ x → ent M r x * ent N x c)
ent-·*· (Matrix' a) (Matrix' b) r c = begin
  col (Matrix' a ·*· Matrix' b) c ! r         ≡⟨ cong (_! r) (col-·*· a b c) ⟩
  mv a (b ! c) ! r                            ≡⟨ mv-sum a (b ! c) r ⟩
  sum (λ x → (b ! c ! x) * (a ! x ! r))       ≡⟨ sum-cong-≗ (λ x → AR.*-comm (b ! c ! x) (a ! x ! r)) ⟩
  sum (λ x → (a ! x ! r) * (b ! c ! x))       ∎
  where open ≡-Reasoning

·*·-assoc : (L : Matrix m n A) (M : Matrix n p A) {q : ℕ} (N : Matrix p q A) →
            (L ·*· M) ·*· N ≡ L ·*· (M ·*· N)
·*·-assoc L M N = mat-ext λ r c → begin
  ent ((L ·*· M) ·*· N) r c
    ≡⟨ ent-·*· (L ·*· M) N r c ⟩
  sum (λ y → ent (L ·*· M) r y * ent N y c)
    ≡⟨ sum-cong-≗ (λ y → cong (_* ent N y c) (ent-·*· L M r y)) ⟩
  sum (λ y → sum (λ x → ent L r x * ent M x y) * ent N y c)
    ≡⟨ sum-cong-≗ (λ y → *-distribʳ-sum (ent N y c) (λ x → ent L r x * ent M x y)) ⟩
  sum (λ y → sum (λ x → (ent L r x * ent M x y) * ent N y c))
    ≡⟨ ∑-comm (λ y x → (ent L r x * ent M x y) * ent N y c) ⟩
  sum (λ x → sum (λ y → (ent L r x * ent M x y) * ent N y c))
    ≡⟨ sum-cong-≗ (λ x → sum-cong-≗ (λ y → AR.*-assoc (ent L r x) (ent M x y) (ent N y c))) ⟩
  sum (λ x → sum (λ y → ent L r x * (ent M x y * ent N y c)))
    ≡⟨ sum-cong-≗ (λ x → sym (*-distribˡ-sum (ent L r x) (λ y → ent M x y * ent N y c))) ⟩
  sum (λ x → ent L r x * sum (λ y → ent M x y * ent N y c))
    ≡⟨ sum-cong-≗ (λ x → cong (ent L r x *_) (sym (ent-·*· M N x c))) ⟩
  sum (λ x → ent L r x * ent (M ·*· N) x c)
    ≡⟨ sym (ent-·*· L (M ·*· N) r c) ⟩
  ent (L ·*· (M ·*· N)) r c
    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The identity

-- The identity matrix.
𝕀 : Matrix n n A
𝕀 = mk δ

ent-𝕀 : (r c : Fin n) → ent (𝕀 {n}) r c ≡ δ r c
ent-𝕀 = ent-mk δ

·*·-identityˡ : (M : Matrix n p A) → 𝕀 ·*· M ≡ M
·*·-identityˡ M = mat-ext λ r c →
  trans (ent-·*· 𝕀 M r c)
        (trans (sum-cong-≗ (λ x → cong (_* ent M x c) (ent-𝕀 r x))) (sum-δˡ (λ x → ent M x c) r))

·*·-identityʳ : (M : Matrix m n A) → M ·*· 𝕀 ≡ M
·*·-identityʳ M = mat-ext λ r c →
  trans (ent-·*· M 𝕀 r c)
        (trans (sum-cong-≗ (λ x → cong (ent M r x *_) (ent-𝕀 x c))) (sum-δʳ (λ x → ent M r x) c))

------------------------------------------------------------------------
-- The adjoint

private
  -- Transposition by lookups.
  transpose-! : ∀ {k l} (a : Vec (Vec A k) l) (r : Fin k) (c : Fin l) →
                vector-transpose a ! r ! c ≡ a ! c ! r
  transpose-! (h ∷ t) r zero = begin
    Vec.zipWith _∷_ h (vector-transpose t) ! r ! zero
      ≡⟨ cong (λ v → v ! zero) (VecP.lookup-zipWith _∷_ r h (vector-transpose t)) ⟩
    h ! r ∎
    where open ≡-Reasoning
  transpose-! (h ∷ t) r (suc c) = begin
    Vec.zipWith _∷_ h (vector-transpose t) ! r ! suc c
      ≡⟨ cong (λ v → v ! suc c) (VecP.lookup-zipWith _∷_ r h (vector-transpose t)) ⟩
    vector-transpose t ! r ! c
      ≡⟨ transpose-! t r c ⟩
    t ! c ! r ∎
    where open ≡-Reasoning

ent-adjoint : (M : Matrix m n A) (r : Fin n) (c : Fin m) → ent (adjoint M) r c ≡ adj (ent M c r)
ent-adjoint (Matrix' a) r c = begin
  vector-transpose (Vec.map (Vec.map adj) a) ! c ! r
    ≡⟨ transpose-! (Vec.map (Vec.map adj) a) c r ⟩
  Vec.map (Vec.map adj) a ! r ! c
    ≡⟨ cong (_! c) (VecP.lookup-map r (Vec.map adj) a) ⟩
  Vec.map adj (a ! r) ! c
    ≡⟨ VecP.lookup-map c adj (a ! r) ⟩
  adj (a ! r ! c) ∎
  where open ≡-Reasoning

adjoint-involutive : (M : Matrix m n A) → adjoint (adjoint M) ≡ M
adjoint-involutive M = mat-ext λ r c →
  trans (ent-adjoint (adjoint M) r c) (trans (cong adj (ent-adjoint M c r)) (adj-adj (ent M r c)))

adjoint-𝕀 : adjoint (𝕀 {n}) ≡ 𝕀
adjoint-𝕀 = mat-ext λ r c → begin
  ent (adjoint 𝕀) r c   ≡⟨ ent-adjoint 𝕀 r c ⟩
  adj (ent 𝕀 c r)       ≡⟨ cong adj (ent-𝕀 c r) ⟩
  adj (δ c r)           ≡⟨ adj-δ c r ⟩
  δ c r                 ≡⟨ δ-sym c r ⟩
  δ r c                 ≡⟨ sym (ent-𝕀 r c) ⟩
  ent 𝕀 r c             ∎
  where
  open ≡-Reasoning
  adj-δ : (x y : Fin n) → adj (δ x y) ≡ δ x y
  adj-δ x y with x FinP.≟ y
  ... | yes _ = adj-1
  ... | no  _ = adj-0

adjoint-·*· : (M : Matrix m n A) (N : Matrix n p A) → adjoint (M ·*· N) ≡ adjoint N ·*· adjoint M
adjoint-·*· M N = mat-ext λ r c → begin
  ent (adjoint (M ·*· N)) r c
    ≡⟨ ent-adjoint (M ·*· N) r c ⟩
  adj (ent (M ·*· N) c r)
    ≡⟨ cong adj (ent-·*· M N c r) ⟩
  adj (sum (λ x → ent M c x * ent N x r))
    ≡⟨ adj-sum (λ x → ent M c x * ent N x r) ⟩
  sum (λ x → adj (ent M c x * ent N x r))
    ≡⟨ sum-cong-≗ (λ x → trans (adj-* (ent M c x) (ent N x r)) (AR.*-comm (adj (ent M c x)) (adj (ent N x r)))) ⟩
  sum (λ x → adj (ent N x r) * adj (ent M c x))
    ≡⟨ sum-cong-≗ (λ x → sym (cong₂ _*_ (ent-adjoint N r x) (ent-adjoint M x c))) ⟩
  sum (λ x → ent (adjoint N) r x * ent (adjoint M) x c)
    ≡⟨ sym (ent-·*· (adjoint N) (adjoint M) r c) ⟩
  ent (adjoint N ·*· adjoint M) r c
    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Sums over functions supported at two points

-- If g and f agree off {a, b}, their sums differ by what happens there.
sum-update : ∀ {n} (f g : Fin n → A) (a b : Fin n) → a ≢ b →
             (∀ x → x ≢ a → x ≢ b → g x ≡ f x) →
             g a + g b ≡ f a + f b → sum g ≡ sum f
sum-update {n} f g a b a≢b agree ab = begin
  sum g                              ≡⟨ sum-cong-≗ (λ x → sym (split x)) ⟩
  sum (λ x → h x + f x)              ≡⟨ ∑-distrib-+ h f ⟩
  sum h + sum f                      ≡⟨ cong (_+ sum f) sum-h ⟩
  0# + sum f                         ≡⟨ AR.+-identityˡ (sum f) ⟩
  sum f                              ∎
  where
  open ≡-Reasoning
  -- h = g - f, supported on {a, b}.
  h : Fin n → A
  h x = g x + - f x
  split : ∀ x → h x + f x ≡ g x
  split x = begin
    (g x + - f x) + f x      ≡⟨ AR.+-assoc (g x) (- f x) (f x) ⟩
    g x + (- f x + f x)      ≡⟨ cong (g x +_) (AR.-‿inverseˡ (f x)) ⟩
    g x + 0#                 ≡⟨ AR.+-identityʳ (g x) ⟩
    g x                      ∎
  h-zero : ∀ x → x ≢ a → x ≢ b → h x ≡ 0#
  h-zero x x≢a x≢b = trans (cong (_+ - f x) (agree x x≢a x≢b)) (AR.-‿inverseʳ (f x))
  -- h restricted to a and to the complement of a.
  hₐ hₒ : Fin n → A
  hₐ x with x FinP.≟ a
  ... | yes _ = h x
  ... | no  _ = 0#
  hₒ x with x FinP.≟ a
  ... | yes _ = 0#
  ... | no  _ = h x
  h≗ : ∀ x → h x ≡ hₐ x + hₒ x
  h≗ x with x FinP.≟ a
  ... | yes _ = sym (AR.+-identityʳ (h x))
  ... | no  _ = sym (AR.+-identityˡ (h x))
  hₐ-a : hₐ a ≡ h a
  hₐ-a with a FinP.≟ a
  ... | yes _ = refl
  ... | no a≢a = contradiction refl a≢a
    where open import Relation.Nullary.Negation using (contradiction)
  hₒ-b : hₒ b ≡ h b
  hₒ-b with b FinP.≟ a
  ... | yes b≡a = contradiction (sym b≡a) a≢b
    where open import Relation.Nullary.Negation using (contradiction)
  ... | no  _ = refl
  sum-hₐ : sum hₐ ≡ h a
  sum-hₐ = trans (sum-single hₐ a zeroₐ) hₐ-a
    where
    zeroₐ : ∀ x → x ≢ a → hₐ x ≡ 0#
    zeroₐ x x≢a with x FinP.≟ a
    ... | yes x≡a = contradiction x≡a x≢a
      where open import Relation.Nullary.Negation using (contradiction)
    ... | no  _ = refl
  sum-hₒ : sum hₒ ≡ h b
  sum-hₒ = trans (sum-single hₒ b zeroₒ) hₒ-b
    where
    zeroₒ : ∀ x → x ≢ b → hₒ x ≡ 0#
    zeroₒ x x≢b with x FinP.≟ a
    ... | yes _ = refl
    ... | no x≢a = h-zero x x≢a x≢b
  sum-h : sum h ≡ 0#
  sum-h = begin
    sum h                    ≡⟨ sum-cong-≗ h≗ ⟩
    sum (λ x → hₐ x + hₒ x)  ≡⟨ ∑-distrib-+ hₐ hₒ ⟩
    sum hₐ + sum hₒ          ≡⟨ cong₂ _+_ sum-hₐ sum-hₒ ⟩
    h a + h b                ≡⟨ lemma ⟩
    0#                       ∎
    where
    -- (g a - f a) + (g b - f b) = (g a + g b) - (f a + f b) = 0.
    lemma : h a + h b ≡ 0#
    lemma = begin
      (g a + - f a) + (g b + - f b)   ≡⟨ S.solve 4 (λ ga fa gb fb → (ga S.:+ S.:- fa) S.:+ (gb S.:+ S.:- fb)
                                             S.:= (ga S.:+ gb) S.:+ S.:- (fa S.:+ fb)) refl (g a) (f a) (g b) (f b) ⟩
      (g a + g b) + - (f a + f b)     ≡⟨ cong (λ z → z + - (f a + f b)) ab ⟩
      (f a + f b) + - (f a + f b)     ≡⟨ AR.-‿inverseʳ (f a + f b) ⟩
      0#                              ∎

-- One-point version.
sum-update₁ : (f g : Fin n → A) (a : Fin n) →
              (∀ x → x ≢ a → g x ≡ f x) → g a ≡ f a → sum g ≡ sum f
sum-update₁ f g a agree ga = sum-cong-≗ pointwise
  where
  pointwise : ∀ x → g x ≡ f x
  pointwise x with x FinP.≟ a
  ... | yes refl = ga
  ... | no  x≢a  = agree x x≢a

------------------------------------------------------------------------
-- Updating a vector at one or two indices

set₁ : {B : Set} → Fin n → B → Vec B n → Vec B n
set₁ a α v = tabulate (λ x → if does (x FinP.≟ a) then α else v ! x)

set₂ : {B : Set} → Fin n → Fin n → B → B → Vec B n → Vec B n
set₂ a b α β v =
  tabulate (λ x → if does (x FinP.≟ a) then α else if does (x FinP.≟ b) then β else v ! x)

module _ {B : Set} where

  set₁-a : (a : Fin n) (α : B) (v : Vec B n) → set₁ a α v ! a ≡ α
  set₁-a a α v with !-tabulate (λ x → if does (x FinP.≟ a) then α else v ! x) a
  ... | eq with a FinP.≟ a
  ...   | yes _   = eq
  ...   | no  a≢a = contradiction refl a≢a
    where open import Relation.Nullary.Negation using (contradiction)

  set₁-≢ : (a : Fin n) (α : B) (v : Vec B n) {x : Fin n} → x ≢ a → set₁ a α v ! x ≡ v ! x
  set₁-≢ a α v {x} x≢a with !-tabulate (λ x → if does (x FinP.≟ a) then α else v ! x) x
  ... | eq with x FinP.≟ a
  ...   | yes x≡a = contradiction x≡a x≢a
    where open import Relation.Nullary.Negation using (contradiction)
  ...   | no  _   = eq

  set₂-a : (a b : Fin n) (α β : B) (v : Vec B n) → set₂ a b α β v ! a ≡ α
  set₂-a a b α β v
    with !-tabulate (λ x → if does (x FinP.≟ a) then α else if does (x FinP.≟ b) then β else v ! x) a
  ... | eq with a FinP.≟ a
  ...   | yes _   = eq
  ...   | no  a≢a = contradiction refl a≢a
    where open import Relation.Nullary.Negation using (contradiction)

  set₂-b : (a b : Fin n) (α β : B) (v : Vec B n) → a ≢ b → set₂ a b α β v ! b ≡ β
  set₂-b a b α β v a≢b
    with !-tabulate (λ x → if does (x FinP.≟ a) then α else if does (x FinP.≟ b) then β else v ! x) b
  ... | eq with b FinP.≟ a | b FinP.≟ b
  ...   | yes b≡a | _       = contradiction (sym b≡a) a≢b
    where open import Relation.Nullary.Negation using (contradiction)
  ...   | no  _   | yes _   = eq
  ...   | no  _   | no  b≢b = contradiction refl b≢b
    where open import Relation.Nullary.Negation using (contradiction)

  set₂-≢ : (a b : Fin n) (α β : B) (v : Vec B n) {x : Fin n} → x ≢ a → x ≢ b →
           set₂ a b α β v ! x ≡ v ! x
  set₂-≢ a b α β v {x} x≢a x≢b
    with !-tabulate (λ x → if does (x FinP.≟ a) then α else if does (x FinP.≟ b) then β else v ! x) x
  ... | eq with x FinP.≟ a | x FinP.≟ b
  ...   | yes x≡a | _       = contradiction x≡a x≢a
    where open import Relation.Nullary.Negation using (contradiction)
  ...   | no  _   | yes x≡b = contradiction x≡b x≢b
    where open import Relation.Nullary.Negation using (contradiction)
  ...   | no  _   | no  _   = eq

------------------------------------------------------------------------
-- The inner product ⟨u , v⟩ = Σₓ uₓ† vₓ

⟨_,_⟩ : Vec A n → Vec A n → A
⟨ u , v ⟩ = sum (λ x → adj (u ! x) * (v ! x))

-- The entries of M†N are the inner products of the columns.
ent-†·*· : (M N : Matrix m n A) (r c : Fin n) → ent (adjoint M ·*· N) r c ≡ ⟨ col M r , col N c ⟩
ent-†·*· M N r c = begin
  ent (adjoint M ·*· N) r c                         ≡⟨ ent-·*· (adjoint M) N r c ⟩
  sum (λ x → ent (adjoint M) r x * ent N x c)       ≡⟨ sum-cong-≗ (λ x → cong (_* ent N x c) (ent-adjoint M r x)) ⟩
  sum (λ x → adj (ent M x r) * ent N x c)           ∎
  where open ≡-Reasoning
