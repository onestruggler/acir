------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics: phase-affine circuits as unitary matrices
--
-- The coefficients are any commutative ring A with an involutive
-- conjugation adj, carrying a primitive p-th root of unity, given as a
-- character phase : F_p → A — phase (a + b) = phase a · phase b, each
-- phase a is a unit with inverse its conjugate, and distinct labels
-- have distinct phases (for A = ℂ, phase k = e^(2πik/p)).
--
-- An operator x ↦ (f x , q x) is the monomial matrix with entry
-- phase (q x) in row f x of column x (mat), basis states being
-- numbered by their labels, wire 0 the most significant (idx, labs).
-- Composition of operators is the product of matrices (mat-⊙), the
-- identity is 𝕀, and the matrix determines the operator
-- (mat-injective), the phases being nonzero and distinct.  The
-- adjoint of the matrix of an invertible operator is the matrix of its
-- inverse (mat-adjoint), so the matrix of a circuit is unitary, an
-- element of the unitary group U N over A (Unitary-mat, U).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)
open import Notations using (₂₊)

import Examples.Groups.Qupit-Phase-Affine.Field as Field

module Examples.Groups.Qupit-Phase-Affine.Matrix
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2))
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (phase : Field.F p-2 p-prime → A)
  (phase-+ : ∀ a b → phase (Field._+_ p-2 p-prime a b) ≡ phase a * phase b)
  (phase-unit : ∀ a → adj (phase a) * phase a ≡ 1#)
  (phase-injective : ∀ a b → phase a ≡ phase b → a ≡ b)
  where

open import Algebra.Bundles using (Group)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; combine ; remQuot)
open import Data.Fin.Properties using (remQuot-combine ; combine-remQuot) renaming (_≟_ to _≟F_)
open import Data.Nat.Base using (zero ; suc ; _^_)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_ ; module ≡-Reasoning)
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)

open import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra isCR adjI
  using ( sum ; sum-cong-≗ ; sum-δʳ ; δ ; δ-refl ; δ-≢ ; ent ; mk ; ent-mk ; mat-ext
        ; ent-·*· ; ·*·-assoc ; 𝕀 ; ent-𝕀 ; ·*·-identityˡ ; ·*·-identityʳ
        ; ent-adjoint ; adjoint-involutive ; adjoint-𝕀 ; adjoint-·*·
        ; adj-* ; adj-0 ; adj-1 ; module AR )

import Examples.Groups.Qupit-Phase-Affine.Semantics as Sem
module 𝔽 = Sem p-2 p-prime
open 𝔽 using (F ; Labels ; Op ; Idₒ ; _⊙_ ; _≐_ ; ≐-trans ; ≐-sym ; p ; 0F ; 1F ; 1≢0)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Numbering the basis states

idx : Labels n → Fin (p ^ n)
idx []      = zero
idx (a ∷ v) = combine a (idx v)

labs : (n : ℕ) → Fin (p ^ n) → Labels n
labs zero    i = []
labs (suc n) i = proj₁ (remQuot {p} (p ^ n) i) ∷ labs n (proj₂ (remQuot {p} (p ^ n) i))

labs-idx : (v : Labels n) → labs n (idx v) ≡ v
labs-idx []      = Eq.refl
labs-idx {suc n} (a ∷ v) =
  Eq.cong₂ _∷_ (Eq.cong proj₁ rc) (Eq.trans (Eq.cong (λ q → labs n (proj₂ q)) rc) (labs-idx v))
  where
  rc : remQuot {p} (p ^ n) (combine a (idx v)) ≡ (a , idx v)
  rc = remQuot-combine {k = p ^ n} a (idx v)

idx-labs : (n : ℕ) (i : Fin (p ^ n)) → idx (labs n i) ≡ i
idx-labs zero    zero = Eq.refl
idx-labs (suc n) i =
  Eq.trans (Eq.cong (combine (proj₁ (remQuot {p} (p ^ n) i))) (idx-labs n (proj₂ (remQuot {p} (p ^ n) i))))
           (combine-remQuot {n = p} (p ^ n) i)

idx-injective : {u v : Labels n} → idx u ≡ idx v → u ≡ v
idx-injective {n} {u = u} {v} e =
  Eq.trans (Eq.sym (labs-idx u)) (Eq.trans (Eq.cong (labs n) e) (labs-idx v))

------------------------------------------------------------------------
-- The phases

private
  -- Inverses in A are unique.
  inv-unique : {x x' y : A} → x * y ≡ 1# → x' * y ≡ 1# → x ≡ x'
  inv-unique {x} {x'} {y} e e' = begin
    x                    ≡⟨ Eq.sym (AR.*-identityʳ x) ⟩
    x * 1#               ≡⟨ Eq.cong (x *_) (Eq.sym (Eq.trans (AR.*-comm y x') e')) ⟩
    x * (y * x')         ≡⟨ Eq.sym (AR.*-assoc x y x') ⟩
    (x * y) * x'         ≡⟨ Eq.cong (_* x') e ⟩
    1# * x'              ≡⟨ AR.*-identityˡ x' ⟩
    x'                   ∎
    where open ≡-Reasoning

phase-0 : phase 0F ≡ 1#
phase-0 = begin
  phase 0F                                   ≡⟨ Eq.sym (AR.*-identityˡ _) ⟩
  1# * phase 0F                              ≡⟨ Eq.cong (_* phase 0F) (Eq.sym (phase-unit 0F)) ⟩
  (adj (phase 0F) * phase 0F) * phase 0F     ≡⟨ AR.*-assoc _ _ _ ⟩
  adj (phase 0F) * (phase 0F * phase 0F)     ≡⟨ Eq.cong (adj (phase 0F) *_) (Eq.sym (Eq.trans (Eq.cong phase (Eq.sym (𝔽.FR.+-identityʳ 0F))) (phase-+ 0F 0F))) ⟩
  adj (phase 0F) * phase 0F                  ≡⟨ phase-unit 0F ⟩
  1#                                         ∎
  where open ≡-Reasoning

adj-phase : (a : F) → adj (phase a) ≡ phase (𝔽.- a)
adj-phase a = inv-unique (phase-unit a)
  (Eq.trans (Eq.sym (phase-+ (𝔽.- a) a)) (Eq.trans (Eq.cong phase (𝔽.FR.-‿inverseˡ a)) phase-0))

phase-nonzero : (a : F) → phase a ≢ 0#
phase-nonzero a e = 1≢0 (phase-injective 1F 0F (begin
  phase 1F             ≡⟨ Eq.sym (AR.*-identityʳ _) ⟩
  phase 1F * 1#        ≡⟨ Eq.cong (phase 1F *_) one≡zero ⟩
  phase 1F * 0#        ≡⟨ AR.zeroʳ _ ⟩
  0#                   ≡⟨ Eq.sym one≡zero ⟩
  1#                   ≡⟨ Eq.sym phase-0 ⟩
  phase 0F             ∎))
  where
  open ≡-Reasoning
  one≡zero : 1# ≡ 0#
  one≡zero = Eq.trans (Eq.sym (phase-unit a)) (Eq.trans (Eq.cong (adj (phase a) *_) e) (AR.zeroʳ _))

private
  neg-inv : (a b : F) → a 𝔽.+ b ≡ 0F → b ≡ 𝔽.- a
  neg-inv a b e = begin
    b                          ≡⟨ Eq.sym (𝔽.FR.+-identityˡ b) ⟩
    0F 𝔽.+ b                   ≡⟨ Eq.cong (𝔽._+ b) (Eq.sym (𝔽.FR.-‿inverseˡ a)) ⟩
    (𝔽.- a 𝔽.+ a) 𝔽.+ b        ≡⟨ 𝔽.FR.+-assoc _ a b ⟩
    𝔽.- a 𝔽.+ (a 𝔽.+ b)        ≡⟨ Eq.cong (𝔽.- a 𝔽.+_) e ⟩
    𝔽.- a 𝔽.+ 0F               ≡⟨ 𝔽.FR.+-identityʳ _ ⟩
    𝔽.- a                      ∎
    where open ≡-Reasoning

------------------------------------------------------------------------
-- The matrix of an operator

-- Column x holds phase (q x), in row f x.
mat : Op n → Matrix (p ^ n) (p ^ n) A
mat {n} M = mk λ r c → δ r (idx (proj₁ (M (labs n c)))) * phase (proj₂ (M (labs n c)))

ent-mat : (M : Op n) (r c : Fin (p ^ n)) →
          ent (mat M) r c ≡ δ r (idx (proj₁ (M (labs n c)))) * phase (proj₂ (M (labs n c)))
ent-mat {n} M r c = ent-mk (λ r c → δ r (idx (proj₁ (M (labs n c)))) * phase (proj₂ (M (labs n c)))) r c

ent-mat-idx : (M : Op n) (r : Fin (p ^ n)) (x : Labels n) →
              ent (mat M) r (idx x) ≡ δ r (idx (proj₁ (M x))) * phase (proj₂ (M x))
ent-mat-idx M r x =
  Eq.trans (ent-mat M r (idx x))
           (Eq.cong (λ y → δ r (idx (proj₁ (M y))) * phase (proj₂ (M y))) (labs-idx x))

private
  δ-eq : {x y : Fin m} → x ≡ y → δ x y ≡ 1#
  δ-eq {x = x} Eq.refl = δ-refl x

  adj-δ : (x y : Fin m) → adj (δ x y) ≡ δ x y
  adj-δ x y = go (x ≟F y)
    where
    go : Dec (x ≡ y) → adj (δ x y) ≡ δ x y
    go (yes e) = Eq.trans (Eq.cong adj (δ-eq e)) (Eq.trans adj-1 (Eq.sym (δ-eq e)))
    go (no ne) = Eq.trans (Eq.cong adj (δ-≢ ne)) (Eq.trans adj-0 (Eq.sym (δ-≢ ne)))

  swap-* : (a d e : A) → a * (d * e) ≡ (a * e) * d
  swap-* a d e = Eq.trans (Eq.cong (a *_) (AR.*-comm d e)) (Eq.sym (AR.*-assoc a e d))

-- The matrix depends only on the operator.
mat-≐ : {M N : Op n} → M ≐ N → mat M ≡ mat N
mat-≐ {n} {M = M} {N} e = mat-ext λ r c →
  Eq.trans (ent-mat M r c)
    (Eq.trans (Eq.cong (λ y → δ r (idx (proj₁ y)) * phase (proj₂ y)) (e (labs n c)))
              (Eq.sym (ent-mat N r c)))

-- The identity operator is the identity matrix.
mat-Id : mat (Idₒ {n}) ≡ 𝕀
mat-Id {n} = mat-ext λ r c → begin
  ent (mat (Idₒ {n})) r c             ≡⟨ ent-mat (Idₒ {n}) r c ⟩
  δ r (idx (labs n c)) * phase 0F     ≡⟨ Eq.cong (δ r (idx (labs n c)) *_) phase-0 ⟩
  δ r (idx (labs n c)) * 1#           ≡⟨ AR.*-identityʳ _ ⟩
  δ r (idx (labs n c))                ≡⟨ Eq.cong (δ r) (idx-labs n c) ⟩
  δ r c                               ≡⟨ Eq.sym (ent-𝕀 r c) ⟩
  ent 𝕀 r c                           ∎
  where open ≡-Reasoning

-- Composition is the product: in column c of mat M ·*· mat N the sum
-- runs over the one nonzero entry of column c of mat N.
mat-⊙ : (M N : Op n) → mat (M ⊙ N) ≡ mat M ·*· mat N
mat-⊙ {n} M N = mat-ext λ r c → Eq.sym (entry r c)
  where
  open ≡-Reasoning
  g : Fin (p ^ n) → Fin (p ^ n) → A
  g r x = δ r (idx (proj₁ (M (labs n x)))) * phase (proj₂ (M (labs n x)))
  entry : ∀ r c → ent (mat M ·*· mat N) r c ≡ ent (mat (M ⊙ N)) r c
  entry r c = begin
    ent (mat M ·*· mat N) r c
      ≡⟨ ent-·*· (mat M) (mat N) r c ⟩
    sum (λ x → ent (mat M) r x * ent (mat N) x c)
      ≡⟨ sum-cong-≗ (λ x → Eq.trans (Eq.cong₂ _*_ (ent-mat M r x) (ent-mat N x c))
                                     (swap-* (g r x) (δ x (idx z)) φ)) ⟩
    sum (λ x → (g r x * φ) * δ x (idx z))
      ≡⟨ sum-δʳ (λ x → g r x * φ) (idx z) ⟩
    g r (idx z) * φ
      ≡⟨ Eq.cong (λ y → (δ r (idx (proj₁ (M y))) * phase (proj₂ (M y))) * φ) (labs-idx z) ⟩
    (δ r (idx (proj₁ (M z))) * phase (proj₂ (M z))) * φ
      ≡⟨ AR.*-assoc (δ r (idx (proj₁ (M z)))) (phase (proj₂ (M z))) φ ⟩
    δ r (idx (proj₁ (M z))) * (phase (proj₂ (M z)) * φ)
      ≡⟨ Eq.cong (δ r (idx (proj₁ (M z))) *_)
           (Eq.trans (AR.*-comm (phase (proj₂ (M z))) φ)
                     (Eq.sym (phase-+ (proj₂ (N (labs n c))) (proj₂ (M z))))) ⟩
    δ r (idx (proj₁ (M z))) * phase (proj₂ (N (labs n c)) 𝔽.+ proj₂ (M z))
      ≡⟨ Eq.sym (ent-mat (M ⊙ N) r c) ⟩
    ent (mat (M ⊙ N)) r c
      ∎
    where
    z : Labels n
    z = proj₁ (N (labs n c))
    φ : A
    φ = phase (proj₂ (N (labs n c)))

-- The matrix determines the operator: in column idx x, the entry in
-- row idx (f x) is phase (q x), which is nonzero.
mat-injective : {M N : Op n} → mat M ≡ mat N → M ≐ N
mat-injective {M = M} {N} e x = go (idx (proj₁ (M x)) ≟F idx (proj₁ (N x)))
  where
  i : Fin _
  i = idx (proj₁ (M x))
  pivot : phase (proj₂ (M x)) ≡ δ i (idx (proj₁ (N x))) * phase (proj₂ (N x))
  pivot = Eq.trans (Eq.sym (Eq.trans (Eq.cong (_* phase (proj₂ (M x))) (δ-refl i))
                                     (AR.*-identityˡ (phase (proj₂ (M x))))))
            (Eq.trans (Eq.sym (ent-mat-idx M i x))
              (Eq.trans (Eq.cong (λ B → ent B i (idx x)) e) (ent-mat-idx N i x)))
  go : Dec (i ≡ idx (proj₁ (N x))) → M x ≡ N x
  go (yes q) = Eq.cong₂ _,_ (idx-injective q)
    (phase-injective (proj₂ (M x)) (proj₂ (N x))
      (Eq.trans pivot (Eq.trans (Eq.cong (_* phase (proj₂ (N x))) (δ-eq q))
                                (AR.*-identityˡ (phase (proj₂ (N x)))))))
  go (no q) = ⊥-elim (phase-nonzero (proj₂ (M x))
    (Eq.trans pivot (Eq.trans (Eq.cong (_* phase (proj₂ (N x))) (δ-≢ q))
                              (AR.zeroˡ (phase (proj₂ (N x)))))))

-- The adjoint of the matrix of an invertible operator is the matrix of
-- its inverse.
mat-adjoint : (M N : Op n) → (N ⊙ M) ≐ Idₒ → (M ⊙ N) ≐ Idₒ → adjoint (mat M) ≡ mat N
mat-adjoint {n} M N NM MN = mat-ext λ r c → begin
  ent (adjoint (mat M)) r c
    ≡⟨ ent-adjoint (mat M) r c ⟩
  adj (ent (mat M) c r)
    ≡⟨ Eq.cong adj (ent-mat M c r) ⟩
  adj (δ c (idx (proj₁ (M (labs n r)))) * phase (proj₂ (M (labs n r))))
    ≡⟨ adj-* (δ c (idx (proj₁ (M (labs n r))))) (phase (proj₂ (M (labs n r)))) ⟩
  adj (δ c (idx (proj₁ (M (labs n r))))) * adj (phase (proj₂ (M (labs n r))))
    ≡⟨ Eq.cong₂ _*_ (adj-δ c (idx (proj₁ (M (labs n r))))) (adj-phase (proj₂ (M (labs n r)))) ⟩
  δ c (idx (proj₁ (M (labs n r)))) * phase (𝔽.- proj₂ (M (labs n r)))
    ≡⟨ entry r c (c ≟F idx (proj₁ (M (labs n r)))) ⟩
  δ r (idx (proj₁ (N (labs n c)))) * phase (proj₂ (N (labs n c)))
    ≡⟨ Eq.sym (ent-mat N r c) ⟩
  ent (mat N) r c
    ∎
  where
  open ≡-Reasoning
  entry : ∀ r c → Dec (c ≡ idx (proj₁ (M (labs n r)))) →
          δ c (idx (proj₁ (M (labs n r)))) * phase (𝔽.- proj₂ (M (labs n r)))
          ≡ δ r (idx (proj₁ (N (labs n c)))) * phase (proj₂ (N (labs n c)))
  entry r c (yes e) = begin
    δ c (idx (proj₁ (M x))) * phase (𝔽.- proj₂ (M x))
      ≡⟨ Eq.cong (_* phase (𝔽.- proj₂ (M x))) (δ-eq e) ⟩
    1# * phase (𝔽.- proj₂ (M x))
      ≡⟨ Eq.cong (λ a → 1# * phase a) (Eq.sym phN) ⟩
    1# * phase (proj₂ (N (labs n c)))
      ≡⟨ Eq.cong (_* phase (proj₂ (N (labs n c)))) (Eq.sym (δ-eq r≡)) ⟩
    δ r (idx (proj₁ (N (labs n c)))) * phase (proj₂ (N (labs n c)))
      ∎
    where
    x : Labels n
    x = labs n r
    bc : labs n c ≡ proj₁ (M x)
    bc = Eq.trans (Eq.cong (labs n) e) (labs-idx (proj₁ (M x)))
    back : proj₁ (N (labs n c)) ≡ x
    back = Eq.trans (Eq.cong (λ y → proj₁ (N y)) bc) (Eq.cong proj₁ (NM x))
    r≡ : r ≡ idx (proj₁ (N (labs n c)))
    r≡ = Eq.trans (Eq.sym (idx-labs n r)) (Eq.cong idx (Eq.sym back))
    phN : proj₂ (N (labs n c)) ≡ 𝔽.- proj₂ (M x)
    phN = Eq.trans (Eq.cong (λ y → proj₂ (N y)) bc)
            (neg-inv (proj₂ (M x)) (proj₂ (N (proj₁ (M x)))) (Eq.cong proj₂ (NM x)))
  entry r c (no ne) =
    Eq.trans (Eq.cong (_* phase (𝔽.- proj₂ (M (labs n r)))) (δ-≢ ne))
      (Eq.trans (AR.zeroˡ (phase (𝔽.- proj₂ (M (labs n r)))))
        (Eq.sym (Eq.trans (Eq.cong (_* phase (proj₂ (N (labs n c)))) (δ-≢ ne'))
                          (AR.zeroˡ (phase (proj₂ (N (labs n c))))))))
    where
    ne' : r ≢ idx (proj₁ (N (labs n c)))
    ne' q = ne (Eq.sym (Eq.trans
      (Eq.cong idx (Eq.trans (Eq.cong (λ y → proj₁ (M y))
                                      (Eq.trans (Eq.cong (labs n) q) (labs-idx (proj₁ (N (labs n c))))))
                             (Eq.cong proj₁ (MN (labs n c)))))
      (idx-labs n c)))

------------------------------------------------------------------------
-- The unitary group over A

Unitary : Matrix m m A → Set
Unitary M = (adjoint M ·*· M ≡ 𝕀) × (M ·*· adjoint M ≡ 𝕀)

Unitary-𝕀 : Unitary (𝕀 {m})
Unitary-𝕀 = Eq.trans (Eq.cong (_·*· 𝕀) adjoint-𝕀) (·*·-identityˡ 𝕀) ,
            Eq.trans (Eq.cong (𝕀 ·*·_) adjoint-𝕀) (·*·-identityˡ 𝕀)

Unitary-·*· : {M N : Matrix m m A} → Unitary M → Unitary N → Unitary (M ·*· N)
Unitary-·*· {M = M} {N} (m₁ , m₂) (n₁ , n₂) = u₁ , u₂
  where
  open ≡-Reasoning
  u₁ : adjoint (M ·*· N) ·*· (M ·*· N) ≡ 𝕀
  u₁ = begin
    adjoint (M ·*· N) ·*· (M ·*· N)               ≡⟨ Eq.cong (_·*· (M ·*· N)) (adjoint-·*· M N) ⟩
    (adjoint N ·*· adjoint M) ·*· (M ·*· N)       ≡⟨ ·*·-assoc (adjoint N) (adjoint M) (M ·*· N) ⟩
    adjoint N ·*· (adjoint M ·*· (M ·*· N))       ≡⟨ Eq.cong (adjoint N ·*·_) (Eq.sym (·*·-assoc (adjoint M) M N)) ⟩
    adjoint N ·*· ((adjoint M ·*· M) ·*· N)       ≡⟨ Eq.cong (λ z → adjoint N ·*· (z ·*· N)) m₁ ⟩
    adjoint N ·*· (𝕀 ·*· N)                       ≡⟨ Eq.cong (adjoint N ·*·_) (·*·-identityˡ N) ⟩
    adjoint N ·*· N                               ≡⟨ n₁ ⟩
    𝕀                                             ∎
  u₂ : (M ·*· N) ·*· adjoint (M ·*· N) ≡ 𝕀
  u₂ = begin
    (M ·*· N) ·*· adjoint (M ·*· N)               ≡⟨ Eq.cong ((M ·*· N) ·*·_) (adjoint-·*· M N) ⟩
    (M ·*· N) ·*· (adjoint N ·*· adjoint M)       ≡⟨ ·*·-assoc M N (adjoint N ·*· adjoint M) ⟩
    M ·*· (N ·*· (adjoint N ·*· adjoint M))       ≡⟨ Eq.cong (M ·*·_) (Eq.sym (·*·-assoc N (adjoint N) (adjoint M))) ⟩
    M ·*· ((N ·*· adjoint N) ·*· adjoint M)       ≡⟨ Eq.cong (λ z → M ·*· (z ·*· adjoint M)) n₂ ⟩
    M ·*· (𝕀 ·*· adjoint M)                       ≡⟨ Eq.cong (M ·*·_) (·*·-identityˡ (adjoint M)) ⟩
    M ·*· adjoint M                               ≡⟨ m₂ ⟩
    𝕀                                             ∎

Unitary-adjoint : {M : Matrix m m A} → Unitary M → Unitary (adjoint M)
Unitary-adjoint {M = M} (m₁ , m₂) =
  Eq.trans (Eq.cong (_·*· adjoint M) (adjoint-involutive M)) m₂ ,
  Eq.trans (Eq.cong (adjoint M ·*·_) (adjoint-involutive M)) m₁

UMat : ℕ → Set
UMat m = Σ (Matrix m m A) Unitary

-- U(m) over A, compared by entries.
U : ℕ → Group 0ℓ 0ℓ
U m = record
  { Carrier = UMat m
  ; _≈_     = λ M N → proj₁ M ≡ proj₁ N
  ; _∙_     = λ M N → proj₁ M ·*· proj₁ N , Unitary-·*· (proj₂ M) (proj₂ N)
  ; ε       = 𝕀 , Unitary-𝕀
  ; _⁻¹     = λ M → adjoint (proj₁ M) , Unitary-adjoint (proj₂ M)
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record { refl = Eq.refl ; sym = Eq.sym ; trans = Eq.trans }
          ; ∙-cong = Eq.cong₂ _·*·_
          }
        ; assoc = λ M N P → ·*·-assoc (proj₁ M) (proj₁ N) (proj₁ P)
        }
      ; identity = (λ M → ·*·-identityˡ (proj₁ M)) , (λ M → ·*·-identityʳ (proj₁ M))
      }
    ; inverse = (λ M → proj₁ (proj₂ M)) , (λ M → proj₂ (proj₂ M))
    ; ⁻¹-cong = Eq.cong adjoint
    }
  }

-- The matrix of an invertible operator is unitary.
Unitary-mat : (M N : Op n) → (N ⊙ M) ≐ Idₒ → (M ⊙ N) ≐ Idₒ → Unitary (mat M)
Unitary-mat {n} M N NM MN =
  Eq.trans (Eq.cong (_·*· mat M) (mat-adjoint M N NM MN))
    (Eq.trans (Eq.sym (mat-⊙ N M)) (Eq.trans (mat-≐ NM) (mat-Id {n}))) ,
  Eq.trans (Eq.cong (mat M ·*·_) (mat-adjoint M N NM MN))
    (Eq.trans (Eq.sym (mat-⊙ M N)) (Eq.trans (mat-≐ MN) (mat-Id {n})))
