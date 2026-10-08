------------------------------------------------------------------------
-- Presentations of groups
--
-- Operators on n qubits as 2ⁿ × 2ⁿ matrices, and the unitary group
--
-- Over a commutative ring A with an involution adj, an operator, a
-- function of two bit vectors, is the matrix with that entry in row
-- idx x of column idx y (mat), basis states being numbered with wire
-- 0 the most significant bit (idx, bits).  Sums over bit vectors are
-- sums over Fin 2ⁿ (Σb-sum), so products of operators are products of
-- matrices (mat-⊙); the identity is 𝕀 (mat-Id); the matrix determines
-- the operator (mat-injective); and an operator whose conjugate
-- transpose is its inverse has a unitary matrix (Unitary-mat), an
-- element of the unitary group U N over A (U).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.Real-Clifford.Semantics.Matrix
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  where

open import Algebra.Bundles using (Group)
open import Data.Bool.Base using (Bool ; true ; false)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; combine ; remQuot ; _↑ˡ_ ; _↑ʳ_)
open import Data.Fin.Properties using (remQuot-combine ; combine-remQuot) renaming (_≟_ to _≟F_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_ ; refl ; module ≡-Reasoning)
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)

open import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra isCR adjI
  using ( sum ; sum-cong-≗ ; δ ; δ-refl ; δ-≢ ; ent ; mk ; ent-mk ; mat-ext
        ; ent-·*· ; ·*·-assoc ; 𝕀 ; ent-𝕀 ; ·*·-identityˡ ; ·*·-identityʳ
        ; ent-adjoint ; adjoint-involutive ; adjoint-𝕀 ; adjoint-·*·
        ; adj-+ ; adj-* ; adj-0 ; adj-1 ; adj-neg )
open import Examples.Groups.Real-Clifford.Semantics.Laws isCR hiding (mat)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Numbering the basis states

fromBit : Bool → Fin 2
fromBit false = zero
fromBit true  = suc zero

toBit : Fin 2 → Bool
toBit zero       = false
toBit (suc zero) = true

idx : Bits n → Fin (2 ^ n)
idx []      = zero
idx (b ∷ v) = combine (fromBit b) (idx v)

bits : (n : ℕ) → Fin (2 ^ n) → Bits n
bits zero    i = []
bits (suc n) i = toBit (proj₁ (remQuot {2} (2 ^ n) i)) ∷ bits n (proj₂ (remQuot {2} (2 ^ n) i))

bits-idx : (v : Bits n) → bits n (idx v) ≡ v
bits-idx []          = refl
bits-idx {suc n} (b ∷ v) =
  Eq.cong₂ _∷_ (Eq.trans (Eq.cong (λ q → toBit (proj₁ q)) rc) (to-from b))
               (Eq.trans (Eq.cong (λ q → bits n (proj₂ q)) rc) (bits-idx v))
  where
  rc : remQuot {2} (2 ^ n) (combine (fromBit b) (idx v)) ≡ (fromBit b , idx v)
  rc = remQuot-combine {k = 2 ^ n} (fromBit b) (idx v)
  to-from : (b : Bool) → toBit (fromBit b) ≡ b
  to-from false = refl
  to-from true  = refl

idx-bits : (n : ℕ) (i : Fin (2 ^ n)) → idx (bits n i) ≡ i
idx-bits zero    zero = refl
idx-bits (suc n) i =
  Eq.trans (Eq.cong₂ combine (from-to (proj₁ (remQuot {2} (2 ^ n) i))) (idx-bits n (proj₂ (remQuot {2} (2 ^ n) i))))
           (combine-remQuot {n = 2} (2 ^ n) i)
  where
  from-to : (q : Fin 2) → fromBit (toBit q) ≡ q
  from-to zero       = refl
  from-to (suc zero) = refl

------------------------------------------------------------------------
-- Sums over Fin 2ⁿ are sums over bit vectors

private
  sum-split : (m k : ℕ) (f : Fin (m +ℕ k) → A) →
              sum f ≡ sum (λ i → f (i ↑ˡ k)) + sum (λ j → f (m ↑ʳ j))
  sum-split zero    k f = Eq.sym (AR.+-identityˡ (sum f))
  sum-split (suc m) k f = Eq.trans (Eq.cong (f zero +_) (sum-split m k (λ i → f (suc i))))
    (Eq.sym (AR.+-assoc (f zero) (sum (λ i → f (suc (i ↑ˡ k)))) (sum (λ j → f (suc (m ↑ʳ j))))))

  sum-two : (k : ℕ) (f : Fin (2 *ℕ k) → A) →
            sum f ≡ sum (λ j → f (combine {2} {k} zero j)) + sum (λ j → f (combine {2} {k} (suc zero) j))
  sum-two k f = Eq.trans (sum-split k (k +ℕ 0) f)
    (Eq.cong (sum (λ j → f (combine {2} {k} zero j)) +_)
      (Eq.trans (sum-split k 0 (λ j → f (k ↑ʳ j)))
                (AR.+-identityʳ (sum (λ j → f (combine {2} {k} (suc zero) j))))))

Σb-sum : (n : ℕ) (f : Fin (2 ^ n) → A) → sum f ≡ Σb {n} (λ v → f (idx {n} v))
Σb-sum zero    f = AR.+-identityʳ (f zero)
Σb-sum (suc n) f = Eq.trans (sum-two (2 ^ n) f)
  (Eq.cong₂ _+_ (Σb-sum n (λ j → f (combine {2} {2 ^ n} zero j)))
                (Σb-sum n (λ j → f (combine {2} {2 ^ n} (suc zero) j))))

------------------------------------------------------------------------
-- The matrix of an operator

mat : Op n → Matrix (2 ^ n) (2 ^ n) A
mat {n} M = mk λ r c → M (bits n r) (bits n c)

ent-mat : (M : Op n) (r c : Fin (2 ^ n)) → ent (mat M) r c ≡ M (bits n r) (bits n c)
ent-mat {n} M = ent-mk (λ r c → M (bits n r) (bits n c))

private
  δb-refl : (x : Bits n) → δb x x ≡ 1#
  δb-refl []          = refl
  δb-refl (true  ∷ x) = δb-refl x
  δb-refl (false ∷ x) = δb-refl x

  δb-≢ : {x y : Bits n} → x ≢ y → δb x y ≡ 0#
  δb-≢ {x = []}      {[]}      ne = ⊥-elim (ne refl)
  δb-≢ {x = true ∷ x}  {true ∷ y}  ne = δb-≢ (λ e → ne (Eq.cong (true ∷_) e))
  δb-≢ {x = false ∷ x} {false ∷ y} ne = δb-≢ (λ e → ne (Eq.cong (false ∷_) e))
  δb-≢ {x = true ∷ x}  {false ∷ y} ne = refl
  δb-≢ {x = false ∷ x} {true ∷ y}  ne = refl

-- The matrix depends only on the operator, and determines it.
mat-≐ : {M N : Op n} → M ≐ N → mat M ≡ mat N
mat-≐ {n} {M = M} {N} e = mat-ext λ r c →
  Eq.trans (ent-mat M r c) (Eq.trans (e (bits n r) (bits n c)) (Eq.sym (ent-mat N r c)))

mat-injective : {M N : Op n} → mat M ≡ mat N → M ≐ N
mat-injective {n} {M = M} {N} e x y = begin
  M x y                                    ≡⟨ Eq.cong₂ M (bits-idx x) (bits-idx y) ⟨
  M (bits n (idx x)) (bits n (idx y))      ≡⟨ ent-mat M (idx x) (idx y) ⟨
  ent (mat M) (idx x) (idx y)              ≡⟨ Eq.cong (λ B → ent B (idx x) (idx y)) e ⟩
  ent (mat N) (idx x) (idx y)              ≡⟨ ent-mat N (idx x) (idx y) ⟩
  N (bits n (idx x)) (bits n (idx y))      ≡⟨ Eq.cong₂ N (bits-idx x) (bits-idx y) ⟩
  N x y                                    ∎
  where open ≡-Reasoning

-- The identity operator is the identity matrix.
mat-Id : mat (Idₒ {n}) ≡ 𝕀
mat-Id {n} = mat-ext λ r c → Eq.trans (ent-mat (Idₒ {n}) r c) (Eq.trans (entry r c (r ≟F c)) (Eq.sym (ent-𝕀 r c)))
  where
  entry : (r c : Fin (2 ^ n)) → Dec (r ≡ c) → δb (bits n r) (bits n c) ≡ δ r c
  entry r .r (yes refl) = Eq.trans (δb-refl (bits n r)) (Eq.sym (δ-refl r))
  entry r c  (no ne)    = Eq.trans (δb-≢ {x = bits n r} {bits n c} λ e → ne (Eq.trans (Eq.sym (idx-bits n r))
                                                    (Eq.trans (Eq.cong (idx {n}) e) (idx-bits n c))))
                                   (Eq.sym (δ-≢ ne))

-- Composition is the product.
mat-⊙ : (M N : Op n) → mat (M ⊙ N) ≡ mat M ·*· mat N
mat-⊙ {n} M N = mat-ext λ r c → begin
  ent (mat (M ⊙ N)) r c
    ≡⟨ ent-mat (M ⊙ N) r c ⟩
  Σb (λ v → M (bits n r) v * N v (bits n c))
    ≡⟨ Σ-cong (λ v → Eq.cong (λ u → M (bits n r) u * N u (bits n c)) (bits-idx v)) ⟨
  Σb {n} (λ v → M (bits n r) (bits n (idx {n} v)) * N (bits n (idx {n} v)) (bits n c))
    ≡⟨ Σb-sum n (λ x → M (bits n r) (bits n x) * N (bits n x) (bits n c)) ⟨
  sum (λ x → M (bits n r) (bits n x) * N (bits n x) (bits n c))
    ≡⟨ sum-cong-≗ (λ x → Eq.cong₂ _*_ (ent-mat M r x) (ent-mat N x c)) ⟨
  sum (λ x → ent (mat M) r x * ent (mat N) x c)
    ≡⟨ ent-·*· (mat M) (mat N) r c ⟨
  ent (mat M ·*· mat N) r c
    ∎
  where open ≡-Reasoning

-- The conjugate transpose.
mat-adjoint : (M N : Op n) → (∀ x y → adj (M x y) ≡ N y x) → adjoint (mat M) ≡ mat N
mat-adjoint {n} M N t = mat-ext λ r c → begin
  ent (adjoint (mat M)) r c          ≡⟨ ent-adjoint (mat M) r c ⟩
  adj (ent (mat M) c r)              ≡⟨ Eq.cong adj (ent-mat M c r) ⟩
  adj (M (bits n c) (bits n r))      ≡⟨ t (bits n c) (bits n r) ⟩
  N (bits n r) (bits n c)            ≡⟨ ent-mat N r c ⟨
  ent (mat N) r c                    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Operators whose entries adj fixes up to transposition

Symmetric : Op n → Set
Symmetric M = ∀ x y → adj (M x y) ≡ M y x

adj-Σ : (f : Bits n → A) → adj (Σb f) ≡ Σb (λ z → adj (f z))
adj-Σ {zero}  f = refl
adj-Σ {suc n} f = Eq.trans (adj-+ _ _)
  (Eq.cong₂ _+_ (adj-Σ (λ bs → f (false ∷ bs))) (adj-Σ (λ bs → f (true ∷ bs))))

-- The conjugate transpose of a product.
adj-⊙ : (M N M' N' : Op n) → (∀ x y → adj (M x y) ≡ M' y x) → (∀ x y → adj (N x y) ≡ N' y x) →
        ∀ x y → adj ((M ⊙ N) x y) ≡ (N' ⊙ M') y x
adj-⊙ M N M' N' tM tN x y = Eq.trans (adj-Σ (λ z → M x z * N z y))
  (Σ-cong (λ z → Eq.trans (adj-* (M x z) (N z y))
                   (Eq.trans (Eq.cong₂ _*_ (tM x z) (tN z y)) (AR.*-comm (M' z x) (N' y z)))))

δb-sym : Symmetric (Idₒ {n})
δb-sym []          []          = adj-1
δb-sym (true  ∷ x) (true  ∷ y) = δb-sym x y
δb-sym (false ∷ x) (false ∷ y) = δb-sym x y
δb-sym (true  ∷ x) (false ∷ y) = adj-0
δb-sym (false ∷ x) (true  ∷ y) = adj-0

tensor-adj : {M M' : Op m} {N N' : Op n} →
             (∀ x y → adj (M x y) ≡ M' y x) → (∀ x y → adj (N x y) ≡ N' y x) →
             ∀ x y → adj (tensor M N x y) ≡ tensor M' N' y x
tensor-adj {zero}  {M = M} {M'} {N} {N'} tM tN x       y       =
  Eq.trans (adj-* (M [] []) (N x y)) (Eq.cong₂ _*_ (tM [] []) (tN x y))
tensor-adj {suc m} {M = M} {M'} {N} {N'} tM tN (a ∷ x) (b ∷ y) =
  tensor-adj {m} {M = λ u v → M (a ∷ u) (b ∷ v)} {M' = λ u v → M' (b ∷ u) (a ∷ v)} {N} {N'}
    (λ u v → tM (a ∷ u) (b ∷ v)) tN x y

tensor-sym : {M : Op m} {N : Op n} → Symmetric M → Symmetric N → Symmetric (tensor M N)
tensor-sym = tensor-adj

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
          { isEquivalence = record { refl = refl ; sym = Eq.sym ; trans = Eq.trans }
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

-- An operator whose conjugate transpose is its inverse has a unitary
-- matrix.
Unitary-mat : (M N : Op n) → (∀ x y → adj (M x y) ≡ N y x) →
              (N ⊙ M) ≐ Idₒ → (M ⊙ N) ≐ Idₒ → Unitary (mat M)
Unitary-mat {n} M N t NM MN =
  Eq.trans (Eq.cong (_·*· mat M) (mat-adjoint M N t))
    (Eq.trans (Eq.sym (mat-⊙ N M)) (Eq.trans (mat-≐ NM) (mat-Id {n}))) ,
  Eq.trans (Eq.cong (mat M ·*·_) (mat-adjoint M N t))
    (Eq.trans (Eq.sym (mat-⊙ M N)) (Eq.trans (mat-≐ MN) (mat-Id {n})))
