------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics: CNOT-dihedral circuits as unitary matrices
-- over 𝔻[ω]
--
-- An operator x ↦ (f x , p x) is the monomial matrix with entry ω^(p x)
-- in row f x of column x (mat), basis states being numbered by their
-- bits, wire 0 the most significant (idx, bits).  Composition of
-- operators is the product of matrices (mat-⊙), the identity is 𝕀,
-- and the matrix determines the operator (mat-injective), the entries
-- ω^k being nonzero and distinct.  The adjoint of the matrix of an
-- invertible operator is the matrix of its inverse (mat-adjoint), so a
-- circuit's matrix is unitary (Unitary-⟦⟧ᵐ).
--
-- The powers of ω are concrete elements of 𝔻[ω]; their laws (ω^(a+b)
-- = ω^a ω^b, conj ω^a = ω^(−a), injectivity, nonvanishing) are decided
-- over ℤ₈ by computation, in blocks that unfold 𝔻[ω]'s operations.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CNOT+Dihedral.Matrix where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; toℕ ; combine ; remQuot)
open import Data.Fin.Properties using (remQuot-combine ; combine-remQuot ; all?)
  renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ ; zero ; suc ; _^_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (toWitness ; _→?_ ; ¬?)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; ωᴰ ; _*ᴰ_ ; adjᴰ ; 0ᴰ ; 1ᴰ ; _≟ᴰ_ ; _^ᴰ_ ; module DR
        ; SemiRingD ; RingD ; AdjointD)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics
  using (UMat ; Unitary ; δ ; δ-refl ; δ-≢ ; sum ; sum-cong-≗ ; sum-δʳ
        ; mk ; ent ; ent-mk ; mat-ext ; ent-·*· ; 𝕀 ; ent-𝕀 ; ent-adjoint
        ; adj-0 ; adj-1 ; adj-*)

open import Examples.Groups.CNOT+Dihedral.Semantics
  using (Bits ; Op ; Idₒ ; _⊙_ ; _≐_ ; ≐-sym ; ≐-trans ; ℤ₈ ; 0₈ ; _≟₈_)
  renaming (_+_ to _+₈_)
open import Examples.Groups.CNOT+Dihedral.Syntactics using (Circuit)
open import Examples.Groups.CNOT+Dihedral.Interpretation using (⟦_⟧ ; ⟦⟧-• ; ⟦⟧-ε)
open import Examples.Groups.CNOT+Dihedral.Soundness using (sound)
open import Examples.Groups.CNOT+Dihedral.Evaluation using (module Inv ; _⁻¹)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Numbering the basis states

bit : Bool → Fin 2
bit false = zero
bit true  = suc zero

unbit : Fin 2 → Bool
unbit zero       = false
unbit (suc zero) = true

idx : Bits n → Fin (2 ^ n)
idx []      = zero
idx (a ∷ v) = combine (bit a) (idx v)

bits : (n : ℕ) → Fin (2 ^ n) → Bits n
bits zero    i = []
bits (suc n) i = unbit (proj₁ (remQuot {2} (2 ^ n) i)) ∷ bits n (proj₂ (remQuot {2} (2 ^ n) i))

bits-idx : (v : Bits n) → bits n (idx v) ≡ v
bits-idx []      = Eq.refl
bits-idx {suc n} (a ∷ v) =
  Eq.cong₂ _∷_ (Eq.trans (Eq.cong (λ p → unbit (proj₁ p)) rc) (unbit-bit a))
               (Eq.trans (Eq.cong (λ p → bits n (proj₂ p)) rc) (bits-idx v))
  where
  rc : remQuot {2} (2 ^ n) (combine (bit a) (idx v)) ≡ (bit a , idx v)
  rc = remQuot-combine {k = 2 ^ n} (bit a) (idx v)

  unbit-bit : ∀ a → unbit (bit a) ≡ a
  unbit-bit false = Eq.refl
  unbit-bit true  = Eq.refl

idx-bits : (n : ℕ) (i : Fin (2 ^ n)) → idx (bits n i) ≡ i
idx-bits zero    zero = Eq.refl
idx-bits (suc n) i =
  Eq.trans (Eq.cong₂ combine (bit-unbit (proj₁ (remQuot {2} (2 ^ n) i)))
                             (idx-bits n (proj₂ (remQuot {2} (2 ^ n) i))))
           (combine-remQuot {n = 2} (2 ^ n) i)
  where
  bit-unbit : ∀ i → bit (unbit i) ≡ i
  bit-unbit zero       = Eq.refl
  bit-unbit (suc zero) = Eq.refl

idx-injective : {u v : Bits n} → idx u ≡ idx v → u ≡ v
idx-injective {n} {u = u} {v} e =
  Eq.trans (Eq.sym (bits-idx u)) (Eq.trans (Eq.cong (bits n) e) (bits-idx v))

------------------------------------------------------------------------
-- The phases ω^k in 𝔻[ω]

phase : ℤ₈ → D
phase a = ωᴰ ^ᴰ toℕ a

-- Negation in ℤ₈.
neg : ℤ₈ → ℤ₈
neg zero                                           = zero
neg (suc zero)                                     = suc (suc (suc (suc (suc (suc (suc zero))))))
neg (suc (suc zero))                               = suc (suc (suc (suc (suc (suc zero)))))
neg (suc (suc (suc zero)))                         = suc (suc (suc (suc (suc zero))))
neg (suc (suc (suc (suc zero))))                   = suc (suc (suc (suc zero)))
neg (suc (suc (suc (suc (suc zero)))))             = suc (suc (suc zero))
neg (suc (suc (suc (suc (suc (suc zero))))))       = suc (suc zero)
neg (suc (suc (suc (suc (suc (suc (suc zero))))))) = suc zero

neg-inv : (a b : ℤ₈) → a +₈ b ≡ 0₈ → b ≡ neg a
neg-inv = toWitness {a? = all? λ a → all? λ b → ((a +₈ b) ≟₈ 0₈) →? (b ≟₈ neg a)} _

opaque
  unfolding _*ᴰ_

  phase-+ : (a b : ℤ₈) → phase (a +₈ b) ≡ phase a *ᴰ phase b
  phase-+ = toWitness {a? = all? λ a → all? λ b → phase (a +₈ b) ≟ᴰ (phase a *ᴰ phase b)} _

  phase-injective : (a b : ℤ₈) → phase a ≡ phase b → a ≡ b
  phase-injective = toWitness {a? = all? λ a → all? λ b → (phase a ≟ᴰ phase b) →? (a ≟₈ b)} _

  phase-nonzero : (a : ℤ₈) → phase a ≢ 0ᴰ
  phase-nonzero = toWitness {a? = all? λ a → ¬? (phase a ≟ᴰ 0ᴰ)} _

opaque
  unfolding _*ᴰ_ adjᴰ

  adj-phase : (a : ℤ₈) → adjᴰ (phase a) ≡ phase (neg a)
  adj-phase = toWitness {a? = all? λ a → adjᴰ (phase a) ≟ᴰ phase (neg a)} _

------------------------------------------------------------------------
-- The matrix of an operator

-- Column x holds ω^(p x), in row f x.
mat : Op n → Matrix (2 ^ n) (2 ^ n) D
mat {n} M = mk λ r c → δ r (idx (proj₁ (M (bits n c)))) *ᴰ phase (proj₂ (M (bits n c)))

ent-mat : (M : Op n) (r c : Fin (2 ^ n)) →
          ent (mat M) r c ≡ δ r (idx (proj₁ (M (bits n c)))) *ᴰ phase (proj₂ (M (bits n c)))
ent-mat {n} M r c = ent-mk (λ r c → δ r (idx (proj₁ (M (bits n c)))) *ᴰ phase (proj₂ (M (bits n c)))) r c

-- The entries of column idx x.
ent-mat-idx : (M : Op n) (r : Fin (2 ^ n)) (x : Bits n) →
              ent (mat M) r (idx x) ≡ δ r (idx (proj₁ (M x))) *ᴰ phase (proj₂ (M x))
ent-mat-idx M r x =
  Eq.trans (ent-mat M r (idx x))
           (Eq.cong (λ y → δ r (idx (proj₁ (M y))) *ᴰ phase (proj₂ (M y))) (bits-idx x))

private
  δ-eq : {x y : Fin m} → x ≡ y → δ x y ≡ 1ᴰ
  δ-eq {x = x} Eq.refl = δ-refl x

  -- δ is real.
  adj-δ : (x y : Fin m) → adjᴰ (δ x y) ≡ δ x y
  adj-δ x y = go (x ≟F y)
    where
    go : Dec (x ≡ y) → adjᴰ (δ x y) ≡ δ x y
    go (yes e) = Eq.trans (Eq.cong adjᴰ (δ-eq e)) (Eq.trans adj-1 (Eq.sym (δ-eq e)))
    go (no ne) = Eq.trans (Eq.cong adjᴰ (δ-≢ ne)) (Eq.trans adj-0 (Eq.sym (δ-≢ ne)))

  -- a (d e) = (a e) d.
  swap-* : (a d e : D) → a *ᴰ (d *ᴰ e) ≡ (a *ᴰ e) *ᴰ d
  swap-* a d e = Eq.trans (Eq.cong (a *ᴰ_) (DR.*-comm d e)) (Eq.sym (DR.*-assoc a e d))

-- The matrix depends only on the operator.
mat-≐ : {M N : Op n} → M ≐ N → mat M ≡ mat N
mat-≐ {n} {M = M} {N} e = mat-ext λ r c →
  Eq.trans (ent-mat M r c)
    (Eq.trans (Eq.cong (λ y → δ r (idx (proj₁ y)) *ᴰ phase (proj₂ y)) (e (bits n c)))
              (Eq.sym (ent-mat N r c)))

-- The identity operator is the identity matrix.
mat-Id : mat (Idₒ {n}) ≡ 𝕀
mat-Id {n} = mat-ext λ r c → begin
  ent (mat (Idₒ {n})) r c   ≡⟨ ent-mat (Idₒ {n}) r c ⟩
  δ r (idx (bits n c)) *ᴰ 1ᴰ   ≡⟨ DR.*-identityʳ (δ r (idx (bits n c))) ⟩
  δ r (idx (bits n c))         ≡⟨ Eq.cong (δ r) (idx-bits n c) ⟩
  δ r c                      ≡⟨ Eq.sym (ent-𝕀 r c) ⟩
  ent 𝕀 r c                  ∎
  where open Eq.≡-Reasoning

-- Composition is the product.  In column c of mat M ·*· mat N, the sum
-- runs over the one nonzero entry of column c of mat N.
mat-⊙ : (M N : Op n) → mat (M ⊙ N) ≡ mat M ·*· mat N
mat-⊙ {n} M N = mat-ext λ r c → Eq.sym (entry r c)
  where
  open Eq.≡-Reasoning
  g : Fin (2 ^ n) → Fin (2 ^ n) → D
  g r x = δ r (idx (proj₁ (M (bits n x)))) *ᴰ phase (proj₂ (M (bits n x)))
  entry : ∀ r c → ent (mat M ·*· mat N) r c ≡ ent (mat (M ⊙ N)) r c
  entry r c = begin
    ent (mat M ·*· mat N) r c
      ≡⟨ ent-·*· (mat M) (mat N) r c ⟩
    sum (λ x → ent (mat M) r x *ᴰ ent (mat N) x c)
      ≡⟨ sum-cong-≗ (λ x → Eq.trans (Eq.cong₂ _*ᴰ_ (ent-mat M r x) (ent-mat N x c))
                                     (swap-* (g r x) (δ x (idx z)) φ)) ⟩
    sum (λ x → (g r x *ᴰ φ) *ᴰ δ x (idx z))
      ≡⟨ sum-δʳ (λ x → g r x *ᴰ φ) (idx z) ⟩
    g r (idx z) *ᴰ φ
      ≡⟨ Eq.cong (λ y → (δ r (idx (proj₁ (M y))) *ᴰ phase (proj₂ (M y))) *ᴰ φ) (bits-idx z) ⟩
    (δ r (idx (proj₁ (M z))) *ᴰ phase (proj₂ (M z))) *ᴰ φ
      ≡⟨ DR.*-assoc (δ r (idx (proj₁ (M z)))) (phase (proj₂ (M z))) φ ⟩
    δ r (idx (proj₁ (M z))) *ᴰ (phase (proj₂ (M z)) *ᴰ φ)
      ≡⟨ Eq.cong (δ r (idx (proj₁ (M z))) *ᴰ_)
           (Eq.trans (DR.*-comm (phase (proj₂ (M z))) φ)
                     (Eq.sym (phase-+ (proj₂ (N (bits n c))) (proj₂ (M z))))) ⟩
    δ r (idx (proj₁ (M z))) *ᴰ phase (proj₂ (N (bits n c)) +₈ proj₂ (M z))
      ≡⟨ Eq.sym (ent-mat (M ⊙ N) r c) ⟩
    ent (mat (M ⊙ N)) r c
      ∎
    where
    z : Bits n
    z = proj₁ (N (bits n c))
    φ : D
    φ = phase (proj₂ (N (bits n c)))

-- The matrix determines the operator: in column idx x, the entry in
-- row idx (f x) is ω^(p x), which is nonzero.
mat-injective : {M N : Op n} → mat M ≡ mat N → M ≐ N
mat-injective {M = M} {N} e x = go (idx (proj₁ (M x)) ≟F idx (proj₁ (N x)))
  where
  i : Fin _
  i = idx (proj₁ (M x))
  pivot : phase (proj₂ (M x)) ≡ δ i (idx (proj₁ (N x))) *ᴰ phase (proj₂ (N x))
  pivot = Eq.trans (Eq.sym (Eq.trans (Eq.cong (_*ᴰ phase (proj₂ (M x))) (δ-refl i))
                                     (DR.*-identityˡ (phase (proj₂ (M x))))))
            (Eq.trans (Eq.sym (ent-mat-idx M i x))
              (Eq.trans (Eq.cong (λ A → ent A i (idx x)) e) (ent-mat-idx N i x)))
  go : Dec (i ≡ idx (proj₁ (N x))) → M x ≡ N x
  go (yes q) = Eq.cong₂ _,_ (idx-injective q)
    (phase-injective (proj₂ (M x)) (proj₂ (N x))
      (Eq.trans pivot (Eq.trans (Eq.cong (_*ᴰ phase (proj₂ (N x))) (δ-eq q))
                                (DR.*-identityˡ (phase (proj₂ (N x)))))))
  go (no q) = ⊥-elim (phase-nonzero (proj₂ (M x))
    (Eq.trans pivot (Eq.trans (Eq.cong (_*ᴰ phase (proj₂ (N x))) (δ-≢ q))
                              (DR.zeroˡ (phase (proj₂ (N x)))))))

-- The adjoint of the matrix of an invertible operator is the matrix of
-- its inverse.  Entry (r , c) of either is ω^(−p x) when x = bits r
-- and c = idx (f x), and zero otherwise.
mat-adjoint : (M N : Op n) → (N ⊙ M) ≐ Idₒ → (M ⊙ N) ≐ Idₒ → adjoint (mat M) ≡ mat N
mat-adjoint {n} M N NM MN = mat-ext λ r c → begin
  ent (adjoint (mat M)) r c
    ≡⟨ ent-adjoint (mat M) r c ⟩
  adjᴰ (ent (mat M) c r)
    ≡⟨ Eq.cong adjᴰ (ent-mat M c r) ⟩
  adjᴰ (δ c (idx (proj₁ (M (bits n r)))) *ᴰ phase (proj₂ (M (bits n r))))
    ≡⟨ adj-* (δ c (idx (proj₁ (M (bits n r))))) (phase (proj₂ (M (bits n r)))) ⟩
  adjᴰ (δ c (idx (proj₁ (M (bits n r))))) *ᴰ adjᴰ (phase (proj₂ (M (bits n r))))
    ≡⟨ Eq.cong₂ _*ᴰ_ (adj-δ c (idx (proj₁ (M (bits n r))))) (adj-phase (proj₂ (M (bits n r)))) ⟩
  δ c (idx (proj₁ (M (bits n r)))) *ᴰ phase (neg (proj₂ (M (bits n r))))
    ≡⟨ entry r c (c ≟F idx (proj₁ (M (bits n r)))) ⟩
  δ r (idx (proj₁ (N (bits n c)))) *ᴰ phase (proj₂ (N (bits n c)))
    ≡⟨ Eq.sym (ent-mat N r c) ⟩
  ent (mat N) r c
    ∎
  where
  open Eq.≡-Reasoning
  entry : ∀ r c → Dec (c ≡ idx (proj₁ (M (bits n r)))) →
          δ c (idx (proj₁ (M (bits n r)))) *ᴰ phase (neg (proj₂ (M (bits n r))))
          ≡ δ r (idx (proj₁ (N (bits n c)))) *ᴰ phase (proj₂ (N (bits n c)))
  entry r c (yes e) = begin
    δ c (idx (proj₁ (M x))) *ᴰ phase (neg (proj₂ (M x)))
      ≡⟨ Eq.cong (_*ᴰ phase (neg (proj₂ (M x)))) (δ-eq e) ⟩
    1ᴰ *ᴰ phase (neg (proj₂ (M x)))
      ≡⟨ Eq.cong (λ a → 1ᴰ *ᴰ phase a) (Eq.sym phN) ⟩
    1ᴰ *ᴰ phase (proj₂ (N (bits n c)))
      ≡⟨ Eq.cong (_*ᴰ phase (proj₂ (N (bits n c)))) (Eq.sym (δ-eq r≡)) ⟩
    δ r (idx (proj₁ (N (bits n c)))) *ᴰ phase (proj₂ (N (bits n c)))
      ∎
    where
    x : Bits n
    x = bits n r
    bc : bits n c ≡ proj₁ (M x)
    bc = Eq.trans (Eq.cong (bits n) e) (bits-idx (proj₁ (M x)))
    back : proj₁ (N (bits n c)) ≡ x
    back = Eq.trans (Eq.cong (λ y → proj₁ (N y)) bc) (Eq.cong proj₁ (NM x))
    r≡ : r ≡ idx (proj₁ (N (bits n c)))
    r≡ = Eq.trans (Eq.sym (idx-bits n r)) (Eq.cong idx (Eq.sym back))
    phN : proj₂ (N (bits n c)) ≡ neg (proj₂ (M x))
    phN = Eq.trans (Eq.cong (λ y → proj₂ (N y)) bc)
            (neg-inv (proj₂ (M x)) (proj₂ (N (proj₁ (M x)))) (Eq.cong proj₂ (NM x)))
  entry r c (no ne) =
    Eq.trans (Eq.cong (_*ᴰ phase (neg (proj₂ (M (bits n r))))) (δ-≢ ne))
      (Eq.trans (DR.zeroˡ (phase (neg (proj₂ (M (bits n r))))))
        (Eq.sym (Eq.trans (Eq.cong (_*ᴰ phase (proj₂ (N (bits n c)))) (δ-≢ ne'))
                          (DR.zeroˡ (phase (proj₂ (N (bits n c))))))))
    where
    -- Row r of column c is nonzero only if f (bits r) = bits c.
    ne' : r ≢ idx (proj₁ (N (bits n c)))
    ne' q = ne (Eq.sym (Eq.trans
      (Eq.cong idx (Eq.trans (Eq.cong (λ y → proj₁ (M y))
                                      (Eq.trans (Eq.cong (bits n) q) (bits-idx (proj₁ (N (bits n c))))))
                             (Eq.cong proj₁ (MN (bits n c)))))
      (idx-bits n c)))

-- So the matrix of an invertible operator is unitary.
Unitary-mat : (M N : Op n) → (N ⊙ M) ≐ Idₒ → (M ⊙ N) ≐ Idₒ → Unitary (mat M)
Unitary-mat {n} M N NM MN =
  Eq.trans (Eq.cong (_·*· mat M) (mat-adjoint M N NM MN))
    (Eq.trans (Eq.sym (mat-⊙ N M)) (Eq.trans (mat-≐ NM) (mat-Id {n}))) ,
  Eq.trans (Eq.cong (mat M ·*·_) (mat-adjoint M N NM MN))
    (Eq.trans (Eq.sym (mat-⊙ M N)) (Eq.trans (mat-≐ MN) (mat-Id {n})))

------------------------------------------------------------------------
-- The matrix of a circuit

⟦_⟧ᵐ : Circuit n → Matrix (2 ^ n) (2 ^ n) D
⟦ w ⟧ᵐ = mat ⟦ w ⟧

-- It is unitary, its inverse being the matrix of the inverse circuit.
Unitary-⟦⟧ᵐ : (w : Circuit n) → Unitary ⟦ w ⟧ᵐ
Unitary-⟦⟧ᵐ {n} w = Unitary-mat ⟦ w ⟧ ⟦ w ⁻¹ ⟧
  (≐-trans (≐-sym (⟦⟧-• (w ⁻¹) w)) (≐-trans (sound (Inv.inverseˡ n {w})) ⟦⟧-ε))
  (≐-trans (≐-sym (⟦⟧-• w (w ⁻¹))) (≐-trans (sound (Inv.inverseʳ n {w})) ⟦⟧-ε))

⟦_⟧ᵘ : Circuit n → UMat (2 ^ n)
⟦ w ⟧ᵘ = ⟦ w ⟧ᵐ , Unitary-⟦⟧ᵐ w
