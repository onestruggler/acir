------------------------------------------------------------------------
-- Presentations of groups
--
-- The bridge at the Gray numbering: scaled operators on n qubits as
-- matrices over 𝔻[i] with the basis vectors numbered by the Gray code,
-- and the completeness of the two-level relations and of the P′ rules
-- in those terms
--
-- Bridge reads a scaled operator as a matrix with the basis vectors
-- in binary order (Real-Clifford.Semantics.Matrix.idx).  From four
-- wires on the auxiliary letters are indexed in Gray order
-- (Numbering), so the same reading is needed at that numbering:
--
--   * Φ s is the matrix with entry op s (cod r) (cod c) at (r , c); it
--     is a monoid homomorphism (Φ-∙, Φ-ε: a sum over bit vectors is a
--     sum over Fin N, renumbered through the binary numbering and the
--     permutation Π), it identifies the pairs _~_ does (Φ-cong), and
--     it identifies no others (Φ-inj: the entries are γ⁻ᵏ times an
--     image of ℤ[i], and ι is injective);
--   * ⟦_⟧ʸ gives the two-level generators on N indices their scaled
--     operators at the Gray numbering, each of which Φ sends to the
--     matrix Clifford+CS-TwoLevel gives it (Φ-gen), so two two-level
--     words with the same scaled reading are equal by the relations
--     (complete-Y) and conversely (sound-Y);
--   * ⟦_⟧ᴾ reads a letter of P′ through its spelling asG, and
--     complete-P is the completeness of the P′ rules for that reading
--     (Auxiliary.Theorem410): the hypothesis of BackAndForth from four
--     wires on.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.BridgeGray (n : ℕ) where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Fin.Permutation using (Permutation ; permutation ; _⟨$⟩ʳ_)
open import Data.Nat using (zero ; suc ; _^_ ; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; _≢_ ; refl ; module ≡-Reasoning)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Instances using (_+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Quantum.Synthesis.Ring
  using (Cplx ; SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS-TwoLevel.Ring
  using (D ; module DR ; emb-injective ; emb-neg ; γ⁻) renaming (γ to γᴰ)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics
  using ( ⟦_⟧ᵐ ; ⟦•⟧ᵐ ; ⟦g⟧ᵐ≡ ; gmat ; coef ; ent-gmat ; δ ; δ-refl ; δ-≢ ; 𝕀 ; mat-ext
        ; ent ; mk ; ent-mk ; ent-·*· ; ent-𝕀 ; sum ; sum-cong-≗ ; <⇒≢
        ; coef-X-a ; coef-X-b ; coef-X-≢ ; coef-K-a ; coef-K-b ; coef-K-≢ ; coef-i-a ; coef-i-≢ )
open import Algebra.Properties.CommutativeMonoid.Sum DR.+-commutativeMonoid using (sum-permute)

import Examples.Groups.Clifford+CS.Semantics as C
open C using (Scaled ; _~_ ; _∙_ ; ε∙)
import Examples.Groups.Clifford+CS.Bridge as B
open B using (ι ; ι-+ ; ι-* ; γ⁻^ ; γᴰ^ ; ι-γ^ ; γ⁻γ^ ; op ; op-cong ; op-∙ ; module L ; module M)
open import Examples.Groups.Clifford+CS.Numbering n
import Examples.Groups.Clifford+CS.BackAndForth as BackAndForth

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)

------------------------------------------------------------------------
-- The algebra of the entries

private
  -- δ on bit vectors, off the diagonal.
  δb-≢ : ∀ {k} (x y : C.Bits k) → x ≢ y → C.δb x y ≡ C.0#
  δb-≢ []          []          ne = ⊥-elim (ne refl)
  δb-≢ (true ∷ x)  (true ∷ y)  ne = δb-≢ x y (λ e → ne (Eq.cong (true ∷_) e))
  δb-≢ (false ∷ x) (false ∷ y) ne = δb-≢ x y (λ e → ne (Eq.cong (false ∷_) e))
  δb-≢ (true ∷ x)  (false ∷ y) ne = refl
  δb-≢ (false ∷ x) (true ∷ y)  ne = refl

  -- ι is injective.
  cplx-inj : ∀ {a b c d} → Cplx a b ≡ Cplx c d → (a C.+i b) ≡ (c C.+i d)
  cplx-inj refl = refl

  ι-inj : ∀ {u v : C.𝔽} → ι u ≡ ι v → u ≡ v
  ι-inj {a C.+i b} {c C.+i d} e = cplx-inj (emb-injective e)

  -- A power of γ⁻¹ is cancelled by the power of γ.
  γγ⁻ : ∀ k (u : D) → γᴰ^ k * (γ⁻^ k * u) ≡ u
  γγ⁻ k u = begin
    γᴰ^ k * (γ⁻^ k * u)   ≡⟨ Eq.sym (DR.*-assoc (γᴰ^ k) (γ⁻^ k) u) ⟩
    (γᴰ^ k * γ⁻^ k) * u   ≡⟨ Eq.cong (_* u) (Eq.trans (DR.*-comm (γᴰ^ k) (γ⁻^ k)) (γ⁻γ^ k)) ⟩
    1# * u                ≡⟨ DR.*-identityˡ u ⟩
    u                     ∎
    where open ≡-Reasoning

  swap₃ : ∀ (x y z : D) → x * (y * z) ≡ y * (x * z)
  swap₃ x y z = begin
    x * (y * z)   ≡⟨ Eq.sym (DR.*-assoc x y z) ⟩
    (x * y) * z   ≡⟨ Eq.cong (_* z) (DR.*-comm x y) ⟩
    (y * x) * z   ≡⟨ DR.*-assoc y x z ⟩
    y * (x * z)   ∎
    where open ≡-Reasoning

------------------------------------------------------------------------
-- Sums over bit vectors are sums over Fin N, numbered by cod

private
  π : Fin N → Fin (2 ^ n)
  π k = M.idx (cod k)

  π⁻ : Fin (2 ^ n) → Fin N
  π⁻ j = idx (M.bits n j)

  Π : Permutation N (2 ^ n)
  Π = permutation π π⁻
        (λ j → Eq.trans (Eq.cong M.idx (cod-idx (M.bits n j))) (M.idx-bits n j))
        (λ k → Eq.trans (Eq.cong idx (M.bits-idx (cod k))) (idx-cod k))

sum-cod : (h : C.Bits n → D) → sum (λ k → h (cod k)) ≡ L.Σb h
sum-cod h = begin
  sum (λ k → h (cod k))
    ≡⟨ sum-cong-≗ (λ k → Eq.cong h (Eq.sym (M.bits-idx (cod k)))) ⟩
  sum (λ k → h (M.bits n (π k)))
    ≡⟨ Eq.sym (sum-permute (λ j → h (M.bits n j)) Π) ⟩
  sum (λ j → h (M.bits n j))
    ≡⟨ M.Σb-sum n (λ j → h (M.bits n j)) ⟩
  L.Σb {n} (λ v → h (M.bits n (M.idx {n} v)))
    ≡⟨ L.Σ-cong {n} (λ v → Eq.cong h (M.bits-idx {n} v)) ⟩
  L.Σb h ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The matrix of a scaled operator

Φ : Scaled n → Matrix N N D
Φ s = mk (λ r c → op s (cod r) (cod c))

ent-Φ : ∀ s r c → ent (Φ s) r c ≡ op s (cod r) (cod c)
ent-Φ s = ent-mk (λ r c → op s (cod r) (cod c))

Φ-cong : {s t : Scaled n} → s ~ t → Φ s ≡ Φ t
Φ-cong {s} {t} e = mat-ext λ r c →
  Eq.trans (ent-Φ s r c) (Eq.trans (op-cong {s = s} {t} e (cod r) (cod c)) (Eq.sym (ent-Φ t r c)))

private
  ι-δ : ∀ r c → ι (C.δb (cod r) (cod c)) ≡ δ r c
  ι-δ r c = go (r FinP.≟ c)
    where
    go : Dec (r ≡ c) → ι (C.δb (cod r) (cod c)) ≡ δ r c
    go (yes refl) = Eq.trans (Eq.cong ι (C.δb-refl (cod r))) (Eq.sym (δ-refl r))
    go (no ne)    = Eq.trans (Eq.cong ι (δb-≢ (cod r) (cod c) (λ e → ne (cod-inj e))))
                             (Eq.sym (δ-≢ ne))

Φ-ε : Φ (ε∙ {n}) ≡ 𝕀
Φ-ε = mat-ext λ r c →
  Eq.trans (ent-Φ (ε∙ {n}) r c)
    (Eq.trans (DR.*-identityˡ _) (Eq.trans (ι-δ r c) (Eq.sym (ent-𝕀 r c))))

Φ-∙ : (s t : Scaled n) → Φ (s ∙ t) ≡ Φ s ·*· Φ t
Φ-∙ s t = mat-ext λ r c → begin
  ent (Φ (s ∙ t)) r c
    ≡⟨ ent-Φ (s ∙ t) r c ⟩
  op (s ∙ t) (cod r) (cod c)
    ≡⟨ op-∙ s t (cod r) (cod c) ⟩
  L.Σb (λ z → op s (cod r) z * op t z (cod c))
    ≡⟨ Eq.sym (sum-cod (λ z → op s (cod r) z * op t z (cod c))) ⟩
  sum (λ k → op s (cod r) (cod k) * op t (cod k) (cod c))
    ≡⟨ Eq.sym (sum-cong-≗ (λ k → Eq.cong₂ _*_ (ent-Φ s r k) (ent-Φ t k c))) ⟩
  sum (λ k → ent (Φ s) r k * ent (Φ t) k c)
    ≡⟨ Eq.sym (ent-·*· (Φ s) (Φ t) r c) ⟩
  ent (Φ s ·*· Φ t) r c ∎
  where open ≡-Reasoning

-- Φ identifies no pairs _~_ does not.
Φ-inj : {s t : Scaled n} → Φ s ≡ Φ t → s ~ t
Φ-inj {ℓ , A} {ℓ′ , A′} e x y = ι-inj (begin
  ι (C.γ^ ℓ′ C.* A x y)
    ≡⟨ ι-* (C.γ^ ℓ′) (A x y) ⟩
  ι (C.γ^ ℓ′) * a
    ≡⟨ Eq.cong (_* a) (ι-γ^ ℓ′) ⟩
  γᴰ^ ℓ′ * a
    ≡⟨ Eq.cong (γᴰ^ ℓ′ *_) (Eq.sym (γγ⁻ ℓ a)) ⟩
  γᴰ^ ℓ′ * (γᴰ^ ℓ * (γ⁻^ ℓ * a))
    ≡⟨ Eq.cong (λ v → γᴰ^ ℓ′ * (γᴰ^ ℓ * v)) E ⟩
  γᴰ^ ℓ′ * (γᴰ^ ℓ * (γ⁻^ ℓ′ * a′))
    ≡⟨ swap₃ (γᴰ^ ℓ′) (γᴰ^ ℓ) (γ⁻^ ℓ′ * a′) ⟩
  γᴰ^ ℓ * (γᴰ^ ℓ′ * (γ⁻^ ℓ′ * a′))
    ≡⟨ Eq.cong (γᴰ^ ℓ *_) (γγ⁻ ℓ′ a′) ⟩
  γᴰ^ ℓ * a′
    ≡⟨ Eq.cong (_* a′) (Eq.sym (ι-γ^ ℓ)) ⟩
  ι (C.γ^ ℓ) * a′
    ≡⟨ Eq.sym (ι-* (C.γ^ ℓ) (A′ x y)) ⟩
  ι (C.γ^ ℓ C.* A′ x y) ∎)
  where
  open ≡-Reasoning
  a a′ : D
  a  = ι (A x y)
  a′ = ι (A′ x y)

  -- The entry at (idx x , idx y).
  E : γ⁻^ ℓ * a ≡ γ⁻^ ℓ′ * a′
  E = begin
    γ⁻^ ℓ * ι (A x y)
      ≡⟨ Eq.cong₂ (λ u v → γ⁻^ ℓ * ι (A u v)) (Eq.sym (cod-idx x)) (Eq.sym (cod-idx y)) ⟩
    op (ℓ , A) (cod (idx x)) (cod (idx y))
      ≡⟨ Eq.sym (ent-Φ (ℓ , A) (idx x) (idx y)) ⟩
    ent (Φ (ℓ , A)) (idx x) (idx y)
      ≡⟨ Eq.cong (λ Mx → ent Mx (idx x) (idx y)) e ⟩
    ent (Φ (ℓ′ , A′)) (idx x) (idx y)
      ≡⟨ ent-Φ (ℓ′ , A′) (idx x) (idx y) ⟩
    op (ℓ′ , A′) (cod (idx x)) (cod (idx y))
      ≡⟨ Eq.cong₂ (λ u v → γ⁻^ ℓ′ * ι (A′ u v)) (cod-idx x) (cod-idx y) ⟩
    γ⁻^ ℓ′ * ι (A′ x y) ∎

------------------------------------------------------------------------
-- The two-level generators on N indices, as scaled operators at the
-- Gray numbering (after Bridge.TwoLevel)

-- Kronecker's delta, over ℤ[i].
δᶠ : Fin N → Fin N → C.𝔽
δᶠ x y with x FinP.≟ y
... | yes _ = C.1#
... | no  _ = C.0#

private
  δᶠ-refl : ∀ x → δᶠ x x ≡ C.1#
  δᶠ-refl x with x FinP.≟ x
  ... | yes _   = refl
  ... | no  x≢x = ⊥-elim (x≢x refl)

  δᶠ-≢ : ∀ {x y} → x ≢ y → δᶠ x y ≡ C.0#
  δᶠ-≢ {x} {y} x≢y with x FinP.≟ y
  ... | yes x≡y = ⊥-elim (x≢y x≡y)
  ... | no  _   = refl

  ι-δᶠ : ∀ x y → ι (δᶠ x y) ≡ δ x y
  ι-δᶠ x y = go (x FinP.≟ y)
    where
    go : Dec (x ≡ y) → ι (δᶠ x y) ≡ δ x y
    go (yes refl) = Eq.trans (Eq.cong ι (δᶠ-refl x)) (Eq.sym (δ-refl x))
    go (no x≢y)   = Eq.trans (Eq.cong ι (δᶠ-≢ x≢y)) (Eq.sym (δ-≢ x≢y))

-- The power of γ⁻¹ a generator carries: one for K, none otherwise.
scale : TL.Gen N → ℕ
scale (TL.X-gen _ _ _) = 0
scale (TL.K-gen _ _ _) = 1
scale (TL.i-gen _)     = 0

-- The coefficients, γ^scale times those of Clifford+CS-TwoLevel, row
-- by row.
coefℤ : TL.Gen N → Fin N → Fin N → C.𝔽
coefℤ (TL.X-gen a b _) r x with r FinP.≟ a | r FinP.≟ b
... | yes _ | _     = δᶠ b x
... | no  _ | yes _ = δᶠ a x
... | no  _ | no  _ = δᶠ r x
coefℤ (TL.K-gen a b _) r x with r FinP.≟ a | r FinP.≟ b
... | yes _ | _     = δᶠ a x C.+ δᶠ b x
... | no  _ | yes _ = δᶠ a x C.+ C.- δᶠ b x
... | no  _ | no  _ = C.γ C.* δᶠ r x
coefℤ (TL.i-gen a) r x with r FinP.≟ a
... | yes _ = δᶠ r x C.* C.ⅈ
... | no  _ = δᶠ r x

private
  module _ {a b : Fin N} .(p : a < b) where
    private
      a≢b : a ≢ b
      a≢b = <⇒≢ p

    cX-a : ∀ x → coefℤ (TL.X-gen a b p) a x ≡ δᶠ b x
    cX-a x with a FinP.≟ a
    ... | yes _   = refl
    ... | no  a≢a = ⊥-elim (a≢a refl)

    cX-b : ∀ x → coefℤ (TL.X-gen a b p) b x ≡ δᶠ a x
    cX-b x with b FinP.≟ a | b FinP.≟ b
    ... | yes b≡a | _       = ⊥-elim (a≢b (Eq.sym b≡a))
    ... | no  _   | yes _   = refl
    ... | no  _   | no  b≢b = ⊥-elim (b≢b refl)

    cX-≢ : ∀ {r} → r ≢ a → r ≢ b → ∀ x → coefℤ (TL.X-gen a b p) r x ≡ δᶠ r x
    cX-≢ {r} r≢a r≢b x with r FinP.≟ a | r FinP.≟ b
    ... | yes r≡a | _       = ⊥-elim (r≢a r≡a)
    ... | no  _   | yes r≡b = ⊥-elim (r≢b r≡b)
    ... | no  _   | no  _   = refl

    cK-a : ∀ x → coefℤ (TL.K-gen a b p) a x ≡ δᶠ a x C.+ δᶠ b x
    cK-a x with a FinP.≟ a
    ... | yes _   = refl
    ... | no  a≢a = ⊥-elim (a≢a refl)

    cK-b : ∀ x → coefℤ (TL.K-gen a b p) b x ≡ δᶠ a x C.+ C.- δᶠ b x
    cK-b x with b FinP.≟ a | b FinP.≟ b
    ... | yes b≡a | _       = ⊥-elim (a≢b (Eq.sym b≡a))
    ... | no  _   | yes _   = refl
    ... | no  _   | no  b≢b = ⊥-elim (b≢b refl)

    cK-≢ : ∀ {r} → r ≢ a → r ≢ b → ∀ x → coefℤ (TL.K-gen a b p) r x ≡ C.γ C.* δᶠ r x
    cK-≢ {r} r≢a r≢b x with r FinP.≟ a | r FinP.≟ b
    ... | yes r≡a | _       = ⊥-elim (r≢a r≡a)
    ... | no  _   | yes r≡b = ⊥-elim (r≢b r≡b)
    ... | no  _   | no  _   = refl

  ci-a : ∀ a x → coefℤ (TL.i-gen a) a x ≡ δᶠ a x C.* C.ⅈ
  ci-a a x with a FinP.≟ a
  ... | yes _   = refl
  ... | no  a≢a = ⊥-elim (a≢a refl)

  ci-≢ : ∀ a {r} → r ≢ a → ∀ x → coefℤ (TL.i-gen a) r x ≡ δᶠ r x
  ci-≢ a {r} r≢a x with r FinP.≟ a
  ... | yes r≡a = ⊥-elim (r≢a r≡a)
  ... | no  _   = refl

-- The scaled operator of a generator, at the Gray numbering.
⟦_⟧ʸ : TL.Gen N → Scaled n
⟦ g ⟧ʸ = scale g , λ x y → coefℤ g (idx x) (idx y)

private
  row : ∀ g r x {u : C.𝔽} {d : D} → coefℤ g r x ≡ u → coef g r x ≡ d →
        γ⁻^ (scale g) * ι u ≡ d → γ⁻^ (scale g) * ι (coefℤ g r x) ≡ coef g r x
  row g r x cu cd e = Eq.trans (Eq.cong (λ v → γ⁻^ (scale g) * ι v) cu) (Eq.trans e (Eq.sym cd))

  cases : ∀ {P : Fin N → Set} {r : Fin N} (a : Fin N) →
          P a → (r ≢ a → P r) → P r
  cases {P} {r} a pa pn with r FinP.≟ a
  ... | yes refl = pa
  ... | no  r≢a  = pn r≢a

  ι-neg : ∀ y → ι (C.- y) ≡ - ι y
  ι-neg (a C.+i b) = emb-neg (Cplx a b)

  one-δ : ∀ r x → γ⁻^ 0 * ι (δᶠ r x) ≡ δ r x
  one-δ r x = Eq.trans (DR.*-identityˡ (ι (δᶠ r x))) (ι-δᶠ r x)

coef-ok : ∀ g r x → γ⁻^ (scale g) * ι (coefℤ g r x) ≡ coef g r x
coef-ok (TL.X-gen a b p) r x =
  cases {λ r → γ⁻^ 0 * ι (coefℤ (TL.X-gen a b p) r x) ≡ coef (TL.X-gen a b p) r x} {r} a
    (row (TL.X-gen a b p) a x (cX-a p x) (coef-X-a p x) (one-δ b x))
    (λ r≢a → cases {λ r → r ≢ a → γ⁻^ 0 * ι (coefℤ (TL.X-gen a b p) r x) ≡ coef (TL.X-gen a b p) r x} {r} b
      (λ _ → row (TL.X-gen a b p) b x (cX-b p x) (coef-X-b p x) (one-δ a x))
      (λ r≢b r≢a → row (TL.X-gen a b p) r x (cX-≢ p r≢a r≢b x) (coef-X-≢ p r≢a r≢b x) (one-δ r x))
      r≢a)
coef-ok (TL.K-gen a b p) r x =
  cases {λ r → γ⁻^ 1 * ι (coefℤ (TL.K-gen a b p) r x) ≡ coef (TL.K-gen a b p) r x} {r} a
    (row (TL.K-gen a b p) a x (cK-a p x) (coef-K-a p x)
      (Eq.cong₂ _*_ (DR.*-identityʳ γ⁻)
        (Eq.trans (ι-+ (δᶠ a x) (δᶠ b x)) (Eq.cong₂ _+_ (ι-δᶠ a x) (ι-δᶠ b x)))))
    (λ r≢a → cases {λ r → r ≢ a → γ⁻^ 1 * ι (coefℤ (TL.K-gen a b p) r x) ≡ coef (TL.K-gen a b p) r x} {r} b
      (λ _ → row (TL.K-gen a b p) b x (cK-b p x) (coef-K-b p x)
        (Eq.cong₂ _*_ (DR.*-identityʳ γ⁻)
          (Eq.trans (ι-+ (δᶠ a x) (C.- δᶠ b x))
            (Eq.cong₂ _+_ (ι-δᶠ a x) (Eq.trans (ι-neg (δᶠ b x)) (Eq.cong -_ (ι-δᶠ b x)))))))
      (λ r≢b r≢a → row (TL.K-gen a b p) r x (cK-≢ p r≢a r≢b x) (coef-K-≢ p r≢a r≢b x) (begin
        (γ⁻ * 1#) * ι (C.γ C.* δᶠ r x)   ≡⟨ Eq.cong ((γ⁻ * 1#) *_) (ι-* C.γ (δᶠ r x)) ⟩
        (γ⁻ * 1#) * (γᴰ * ι (δᶠ r x))  ≡⟨ Eq.cong (_* (γᴰ * ι (δᶠ r x))) (DR.*-identityʳ γ⁻) ⟩
        γ⁻ * (γᴰ * ι (δᶠ r x))         ≡⟨ Eq.sym (DR.*-assoc γ⁻ γᴰ (ι (δᶠ r x))) ⟩
        (γ⁻ * γᴰ) * ι (δᶠ r x)         ≡⟨ DR.*-identityˡ _ ⟩
        ι (δᶠ r x)                           ≡⟨ ι-δᶠ r x ⟩
        δ r x                                ∎))
      r≢a)
  where open ≡-Reasoning
coef-ok (TL.i-gen a) r x =
  cases {λ r → γ⁻^ 0 * ι (coefℤ (TL.i-gen a) r x) ≡ coef (TL.i-gen a) r x} {r} a
    (row (TL.i-gen a) a x (ci-a a x) (coef-i-a a x) (begin
      1# * ι (δᶠ a x C.* C.ⅈ)  ≡⟨ DR.*-identityˡ (ι (δᶠ a x C.* C.ⅈ)) ⟩
      ι (δᶠ a x C.* C.ⅈ)       ≡⟨ ι-* (δᶠ a x) C.ⅈ ⟩
      ι (δᶠ a x) * ι C.ⅈ       ≡⟨ Eq.cong (λ v → v * ι C.ⅈ) (ι-δᶠ a x) ⟩
      δ a x * ι C.ⅈ            ∎))
    (λ r≢a → row (TL.i-gen a) r x (ci-≢ a r≢a x) (coef-i-≢ a r≢a x) (one-δ r x))
  where open ≡-Reasoning

-- Each generator's scaled operator is its matrix.
Φ-gen : ∀ g → Φ ⟦ g ⟧ʸ ≡ ⟦ [ g ]ʷ ⟧ᵐ
Φ-gen g = Eq.trans (mat-ext λ r c → begin
    ent (Φ ⟦ g ⟧ʸ) r c
      ≡⟨ ent-Φ ⟦ g ⟧ʸ r c ⟩
    γ⁻^ (scale g) * ι (coefℤ g (idx (cod r)) (idx (cod c)))
      ≡⟨ Eq.cong₂ (λ r′ c′ → γ⁻^ (scale g) * ι (coefℤ g r′ c′)) (idx-cod r) (idx-cod c) ⟩
    γ⁻^ (scale g) * ι (coefℤ g r c)
      ≡⟨ coef-ok g r c ⟩
    coef g r c
      ≡⟨ Eq.sym (ent-gmat g r c) ⟩
    ent (gmat g) r c ∎)
  (Eq.sym (⟦g⟧ᵐ≡ g))
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Two-level words: completeness and soundness of the relations for
-- the scaled reading

module BF = BackAndForth n (TL._===_ {N}) ⟦_⟧ʸ
open BF using (⟦_⟧Y) public

Φ-Y : ∀ u → Φ ⟦ u ⟧Y ≡ ⟦ u ⟧ᵐ
Φ-Y [ g ]ʷ  = Φ-gen g
Φ-Y ε       = Φ-ε
Φ-Y (u • t) = Eq.trans (Φ-∙ ⟦ u ⟧Y ⟦ t ⟧Y)
                (Eq.trans (Eq.cong₂ _·*·_ (Φ-Y u) (Φ-Y t)) (Eq.sym (⟦•⟧ᵐ u t)))

private
  _≈ᵀ_ : Word (TL.Gen N) → Word (TL.Gen N) → Set
  _≈ᵀ_ = PB._≈_ (TL._===_ {N})

open import Examples.Groups.Clifford+CS-TwoLevel.MainLemma {N} using (relations-complete)
open import Examples.Groups.Clifford+CS-TwoLevel.Reduction {N} using (sound-act)

complete-Y : ∀ {u t : Word (TL.Gen N)} → ⟦ u ⟧Y ~ ⟦ t ⟧Y → u ≈ᵀ t
complete-Y {u} {t} e =
  relations-complete (Eq.trans (Eq.sym (Φ-Y u)) (Eq.trans (Φ-cong {s = ⟦ u ⟧Y} {⟦ t ⟧Y} e) (Φ-Y t)))

sound-Y : ∀ {u t : Word (TL.Gen N)} → u ≈ᵀ t → ⟦ u ⟧Y ~ ⟦ t ⟧Y
sound-Y {u} {t} e =
  Φ-inj {s = ⟦ u ⟧Y} {⟦ t ⟧Y} (Eq.trans (Φ-Y u) (Eq.trans (sound-act e 𝕀) (Eq.sym (Φ-Y t))))

------------------------------------------------------------------------
-- Words over P′, read through their spellings

⟦_⟧ᴾ : GenP N → Scaled n
⟦ x ⟧ᴾ = ⟦ asG x ⟧Y

module BFP = BackAndForth n (N R,_===_) ⟦_⟧ᴾ
open BFP using () renaming (⟦_⟧Y to ⟦_⟧PY) public

-- The reading of a word over P′ is that of its spelling.
PY-asG : ∀ (u : Word (GenP N)) → ⟦ u ⟧PY ~ ⟦ (asG ʷ) u ⟧Y
PY-asG [ x ]ʷ  = C.~-refl ⟦ asG x ⟧Y
PY-asG ε       = C.~-refl (ε∙ {n})
PY-asG (u • v) =
  C.∙-cong {s = ⟦ u ⟧PY} {s' = ⟦ (asG ʷ) u ⟧Y} {t = ⟦ v ⟧PY} {t' = ⟦ (asG ʷ) v ⟧Y}
           (PY-asG u) (PY-asG v)

-- Completeness of the P′ rules for the scaled reading, from sixteen
-- basis vectors on: the hypothesis of BackAndForth.
module Complete (big : 16 ≤ N) where

  open import Examples.Groups.Clifford+CS.Auxiliary.Theorem410 N′ big using (complete)

  complete-P : ∀ {u t : Word (GenP N)} → ⟦ u ⟧PY ~ ⟦ t ⟧PY → PB._≈_ (N R,_===_) u t
  complete-P {u} {t} e = complete {u} {t} (begin
    ⟦ (asG ʷ) u ⟧ᵐ
      ≡⟨ Eq.sym (Φ-Y ((asG ʷ) u)) ⟩
    Φ ⟦ (asG ʷ) u ⟧Y
      ≡⟨ Eq.sym (Φ-cong {s = ⟦ u ⟧PY} {⟦ (asG ʷ) u ⟧Y} (PY-asG u)) ⟩
    Φ ⟦ u ⟧PY
      ≡⟨ Φ-cong {s = ⟦ u ⟧PY} {⟦ t ⟧PY} e ⟩
    Φ ⟦ t ⟧PY
      ≡⟨ Φ-cong {s = ⟦ t ⟧PY} {⟦ (asG ʷ) t ⟧Y} (PY-asG t) ⟩
    Φ ⟦ (asG ʷ) t ⟧Y
      ≡⟨ Φ-Y ((asG ʷ) t) ⟩
    ⟦ (asG ʷ) t ⟧ᵐ ∎)
    where open ≡-Reasoning
