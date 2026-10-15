------------------------------------------------------------------------
-- Presentations of groups
--
-- From scaled Gaussian-integer operators to matrices over 𝔻[i], and
-- the completeness of the two-level relations in those terms
--
-- The circuits of this development denote scaled operators over ℤ[i]
-- (Semantics.Scaled): (ℓ , M) is the matrix γ^(−ℓ) M over 𝔻[i] =
-- ℤ[½,i], an operator being indexed by bit vectors.  The two-level
-- presentation of Bian and Selinger is proved complete in
-- Clifford+CS-TwoLevel for EucDomain matrices over 𝔻[i], indexed by
-- Fin N.  This module connects the two:
--
--   * Φ reads a scaled operator on n qubits as a 2ⁿ × 2ⁿ matrix over
--     𝔻[i] (basis states numbered with wire 0 the most significant bit,
--     Real-Clifford.Semantics.Matrix.idx); it sends ∙ to the matrix
--     product, ε∙ to the identity, and the scaling equivalence _~_ to
--     equality (Φ-∙, Φ-ε, Φ-cong) — a monoid homomorphism;
--   * TwoLevel n gives the one- and two-level generators on N = 2ⁿ
--     indices their scaled operators (⟦_⟧ʸ), each of which Φ sends to
--     the matrix Clifford+CS-TwoLevel gives it (Φ-gen), so that two
--     two-level words whose scaled readings agree have the same matrix,
--     and are therefore equal by the relations (complete-Y): the
--     completeness hypothesis of BackAndForth, discharged.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --lossy-unification #-}

module Examples.Groups.Clifford+CS.Bridge where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat using (ℕ ; zero ; suc ; _^_) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl ; module ≡-Reasoning)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Instances using (_+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Quantum.Synthesis.Ring
  using (Cplx ; SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)
open import Quantum.Synthesis.Ring.Properties using (isCommutativeRing-DComplex ; adj-DComplex)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS-TwoLevel.Ring
  using (D ; module DR ; emb ; emb-+ ; emb-* ; emb-neg ; γ⁻) renaming (γ to γᴰ)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics
  using ( ⟦_⟧ᵐ ; ⟦•⟧ᵐ ; ⟦g⟧ᵐ≡ ; gmat ; coef ; ent-gmat ; δ ; δ-refl ; δ-≢ ; 𝕀 ; mat-ext ; <⇒≢
        ; coef-X-a ; coef-X-b ; coef-X-≢ ; coef-K-a ; coef-K-b ; coef-K-≢ ; coef-i-a ; coef-i-≢ )
import Examples.Groups.Clifford+CS-TwoLevel.MainLemma as TLM

import Examples.Groups.Real-Clifford.Semantics.Laws
import Examples.Groups.Real-Clifford.Semantics.Matrix

import Examples.Groups.Clifford+CS.Semantics as C
open C using (Scaled ; _~_ ; _∙_ ; ε∙)
import Examples.Groups.Clifford+CS.BackAndForth as BackAndForth

module L = Examples.Groups.Real-Clifford.Semantics.Laws {A = D} isCommutativeRing-DComplex
module M = Examples.Groups.Real-Clifford.Semantics.Matrix {A = D} isCommutativeRing-DComplex adj-DComplex

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gaussian integers in 𝔻[i]

ι : C.𝔽 → D
ι (a C.+i b) = emb (Cplx a b)

ι-+ : ∀ x y → ι (x C.+ y) ≡ ι x + ι y
ι-+ (a C.+i b) (c C.+i d) = emb-+ (Cplx a b) (Cplx c d)

ι-* : ∀ x y → ι (x C.* y) ≡ ι x * ι y
ι-* (a C.+i b) (c C.+i d) = emb-* (Cplx a b) (Cplx c d)

ι-δb : (x y : C.Bits n) → ι (C.δb x y) ≡ L.δb x y
ι-δb []          []          = refl
ι-δb (true  ∷ x) (true  ∷ y) = ι-δb x y
ι-δb (false ∷ x) (false ∷ y) = ι-δb x y
ι-δb (true  ∷ x) (false ∷ y) = refl
ι-δb (false ∷ x) (true  ∷ y) = refl

ι-Σ : (f : C.Bits n → C.𝔽) → ι (C.Σb f) ≡ L.Σb (λ z → ι (f z))
ι-Σ {zero}  f = refl
ι-Σ {suc n} f =
  Eq.trans (ι-+ (C.Σb (λ bs → f (false ∷ bs))) (C.Σb (λ bs → f (true ∷ bs))))
           (Eq.cong₂ _+_ (ι-Σ (λ bs → f (false ∷ bs))) (ι-Σ (λ bs → f (true ∷ bs))))

------------------------------------------------------------------------
-- Powers of γ and of γ⁻¹ in 𝔻[i]

γ⁻^ γᴰ^ : ℕ → D
γ⁻^ zero    = 1#
γ⁻^ (suc k) = γ⁻ * γ⁻^ k
γᴰ^ zero    = 1#
γᴰ^ (suc k) = γᴰ * γᴰ^ k

ι-γ^ : ∀ k → ι (C.γ^ k) ≡ γᴰ^ k
ι-γ^ k = Eq.trans (Eq.cong ι (C.γ^-def k)) (go k)
  where
  go : ∀ k → ι (C.γ C.^ k) ≡ γᴰ^ k
  go zero    = refl
  go (suc k) = Eq.trans (ι-* C.γ (C.γ C.^ k)) (Eq.cong (γᴰ *_) (go k))

-- Rearranging four factors.  (The ring solver, run over 𝔻[i] with the
-- constants γ⁻ and γ among its arguments, exhausts the heap.)
cross : ∀ (a b c d : D) → (a * b) * (c * d) ≡ (a * c) * (b * d)
cross a b c d = begin
  (a * b) * (c * d)   ≡⟨ DR.*-assoc a b (c * d) ⟩
  a * (b * (c * d))   ≡⟨ Eq.cong (a *_) (Eq.sym (DR.*-assoc b c d)) ⟩
  a * ((b * c) * d)   ≡⟨ Eq.cong (λ x → a * (x * d)) (DR.*-comm b c) ⟩
  a * ((c * b) * d)   ≡⟨ Eq.cong (a *_) (DR.*-assoc c b d) ⟩
  a * (c * (b * d))   ≡⟨ Eq.sym (DR.*-assoc a c (b * d)) ⟩
  (a * c) * (b * d)   ∎
  where open ≡-Reasoning

γ⁻γ^ : ∀ k → γ⁻^ k * γᴰ^ k ≡ 1#
γ⁻γ^ zero    = DR.*-identityˡ 1#
γ⁻γ^ (suc k) = begin
  (γ⁻ * γ⁻^ k) * (γᴰ * γᴰ^ k)   ≡⟨ cross γ⁻ (γ⁻^ k) γᴰ (γᴰ^ k) ⟩
  (γ⁻ * γᴰ) * (γ⁻^ k * γᴰ^ k)   ≡⟨ Eq.cong ((γ⁻ * γᴰ) *_) (γ⁻γ^ k) ⟩
  (γ⁻ * γᴰ) * 1#                ≡⟨ DR.*-identityʳ (γ⁻ * γᴰ) ⟩
  γ⁻ * γᴰ                       ≡⟨⟩
  1#                            ∎
  where open ≡-Reasoning

γ⁻^-+ : ∀ m n → γ⁻^ (m +ℕ n) ≡ γ⁻^ m * γ⁻^ n
γ⁻^-+ zero    n = Eq.sym (DR.*-identityˡ (γ⁻^ n))
γ⁻^-+ (suc m) n = Eq.trans (Eq.cong (γ⁻ *_) (γ⁻^-+ m n)) (Eq.sym (DR.*-assoc γ⁻ (γ⁻^ m) (γ⁻^ n)))

------------------------------------------------------------------------
-- The operator over 𝔻[i] of a scaled operator, and its matrix

op : Scaled n → L.Op n
op (ℓ , A) x y = γ⁻^ ℓ * ι (A x y)

-- The matrix is opaque, and used through Φ-def and the lemmas below:
-- the conversion checker then compares two readings Φ s and Φ t by
-- comparing s and t, rather than by unfolding both to their entries
-- (2ⁿ × 2ⁿ expressions over 𝔻[i]).
opaque
  Φ : Scaled n → Matrix (2 ^ n) (2 ^ n) D
  Φ s = M.mat (op s)

  Φ-def : (s : Scaled n) → Φ s ≡ M.mat (op s)
  Φ-def s = refl

-- Equivalent scaled operators are the same operator over 𝔻[i].
op-cong : {s t : Scaled n} → s ~ t → op s L.≐ op t
op-cong {s = ℓ , A} {ℓ' , A'} e x y = begin
  γ⁻^ ℓ * u                               ≡⟨ Eq.sym (DR.*-identityʳ _) ⟩
  (γ⁻^ ℓ * u) * 1#                        ≡⟨ Eq.cong ((γ⁻^ ℓ * u) *_) (Eq.sym (γ⁻γ^ ℓ')) ⟩
  (γ⁻^ ℓ * u) * (γ⁻^ ℓ' * γᴰ^ ℓ')         ≡⟨ cross (γ⁻^ ℓ) u (γ⁻^ ℓ') (γᴰ^ ℓ') ⟩
  (γ⁻^ ℓ * γ⁻^ ℓ') * (u * γᴰ^ ℓ')         ≡⟨ Eq.cong ((γ⁻^ ℓ * γ⁻^ ℓ') *_) (DR.*-comm u (γᴰ^ ℓ')) ⟩
  (γ⁻^ ℓ * γ⁻^ ℓ') * (γᴰ^ ℓ' * u)         ≡⟨ Eq.cong ((γ⁻^ ℓ * γ⁻^ ℓ') *_) key ⟩
  (γ⁻^ ℓ * γ⁻^ ℓ') * (γᴰ^ ℓ * v)          ≡⟨ cross (γ⁻^ ℓ) (γ⁻^ ℓ') (γᴰ^ ℓ) v ⟩
  (γ⁻^ ℓ * γᴰ^ ℓ) * (γ⁻^ ℓ' * v)          ≡⟨ DR.*-comm (γ⁻^ ℓ * γᴰ^ ℓ) (γ⁻^ ℓ' * v) ⟩
  (γ⁻^ ℓ' * v) * (γ⁻^ ℓ * γᴰ^ ℓ)          ≡⟨ Eq.cong ((γ⁻^ ℓ' * v) *_) (γ⁻γ^ ℓ) ⟩
  (γ⁻^ ℓ' * v) * 1#                       ≡⟨ DR.*-identityʳ _ ⟩
  γ⁻^ ℓ' * v                              ∎
  where
  open ≡-Reasoning
  u v : D
  u = ι (A x y)
  v = ι (A' x y)
  key : γᴰ^ ℓ' * u ≡ γᴰ^ ℓ * v
  key = Eq.trans (Eq.cong (_* u) (Eq.sym (ι-γ^ ℓ')))
          (Eq.trans (Eq.sym (ι-* (C.γ^ ℓ') (A x y)))
            (Eq.trans (Eq.cong ι (e x y))
              (Eq.trans (ι-* (C.γ^ ℓ) (A' x y)) (Eq.cong (_* v) (ι-γ^ ℓ)))))

-- The product is the product.
op-∙ : (s t : Scaled n) → op (s ∙ t) L.≐ (op s L.⊙ op t)
op-∙ (ℓ , A) (ℓ' , A') x y = begin
  γ⁻^ (ℓ +ℕ ℓ') * ι (C.Σb (λ z → A x z C.* A' z y))
    ≡⟨ Eq.cong (γ⁻^ (ℓ +ℕ ℓ') *_) (ι-Σ (λ z → A x z C.* A' z y)) ⟩
  γ⁻^ (ℓ +ℕ ℓ') * L.Σb (λ z → ι (A x z C.* A' z y))
    ≡⟨ Eq.sym (L.Σ-scaleˡ (γ⁻^ (ℓ +ℕ ℓ')) (λ z → ι (A x z C.* A' z y))) ⟩
  L.Σb (λ z → γ⁻^ (ℓ +ℕ ℓ') * ι (A x z C.* A' z y))
    ≡⟨ L.Σ-cong step ⟩
  L.Σb (λ z → (γ⁻^ ℓ * ι (A x z)) * (γ⁻^ ℓ' * ι (A' z y))) ∎
  where
  open ≡-Reasoning
  step : ∀ z → γ⁻^ (ℓ +ℕ ℓ') * ι (A x z C.* A' z y) ≡ (γ⁻^ ℓ * ι (A x z)) * (γ⁻^ ℓ' * ι (A' z y))
  step z = Eq.trans (Eq.cong₂ _*_ (γ⁻^-+ ℓ ℓ') (ι-* (A x z) (A' z y)))
             (cross (γ⁻^ ℓ) (γ⁻^ ℓ') (ι (A x z)) (ι (A' z y)))

op-ε : op (ε∙ {n}) L.≐ L.Idₒ
op-ε x y = Eq.trans (DR.*-identityˡ _) (ι-δb x y)

Φ-cong : {s t : Scaled n} → s ~ t → Φ s ≡ Φ t
Φ-cong {s = s} {t} e =
  Eq.trans (Φ-def s) (Eq.trans (M.mat-≐ {M = op s} {N = op t} (op-cong {s = s} {t} e)) (Eq.sym (Φ-def t)))

Φ-∙ : (s t : Scaled n) → Φ (s ∙ t) ≡ Φ s ·*· Φ t
Φ-∙ s t =
  Eq.trans (Φ-def (s ∙ t))
    (Eq.trans (M.mat-≐ {M = op (s ∙ t)} {N = op s L.⊙ op t} (op-∙ s t))
      (Eq.trans (M.mat-⊙ (op s) (op t)) (Eq.sym (Eq.cong₂ _·*·_ (Φ-def s) (Φ-def t)))))

Φ-ε : Φ (ε∙ {n}) ≡ 𝕀
Φ-ε {n} = Eq.trans (Φ-def (ε∙ {n})) (Eq.trans (M.mat-≐ {M = op (ε∙ {n})} {N = L.Idₒ} op-ε) (M.mat-Id {n}))

------------------------------------------------------------------------
-- The two-level generators on 2ⁿ indices, as scaled operators

module TwoLevel (n : ℕ) where

  private
    N : ℕ
    N = 2 ^ n

  -- Kronecker's delta, over ℤ[i].
  δᶠ : Fin N → Fin N → C.𝔽
  δᶠ x y with x FinP.≟ y
  ... | yes _ = C.1#
  ... | no  _ = C.0#

  -- A word of caution: a `with` on x ≟ y whose goal mentions the
  -- matrices of Clifford+CS-TwoLevel (δ, coef) exhausts the heap — the
  -- abstraction normalises the ring structures those carry as module
  -- parameters.  So the comparisons below are decided first, and the
  -- equations are rewritten with Clifford+CS-TwoLevel's lemmas.
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

  -- The coefficients, γ^scale times those of Clifford+CS-TwoLevel
  -- (Action.coef), row by row.
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

  -- The rows.
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

  -- The scaled operator of a generator.
  ⟦_⟧ʸ : TL.Gen N → Scaled n
  ⟦ g ⟧ʸ = scale g , λ x y → coefℤ g (M.idx x) (M.idx y)

  private
    -- One row: rewrite both sides by their row lemmas.
    row : ∀ g r x {u : C.𝔽} {d : D} → coefℤ g r x ≡ u → coef g r x ≡ d →
          γ⁻^ (scale g) * ι u ≡ d → γ⁻^ (scale g) * ι (coefℤ g r x) ≡ coef g r x
    row g r x cu cd e = Eq.trans (Eq.cong (λ v → γ⁻^ (scale g) * ι v) cu) (Eq.trans e (Eq.sym cd))

    -- Case analysis on an index comparison.
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
          (γ⁻ * 1#) * (γᴰ * ι (δᶠ r x))    ≡⟨ Eq.cong (_* (γᴰ * ι (δᶠ r x))) (DR.*-identityʳ γ⁻) ⟩
          γ⁻ * (γᴰ * ι (δᶠ r x))           ≡⟨ Eq.sym (DR.*-assoc γ⁻ γᴰ (ι (δᶠ r x))) ⟩
          (γ⁻ * γᴰ) * ι (δᶠ r x)           ≡⟨ DR.*-identityˡ _ ⟩
          ι (δᶠ r x)                       ≡⟨ ι-δᶠ r x ⟩
          δ r x                            ∎))
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
        ≡⟨ Eq.cong (λ A → ent A r c) (Φ-def ⟦ g ⟧ʸ) ⟩
      ent (M.mat (op ⟦ g ⟧ʸ)) r c
        ≡⟨ M.ent-mat (op ⟦ g ⟧ʸ) r c ⟩
      γ⁻^ (scale g) * ι (coefℤ g (M.idx (M.bits n r)) (M.idx (M.bits n c)))
        ≡⟨ Eq.cong₂ (λ r′ c′ → γ⁻^ (scale g) * ι (coefℤ g r′ c′)) (M.idx-bits n r) (M.idx-bits n c) ⟩
      γ⁻^ (scale g) * ι (coefℤ g r c)
        ≡⟨ coef-ok g r c ⟩
      coef g r c
        ≡⟨ Eq.sym (ent-gmat g r c) ⟩
      ent (gmat g) r c ∎)
    (Eq.sym (⟦g⟧ᵐ≡ g))
    where
    open ≡-Reasoning
    open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (ent)

  ----------------------------------------------------------------------
  -- Words, and the completeness of the two-level relations

  module BF = BackAndForth n (TL._===_ {N}) ⟦_⟧ʸ
  open BF using (⟦_⟧Y) public

  Φ-Y : ∀ u → Φ ⟦ u ⟧Y ≡ ⟦ u ⟧ᵐ
  Φ-Y [ g ]ʷ  = Φ-gen g
  Φ-Y ε       = Φ-ε {n}
  Φ-Y (u • t) = Eq.trans (Φ-∙ ⟦ u ⟧Y ⟦ t ⟧Y)
                  (Eq.trans (Eq.cong₂ _·*·_ (Φ-Y u) (Φ-Y t)) (Eq.sym (⟦•⟧ᵐ u t)))

  -- Two two-level words with the same scaled matrix are equal by the
  -- relations of Figure 1 of Bian and Selinger.
  complete-Y : ∀ {u t : Word (TL.Gen N)} → ⟦ u ⟧Y ~ ⟦ t ⟧Y → PB._≈_ (TL._===_ {N}) u t
  complete-Y {u} {t} e =
    TLM.relations-complete {N} (Eq.trans (Eq.sym (Φ-Y u)) (Eq.trans (Φ-cong {s = ⟦ u ⟧Y} {⟦ t ⟧Y} e) (Φ-Y t)))
