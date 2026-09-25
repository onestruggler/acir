------------------------------------------------------------------------
-- Presentations of groups
--
-- δ-adic scaling in 𝔻[ω]: the element w / δᵏ for w ∈ ℤ[ω].  Every
-- element of 𝔻[ω] has this form (so it has δ-exponents, Definition
-- 2.6), and the form determines w once k is fixed.  The scalars of
-- the generators: ω = emb ωᶻ, and 1/√2 = λω / δ² (λ = 1 + √2).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale where

open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
import Data.Nat.Solver as ℕSolver
open import Data.Product.Base using (∃ ; ∃₂ ; _,_)
open import Data.Bool.Base using (T)
import Data.Rational.Base as ℚ
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ ; *≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality

open import Instances using (toℚ)
open import Quantum.Synthesis.Ring
  using (Dyadic ; Dyadic' ; Omega ; 2^ ; Canonical ; ToRationalDyadic ; SemiRingDyadic ; RingDyadic
        ; SemiRingOmega ; RingOmega)
open import Quantum.Synthesis.Ring.Properties using (commutativeRing-𝔻)
open import Quantum.Synthesis.Ring.Properties.Dyadic
  using (toℚ-injective ; toℚ-u ; u ; u-* ; dyadic-spec′ ; nz)
import Quantum.Synthesis.Ring.Properties.Common as Common

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring

------------------------------------------------------------------------
-- Scalars ω and λω

-- λω = 1 + ω + ω², a unit of ℤ[ω].
λωᶻ : Z
λωᶻ = Omega (+ 0) (+ 1) (+ 1) (+ 1)

opaque
  unfolding _*ᴰ_

  -- 1/√2 = λω / δ².
  √½≡ : √½ ≡ emb λωᶻ DR.* (δ⁻ DR.* δ⁻)
  √½≡ = refl

------------------------------------------------------------------------
-- Scaling

-- sc is opaque, and sc-def unfolds it.
opaque
  -- sc k w = w / δᵏ.
  sc : ℕ → Z → D
  sc k w = emb w DR.* (δ⁻ ^ᴰ k)

  sc-def : ∀ k w → sc k w ≡ emb w DR.* (δ⁻ ^ᴰ k)
  sc-def k w = refl

sc-+ : ∀ k w w' → sc k (w ZR.+ w') ≡ sc k w DR.+ sc k w'
sc-+ k w w' = begin
  sc k (w ZR.+ w')                  ≡⟨ sc-def k (w ZR.+ w') ⟩
  emb (w ZR.+ w') DR.* X            ≡⟨ cong (DR._* X) (emb-+ w w') ⟩
  (emb w DR.+ emb w') DR.* X        ≡⟨ DR.distribʳ X (emb w) (emb w') ⟩
  emb w DR.* X DR.+ emb w' DR.* X   ≡⟨ sym (cong₂ DR._+_ (sc-def k w) (sc-def k w')) ⟩
  sc k w DR.+ sc k w'               ∎
  where
  open ≡-Reasoning
  X = δ⁻ ^ᴰ k

sc-neg : ∀ k w → sc k (ZR.- w) ≡ DR.- sc k w
sc-neg k w = begin
  sc k (ZR.- w)             ≡⟨ sc-def k (ZR.- w) ⟩
  emb (ZR.- w) DR.* X       ≡⟨ cong (DR._* X) (emb-neg w) ⟩
  (DR.- emb w) DR.* X       ≡⟨ DA.-‿*-distrib X (emb w) ⟩
  DR.- (emb w DR.* X)       ≡⟨ cong DR.-_ (sym (sc-def k w)) ⟩
  DR.- sc k w               ∎
  where
  open ≡-Reasoning
  X = δ⁻ ^ᴰ k

-- Scalars from ℤ[ω] pass through.
sc-* : ∀ k c w → sc k (c ZR.* w) ≡ emb c DR.* sc k w
sc-* k c w = begin
  sc k (c ZR.* w)               ≡⟨ sc-def k (c ZR.* w) ⟩
  emb (c ZR.* w) DR.* X         ≡⟨ cong (DR._* X) (emb-* c w) ⟩
  (emb c DR.* emb w) DR.* X     ≡⟨ DR.*-assoc (emb c) (emb w) X ⟩
  emb c DR.* (emb w DR.* X)     ≡⟨ cong (emb c DR.*_) (sym (sc-def k w)) ⟩
  emb c DR.* sc k w             ∎
  where
  open ≡-Reasoning
  X = δ⁻ ^ᴰ k

sc-0 : ∀ k → sc k ZR.0# ≡ DR.0#
sc-0 k = trans (sc-def k ZR.0#) (DR.zeroˡ (δ⁻ ^ᴰ k))

-- Dividing by δ once more.
δ⁻-sc : ∀ k w → δ⁻ DR.* sc k w ≡ sc (suc k) w
δ⁻-sc k w = begin
  δ⁻ DR.* sc k w                ≡⟨ cong (δ⁻ DR.*_) (sc-def k w) ⟩
  δ⁻ DR.* (emb w DR.* X)        ≡⟨ DA.*-3 δ⁻ (emb w) X ⟩
  emb w DR.* (δ⁻ DR.* X)        ≡⟨ sym (sc-def (suc k) w) ⟩
  sc (suc k) w                  ∎
  where
  open ≡-Reasoning
  X = δ⁻ ^ᴰ k

-- A factor δ in the numerator cancels one in the denominator.
sc-δ : ∀ k w → sc (suc k) (δᶻ ZR.* w) ≡ sc k w
sc-δ k w = begin
  sc (suc k) (δᶻ ZR.* w)                ≡⟨ sc-def (suc k) (δᶻ ZR.* w) ⟩
  emb (δᶻ ZR.* w) DR.* (δ⁻ DR.* X)      ≡⟨ cong (DR._* (δ⁻ DR.* X)) (emb-* δᶻ w) ⟩
  (δ DR.* emb w) DR.* (δ⁻ DR.* X)       ≡⟨ DA.*-4 δ (emb w) δ⁻ X ⟩
  (δ DR.* δ⁻) DR.* (emb w DR.* X)       ≡⟨ cong (DR._* (emb w DR.* X)) δ*δ⁻ ⟩
  DR.1# DR.* (emb w DR.* X)             ≡⟨ DR.*-identityˡ (emb w DR.* X) ⟩
  emb w DR.* X                          ≡⟨ sym (sc-def k w) ⟩
  sc k w                                ∎
  where
  open ≡-Reasoning
  X = δ⁻ ^ᴰ k

sc-δ^ : ∀ d k w → sc (d ℕ.+ k) ((δᶻ ^ᶻ d) ZR.* w) ≡ sc k w
sc-δ^ zero k w = cong (sc k) (ZR.*-identityˡ w)
sc-δ^ (suc d) k w = begin
  sc (suc (d ℕ.+ k)) ((δᶻ ZR.* (δᶻ ^ᶻ d)) ZR.* w)   ≡⟨ cong (sc (suc (d ℕ.+ k))) (ZR.*-assoc δᶻ (δᶻ ^ᶻ d) w) ⟩
  sc (suc (d ℕ.+ k)) (δᶻ ZR.* ((δᶻ ^ᶻ d) ZR.* w))   ≡⟨ sc-δ (d ℕ.+ k) ((δᶻ ^ᶻ d) ZR.* w) ⟩
  sc (d ℕ.+ k) ((δᶻ ^ᶻ d) ZR.* w)                   ≡⟨ sc-δ^ d k w ⟩
  sc k w                                           ∎
  where open ≡-Reasoning

-- Raising the exponent.
sc-raise : ∀ d k w → sc k w ≡ sc (d ℕ.+ k) ((δᶻ ^ᶻ d) ZR.* w)
sc-raise d k w = sym (sc-δ^ d k w)

-- The numerator is determined by the exponent.
sc-cancel : ∀ k w → sc k w DR.* (δ ^ᴰ k) ≡ emb w
sc-cancel k w = begin
  sc k w DR.* (δ ^ᴰ k)                ≡⟨ cong (DR._* (δ ^ᴰ k)) (sc-def k w) ⟩
  (emb w DR.* X) DR.* (δ ^ᴰ k)        ≡⟨ DR.*-assoc (emb w) X (δ ^ᴰ k) ⟩
  emb w DR.* (X DR.* (δ ^ᴰ k))        ≡⟨ cong (emb w DR.*_) (DA.^-inverse δ⁻ δ k δ⁻*δ) ⟩
  emb w DR.* DR.1#                    ≡⟨ DR.*-identityʳ (emb w) ⟩
  emb w                               ∎
  where
  open ≡-Reasoning
  X = δ⁻ ^ᴰ k

sc-injective : ∀ k {w w'} → sc k w ≡ sc k w' → w ≡ w'
sc-injective k {w} {w'} eq =
  emb-injective (trans (sym (sc-cancel k w)) (trans (cong (DR._* (δ ^ᴰ k)) eq) (sc-cancel k w')))

-- The Hadamard scalar: w / √2 at scale k is λω w at scale k + 2.
sc-√½ : ∀ k w → √½ DR.* sc k w ≡ sc (suc (suc k)) (λωᶻ ZR.* w)
sc-√½ k w = begin
  √½ DR.* sc k w                                          ≡⟨ cong₂ DR._*_ √½≡ (sc-def k w) ⟩
  (emb λωᶻ DR.* (δ⁻ DR.* δ⁻)) DR.* (emb w DR.* X)         ≡⟨ DA.*-4 (emb λωᶻ) (δ⁻ DR.* δ⁻) (emb w) X ⟩
  (emb λωᶻ DR.* emb w) DR.* ((δ⁻ DR.* δ⁻) DR.* X)         ≡⟨ cong₂ DR._*_ (sym (emb-* λωᶻ w)) (DR.*-assoc δ⁻ δ⁻ X) ⟩
  emb (λωᶻ ZR.* w) DR.* (δ⁻ DR.* (δ⁻ DR.* X))             ≡⟨ sym (sc-def (suc (suc k)) (λωᶻ ZR.* w)) ⟩
  sc (suc (suc k)) (λωᶻ ZR.* w)                           ∎
  where
  open ≡-Reasoning
  X = δ⁻ ^ᴰ k

-- The phase: ω w at scale k.
sc-ω : ∀ k w → ωᴰ DR.* sc k w ≡ sc k (ωᶻ ZR.* w)
sc-ω k w = sym (sc-* k ωᶻ w)

------------------------------------------------------------------------
-- Every element of 𝔻[ω] is some w / δᴷ

private
  -- Omega-scalar products, over an abstract commutative ring.
  module Scalar (R : CommutativeRing 0ℓ 0ℓ) where
    open CommutativeRing R using (Carrier ; _+_ ; _*_ ; -_ ; 0# ; _≈_) renaming (refl to ≈-refl)
    private
      module S = Common.ZSolver R
      open S using (solve ; _:+_ ; _:*_ ; :-_ ; _:=_ ; con)
    sa : ∀ p q r s t → p * t + q * 0# + r * 0# + s * 0# ≈ p * t
    sa = solve 5 (λ p q r s t → p :* t :+ q :* con (+ 0) :+ r :* con (+ 0) :+ s :* con (+ 0) := p :* t) ≈-refl
    sb : ∀ p q r s t → q * t + r * 0# + s * 0# + - (p * 0#) ≈ q * t
    sb = solve 5 (λ p q r s t → q :* t :+ r :* con (+ 0) :+ s :* con (+ 0) :+ :- (p :* con (+ 0)) := q :* t) ≈-refl
    sc′ : ∀ p q r s t → r * t + s * 0# + - (p * 0#) + - (q * 0#) ≈ r * t
    sc′ = solve 5 (λ p q r s t → r :* t :+ s :* con (+ 0) :+ :- (p :* con (+ 0)) :+ :- (q :* con (+ 0)) := r :* t) ≈-refl
    sd : ∀ p q r s t → s * t + - (p * 0#) + - (q * 0#) + - (r * 0#) ≈ s * t
    sd = solve 5 (λ p q r s t → s :* t :+ :- (p :* con (+ 0)) :+ :- (q :* con (+ 0)) :+ :- (r :* con (+ 0)) := s :* t) ≈-refl
    z0 : ∀ t → 0# * t ≈ 0#
    z0 = solve 1 (λ t → con (+ 0) :* t := con (+ 0)) ≈-refl

  module 𝔻Sc = Scalar commutativeRing-𝔻

  cong₄ : ∀ {A B C E F : Set} (f : A → B → C → E → F) {a a′ b b′ c c′ e e′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → f a b c e ≡ f a′ b′ c′ e′
  cong₄ f refl refl refl refl = refl

  -- The scalar t in 𝔻[ω].
  scal : Dyadic → D
  scal t = Omega 𝔻R.0# 𝔻R.0# 𝔻R.0# t

opaque
  unfolding _*ᴰ_

  -- A product with a scalar, componentwise.
  scal-* : ∀ p q r s t → Omega p q r s DR.* scal t ≡ Omega (p 𝔻R.* t) (q 𝔻R.* t) (r 𝔻R.* t) (s 𝔻R.* t)
  scal-* p q r s t = cong₄ Omega (𝔻Sc.sa p q r s t) (𝔻Sc.sb p q r s t) (𝔻Sc.sc′ p q r s t) (𝔻Sc.sd p q r s t)

private
  -- (a / d) · (d / 1) = a / 1 in the unnormalised rationals.
  /-cancel : ∀ a d .{{_ : ℕ.NonZero d}} →
             (a ℚᵘ./ d) ℚᵘ.* ((+ d) ℚᵘ./ 1) ℚᵘ.≃ (a ℚᵘ./ 1)
  /-cancel a (suc d) = *≡* (begin
    (a ℤ.* + suc d) ℤ.* + 1        ≡⟨ ℤP.*-identityʳ _ ⟩
    a ℤ.* + suc d                  ≡⟨ cong (λ k → a ℤ.* + k) (sym (ℕP.*-identityʳ (suc d))) ⟩
    a ℤ.* + (suc d ℕ.* 1)          ∎)
    where open ≡-Reasoning

  -- A dyadic fraction a/2ⁿ times 2ⁿ is a.
  dyadic-cancel : ∀ a n .(c : T (Canonical a n)) → Dyadic' a n c 𝔻R.* ι₀ (+ 2^ n) ≡ ι₀ a
  dyadic-cancel a n c = toℚ-injective (begin
    toℚ (x 𝔻R.* y)            ≡⟨ toℚ-u (x 𝔻R.* y) ⟩
    ℚ.fromℚᵘ (u (x 𝔻R.* y))   ≡⟨ ℚP.fromℚᵘ-cong (ℚᵘP.≃-trans (u-* dyadic-spec′ x y)
                                                              (/-cancel a (2^ n) {{nz n}})) ⟩
    ℚ.fromℚᵘ (u (ι₀ a))       ≡⟨ sym (toℚ-u (ι₀ a)) ⟩
    toℚ (ι₀ a)                ∎)
    where
    open ≡-Reasoning
    x = Dyadic' a n c
    y = ι₀ (+ 2^ n)

  -- a/2ⁿ · 2ⁿ⁺ᵐ = a·2ᵐ.
  dyadic-scale : ∀ a n m .(c : T (Canonical a n)) →
                 Dyadic' a n c 𝔻R.* ι₀ (+ 2^ (n ℕ.+ m)) ≡ ι₀ (a ℤ.* + 2^ m)
  dyadic-scale a n m c = begin
    x 𝔻R.* ι₀ (+ 2^ (n ℕ.+ m))                   ≡⟨ cong (λ k → x 𝔻R.* ι₀ (+ k)) (ℕP.^-distribˡ-+-* 2 n m) ⟩
    x 𝔻R.* ι₀ (+ (2^ n ℕ.* 2^ m))                ≡⟨ cong (λ z → x 𝔻R.* ι₀ z) (ℤP.pos-* (2^ n) (2^ m)) ⟩
    x 𝔻R.* ι₀ (+ 2^ n ℤ.* + 2^ m)                ≡⟨ cong (x 𝔻R.*_) (ι₀-* (+ 2^ n) (+ 2^ m)) ⟩
    x 𝔻R.* (ι₀ (+ 2^ n) 𝔻R.* ι₀ (+ 2^ m))        ≡⟨ sym (𝔻R.*-assoc x _ _) ⟩
    (x 𝔻R.* ι₀ (+ 2^ n)) 𝔻R.* ι₀ (+ 2^ m)        ≡⟨ cong (𝔻R._* ι₀ (+ 2^ m)) (dyadic-cancel a n c) ⟩
    ι₀ a 𝔻R.* ι₀ (+ 2^ m)                        ≡⟨ sym (ι₀-* a (+ 2^ m)) ⟩
    ι₀ (a ℤ.* + 2^ m)                            ∎
    where
    open ≡-Reasoning
    x = Dyadic' a n c

  -- a/2ⁿ · 2ᴺ = a · 2^(N - n), for N = n + m.
  scale-at : ∀ a n m N .(c : T (Canonical a n)) → N ≡ n ℕ.+ m →
             Dyadic' a n c 𝔻R.* ι₀ (+ 2^ N) ≡ ι₀ (a ℤ.* + 2^ m)
  scale-at a n m N c refl = dyadic-scale a n m c

  -- 2ᴺ in 𝔻[ω].
  two^ : ∀ N → emb 2ᶻ ^ᴰ N ≡ scal (ι₀ (+ 2^ N))
  two^ zero = refl
  two^ (suc N) = begin
    emb 2ᶻ DR.* (emb 2ᶻ ^ᴰ N)                          ≡⟨ cong (emb 2ᶻ DR.*_) (two^ N) ⟩
    emb 2ᶻ DR.* scal (ι₀ (+ 2^ N))                     ≡⟨ scal-* _ _ _ _ (ι₀ (+ 2^ N)) ⟩
    Omega (𝔻R.0# 𝔻R.* Tn) (𝔻R.0# 𝔻R.* Tn) (𝔻R.0# 𝔻R.* Tn) (ι₀ (+ 2) 𝔻R.* Tn)
      ≡⟨ cong₄ Omega (𝔻Sc.z0 Tn) (𝔻Sc.z0 Tn) (𝔻Sc.z0 Tn)
                     (trans (sym (ι₀-* (+ 2) (+ 2^ N))) (cong ι₀ (sym (ℤP.pos-* 2 (2^ N))))) ⟩
    scal (ι₀ (+ 2^ (suc N)))                           ∎
    where
    open ≡-Reasoning
    Tn = ι₀ (+ 2^ N)

  -- ½ = u / δ⁴ with u = δ⁴/2 = 2ω³ + 3ω² + 2ω, a unit of ℤ[ω].
  uᶻ : Z
  uᶻ = Omega (+ 2) (+ 3) (+ 2) (+ 0)

  ι : D
  ι = emb uᶻ DR.* (δ⁻ DR.* (δ⁻ DR.* (δ⁻ DR.* δ⁻)))

opaque
  unfolding _*ᴰ_

  2*ι : emb 2ᶻ DR.* ι ≡ DR.1#
  2*ι = refl

private
  module ℕS = ℕSolver.+-*-Solver

  -- The decomposition: x = w / δᴷ with K = 4N, w = uᴺ (x · 2ᴺ).
  rep′ : (x : D) → ∃₂ λ K w → x ≡ sc K w
  rep′ (Omega (Dyadic' a n₁ c₁) (Dyadic' b n₂ c₂) (Dyadic' c n₃ c₃) (Dyadic' d n₄ c₄)) =
    K , (uᶻ ^ᶻ N) ZR.* Wᶻ , (begin
      x                                             ≡⟨ sym (DR.*-identityʳ x) ⟩
      x DR.* DR.1#                                  ≡⟨ cong (x DR.*_) (sym (DA.^-inverse (emb 2ᶻ) ι N 2*ι)) ⟩
      x DR.* ((emb 2ᶻ ^ᴰ N) DR.* (ι ^ᴰ N))          ≡⟨ sym (DR.*-assoc x (emb 2ᶻ ^ᴰ N) (ι ^ᴰ N)) ⟩
      (x DR.* (emb 2ᶻ ^ᴰ N)) DR.* (ι ^ᴰ N)          ≡⟨ cong (DR._* (ι ^ᴰ N)) xW ⟩
      emb Wᶻ DR.* (ι ^ᴰ N)                           ≡⟨ cong (emb Wᶻ DR.*_) ιᴺ ⟩
      emb Wᶻ DR.* ((emb uᶻ ^ᴰ N) DR.* (δ⁻ ^ᴰ K))     ≡⟨ sym (DR.*-assoc (emb Wᶻ) (emb uᶻ ^ᴰ N) (δ⁻ ^ᴰ K)) ⟩
      (emb Wᶻ DR.* (emb uᶻ ^ᴰ N)) DR.* (δ⁻ ^ᴰ K)     ≡⟨ cong (DR._* (δ⁻ ^ᴰ K)) (DR.*-comm (emb Wᶻ) (emb uᶻ ^ᴰ N)) ⟩
      ((emb uᶻ ^ᴰ N) DR.* emb Wᶻ) DR.* (δ⁻ ^ᴰ K)     ≡⟨ cong (λ z → (z DR.* emb Wᶻ) DR.* (δ⁻ ^ᴰ K)) (sym (emb-^ uᶻ N)) ⟩
      (emb (uᶻ ^ᶻ N) DR.* emb Wᶻ) DR.* (δ⁻ ^ᴰ K)     ≡⟨ cong (DR._* (δ⁻ ^ᴰ K)) (sym (emb-* (uᶻ ^ᶻ N) Wᶻ)) ⟩
      emb ((uᶻ ^ᶻ N) ZR.* Wᶻ) DR.* (δ⁻ ^ᴰ K)        ≡⟨ sym (sc-def K ((uᶻ ^ᶻ N) ZR.* Wᶻ)) ⟩
      sc K ((uᶻ ^ᶻ N) ZR.* Wᶻ)                      ∎)
    where
    open ≡-Reasoning
    N = n₁ ℕ.+ n₂ ℕ.+ n₃ ℕ.+ n₄
    K = N ℕ.+ (N ℕ.+ (N ℕ.+ N))
    x = Omega (Dyadic' a n₁ c₁) (Dyadic' b n₂ c₂) (Dyadic' c n₃ c₃) (Dyadic' d n₄ c₄)
    m₁ = n₂ ℕ.+ n₃ ℕ.+ n₄
    m₂ = n₁ ℕ.+ n₃ ℕ.+ n₄
    m₃ = n₁ ℕ.+ n₂ ℕ.+ n₄
    m₄ = n₁ ℕ.+ n₂ ℕ.+ n₃
    Wᶻ = Omega (a ℤ.* + 2^ m₁) (b ℤ.* + 2^ m₂) (c ℤ.* + 2^ m₃) (d ℤ.* + 2^ m₄)
    open ℕS using (_:+_ ; _:=_)
    xW : x DR.* (emb 2ᶻ ^ᴰ N) ≡ emb Wᶻ
    xW = trans (cong (x DR.*_) (two^ N))
           (trans (scal-* _ _ _ _ (ι₀ (+ 2^ N)))
             (cong₄ Omega
               (scale-at a n₁ m₁ N c₁ (ℕS.solve 4 (λ p q r s → p :+ q :+ r :+ s := p :+ (q :+ r :+ s)) refl n₁ n₂ n₃ n₄))
               (scale-at b n₂ m₂ N c₂ (ℕS.solve 4 (λ p q r s → p :+ q :+ r :+ s := q :+ (p :+ r :+ s)) refl n₁ n₂ n₃ n₄))
               (scale-at c n₃ m₃ N c₃ (ℕS.solve 4 (λ p q r s → p :+ q :+ r :+ s := r :+ (p :+ q :+ s)) refl n₁ n₂ n₃ n₄))
               (scale-at d n₄ m₄ N c₄ (ℕS.solve 4 (λ p q r s → p :+ q :+ r :+ s := s :+ (p :+ q :+ r)) refl n₁ n₂ n₃ n₄))))
    -- ιᴺ = uᴺ δ⁻ᴷ.
    ιᴺ : ι ^ᴰ N ≡ (emb uᶻ ^ᴰ N) DR.* (δ⁻ ^ᴰ K)
    ιᴺ = trans (DA.^-*-distrib (emb uᶻ) (δ⁻ DR.* (δ⁻ DR.* (δ⁻ DR.* δ⁻))) N)
           (cong ((emb uᶻ ^ᴰ N) DR.*_)
             (trans (DA.^-*-distrib δ⁻ (δ⁻ DR.* (δ⁻ DR.* δ⁻)) N)
               (trans (cong ((δ⁻ ^ᴰ N) DR.*_)
                        (trans (DA.^-*-distrib δ⁻ (δ⁻ DR.* δ⁻) N)
                          (trans (cong ((δ⁻ ^ᴰ N) DR.*_) (trans (DA.^-*-distrib δ⁻ δ⁻ N) (sym (DA.^-+ δ⁻ N N))))
                                 (sym (DA.^-+ δ⁻ N (N ℕ.+ N))))))
                      (sym (DA.^-+ δ⁻ N (N ℕ.+ (N ℕ.+ N)))))))

-- Opaque, so that clients see only its type.
opaque
  rep : (x : D) → ∃₂ λ K w → x ≡ sc K w
  rep = rep′
