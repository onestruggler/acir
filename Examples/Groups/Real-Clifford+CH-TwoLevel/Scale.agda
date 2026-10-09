------------------------------------------------------------------------
-- Presentations of groups
--
-- Scaled elements: w / √2ᵏ for w ∈ ℤ[√2], written sc k w.  Every
-- element of 𝔻[√2] = ℤ[1/√2] is of this form (rep), and the Hadamard
-- scalar 1/√2 raises the exponent by one (√½-sc).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Scale where

open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
import Data.Nat.Solver as ℕSolver
open import Data.Product.Base using (∃₂ ; _,_)
open import Data.Bool.Base using (T)
import Data.Rational.Base as ℚ
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ ; *≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality

open import Instances using (toℚ)
open import Quantum.Synthesis.Ring
  using (Dyadic ; Dyadic' ; RootTwo ; 2^ ; Canonical ; ToRationalDyadic ; SemiRingDyadic ; RingDyadic
        ; SemiRingRootTwo ; RingRootTwo)
open import Quantum.Synthesis.Ring.Properties using (commutativeRing-𝔻)
open import Quantum.Synthesis.Ring.Properties.Dyadic
  using (toℚ-injective ; toℚ-u ; u ; u-* ; dyadic-spec′ ; nz)
import Quantum.Synthesis.Ring.Properties.Common as Common

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring

------------------------------------------------------------------------
-- Scaling
-- sc is opaque, and sc-def unfolds it.

opaque
  -- sc k w = w / √2ᵏ.
  sc : ℕ → Z → D
  sc k w = emb w DR.* (√½ ^ᴰ k)

  sc-def : ∀ k w → sc k w ≡ emb w DR.* (√½ ^ᴰ k)
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
  X = √½ ^ᴰ k

sc-neg : ∀ k w → sc k (ZR.- w) ≡ DR.- sc k w
sc-neg k w = begin
  sc k (ZR.- w)             ≡⟨ sc-def k (ZR.- w) ⟩
  emb (ZR.- w) DR.* X       ≡⟨ cong (DR._* X) (emb-neg w) ⟩
  (DR.- emb w) DR.* X       ≡⟨ DA.-‿*-distrib X (emb w) ⟩
  DR.- (emb w DR.* X)       ≡⟨ cong DR.-_ (sym (sc-def k w)) ⟩
  DR.- sc k w               ∎
  where
  open ≡-Reasoning
  X = √½ ^ᴰ k

-- Scalars from ℤ[√2] pass through.
sc-* : ∀ k c w → sc k (c ZR.* w) ≡ emb c DR.* sc k w
sc-* k c w = begin
  sc k (c ZR.* w)               ≡⟨ sc-def k (c ZR.* w) ⟩
  emb (c ZR.* w) DR.* X         ≡⟨ cong (DR._* X) (emb-* c w) ⟩
  (emb c DR.* emb w) DR.* X     ≡⟨ DR.*-assoc (emb c) (emb w) X ⟩
  emb c DR.* (emb w DR.* X)     ≡⟨ cong (emb c DR.*_) (sym (sc-def k w)) ⟩
  emb c DR.* sc k w             ∎
  where
  open ≡-Reasoning
  X = √½ ^ᴰ k

sc-0 : ∀ k → sc k ZR.0# ≡ DR.0#
sc-0 k = trans (sc-def k ZR.0#) (DR.zeroˡ (√½ ^ᴰ k))

-- Dividing by √2 once more: the Hadamard scalar.
√½-sc : ∀ k w → √½ DR.* sc k w ≡ sc (suc k) w
√½-sc k w = begin
  √½ DR.* sc k w                ≡⟨ cong (√½ DR.*_) (sc-def k w) ⟩
  √½ DR.* (emb w DR.* X)        ≡⟨ DA.*-3 √½ (emb w) X ⟩
  emb w DR.* (√½ DR.* X)        ≡⟨ sym (sc-def (suc k) w) ⟩
  sc (suc k) w                  ∎
  where
  open ≡-Reasoning
  X = √½ ^ᴰ k

-- A factor √2 in the numerator cancels one in the denominator.
sc-δ : ∀ k w → sc (suc k) (√2ᶻ ZR.* w) ≡ sc k w
sc-δ k w = begin
  sc (suc k) (√2ᶻ ZR.* w)               ≡⟨ sc-def (suc k) (√2ᶻ ZR.* w) ⟩
  emb (√2ᶻ ZR.* w) DR.* (√½ DR.* X)     ≡⟨ cong (DR._* (√½ DR.* X)) (emb-* √2ᶻ w) ⟩
  (√2ᴰ DR.* emb w) DR.* (√½ DR.* X)     ≡⟨ DA.*-4 √2ᴰ (emb w) √½ X ⟩
  (√2ᴰ DR.* √½) DR.* (emb w DR.* X)     ≡⟨ cong (DR._* (emb w DR.* X)) √2*√½ ⟩
  DR.1# DR.* (emb w DR.* X)             ≡⟨ DR.*-identityˡ (emb w DR.* X) ⟩
  emb w DR.* X                          ≡⟨ sym (sc-def k w) ⟩
  sc k w                                ∎
  where
  open ≡-Reasoning
  X = √½ ^ᴰ k

sc-δ^ : ∀ d k w → sc (d ℕ.+ k) ((√2ᶻ ^ᶻ d) ZR.* w) ≡ sc k w
sc-δ^ zero k w = cong (sc k) (ZR.*-identityˡ w)
sc-δ^ (suc d) k w = begin
  sc (suc (d ℕ.+ k)) ((√2ᶻ ZR.* (√2ᶻ ^ᶻ d)) ZR.* w)   ≡⟨ cong (sc (suc (d ℕ.+ k))) (ZR.*-assoc √2ᶻ (√2ᶻ ^ᶻ d) w) ⟩
  sc (suc (d ℕ.+ k)) (√2ᶻ ZR.* ((√2ᶻ ^ᶻ d) ZR.* w))   ≡⟨ sc-δ (d ℕ.+ k) ((√2ᶻ ^ᶻ d) ZR.* w) ⟩
  sc (d ℕ.+ k) ((√2ᶻ ^ᶻ d) ZR.* w)                   ≡⟨ sc-δ^ d k w ⟩
  sc k w                                             ∎
  where open ≡-Reasoning

-- Raising the exponent.
sc-raise : ∀ d k w → sc k w ≡ sc (d ℕ.+ k) ((√2ᶻ ^ᶻ d) ZR.* w)
sc-raise d k w = sym (sc-δ^ d k w)

-- The numerator is determined by the exponent.
sc-cancel : ∀ k w → sc k w DR.* (√2ᴰ ^ᴰ k) ≡ emb w
sc-cancel k w = begin
  sc k w DR.* (√2ᴰ ^ᴰ k)                ≡⟨ cong (DR._* (√2ᴰ ^ᴰ k)) (sc-def k w) ⟩
  (emb w DR.* X) DR.* (√2ᴰ ^ᴰ k)        ≡⟨ DR.*-assoc (emb w) X (√2ᴰ ^ᴰ k) ⟩
  emb w DR.* (X DR.* (√2ᴰ ^ᴰ k))        ≡⟨ cong (emb w DR.*_) (DA.^-inverse √½ √2ᴰ k √½*√2) ⟩
  emb w DR.* DR.1#                     ≡⟨ DR.*-identityʳ (emb w) ⟩
  emb w                                ∎
  where
  open ≡-Reasoning
  X = √½ ^ᴰ k

sc-injective : ∀ k {w w'} → sc k w ≡ sc k w' → w ≡ w'
sc-injective k {w} {w'} eq =
  emb-injective (trans (sym (sc-cancel k w)) (trans (cong (DR._* (√2ᴰ ^ᴰ k)) eq) (sc-cancel k w')))

------------------------------------------------------------------------
-- Every element of 𝔻[√2] is some w / √2ᴷ

private
  -- Rational multiples, over an abstract commutative ring.
  module Scalar (R : CommutativeRing 0ℓ 0ℓ) where
    open CommutativeRing R using (Carrier ; _+_ ; _*_ ; -_ ; 0# ; _≈_) renaming (refl to ≈-refl)
    private
      module S = Common.ZSolver R
      open S using (solve ; _:+_ ; _:*_ ; :-_ ; _:=_ ; con)

    sa : ∀ p q t → p * t + (q * 0# + q * 0#) ≈ p * t
    sa = solve 3 (λ p q t → p :* t :+ (q :* con (+ 0) :+ q :* con (+ 0)) := p :* t) ≈-refl

    sb : ∀ p q t → p * 0# + t * q ≈ q * t
    sb = solve 3 (λ p q t → p :* con (+ 0) :+ t :* q := q :* t) ≈-refl

    z0 : ∀ t → 0# * t ≈ 0#
    z0 = solve 1 (λ t → con (+ 0) :* t := con (+ 0)) ≈-refl

  module 𝔻Sc = Scalar commutativeRing-𝔻

  -- The rational scalar t in 𝔻[√2].
  scal : Dyadic → D
  scal t = RootTwo 𝔻R.0# t

opaque
  unfolding _*ᴰ_

  -- A product with a rational scalar, componentwise.
  scal-* : ∀ p q t → RootTwo p q DR.* RootTwo t 𝔻R.0# ≡ RootTwo (p 𝔻R.* t) (q 𝔻R.* t)
  scal-* p q t = cong₂ RootTwo (𝔻Sc.sa p q t) (𝔻Sc.sb p q t)

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

  -- 2 in both rings.
  2ᶻ : Z
  2ᶻ = RootTwo (+ 2) (+ 0)

  -- 2ᴺ in 𝔻[√2].
  two^ : ∀ N → emb 2ᶻ ^ᴰ N ≡ RootTwo (ι₀ (+ 2^ N)) 𝔻R.0#
  two^ zero = refl
  two^ (suc N) = begin
    emb 2ᶻ DR.* (emb 2ᶻ ^ᴰ N)                          ≡⟨ cong (emb 2ᶻ DR.*_) (two^ N) ⟩
    emb 2ᶻ DR.* RootTwo Tn 𝔻R.0#                       ≡⟨ scal-* _ _ Tn ⟩
    RootTwo (ι₀ (+ 2) 𝔻R.* Tn) (𝔻R.0# 𝔻R.* Tn)
      ≡⟨ cong₂ RootTwo (trans (sym (ι₀-* (+ 2) (+ 2^ N))) (cong ι₀ (sym (ℤP.pos-* 2 (2^ N)))))
                       (𝔻Sc.z0 Tn) ⟩
    RootTwo (ι₀ (+ 2^ (suc N))) 𝔻R.0#                  ∎
    where
    open ≡-Reasoning
    Tn = ι₀ (+ 2^ N)

opaque
  unfolding _*ᴰ_

  -- 2 · (1/√2)² = 1.
  2*½ : emb 2ᶻ DR.* (√½ DR.* √½) ≡ DR.1#
  2*½ = refl

private
  module ℕS = ℕSolver.+-*-Solver

  -- The decomposition: x = W / √2^(2N), W = x · 2ᴺ.
  rep′ : (x : D) → ∃₂ λ K w → x ≡ sc K w
  rep′ (RootTwo (Dyadic' a n₁ c₁) (Dyadic' b n₂ c₂)) =
    N ℕ.+ N , Wᶻ , (begin
      x                                             ≡⟨ sym (DR.*-identityʳ x) ⟩
      x DR.* DR.1#                                  ≡⟨ cong (x DR.*_) (sym (DA.^-inverse (emb 2ᶻ) (√½ DR.* √½) N 2*½)) ⟩
      x DR.* ((emb 2ᶻ ^ᴰ N) DR.* ((√½ DR.* √½) ^ᴰ N)) ≡⟨ sym (DR.*-assoc x (emb 2ᶻ ^ᴰ N) _) ⟩
      (x DR.* (emb 2ᶻ ^ᴰ N)) DR.* ((√½ DR.* √½) ^ᴰ N) ≡⟨ cong₂ DR._*_ xW ½ᴺ ⟩
      emb Wᶻ DR.* (√½ ^ᴰ (N ℕ.+ N))                  ≡⟨ sym (sc-def (N ℕ.+ N) Wᶻ) ⟩
      sc (N ℕ.+ N) Wᶻ                               ∎)
    where
    open ≡-Reasoning
    N = n₁ ℕ.+ n₂
    x = RootTwo (Dyadic' a n₁ c₁) (Dyadic' b n₂ c₂)
    Wᶻ = RootTwo (a ℤ.* + 2^ n₂) (b ℤ.* + 2^ n₁)
    open ℕS using (_:+_ ; _:=_)
    xW : x DR.* (emb 2ᶻ ^ᴰ N) ≡ emb Wᶻ
    xW = trans (cong (x DR.*_) (two^ N))
           (trans (scal-* _ _ (ι₀ (+ 2^ N)))
             (cong₂ RootTwo
               (scale-at a n₁ n₂ N c₁ refl)
               (scale-at b n₂ n₁ N c₂ (ℕS.solve 2 (λ p q → p :+ q := q :+ p) refl n₁ n₂))))
    ½ᴺ : (√½ DR.* √½) ^ᴰ N ≡ √½ ^ᴰ (N ℕ.+ N)
    ½ᴺ = trans (DA.^-*-distrib √½ √½ N) (sym (DA.^-+ √½ N N))

-- Opaque, so that clients see only its type.
opaque
  rep : (x : D) → ∃₂ λ K w → x ≡ sc K w
  rep = rep′
