------------------------------------------------------------------------
-- Presentations of groups
--
-- γ-adic scaling in 𝔻[i]: the element w / γᵏ for w ∈ ℤ[i].  Every
-- element of 𝔻[i] has this form (so it has denominator exponents,
-- Definition "denominator exponent" of §2.1), and the form determines
-- w once k is fixed.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Scale where

open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; ∃₂ ; _,_)
open import Data.Bool.Base using (T)
import Data.Rational.Base as ℚ
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ ; *≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality

open import Instances using (toℚ)
open import Quantum.Synthesis.Ring
  using (Dyadic ; Dyadic' ; Cplx ; 2^ ; Canonical ; ToRationalDyadic ; SemiRingDyadic ; RingDyadic)
open import Quantum.Synthesis.Ring.Properties.Dyadic
  using (toℚ-injective ; toℚ-u ; u ; u-* ; dyadic-spec′ ; nz)
import Algebra.Properties.Ring as RingProperties

open import Examples.Groups.Clifford+CS-TwoLevel.Ring

------------------------------------------------------------------------
-- Scaling

-- sc is opaque: its lemmas below are all that is known of it, which
-- keeps the type checker from unfolding it into 𝔻[i] arithmetic.
opaque
  -- sc k w = w / γᵏ.
  sc : ℕ → Z → D
  sc k w = emb w DR.* (γ⁻ ^ᴰ k)

  sc-def : ∀ k w → sc k w ≡ emb w DR.* (γ⁻ ^ᴰ k)
  sc-def k w = refl

  sc-+ : ∀ k w w' → sc k (w ZR.+ w') ≡ sc k w DR.+ sc k w'
  sc-+ k w w' = trans (cong (DR._* (γ⁻ ^ᴰ k)) (emb-+ w w'))
                      (DA.+-*-distrib (γ⁻ ^ᴰ k) (emb w) (emb w'))

  sc-neg : ∀ k w → sc k (ZR.- w) ≡ DR.- sc k w
  sc-neg k w = trans (cong (DR._* (γ⁻ ^ᴰ k)) (emb-neg w)) (DA.-‿*-distrib (γ⁻ ^ᴰ k) (emb w))

  -- Scalars from ℤ[i] pass through.
  sc-* : ∀ k c w → sc k (c ZR.* w) ≡ emb c DR.* sc k w
  sc-* k c w = trans (cong (DR._* (γ⁻ ^ᴰ k)) (emb-* c w)) (DA.*-assoc (emb c) (emb w) (γ⁻ ^ᴰ k))

  sc-0 : ∀ k → sc k ZR.0# ≡ DR.0#
  sc-0 k = DR.zeroˡ (γ⁻ ^ᴰ k)

  -- Dividing by γ once more.
  γ⁻-sc : ∀ k w → γ⁻ DR.* sc k w ≡ sc (suc k) w
  γ⁻-sc k w = DA.*-3 γ⁻ (emb w) (γ⁻ ^ᴰ k)

  -- A factor γ in the numerator cancels one in the denominator.
  sc-γ : ∀ k w → sc (suc k) (γᶻ ZR.* w) ≡ sc k w
  sc-γ k w = begin
    emb (γᶻ ZR.* w) DR.* (γ⁻ DR.* (γ⁻ ^ᴰ k))       ≡⟨ cong (DR._* (γ⁻ DR.* (γ⁻ ^ᴰ k))) (emb-* γᶻ w) ⟩
    (γ DR.* emb w) DR.* (γ⁻ DR.* (γ⁻ ^ᴰ k))        ≡⟨ DA.*-4 γ (emb w) γ⁻ (γ⁻ ^ᴰ k) ⟩
    (γ DR.* γ⁻) DR.* (emb w DR.* (γ⁻ ^ᴰ k))        ≡⟨ cong (DR._* sc k w) γ*γ⁻ ⟩
    DR.1# DR.* sc k w                              ≡⟨ DA.*-identityˡ (sc k w) ⟩
    sc k w                                         ∎
    where open ≡-Reasoning

  sc-γ^ : ∀ d k w → sc (d ℕ.+ k) ((γᶻ ^ᶻ d) ZR.* w) ≡ sc k w
  sc-γ^ zero k w = cong (sc k) (ZR.*-identityˡ w)
  sc-γ^ (suc d) k w = begin
    sc (suc (d ℕ.+ k)) ((γᶻ ZR.* (γᶻ ^ᶻ d)) ZR.* w)   ≡⟨ cong (sc (suc (d ℕ.+ k))) (ZR.*-assoc γᶻ (γᶻ ^ᶻ d) w) ⟩
    sc (suc (d ℕ.+ k)) (γᶻ ZR.* ((γᶻ ^ᶻ d) ZR.* w))   ≡⟨ sc-γ (d ℕ.+ k) ((γᶻ ^ᶻ d) ZR.* w) ⟩
    sc (d ℕ.+ k) ((γᶻ ^ᶻ d) ZR.* w)                   ≡⟨ sc-γ^ d k w ⟩
    sc k w                                           ∎
    where open ≡-Reasoning

  -- Raising the exponent.
  sc-raise : ∀ d k w → sc k w ≡ sc (d ℕ.+ k) ((γᶻ ^ᶻ d) ZR.* w)
  sc-raise d k w = sym (sc-γ^ d k w)

  -- The numerator is determined by the exponent.
  sc-cancel : ∀ k w → sc k w DR.* (γ ^ᴰ k) ≡ emb w
  sc-cancel k w = begin
    (emb w DR.* (γ⁻ ^ᴰ k)) DR.* (γ ^ᴰ k)    ≡⟨ DA.*-assoc (emb w) (γ⁻ ^ᴰ k) (γ ^ᴰ k) ⟩
    emb w DR.* ((γ⁻ ^ᴰ k) DR.* (γ ^ᴰ k))    ≡⟨ cong (emb w DR.*_) (DA.^-inverse γ⁻ γ k γ⁻*γ) ⟩
    emb w DR.* DR.1#                        ≡⟨ DR.*-identityʳ (emb w) ⟩
    emb w                                   ∎
    where open ≡-Reasoning

  sc-injective : ∀ k {w w'} → sc k w ≡ sc k w' → w ≡ w'
  sc-injective k {w} {w'} eq = emb-injective (begin
    emb w                    ≡⟨ sym (sc-cancel k w) ⟩
    sc k w DR.* (γ ^ᴰ k)     ≡⟨ cong (DR._* (γ ^ᴰ k)) eq ⟩
    sc k w' DR.* (γ ^ᴰ k)    ≡⟨ sc-cancel k w' ⟩
    emb w'                   ∎)
    where open ≡-Reasoning

------------------------------------------------------------------------
-- Every element of 𝔻[i] is some w / γᴷ

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

  -- 2ᴺ in ℤ[i].
  two^ : ℕ → Z
  two^ N = Cplx (+ 2^ N) (+ 0)

  two^≡ : ∀ N → two^ N ≡ 2ᶻ ^ᶻ N
  two^≡ zero = refl
  two^≡ (suc N) = begin
    Cplx (+ 2^ (suc N)) (+ 0)            ≡⟨ cong₂ Cplx re-eq refl ⟩
    2ᶻ ZR.* two^ N                       ≡⟨ cong (2ᶻ ZR.*_) (two^≡ N) ⟩
    2ᶻ ZR.* (2ᶻ ^ᶻ N)                    ∎
    where
    open ≡-Reasoning
    re-eq : + 2^ (suc N) ≡ + 2 ℤ.* + 2^ N ℤ.+ ℤ.- (+ 0 ℤ.* + 0)
    re-eq = trans (ℤP.pos-* 2 (2^ N)) (sym (ℤP.+-identityʳ _))

  -- x · 2ᴺ for x = a/2ⁿ + (b/2ᵐ) i and N = n + m.
  times-two^ : ∀ a n m b .(c : T (Canonical a n)) .(c' : T (Canonical b m)) →
               Cplx (Dyadic' a n c) (Dyadic' b m c') DR.* emb (two^ (n ℕ.+ m))
               ≡ emb (Cplx (a ℤ.* + 2^ m) (b ℤ.* + 2^ n))
  times-two^ a n m b c c' = cong₂ Cplx re-eq im-eq
    where
    open ≡-Reasoning
    x = Dyadic' a n c
    y = Dyadic' b m c'
    T′ = ι₀ (+ 2^ (n ℕ.+ m))
    re-eq : x 𝔻R.* T′ 𝔻R.- y 𝔻R.* 𝔻R.0# ≡ ι₀ (a ℤ.* + 2^ m)
    re-eq = begin
      x 𝔻R.* T′ 𝔻R.- y 𝔻R.* 𝔻R.0#     ≡⟨ cong (λ z → x 𝔻R.* T′ 𝔻R.- z) (𝔻R.zeroʳ y) ⟩
      x 𝔻R.* T′ 𝔻R.- 𝔻R.0#            ≡⟨ cong (x 𝔻R.* T′ 𝔻R.+_) -0#≈0# ⟩
      x 𝔻R.* T′ 𝔻R.+ 𝔻R.0#            ≡⟨ 𝔻R.+-identityʳ _ ⟩
      x 𝔻R.* T′                        ≡⟨ dyadic-scale a n m c ⟩
      ι₀ (a ℤ.* + 2^ m)               ∎
      where open RingProperties 𝔻R.ring using (-0#≈0#)
    im-eq : x 𝔻R.* 𝔻R.0# 𝔻R.+ y 𝔻R.* T′ ≡ ι₀ (b ℤ.* + 2^ n)
    im-eq = begin
      x 𝔻R.* 𝔻R.0# 𝔻R.+ y 𝔻R.* T′     ≡⟨ cong (𝔻R._+ y 𝔻R.* T′) (𝔻R.zeroʳ x) ⟩
      𝔻R.0# 𝔻R.+ y 𝔻R.* T′            ≡⟨ 𝔻R.+-identityˡ _ ⟩
      y 𝔻R.* T′                        ≡⟨ cong (λ k → y 𝔻R.* ι₀ (+ 2^ k)) (ℕP.+-comm n m) ⟩
      y 𝔻R.* ι₀ (+ 2^ (m ℕ.+ n))       ≡⟨ dyadic-scale b m n c' ⟩
      ι₀ (b ℤ.* + 2^ n)               ∎

private

  -- The decomposition: x = w / γᴷ with K = 2N, w = iᴺ(a·2ᵐ + b·2ⁿ i).
  rep′ : (x : D) → ∃₂ λ K w → x ≡ sc K w
  rep′ (Cplx (Dyadic' a n c) (Dyadic' b m c')) =
    N ℕ.+ N , (ⅈᶻ ^ᶻ N) ZR.* W , (begin
      x                                             ≡⟨ sym (DR.*-identityʳ x) ⟩
      x DR.* DR.1#                                  ≡⟨ cong (x DR.*_) (sym (DA.^-inverse (emb 2ᶻ) ι N refl)) ⟩
      x DR.* ((emb 2ᶻ ^ᴰ N) DR.* (ι ^ᴰ N))          ≡⟨ sym (DR.*-assoc x (emb 2ᶻ ^ᴰ N) (ι ^ᴰ N)) ⟩
      (x DR.* (emb 2ᶻ ^ᴰ N)) DR.* (ι ^ᴰ N)          ≡⟨ cong (λ z → (x DR.* z) DR.* (ι ^ᴰ N))
                                                          (trans (sym (emb-^ 2ᶻ N)) (cong emb (sym (two^≡ N)))) ⟩
      (x DR.* emb (two^ N)) DR.* (ι ^ᴰ N)           ≡⟨ cong (DR._* (ι ^ᴰ N)) (times-two^ a n m b c c') ⟩
      emb W DR.* (ι ^ᴰ N)                           ≡⟨ cong (emb W DR.*_) (DA.^-*-distrib ⅈ (γ⁻ DR.* γ⁻) N) ⟩
      emb W DR.* ((ⅈ ^ᴰ N) DR.* ((γ⁻ DR.* γ⁻) ^ᴰ N))  ≡⟨ cong (λ z → emb W DR.* ((ⅈ ^ᴰ N) DR.* z))
                                                            (trans (DA.^-*-distrib γ⁻ γ⁻ N) (sym (DA.^-+ γ⁻ N N))) ⟩
      emb W DR.* ((ⅈ ^ᴰ N) DR.* (γ⁻ ^ᴰ (N ℕ.+ N)))  ≡⟨ sym (DR.*-assoc (emb W) (ⅈ ^ᴰ N) (γ⁻ ^ᴰ (N ℕ.+ N))) ⟩
      (emb W DR.* (ⅈ ^ᴰ N)) DR.* (γ⁻ ^ᴰ (N ℕ.+ N))  ≡⟨ cong (DR._* (γ⁻ ^ᴰ (N ℕ.+ N))) (DR.*-comm (emb W) (ⅈ ^ᴰ N)) ⟩
      ((ⅈ ^ᴰ N) DR.* emb W) DR.* (γ⁻ ^ᴰ (N ℕ.+ N))  ≡⟨ cong (λ z → (z DR.* emb W) DR.* (γ⁻ ^ᴰ (N ℕ.+ N))) (sym (emb-^ ⅈᶻ N)) ⟩
      (emb (ⅈᶻ ^ᶻ N) DR.* emb W) DR.* (γ⁻ ^ᴰ (N ℕ.+ N))  ≡⟨ cong (DR._* (γ⁻ ^ᴰ (N ℕ.+ N))) (sym (emb-* (ⅈᶻ ^ᶻ N) W)) ⟩
      emb ((ⅈᶻ ^ᶻ N) ZR.* W) DR.* (γ⁻ ^ᴰ (N ℕ.+ N))     ≡⟨ sym (sc-def (N ℕ.+ N) ((ⅈᶻ ^ᶻ N) ZR.* W)) ⟩
      sc (N ℕ.+ N) ((ⅈᶻ ^ᶻ N) ZR.* W)               ∎)
    where
    open ≡-Reasoning
    N = n ℕ.+ m
    x = Cplx (Dyadic' a n c) (Dyadic' b m c')
    W = Cplx (a ℤ.* + 2^ m) (b ℤ.* + 2^ n)
    -- 1/2 = i/γ², so 2ᴺ · (i γ⁻ γ⁻)ᴺ = 1.
    ι = ⅈ DR.* (γ⁻ DR.* γ⁻)

-- Opaque, so that clients see only its type.
opaque
  rep : (x : D) → ∃₂ λ K w → x ≡ sc K w
  rep = rep′
