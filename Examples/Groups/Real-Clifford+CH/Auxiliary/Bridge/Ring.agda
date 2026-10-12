------------------------------------------------------------------------
-- Presentations of groups
--
-- ℤ[√2] of Semantics.Ring inside the ℤ[1/√2] of Real-Clifford+CH-TwoLevel
--
-- The bridge to Theorem 4.4 reads the matrices of this development, a
-- power of 1/√2 times a matrix over ℤ[√2] (Semantics.Scaled), as
-- matrices over the ring 𝔻[√2] = ℤ[1/√2] of Real-Clifford+CH-
-- TwoLevel, where the presentation of O_N(ℤ[1/√2]) by Figure 6 is
-- proved.  Its first piece is the ring map ι : a + b √2 ↦ a + b √2,
-- through EucDomain's ℤ[√2], and the powers of √2 and 1/√2 there.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Ring where

open import Data.Integer.Base as ℤ using (ℤ)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; cong ; cong₂ ; trans ; sym)

open import Quantum.Synthesis.Ring using (RootTwo)
import Examples.Groups.Real-Clifford+CH.Semantics.Ring as R
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; Z ; emb ; emb-+ ; emb-* ; emb-neg ; module DR ; module ZR ; √2ᴰ ; √½ ; √½*√2 ; -1ᴰ)

------------------------------------------------------------------------
-- The ring map

-- a + b √2 in EucDomain's ℤ[√2].
toZ : R.ℤ√2 → Z
toZ (a R.+√2 b) = RootTwo a b

private
  two : ∀ x → ℤ.+ 2 ℤ.* x ≡ x ℤ.+ x
  two x = trans (ℤP.*-distribʳ-+ x (ℤ.+ 1) (ℤ.+ 1)) (cong₂ ℤ._+_ (ℤP.*-identityˡ x) (ℤP.*-identityˡ x))

toZ-+ : ∀ x y → toZ (x R.+ y) ≡ toZ x ZR.+ toZ y
toZ-+ (a R.+√2 b) (c R.+√2 d) = refl

toZ-* : ∀ x y → toZ (x R.* y) ≡ toZ x ZR.* toZ y
toZ-* (a R.+√2 b) (c R.+√2 d) =
  cong₂ RootTwo (cong (λ t → a ℤ.* c ℤ.+ t) (two (b ℤ.* d))) (cong (λ t → a ℤ.* d ℤ.+ t) (ℤP.*-comm b c))

toZ-neg : ∀ x → toZ (R.- x) ≡ ZR.- toZ x
toZ-neg (a R.+√2 b) = refl

-- ℤ[√2] → ℤ[1/√2].
ι : R.ℤ√2 → D
ι x = emb (toZ x)

ι-+ : ∀ x y → ι (x R.+ y) ≡ ι x DR.+ ι y
ι-+ x y = trans (cong emb (toZ-+ x y)) (emb-+ (toZ x) (toZ y))

ι-* : ∀ x y → ι (x R.* y) ≡ ι x DR.* ι y
ι-* x y = trans (cong emb (toZ-* x y)) (emb-* (toZ x) (toZ y))

ι-neg : ∀ x → ι (R.- x) ≡ DR.- ι x
ι-neg x = trans (cong emb (toZ-neg x)) (emb-neg (toZ x))

ι-0 : ι R.0# ≡ DR.0#
ι-0 = refl

ι-1 : ι R.1# ≡ DR.1#
ι-1 = refl

ι--1 : ι R.-1# ≡ -1ᴰ
ι--1 = refl

ι-√2 : ι R.√2 ≡ √2ᴰ
ι-√2 = refl

------------------------------------------------------------------------
-- Powers of √2 and of 1/√2

√2^ᴰ √½^ : ℕ → D
√2^ᴰ zero    = DR.1#
√2^ᴰ (suc k) = √2ᴰ DR.* √2^ᴰ k
√½^ zero    = DR.1#
√½^ (suc k) = √½ DR.* √½^ k

ι-√2^ : ∀ k → ι (R.√2^ k) ≡ √2^ᴰ k
ι-√2^ zero    = refl
ι-√2^ (suc k) =
  trans (cong ι (R.strict-id (R.√2 R.* R.√2^ k))) (trans (ι-* R.√2 (R.√2^ k)) (cong (√2ᴰ DR.*_) (ι-√2^ k)))

-- (a b) (c d) = (a c) (b d).
interchange : ∀ a b c d → (a DR.* b) DR.* (c DR.* d) ≡ (a DR.* c) DR.* (b DR.* d)
interchange a b c d =
  trans (DR.*-assoc a b (c DR.* d))
    (trans (cong (a DR.*_) (trans (sym (DR.*-assoc b c d)) (trans (cong (DR._* d) (DR.*-comm b c)) (DR.*-assoc c b d))))
           (sym (DR.*-assoc a c (b DR.* d))))

√½^-+ : ∀ m k → √½^ (m +ℕ k) ≡ √½^ m DR.* √½^ k
√½^-+ zero    k = sym (DR.*-identityˡ (√½^ k))
√½^-+ (suc m) k = trans (cong (√½ DR.*_) (√½^-+ m k)) (sym (DR.*-assoc √½ (√½^ m) (√½^ k)))

-- (1/√2)ᵏ √2ᵏ = 1.
√½√2^ : ∀ k → √½^ k DR.* √2^ᴰ k ≡ DR.1#
√½√2^ zero    = DR.*-identityˡ DR.1#
√½√2^ (suc k) =
  trans (interchange √½ (√½^ k) √2ᴰ (√2^ᴰ k))
    (trans (cong₂ DR._*_ √½*√2 (√½√2^ k)) (DR.*-identityˡ DR.1#))
