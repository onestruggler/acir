------------------------------------------------------------------------
-- Presentations of groups
--
-- The entries of the scaled dyadic matrices: ℤ[1/√2] = 𝔻[√2], the
-- ring of Real-Clifford+CH-TwoLevel, with the dyadic fractions 𝔻 of
-- Oₙ(ℤ[1/2]) embedded as a + 0√2 (e), and the scalars 1/2 (of K) and
-- 1/√2 (of H).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring where

open import Data.Integer.Base using (+_)
open import Relation.Binary.PropositionalEquality

open import Quantum.Synthesis.Ring using (Dyadic ; Dyadic' ; RootTwo)

import Examples.Groups.CCX+HH-TwoLevel.Ring as R1
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2

open R2 public using (D ; isCommutativeRing-D ; adj-D ; √½ ; module DR)

------------------------------------------------------------------------
-- The embedding 𝔻 → 𝔻[√2]

e : R1.D → D
e x = RootTwo x R1.0ᴰ

-- The rational part.
ℜ : D → Dyadic
ℜ (RootTwo a _) = a

e-injective : ∀ {x y} → e x ≡ e y → x ≡ y
e-injective eq = cong ℜ eq

-- An embedded element has no √2 part.
√2-part : D → Dyadic
√2-part (RootTwo _ b) = b

√2-part-e : ∀ x → √2-part (e x) ≡ R1.0ᴰ
√2-part-e x = refl

opaque
  unfolding R1._+ᴰ_ R1._*ᴰ_ R1.-ᴰ_ R1.adjᴰ R2._+ᴰ_ R2._*ᴰ_ R2.-ᴰ_ R2.adjᴰ

  e-+ : ∀ x y → e (x R1.DR.+ y) ≡ e x DR.+ e y
  e-+ x y = refl

  e-neg : ∀ x → e (R1.DR.- x) ≡ DR.- e x
  e-neg x = refl

  e-* : ∀ x y → e (x R1.DR.* y) ≡ e x DR.* e y
  e-* x y = cong₂ RootTwo (sym (R1.𝔻R.+-identityʳ (x R1.𝔻R.* y)))
                          (sym (trans (cong₂ R1.𝔻R._+_ (R1.𝔻R.zeroʳ x) (R1.𝔻R.zeroʳ y)) (R1.𝔻R.+-identityʳ R1.𝔻R.0#)))

  e-adj : ∀ x → e (R1.adjᴰ x) ≡ R2.adjᴰ (e x)
  e-adj x = refl

e-0 : e R1.DR.0# ≡ DR.0#
e-0 = refl

e-1 : e R1.DR.1# ≡ DR.1#
e-1 = refl

------------------------------------------------------------------------
-- The scalars

-- 1/2.
½ : D
½ = e R1.½ᴰ

opaque
  unfolding R2._+ᴰ_ R2._*ᴰ_ R2.adjᴰ

  ½-self : R2.adjᴰ ½ ≡ ½
  ½-self = refl

  ½-quarter : ½ DR.* ½ DR.+ ½ DR.* ½ DR.+ ½ DR.* ½ DR.+ ½ DR.* ½ ≡ DR.1#
  ½-quarter = refl

  √½-self : R2.adjᴰ √½ ≡ √½
  √½-self = refl

  √½-sq : √½ DR.* √½ ≡ ½
  √½-sq = refl

  √½-half : √½ DR.* √½ DR.+ √½ DR.* √½ ≡ DR.1#
  √½-half = refl
