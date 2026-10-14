------------------------------------------------------------------------
-- Presentations of groups
--
-- 𝔻[i] in 𝔻[ω]: the entries of Bian and Selinger's Clifford+CS
-- matrices read in the ring of CliffCS₂'s
--
-- Bian and Selinger's two-level and 3-qubit Clifford+CS presentations
-- have their matrices over 𝔻[i] = ℤ[½,i] (EucDomain's DComplex, x + yi);
-- CliffCS₂'s values are read in 𝔻[ω] = ℤ[1/√2,i] (EucDomain's DOmega,
-- aω³ + bω² + cω + d), as Clifford+T's are.  i is ω², so x + yi is
-- 0ω³ + yω² + 0ω + x: ι is that inclusion, an injective ring
-- homomorphism — its product is four identities in the dyadic
-- fractions, by the ring solver — sending i to ω².
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Ring where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Integer.Base using (+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; cong ; sym)

open import Quantum.Synthesis.Ring using (Omega ; Cplx ; Dyadic)
open import Quantum.Synthesis.Ring.Properties using (commutativeRing-𝔻)
import Quantum.Synthesis.Ring.Properties.Common as Common

import Examples.Groups.Clifford+CS-TwoLevel.Ring as CSR
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; module DR ; ωᴰ ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)

private
  module 𝔻R = CommutativeRing commutativeRing-𝔻
  module 𝔻S = Common.ZSolver commutativeRing-𝔻
  open 𝔻S using (solve ; _:=_ ; _:+_ ; _:*_ ; _:-_ ; :-_ ; con)

  cong₄ : ∀ {A B C E F : Set} (f : A → B → C → E → F) {a a′ b b′ c c′ e e′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → f a b c e ≡ f a′ b′ c′ e′
  cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- The inclusion

ι : CSR.D → D
ι (Cplx x y) = Omega 𝔻R.0# y 𝔻R.0# x

ι-injective : ∀ {a b} → ι a ≡ ι b → a ≡ b
ι-injective {Cplx x y} {Cplx x′ y′} e = Eq.cong₂ Cplx (cong re e) (cong im e)
  where
  re im : D → Dyadic
  re (Omega _ _ _ d) = d
  im (Omega _ b _ _) = b

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  ι-+ : ∀ a b → ι (a CSR.DR.+ b) ≡ ι a DR.+ ι b
  ι-+ (Cplx x y) (Cplx x′ y′) =
    cong₄ Omega (solve 0 (con (+ 0) := con (+ 0) :+ con (+ 0)) refl) refl
                (solve 0 (con (+ 0) := con (+ 0) :+ con (+ 0)) refl) refl

  ι-neg : ∀ a → ι (CSR.DR.- a) ≡ DR.- ι a
  ι-neg (Cplx x y) =
    cong₄ Omega (solve 0 (con (+ 0) := :- con (+ 0)) refl) refl
                (solve 0 (con (+ 0) := :- con (+ 0)) refl) refl

  ι-* : ∀ a b → ι (a CSR.DR.* b) ≡ ι a DR.* ι b
  ι-* (Cplx x y) (Cplx x′ y′) = cong₄ Omega
    (solve 4 (λ x y x′ y′ →
       con (+ 0)
       := (((con (+ 0) :* x′) :+ (y :* con (+ 0))) :+ (con (+ 0) :* y′)) :+ (x :* con (+ 0)))
       refl x y x′ y′)
    (solve 4 (λ x y x′ y′ →
       (x :* y′) :+ (y :* x′)
       := (((y :* x′) :+ (con (+ 0) :* con (+ 0))) :+ (x :* y′)) :- (con (+ 0) :* con (+ 0)))
       refl x y x′ y′)
    (solve 4 (λ x y x′ y′ →
       con (+ 0)
       := (((con (+ 0) :* x′) :+ (x :* con (+ 0))) :- (con (+ 0) :* y′)) :- (y :* con (+ 0)))
       refl x y x′ y′)
    (solve 4 (λ x y x′ y′ →
       (x :* x′) :- (y :* y′)
       := (((x :* x′) :- (con (+ 0) :* con (+ 0))) :- (y :* y′)) :- (con (+ 0) :* con (+ 0)))
       refl x y x′ y′)

  -- i is ω².
  ι-i : ι CSR.ⅈ ≡ ωᴰ DR.* ωᴰ
  ι-i = refl

ι-0 : ι CSR.DR.0# ≡ DR.0#
ι-0 = refl

ι-1 : ι CSR.DR.1# ≡ DR.1#
ι-1 = refl
