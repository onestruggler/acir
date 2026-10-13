------------------------------------------------------------------------
-- Presentations of groups
--
-- The four Hadamard entries of the scaled Schreier table.
--
-- Use representatives 1, M0, X01, M0 X01 for the four dyadic charges
-- 00, 10, 11, 01.  IH fixes 00 and 01 and interchanges 10 and 11.
-- Its Schreier generator is IH at 00 and (M0 M1) IH otherwise.
-- Thus extending the dyadic kernel decoder needs only a sign pair
-- and the physical H on wire 0.  Every equation below follows from
-- Tables 1 and 2, uniformly in the even dimension 2(k+1).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; suc ; _*_ ; s≤s ; z≤n)

module Examples.Groups.CCX+H.GeneralN.HadamardSchreier (k : ℕ) where

open import Data.Fin.Base using (zero ; suc)
import Relation.Binary.PropositionalEquality as Eq
open import Word.Base using (Word ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP

import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as UD
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Normal as Normal

private
  N = suc k * 2
  module P = PB (T._===ᴸ_ {N})
  module Q = PP (T._===ᴸ_ {N})
  module B = PB (U._===_ {N})

open P
open Q using (by-assoc)
open import Relation.Binary.Reasoning.Setoid Q.word-setoid

M0 M1 X01 IH pair : Word (T.Genᴸ N)
M0 = T.Mᴸ zero
M1 = T.Mᴸ (suc zero)
X01 = T.Xᴸ zero (suc zero) (s≤s z≤n)
IH = T.H
pair = M0 • M1

private
  hx : IH • X01 ≈ M1 • IH
  hx = Normal.past k (axiom (T.r7d₀ (s≤s z≤n) Eq.refl Eq.refl))

  hm : IH • M0 ≈ (M0 • X01 • M0) • IH
  hm = Normal.past k (axiom (T.r7c (s≤s z≤n) Eq.refl Eq.refl))

  xm1 : X01 • M1 ≈ M0 • X01
  xm1 = axiom (T.table1 (U.r3c (s≤s z≤n)))

  xm0 : X01 • M0 ≈ M1 • X01
  xm0 = T.⌊⌋-cong
    (B.sym (UD.flip (U.X-gen zero (suc zero) (s≤s z≤n))
      (B.sym (B.axiom (U.r3c (s≤s z≤n))))))

  mm : M0 • M0 ≈ ε
  mm = axiom (T.table1 U.r1b)

  xx : X01 • X01 ≈ ε
  xx = axiom (T.table1 (U.r1a (s≤s z≤n)))

  m10 : M1 • M0 ≈ M0 • M1
  m10 = sym (axiom (T.table1 (U.r2d (λ ()))))

edge00 : ε • IH • ε ≈ IH
edge00 = trans left-unit right-unit

edge10 : M0 • IH • X01 ≈ pair • IH
edge10 = trans (cong refl hx) (sym assoc)

edge11 : X01 • IH • M0 ≈ pair • IH
edge11 = begin
  X01 • IH • M0                    ≈⟨ cong refl hm ⟩
  X01 • ((M0 • X01 • M0) • IH)     ≈⟨ by-assoc Eq.refl ⟩
  (X01 • M0) • (X01 • M0 • IH)     ≈⟨ cong xm0 refl ⟩
  (M1 • X01) • (X01 • M0 • IH)     ≈⟨ by-assoc Eq.refl ⟩
  M1 • ((X01 • X01) • (M0 • IH))   ≈⟨ cong refl (cong xx refl) ⟩
  M1 • (ε • (M0 • IH))             ≈⟨ cong refl left-unit ⟩
  M1 • M0 • IH                    ≈⟨ sym assoc ⟩
  (M1 • M0) • IH                  ≈⟨ cong m10 refl ⟩
  pair • IH                        ∎

edge01 : (M0 • X01) • IH • (X01 • M0) ≈ pair • IH
edge01 = begin
  (M0 • X01) • IH • (X01 • M0)     ≈⟨ by-assoc Eq.refl ⟩
  M0 • X01 • ((IH • X01) • M0)     ≈⟨ cong refl (cong refl (cong hx refl)) ⟩
  M0 • X01 • ((M1 • IH) • M0)      ≈⟨ by-assoc Eq.refl ⟩
  M0 • ((X01 • M1) • (IH • M0))    ≈⟨ cong refl (cong xm1 refl) ⟩
  M0 • ((M0 • X01) • (IH • M0))    ≈⟨ by-assoc Eq.refl ⟩
  (M0 • M0) • (X01 • IH • M0)      ≈⟨ cong mm refl ⟩
  ε • (X01 • IH • M0)              ≈⟨ left-unit ⟩
  X01 • IH • M0                    ≈⟨ edge11 ⟩
  pair • IH                        ∎
