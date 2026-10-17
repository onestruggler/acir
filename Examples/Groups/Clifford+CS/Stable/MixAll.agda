------------------------------------------------------------------------
-- Presentations of groups
--
-- (F4) at every width, from completeness on five to eight wires
--
-- Stable.Mixed reduces (F4) — a white and a black controlled generator
-- commute — to the white versions of the transport's base facts
-- (`MixBase`).  On six wires they are Stable.Six.Mix1S … Mix3 (from
-- completeness on five), on seven to nine the white sections of
-- Stable.Base7, Base8, Base9 (from completeness one width down): the
-- S-boxes move as for the black facts, X on the control rides along
-- (Stable.XPlace), and on five wires the white and the black S-box
-- commute by (F4) there.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.MixAll where

open import Data.Nat using (ℕ ; zero ; suc ; s≤s)
import Data.Nat as ℕ
open import Word.Base using (_•_)

open import Notations using (₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Syntactics using (S-gate ; K-gate ; CS-gate ; gate₂)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ ; λ⁰)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Insert4 using (top2)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ)
open import Examples.Groups.Clifford+CS.Stable.Mixed using (MixBase ; module Reduce)
import Examples.Groups.Clifford+CS.Stable.Six.Mix1S as M1S
import Examples.Groups.Clifford+CS.Stable.Six.Mix1K as M1K
import Examples.Groups.Clifford+CS.Stable.Six.Mix2S as M2S
import Examples.Groups.Clifford+CS.Stable.Six.Mix2K as M2K
import Examples.Groups.Clifford+CS.Stable.Six.Mix3 as M3
import Examples.Groups.Clifford+CS.Stable.Base7 as B7
import Examples.Groups.Clifford+CS.Stable.Base8 as B8
import Examples.Groups.Clifford+CS.Stable.Base9 as B9

mixbase : Completeᵧ 5 → Completeᵧ 6 → Completeᵧ 7 → Completeᵧ 8 → MixBase
mixbase c₅ c₆ c₇ c₈ = record
  { b₁ = λ { S-gate → M1S.mix₁-S c₅ ; K-gate → M1K.mix₁-K c₅ }
  ; b₂ = λ { S-gate → M2S.mix₂-S c₅ ; K-gate → M2K.mix₂-K c₅ }
  ; b₃ = b₃
  }
  where
  b₃ : ∀ m → m ℕ.≤ 3 →
       (₂₊ (₄₊ m)) ⊢ᵧ λ⁰ {suc m} (top2 (₃₊ m) CS-gate) • λ¹ {suc m} (gate₂ CS-gate)
                    ≈ λ¹ {suc m} (gate₂ CS-gate) • λ⁰ {suc m} (top2 (₃₊ m) CS-gate)
  b₃ zero                      _ = M3.mix₃ c₅
  b₃ (suc zero)                _ = B7.mix-base-7 c₅ c₆
  b₃ (suc (suc zero))          _ = B8.mix-base-8 c₅ c₇
  b₃ (suc (suc (suc zero)))    _ = B9.mix-base-9 c₅ c₈
  b₃ (suc (suc (suc (suc m)))) (s≤s (s≤s (s≤s ())))

-- (F4) at every width.
f4 : Completeᵧ 5 → Completeᵧ 6 → Completeᵧ 7 → Completeᵧ 8 → ∀ m → F4ᵗ m
f4 c₅ c₆ c₇ c₈ = Reduce.f4 c₅ (mixbase c₅ c₆ c₇ c₈)
