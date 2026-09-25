------------------------------------------------------------------------
-- Presentations of groups
--
-- Greylyn's presentation of U₄(ℤ[1/√2,i]) as stated in Generator,
-- with indices ₀–₃, and the presentation of Clifford+T-2qubit-TwoLevel
-- at n = 4, with indices in Fin 4, are the same: the relations
-- correspond one to one under the translation of indices, in both
-- directions, and the translations are mutually inverse on generators.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Greylyn-TwoLevel where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; ≢-sym)
open import Relation.Nullary.Decidable using (recompute)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactics.Judgement
open import Examples.Groups.Clifford+T-2qubit.Generator using (module Greylyn)
open Greylyn
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics as TL

private
  module P₄ = PB (TL._===_ {4})

------------------------------------------------------------------------
-- Indices

idx : Index → Fin 4
idx ₀ = zero
idx ₁ = suc zero
idx ₂ = suc (suc zero)
idx ₃ = suc (suc (suc zero))

less→ : ∀ {j k} → Less j k → idx j < idx k
less→ ₀₁ = s≤s z≤n
less→ ₀₂ = s≤s z≤n
less→ ₀₃ = s≤s z≤n
less→ ₁₂ = s≤s (s≤s z≤n)
less→ ₁₃ = s≤s (s≤s z≤n)
less→ ₂₃ = s≤s (s≤s (s≤s z≤n))

neq→ : ∀ {j k} → Neq j k → idx j ≢ idx k
neq→ ₀₁ ()
neq→ ₀₂ ()
neq→ ₀₃ ()
neq→ ₁₂ ()
neq→ ₁₃ ()
neq→ ₂₃ ()
neq→ ₁₀ ()
neq→ ₂₀ ()
neq→ ₃₀ ()
neq→ ₂₁ ()
neq→ ₃₁ ()
neq→ ₃₂ ()

idx⁻ : Fin 4 → Index
idx⁻ zero = ₀
idx⁻ (suc zero) = ₁
idx⁻ (suc (suc zero)) = ₂
idx⁻ (suc (suc (suc zero))) = ₃

less← : (a b : Fin 4) → a < b → Less (idx⁻ a) (idx⁻ b)
less← zero (suc zero) _ = ₀₁
less← zero (suc (suc zero)) _ = ₀₂
less← zero (suc (suc (suc zero))) _ = ₀₃
less← (suc zero) (suc (suc zero)) _ = ₁₂
less← (suc zero) (suc (suc (suc zero))) _ = ₁₃
less← (suc (suc zero)) (suc (suc (suc zero))) _ = ₂₃
less← zero zero ()
less← (suc zero) zero ()
less← (suc zero) (suc zero) (s≤s ())
less← (suc (suc zero)) zero ()
less← (suc (suc zero)) (suc zero) (s≤s ())
less← (suc (suc zero)) (suc (suc zero)) (s≤s (s≤s ()))
less← (suc (suc (suc zero))) zero ()
less← (suc (suc (suc zero))) (suc zero) (s≤s ())
less← (suc (suc (suc zero))) (suc (suc zero)) (s≤s (s≤s ()))
less← (suc (suc (suc zero))) (suc (suc (suc zero))) (s≤s (s≤s (s≤s ())))

neq← : (a b : Fin 4) → a ≢ b → Neq (idx⁻ a) (idx⁻ b)
neq← zero (suc zero) _ = ₀₁
neq← zero (suc (suc zero)) _ = ₀₂
neq← zero (suc (suc (suc zero))) _ = ₀₃
neq← (suc zero) (suc (suc zero)) _ = ₁₂
neq← (suc zero) (suc (suc (suc zero))) _ = ₁₃
neq← (suc (suc zero)) (suc (suc (suc zero))) _ = ₂₃
neq← (suc zero) zero _ = ₁₀
neq← (suc (suc zero)) zero _ = ₂₀
neq← (suc (suc (suc zero))) zero _ = ₃₀
neq← (suc (suc zero)) (suc zero) _ = ₂₁
neq← (suc (suc (suc zero))) (suc zero) _ = ₃₁
neq← (suc (suc (suc zero))) (suc (suc zero)) _ = ₃₂
neq← zero zero ne = ⊥-elim (ne Eq.refl)
neq← (suc zero) (suc zero) ne = ⊥-elim (ne Eq.refl)
neq← (suc (suc zero)) (suc (suc zero)) ne = ⊥-elim (ne Eq.refl)
neq← (suc (suc (suc zero))) (suc (suc (suc zero))) ne = ⊥-elim (ne Eq.refl)

------------------------------------------------------------------------
-- The translations

gen→ : Generator → TL.Gen 4
gen→ (ω-gen j) = TL.ω-gen (idx j)
gen→ (X-gen {j} {k} jk) = TL.X-gen (idx j) (idx k) (less→ jk)
gen→ (H-gen {j} {k} jk) = TL.H-gen (idx j) (idx k) (less→ jk)

gen← : TL.Gen 4 → Generator
gen← (TL.ω-gen a) = ω-gen (idx⁻ a)
gen← (TL.X-gen a b p) = X-gen (less← a b (recompute (a FinP.<? b) p))
gen← (TL.H-gen a b p) = H-gen (less← a b (recompute (a FinP.<? b) p))

to : Generator → Word (TL.Gen 4)
to g = [ gen→ g ]ʷ

from : TL.Gen 4 → Word Generator
from g = [ gen← g ]ʷ

------------------------------------------------------------------------
-- The relations correspond

to-ax : ∀ {w v} → w === v ∈ Rel → (to ʷ) w P₄.≈ (to ʷ) v
to-ax [1] = P₄.axiom TL.order-ω
to-ax ([2] {jk = jk}) = P₄.axiom (TL.order-H (less→ jk))
to-ax ([3] {jk = jk}) = P₄.axiom (TL.order-X (less→ jk))
to-ax ([4] {jk = jk}) = P₄.axiom (TL.comm-ωω (neq→ jk))
to-ax ([5] {jk = jk} {lj = lj} {lk = lk}) = P₄.axiom (TL.comm-ωH (less→ jk) (neq→ lj) (neq→ lk))
to-ax ([6] {jk = jk} {lj = lj} {lk = lk}) = P₄.axiom (TL.comm-ωX (less→ jk) (neq→ lj) (neq→ lk))
to-ax ([7] {jk = jk} {lt = lt} {lj = lj} {lk = lk} {tj = tj} {tk = tk}) =
  P₄.axiom (TL.comm-HH (less→ jk) (less→ lt) (≢-sym (neq→ lj)) (≢-sym (neq→ tj)) (≢-sym (neq→ lk)) (≢-sym (neq→ tk)))
to-ax ([8] {jk = jk} {lt = lt} {lj = lj} {lk = lk} {tj = tj} {tk = tk}) =
  P₄.axiom (TL.comm-HX (less→ jk) (less→ lt) (≢-sym (neq→ lj)) (≢-sym (neq→ tj)) (≢-sym (neq→ lk)) (≢-sym (neq→ tk)))
to-ax ([9] {jk = jk} {lt = lt} {lj = lj} {lk = lk} {tj = tj} {tk = tk}) =
  P₄.axiom (TL.comm-XX (less→ jk) (less→ lt) (≢-sym (neq→ lj)) (≢-sym (neq→ tj)) (≢-sym (neq→ lk)) (≢-sym (neq→ tk)))
to-ax ([10] {jk = jk}) = P₄.axiom (TL.swap-Xω (less→ jk))
to-ax ([11] {jk = jk}) = P₄.axiom (TL.swap-Xω′ (less→ jk))
to-ax ([12] {jk = jk} {kl = kl}) = P₄.axiom (TL.swap-XX (less→ jk) (less→ kl))
to-ax ([13] {jk = jk} {lj = lj}) = P₄.axiom (TL.swap-XX′ (less→ lj) (less→ jk))
to-ax ([14] {jk = jk} {kl = kl}) = P₄.axiom (TL.swap-XH (less→ jk) (less→ kl))
to-ax ([15] {jk = jk} {lj = lj}) = P₄.axiom (TL.swap-XH′ (less→ lj) (less→ jk))
to-ax ([16] {jk = jk}) = P₄.axiom (TL.scalar-X (less→ jk))
to-ax ([17] {jk = jk}) = P₄.axiom (TL.scalar-H (less→ jk))
to-ax ([18] {jk = jk}) = P₄.axiom (TL.rel-18 (less→ jk))
to-ax ([19] {jk = jk}) = P₄.axiom (TL.rel-19 (less→ jk))
to-ax ([20] {jk = jk} {kl = kl} {lt = lt}) = P₄.axiom (TL.rel-20 (less→ jk) (less→ kl) (less→ lt))

from-ax : ∀ {w v} → TL._===_ {4} w v → Rel ⊢ (from ʷ) w === (from ʷ) v
from-ax TL.order-ω = axiom [1]
from-ax (TL.order-H p) = axiom [2]
from-ax (TL.order-X p) = axiom [3]
from-ax (TL.comm-ωω {j = j} {k = k} ne) = axiom ([4] {jk = neq← j k ne})
from-ax (TL.comm-ωH {k = k} {l = l} {j = j} p ne₁ ne₂) = axiom ([5] {lj = neq← j k ne₁} {lk = neq← j l ne₂})
from-ax (TL.comm-ωX {k = k} {l = l} {j = j} p ne₁ ne₂) = axiom ([6] {lj = neq← j k ne₁} {lk = neq← j l ne₂})
from-ax (TL.comm-HH {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  axiom ([7] {lj = neq← l j (≢-sym jl)} {lk = neq← l k (≢-sym kl)} {tj = neq← m j (≢-sym jm)} {tk = neq← m k (≢-sym km)})
from-ax (TL.comm-HX {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  axiom ([8] {lj = neq← l j (≢-sym jl)} {lk = neq← l k (≢-sym kl)} {tj = neq← m j (≢-sym jm)} {tk = neq← m k (≢-sym km)})
from-ax (TL.comm-XX {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  axiom ([9] {lj = neq← l j (≢-sym jl)} {lk = neq← l k (≢-sym kl)} {tj = neq← m j (≢-sym jm)} {tk = neq← m k (≢-sym km)})
from-ax (TL.swap-Xω p) = axiom [10]
from-ax (TL.swap-Xω′ p) = axiom [11]
from-ax (TL.swap-XX p q) = axiom [12]
from-ax (TL.swap-XX′ p q) = axiom [13]
from-ax (TL.swap-XH p q) = axiom [14]
from-ax (TL.swap-XH′ p q) = axiom [15]
from-ax (TL.scalar-X p) = axiom [16]
from-ax (TL.scalar-H p) = axiom [17]
from-ax (TL.rel-18 p) = axiom [18]
from-ax (TL.rel-19 p) = axiom [19]
from-ax (TL.rel-20 {k = k} {l = l} jk kl lm) = axiom ([20] {kl = less← k l (recompute (k FinP.<? l) kl)})

-- Derivations translate.
to-cong : ∀ {w v} → Rel ⊢ w === v → (to ʷ) w P₄.≈ (to ʷ) v
to-cong = PP.StarCongruence.fʷ-cong {X = Generator} Rel {B = TL.Gen 4} (TL._===_ {4}) to to-ax

from-cong : ∀ {w v} → w P₄.≈ v → Rel ⊢ (from ʷ) w === (from ʷ) v
from-cong = PP.StarCongruence.fʷ-cong {X = TL.Gen 4} (TL._===_ {4}) {B = Generator} Rel from from-ax

------------------------------------------------------------------------
-- The translations are inverse on generators

from-to-gen : ∀ g → (from ʷ) (to g) ≡ [ g ]ʷ
from-to-gen (ω-gen ₀) = Eq.refl
from-to-gen (ω-gen ₁) = Eq.refl
from-to-gen (ω-gen ₂) = Eq.refl
from-to-gen (ω-gen ₃) = Eq.refl
from-to-gen (X-gen ₀₁) = Eq.refl
from-to-gen (X-gen ₀₂) = Eq.refl
from-to-gen (X-gen ₀₃) = Eq.refl
from-to-gen (X-gen ₁₂) = Eq.refl
from-to-gen (X-gen ₁₃) = Eq.refl
from-to-gen (X-gen ₂₃) = Eq.refl
from-to-gen (H-gen ₀₁) = Eq.refl
from-to-gen (H-gen ₀₂) = Eq.refl
from-to-gen (H-gen ₀₃) = Eq.refl
from-to-gen (H-gen ₁₂) = Eq.refl
from-to-gen (H-gen ₁₃) = Eq.refl
from-to-gen (H-gen ₂₃) = Eq.refl

from-to : ∀ w → (from ʷ) ((to ʷ) w) ≡ w
from-to [ g ]ʷ = from-to-gen g
from-to ε = Eq.refl
from-to (w • v) = Eq.cong₂ _•_ (from-to w) (from-to v)
