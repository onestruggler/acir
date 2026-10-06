------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level presentation of U₈(ℤ[1/2,i]) as stated in Theorem
-- (module TwoLevel), with indices ₀–₇, and the presentation of
-- Clifford+CS-TwoLevel at n = 8, with indices in Fin 8, are the same:
-- the relations correspond one to one under the translation of
-- indices, in both directions, and the translations are mutually
-- inverse on generators.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-3qubit.TwoLevel-Bridge where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (z≤n ; s≤s)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; ≢-sym)
open import Relation.Nullary.Decidable using (recompute)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactics.Judgement
open import Examples.Groups.Clifford+CS-3qubit.Index
open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module TwoLevel)
open TwoLevel
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL

private
  module P₈ = PB (TL._===_ {8})

------------------------------------------------------------------------
-- Indices

idx : Index → Fin 8
idx ₀ = zero
idx ₁ = suc zero
idx ₂ = suc (suc zero)
idx ₃ = suc (suc (suc zero))
idx ₄ = suc (suc (suc (suc zero)))
idx ₅ = suc (suc (suc (suc (suc zero))))
idx ₆ = suc (suc (suc (suc (suc (suc zero)))))
idx ₇ = suc (suc (suc (suc (suc (suc (suc zero))))))

less→ : ∀ {j k} → Less j k → idx j < idx k
less→ ₀₁ = s≤s z≤n
less→ ₀₂ = s≤s z≤n
less→ ₀₃ = s≤s z≤n
less→ ₀₄ = s≤s z≤n
less→ ₀₅ = s≤s z≤n
less→ ₀₆ = s≤s z≤n
less→ ₀₇ = s≤s z≤n
less→ ₁₂ = s≤s (s≤s z≤n)
less→ ₁₃ = s≤s (s≤s z≤n)
less→ ₁₄ = s≤s (s≤s z≤n)
less→ ₁₅ = s≤s (s≤s z≤n)
less→ ₁₆ = s≤s (s≤s z≤n)
less→ ₁₇ = s≤s (s≤s z≤n)
less→ ₂₃ = s≤s (s≤s (s≤s z≤n))
less→ ₂₄ = s≤s (s≤s (s≤s z≤n))
less→ ₂₅ = s≤s (s≤s (s≤s z≤n))
less→ ₂₆ = s≤s (s≤s (s≤s z≤n))
less→ ₂₇ = s≤s (s≤s (s≤s z≤n))
less→ ₃₄ = s≤s (s≤s (s≤s (s≤s z≤n)))
less→ ₃₅ = s≤s (s≤s (s≤s (s≤s z≤n)))
less→ ₃₆ = s≤s (s≤s (s≤s (s≤s z≤n)))
less→ ₃₇ = s≤s (s≤s (s≤s (s≤s z≤n)))
less→ ₄₅ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
less→ ₄₆ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
less→ ₄₇ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
less→ ₅₆ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
less→ ₅₇ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
less→ ₆₇ = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

neq→ : ∀ {j k} → Neq j k → idx j ≢ idx k
neq→ (f<s jk) = FinP.<⇒≢ (less→ jk)
neq→ (f>s kj) = ≢-sym (FinP.<⇒≢ (less→ kj))

idx⁻ : Fin 8 → Index
idx⁻ zero = ₀
idx⁻ (suc zero) = ₁
idx⁻ (suc (suc zero)) = ₂
idx⁻ (suc (suc (suc zero))) = ₃
idx⁻ (suc (suc (suc (suc zero)))) = ₄
idx⁻ (suc (suc (suc (suc (suc zero))))) = ₅
idx⁻ (suc (suc (suc (suc (suc (suc zero)))))) = ₆
idx⁻ (suc (suc (suc (suc (suc (suc (suc zero))))))) = ₇

less← : (a b : Fin 8) → a < b → Less (idx⁻ a) (idx⁻ b)
less← zero (suc zero) _ = ₀₁
less← zero (suc (suc zero)) _ = ₀₂
less← zero (suc (suc (suc zero))) _ = ₀₃
less← zero (suc (suc (suc (suc zero)))) _ = ₀₄
less← zero (suc (suc (suc (suc (suc zero))))) _ = ₀₅
less← zero (suc (suc (suc (suc (suc (suc zero)))))) _ = ₀₆
less← zero (suc (suc (suc (suc (suc (suc (suc zero))))))) _ = ₀₇
less← (suc zero) (suc (suc zero)) _ = ₁₂
less← (suc zero) (suc (suc (suc zero))) _ = ₁₃
less← (suc zero) (suc (suc (suc (suc zero)))) _ = ₁₄
less← (suc zero) (suc (suc (suc (suc (suc zero))))) _ = ₁₅
less← (suc zero) (suc (suc (suc (suc (suc (suc zero)))))) _ = ₁₆
less← (suc zero) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ = ₁₇
less← (suc (suc zero)) (suc (suc (suc zero))) _ = ₂₃
less← (suc (suc zero)) (suc (suc (suc (suc zero)))) _ = ₂₄
less← (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) _ = ₂₅
less← (suc (suc zero)) (suc (suc (suc (suc (suc (suc zero)))))) _ = ₂₆
less← (suc (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ = ₂₇
less← (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) _ = ₃₄
less← (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) _ = ₃₅
less← (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) _ = ₃₆
less← (suc (suc (suc zero))) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ = ₃₇
less← (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) _ = ₄₅
less← (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc zero)))))) _ = ₄₆
less← (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ = ₄₇
less← (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc zero)))))) _ = ₅₆
less← (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ = ₅₇
less← (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) _ = ₆₇
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
less← (suc (suc (suc (suc zero)))) zero ()
less← (suc (suc (suc (suc zero)))) (suc zero) (s≤s ())
less← (suc (suc (suc (suc zero)))) (suc (suc zero)) (s≤s (s≤s ()))
less← (suc (suc (suc (suc zero)))) (suc (suc (suc zero))) (s≤s (s≤s (s≤s ())))
less← (suc (suc (suc (suc zero)))) (suc (suc (suc (suc zero)))) (s≤s (s≤s (s≤s (s≤s ()))))
less← (suc (suc (suc (suc (suc zero))))) zero ()
less← (suc (suc (suc (suc (suc zero))))) (suc zero) (s≤s ())
less← (suc (suc (suc (suc (suc zero))))) (suc (suc zero)) (s≤s (s≤s ()))
less← (suc (suc (suc (suc (suc zero))))) (suc (suc (suc zero))) (s≤s (s≤s (s≤s ())))
less← (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) (s≤s (s≤s (s≤s (s≤s ()))))
less← (suc (suc (suc (suc (suc zero))))) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))
less← (suc (suc (suc (suc (suc (suc zero)))))) zero ()
less← (suc (suc (suc (suc (suc (suc zero)))))) (suc zero) (s≤s ())
less← (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc zero)) (s≤s (s≤s ()))
less← (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) (s≤s (s≤s (s≤s ())))
less← (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc zero)))) (s≤s (s≤s (s≤s (s≤s ()))))
less← (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))
less← (suc (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc (suc zero)))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))
less← (suc (suc (suc (suc (suc (suc (suc zero))))))) zero ()
less← (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc zero) (s≤s ())
less← (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) (s≤s (s≤s ()))
less← (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc zero))) (s≤s (s≤s (s≤s ())))
less← (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc zero)))) (s≤s (s≤s (s≤s (s≤s ()))))
less← (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))
less← (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))
less← (suc (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))

neq← : (a b : Fin 8) → a ≢ b → Neq (idx⁻ a) (idx⁻ b)
neq← a b ne with FinP.<-cmp a b
... | tri< lt _ _ = f<s (less← a b lt)
... | tri≈ _ eq _ = ⊥-elim (ne eq)
... | tri> _ _ gt = f>s (less← b a gt)

------------------------------------------------------------------------
-- The translations

gen→ : Gen → TL.Gen 8
gen→ (i-gen j) = TL.i-gen (idx j)
gen→ (X-gen {j} {k} jk) = TL.X-gen (idx j) (idx k) (less→ jk)
gen→ (K-gen {j} {k} jk) = TL.K-gen (idx j) (idx k) (less→ jk)

gen← : TL.Gen 8 → Gen
gen← (TL.i-gen a) = i-gen (idx⁻ a)
gen← (TL.X-gen a b p) = X-gen (less← a b (recompute (a FinP.<? b) p))
gen← (TL.K-gen a b p) = K-gen (less← a b (recompute (a FinP.<? b) p))

to : Gen → Word (TL.Gen 8)
to g = [ gen→ g ]ʷ

from : TL.Gen 8 → Word Gen
from g = [ gen← g ]ʷ

------------------------------------------------------------------------
-- The relations correspond

to-ax : ∀ {w v} → w === v ∈ Rel → (to ʷ) w P₈.≈ (to ʷ) v
to-ax [1] = P₈.axiom TL.order-i
to-ax ([2] {jk = jk}) = P₈.axiom (TL.order-X (less→ jk))
to-ax ([3] {jk = jk}) = P₈.axiom (TL.order-K (less→ jk))
to-ax ([4] {jk = jk}) = P₈.axiom (TL.comm-ii (neq→ jk))
to-ax ([5] {kl = kl} {jk = jk} {jl = jl}) = P₈.axiom (TL.comm-iX (less→ kl) (neq→ jk) (neq→ jl))
to-ax ([6] {kl = kl} {jk = jk} {jl = jl}) = P₈.axiom (TL.comm-iK (less→ kl) (neq→ jk) (neq→ jl))
to-ax ([7] {jk = jk} {lm = lm} {jl = jl} {jm = jm} {kl = kl} {km = km}) =
  P₈.axiom (TL.comm-XX (less→ jk) (less→ lm) (neq→ jl) (neq→ jm) (neq→ kl) (neq→ km))
to-ax ([8] {jk = jk} {lm = lm} {jl = jl} {jm = jm} {kl = kl} {km = km}) =
  P₈.axiom (TL.comm-XK (less→ jk) (less→ lm) (neq→ jl) (neq→ jm) (neq→ kl) (neq→ km))
to-ax ([9] {jk = jk} {lm = lm} {jl = jl} {jm = jm} {kl = kl} {km = km}) =
  P₈.axiom (TL.comm-KK (less→ jk) (less→ lm) (neq→ jl) (neq→ jm) (neq→ kl) (neq→ km))
to-ax ([10] {jk = jk}) = P₈.axiom (TL.swap-iX (less→ jk))
to-ax ([11] {kl = kl} {jk = jk}) = P₈.axiom (TL.swap-XX (less→ jk) (less→ kl))
to-ax ([12] {kl = kl} {jk = jk}) = P₈.axiom (TL.swap-XX′ (less→ jk) (less→ kl))
to-ax ([13] {kl = kl} {jk = jk}) = P₈.axiom (TL.swap-KX (less→ jk) (less→ kl))
to-ax ([14] {kl = kl} {jk = jk}) = P₈.axiom (TL.swap-KX′ (less→ jk) (less→ kl))
to-ax ([15] {jk = jk}) = P₈.axiom (TL.rel-13 (less→ jk))
to-ax ([16] {jk = jk}) = P₈.axiom (TL.rel-14 (less→ jk))
to-ax ([17] {jk = jk}) = P₈.axiom (TL.rel-15 (less→ jk))
to-ax ([18] {jk = jk}) = P₈.axiom (TL.rel-16 (less→ jk))
to-ax ([19] {jk = jk} {lm = lm} {jl = jl} {km = km} {kl = kl}) =
  P₈.axiom (TL.rel-17 (less→ jk) (less→ lm) (less→ jl) (less→ km) (neq→ kl))

from-ax : ∀ {w v} → TL._===_ {8} w v → Rel ⊢ (from ʷ) w === (from ʷ) v
from-ax TL.order-i = axiom [1]
from-ax (TL.order-X p) = axiom [2]
from-ax (TL.order-K p) = axiom [3]
from-ax (TL.comm-ii {j = j} {k = k} ne) = axiom ([4] {jk = neq← j k ne})
from-ax (TL.comm-iX {k = k} {l = l} {j = j} p ne₁ ne₂) = axiom ([5] {jk = neq← j k ne₁} {jl = neq← j l ne₂})
from-ax (TL.comm-iK {k = k} {l = l} {j = j} p ne₁ ne₂) = axiom ([6] {jk = neq← j k ne₁} {jl = neq← j l ne₂})
from-ax (TL.comm-XX {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  axiom ([7] {jl = neq← j l jl} {jm = neq← j m jm} {kl = neq← k l kl} {km = neq← k m km})
from-ax (TL.comm-XK {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  axiom ([8] {jl = neq← j l jl} {jm = neq← j m jm} {kl = neq← k l kl} {km = neq← k m km})
from-ax (TL.comm-KK {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  axiom ([9] {jl = neq← j l jl} {jm = neq← j m jm} {kl = neq← k l kl} {km = neq← k m km})
from-ax (TL.swap-iX p) = axiom [10]
from-ax (TL.swap-XX p q) = axiom [11]
from-ax (TL.swap-XX′ p q) = axiom [12]
from-ax (TL.swap-KX p q) = axiom [13]
from-ax (TL.swap-KX′ p q) = axiom [14]
from-ax (TL.rel-13 p) = axiom [15]
from-ax (TL.rel-14 p) = axiom [16]
from-ax (TL.rel-15 p) = axiom [17]
from-ax (TL.rel-16 p) = axiom [18]
from-ax (TL.rel-17 {k = k} {l = l} jk lm jl km ne) = axiom ([19] {kl = neq← k l ne})

-- Derivations translate.
to-cong : ∀ {w v} → Rel ⊢ w === v → (to ʷ) w P₈.≈ (to ʷ) v
to-cong = PP.StarCongruence.fʷ-cong {X = Gen} Rel {B = TL.Gen 8} (TL._===_ {8}) to to-ax

from-cong : ∀ {w v} → w P₈.≈ v → Rel ⊢ (from ʷ) w === (from ʷ) v
from-cong = PP.StarCongruence.fʷ-cong {X = TL.Gen 8} (TL._===_ {8}) {B = Gen} Rel from from-ax

------------------------------------------------------------------------
-- The translations are inverse on generators

from-to-gen : ∀ g → (from ʷ) (to g) ≡ [ g ]ʷ
from-to-gen (i-gen ₀) = Eq.refl
from-to-gen (i-gen ₁) = Eq.refl
from-to-gen (i-gen ₂) = Eq.refl
from-to-gen (i-gen ₃) = Eq.refl
from-to-gen (i-gen ₄) = Eq.refl
from-to-gen (i-gen ₅) = Eq.refl
from-to-gen (i-gen ₆) = Eq.refl
from-to-gen (i-gen ₇) = Eq.refl
from-to-gen (X-gen ₀₁) = Eq.refl
from-to-gen (X-gen ₀₂) = Eq.refl
from-to-gen (X-gen ₀₃) = Eq.refl
from-to-gen (X-gen ₀₄) = Eq.refl
from-to-gen (X-gen ₀₅) = Eq.refl
from-to-gen (X-gen ₀₆) = Eq.refl
from-to-gen (X-gen ₀₇) = Eq.refl
from-to-gen (X-gen ₁₂) = Eq.refl
from-to-gen (X-gen ₁₃) = Eq.refl
from-to-gen (X-gen ₁₄) = Eq.refl
from-to-gen (X-gen ₁₅) = Eq.refl
from-to-gen (X-gen ₁₆) = Eq.refl
from-to-gen (X-gen ₁₇) = Eq.refl
from-to-gen (X-gen ₂₃) = Eq.refl
from-to-gen (X-gen ₂₄) = Eq.refl
from-to-gen (X-gen ₂₅) = Eq.refl
from-to-gen (X-gen ₂₆) = Eq.refl
from-to-gen (X-gen ₂₇) = Eq.refl
from-to-gen (X-gen ₃₄) = Eq.refl
from-to-gen (X-gen ₃₅) = Eq.refl
from-to-gen (X-gen ₃₆) = Eq.refl
from-to-gen (X-gen ₃₇) = Eq.refl
from-to-gen (X-gen ₄₅) = Eq.refl
from-to-gen (X-gen ₄₆) = Eq.refl
from-to-gen (X-gen ₄₇) = Eq.refl
from-to-gen (X-gen ₅₆) = Eq.refl
from-to-gen (X-gen ₅₇) = Eq.refl
from-to-gen (X-gen ₆₇) = Eq.refl
from-to-gen (K-gen ₀₁) = Eq.refl
from-to-gen (K-gen ₀₂) = Eq.refl
from-to-gen (K-gen ₀₃) = Eq.refl
from-to-gen (K-gen ₀₄) = Eq.refl
from-to-gen (K-gen ₀₅) = Eq.refl
from-to-gen (K-gen ₀₆) = Eq.refl
from-to-gen (K-gen ₀₇) = Eq.refl
from-to-gen (K-gen ₁₂) = Eq.refl
from-to-gen (K-gen ₁₃) = Eq.refl
from-to-gen (K-gen ₁₄) = Eq.refl
from-to-gen (K-gen ₁₅) = Eq.refl
from-to-gen (K-gen ₁₆) = Eq.refl
from-to-gen (K-gen ₁₇) = Eq.refl
from-to-gen (K-gen ₂₃) = Eq.refl
from-to-gen (K-gen ₂₄) = Eq.refl
from-to-gen (K-gen ₂₅) = Eq.refl
from-to-gen (K-gen ₂₆) = Eq.refl
from-to-gen (K-gen ₂₇) = Eq.refl
from-to-gen (K-gen ₃₄) = Eq.refl
from-to-gen (K-gen ₃₅) = Eq.refl
from-to-gen (K-gen ₃₆) = Eq.refl
from-to-gen (K-gen ₃₇) = Eq.refl
from-to-gen (K-gen ₄₅) = Eq.refl
from-to-gen (K-gen ₄₆) = Eq.refl
from-to-gen (K-gen ₄₇) = Eq.refl
from-to-gen (K-gen ₅₆) = Eq.refl
from-to-gen (K-gen ₅₇) = Eq.refl
from-to-gen (K-gen ₆₇) = Eq.refl

from-to : ∀ w → (from ʷ) ((to ʷ) w) ≡ w
from-to [ g ]ʷ = from-to-gen g
from-to ε = Eq.refl
from-to (w • v) = Eq.cong₂ _•_ (from-to w) (from-to v)

idx-idx⁻ : ∀ a → idx (idx⁻ a) ≡ a
idx-idx⁻ zero = Eq.refl
idx-idx⁻ (suc zero) = Eq.refl
idx-idx⁻ (suc (suc zero)) = Eq.refl
idx-idx⁻ (suc (suc (suc zero))) = Eq.refl
idx-idx⁻ (suc (suc (suc (suc zero)))) = Eq.refl
idx-idx⁻ (suc (suc (suc (suc (suc zero))))) = Eq.refl
idx-idx⁻ (suc (suc (suc (suc (suc (suc zero)))))) = Eq.refl
idx-idx⁻ (suc (suc (suc (suc (suc (suc (suc zero))))))) = Eq.refl

private
  -- A generator is determined by its indices: the proof that they are
  -- in order is irrelevant.
  X≡ : ∀ {a a′ b b′ : Fin 8} .{p : a < b} .{p′ : a′ < b′} → a ≡ a′ → b ≡ b′ → TL.X-gen a b p ≡ TL.X-gen a′ b′ p′
  X≡ Eq.refl Eq.refl = Eq.refl

  K≡ : ∀ {a a′ b b′ : Fin 8} .{p : a < b} .{p′ : a′ < b′} → a ≡ a′ → b ≡ b′ → TL.K-gen a b p ≡ TL.K-gen a′ b′ p′
  K≡ Eq.refl Eq.refl = Eq.refl

to-from-gen : ∀ g → (to ʷ) (from g) ≡ [ g ]ʷ
to-from-gen (TL.i-gen a) = Eq.cong (λ b → [ TL.i-gen b ]ʷ) (idx-idx⁻ a)
to-from-gen (TL.X-gen a b p) = Eq.cong [_]ʷ (X≡ (idx-idx⁻ a) (idx-idx⁻ b))
to-from-gen (TL.K-gen a b p) = Eq.cong [_]ʷ (K≡ (idx-idx⁻ a) (idx-idx⁻ b))

to-from : ∀ w → (to ʷ) ((from ʷ) w) ≡ w
to-from [ g ]ʷ = to-from-gen g
to-from ε = Eq.refl
to-from (w • v) = Eq.cong₂ _•_ (to-from w) (to-from v)
