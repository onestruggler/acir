------------------------------------------------------------------------
-- Presentations of groups
--
-- Every physical X,CX,CCX,HH generator is an involution at every width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.GateInvolutions where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; isCommutativeRing-D ; adj-D ; ½ᴰ)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition using (Partition)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (contiguous ; alternating)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-compose ; parallel-cong ; parallel-id)
open import Examples.Groups.CCX+HH.GeneralN.LocalHadamard using (hh-involutive)
open import Examples.Groups.CCX+HH.GeneralN.PhysicalEquality using (action⇒matrix)

parallel-involutive : ∀ {m n} (p : Partition m n) (f : Vec D m → Vec D m) →
  (∀ v → f (f v) ≡ v) → ∀ v → parallel p f f (parallel p f f v) ≡ v
parallel-involutive p f inv v = trans (parallel-compose p f f f f v)
  (trans (parallel-cong p {f′ = λ x → x} {g′ = λ x → x} inv inv v) (parallel-id p v))

x-involutive : ∀ n v → Q.x n (Q.x n v) ≡ v
x-involutive zero (a ∷ b ∷ []) = refl
x-involutive (suc n) = parallel-involutive (contiguous _) (Q.x n) (x-involutive n)

cx-involutive : ∀ n v → Q.cx n (Q.cx n v) ≡ v
cx-involutive zero (a ∷ b ∷ c ∷ d ∷ []) = refl
cx-involutive (suc n) = parallel-involutive (contiguous _) (Q.cx n) (cx-involutive n)

ccx-involutive : ∀ n v → Q.ccx n (Q.ccx n v) ≡ v
ccx-involutive zero (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
ccx-involutive (suc n) = parallel-involutive (contiguous _) (Q.ccx n) (ccx-involutive n)

action-involutive : ∀ {n} (g : H.Gen n) v → Q.gate-action g (Q.gate-action g v) ≡ v
action-involutive (H.gate₀ ())
action-involutive (H.gate₁ {n} H.X-gate) = x-involutive n
action-involutive (H.gate₂ {n} H.CX-gate) = cx-involutive n
action-involutive (H.gate₂ {n} H.HH-gate) = hh-involutive n
action-involutive (H.gate₃ {n} H.CCX-gate) = ccx-involutive n
action-involutive (H._↥ {n} g) = parallel-involutive (alternating (2 ^ n))
  (Q.gate-action g) (action-involutive g)

matrix-involutive : ∀ {n} (g : H.Gen n) →
  Q.interpret ([ g ]ʷ • [ g ]ʷ) ≡ Q.interpret {n} ε
matrix-involutive g = action⇒matrix ([ g ]ʷ • [ g ]ʷ) ε (action-involutive g)
