------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness on no wires
--
-- With no wire there is one gate, the scalar iI, and its words denote
-- the scalars i^k.  The back-and-forth argument with the one-level
-- words on a single index, i_[0] and nothing else: the encoding sends
-- iI to i_[0] and the decoding back, and of the relations of Bian and
-- Selinger only i_[0]⁴ = ε applies to a single index, which is the
-- rule order-I.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.ZeroQubit where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_ ; ~-sym)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+CS.Bridge as Bridge
import Examples.Groups.Clifford+CS.TwoLevelTries as TwoLevelTries

private
  module T = Bridge.TwoLevel 0
  module TT = TwoLevelTries 0

------------------------------------------------------------------------
-- The encoding and the decoding

e : Gen 0 → Word (TL.Gen 1)
e I-gen = TL.i zero

-- There are no two indices, so no X or K letter; they decode to ε.
d : TL.Gen 1 → Circuit 0
d (TL.i-gen _)     = iI
d (TL.X-gen _ _ _) = ε
d (TL.K-gen _ _ _) = ε

d∘e : ∀ g → 0 ⊢ [ g ]ʷ ≈ (d ʷ) (e g)
d∘e I-gen = PB.refl

e-sem : ∀ g → T.⟦ e g ⟧Y ~ ⟦ [ g ]ʷ ⟧
e-sem I-gen = ~-sym {s = ⟦ iI ⟧} {T.⟦ TL.i zero ⟧Y} (TT.by-same iI (TL.i zero) refl)

------------------------------------------------------------------------
-- The decoding respects the relations

private
  -- One index: no two are ordered, none two are distinct.
  no< : {a b : Fin 1} → .(a < b) → ⊥
  no< {zero} {zero} p = absurd (recompute (0 ℕP.<? 0) p)
    where
    absurd : 0 ℕ.< 0 → ⊥
    absurd ()

  no≢ : {a b : Fin 1} → a ≢ b → ⊥
  no≢ {zero} {zero} ne = ne refl

d-wd : ∀ {u t} → TL._===_ {1} u t → 0 ⊢ (d ʷ) u ≈ (d ʷ) t
d-wd TL.order-i                         = PB.axiom (srel order-I)
d-wd (TL.order-X {j = j} {k = k} p)     = ⊥-elim (no< {j} {k} p)
d-wd (TL.order-K {j = j} {k = k} p)     = ⊥-elim (no< {j} {k} p)
d-wd (TL.comm-ii jk)                    = ⊥-elim (no≢ jk)
d-wd (TL.comm-iX {k = k} {l = l} p jk jl) = ⊥-elim (no< {k} {l} p)
d-wd (TL.comm-iK {k = k} {l = l} p jk jl) = ⊥-elim (no< {k} {l} p)
d-wd (TL.comm-XX {j = j} {k = k} p q jl jm kl km) = ⊥-elim (no< {j} {k} p)
d-wd (TL.comm-XK {j = j} {k = k} p q jl jm kl km) = ⊥-elim (no< {j} {k} p)
d-wd (TL.comm-KK {j = j} {k = k} p q jl jm kl km) = ⊥-elim (no< {j} {k} p)
d-wd (TL.swap-iX {j = j} {k = k} p)     = ⊥-elim (no< {j} {k} p)
d-wd (TL.swap-XX {j = j} {k = k} p q)   = ⊥-elim (no< {j} {k} p)
d-wd (TL.swap-XX′ {j = j} {k = k} p q)  = ⊥-elim (no< {j} {k} p)
d-wd (TL.swap-KX {j = j} {k = k} p q)   = ⊥-elim (no< {j} {k} p)
d-wd (TL.swap-KX′ {j = j} {k = k} p q)  = ⊥-elim (no< {j} {k} p)
d-wd (TL.rel-13 {j = j} {k = k} p)      = ⊥-elim (no< {j} {k} p)
d-wd (TL.rel-14 {j = j} {k = k} p)      = ⊥-elim (no< {j} {k} p)
d-wd (TL.rel-15 {j = j} {k = k} p)      = ⊥-elim (no< {j} {k} p)
d-wd (TL.rel-16 {j = j} {k = k} p)      = ⊥-elim (no< {j} {k} p)
d-wd (TL.rel-17 {j = j} {k = k} jk lm jl km k≢l) = ⊥-elim (no< {j} {k} jk)

------------------------------------------------------------------------
-- Completeness on no wires

open T.BF.Complete T.complete-Y e e-sem d d-wd d∘e public using (complete)
