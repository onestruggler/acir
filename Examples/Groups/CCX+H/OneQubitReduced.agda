------------------------------------------------------------------------
-- Presentations of groups
--
-- The one-wire Clément translation reduces to three circuit equations:
-- X^2 = H^2 = (X H)^8 = 1.  Every original translated axiom is derived
-- by checked involutory relator reduction, so completeness is inherited
-- from the existing translated presentation, not a separate method.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.OneQubitReduced where

open import Data.Bool.Base using (false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (s≤s)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable using (yes ; no ; recompute)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.OneQubit as Old
open import Examples.Groups.CCX+H.Semantics using (interpret)
import Examples.Groups.CCX+HH.RelatorReduction as Reduction
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as Ring
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as Physical
import Examples.Groups.CCX+H.GeneralN.SmallPhysicalSemantics as Bridge

pattern X-gen = gate₁ X-gate
pattern H-gen = gate₁ H-gate

data Relations : WRel (Gen 1) where
  x-square : Relations (X • X) ε
  h-square : Relations (H • H) ε
  period : Relations ((X • H) ^ 8) ε

open PB Relations public hiding (_===_)
open PP Relations using (by-assoc)

private
  eq : DecidableEquality (Gen 1)
  eq X-gen X-gen = yes Eq.refl
  eq X-gen H-gen = no (λ ())
  eq H-gen X-gen = no (λ ())
  eq H-gen H-gen = yes Eq.refl
  eq (gate₀ ()) g
  eq ((gate₀ ()) ↥) g
  eq g (gate₀ ())
  eq g ((gate₀ ()) ↥)

  involution : ∀ g → [ g ]ʷ • [ g ]ʷ ≈ ε
  involution X-gen = axiom x-square
  involution H-gen = axiom h-square
  involution (gate₀ ())
  involution ((gate₀ ()) ↥)

  module R = Reduction eq
  module Calc = R.Theory Relations involution

  cycle : List (Gen 1)
  cycle = X-gen ∷ H-gen ∷ X-gen ∷ H-gen ∷ X-gen ∷ H-gen ∷ X-gen ∷ H-gen ∷
          X-gen ∷ H-gen ∷ X-gen ∷ H-gen ∷ X-gen ∷ H-gen ∷ X-gen ∷ H-gen ∷ []

  cycle-trivial : R.read cycle ≈ ε
  cycle-trivial = trans (by-assoc {w = R.read cycle} {v = (X • H) ^ 8} Eq.refl) (axiom period)

  empty-relator : ∀ {u v} → R.reduce (R.relator u v) ≡ [] → u ≈ v
  empty-relator {u} {v} check = Calc.derive-equation {u} {v} {selected = []}
    (R.certificate [] 0 false check) refl

  lt : ∀ {a b : Fin 2} → .(a < b) → a < b
  lt {a} {b} p = recompute (a FP.<? b) p

  full2 : ∀ (a b : Fin 2) → a < b → a ≡ zero × b ≡ suc zero
  full2 zero zero ()
  full2 zero (suc zero) p = Eq.refl , Eq.refl
  full2 (suc zero) zero ()
  full2 (suc zero) (suc zero) (s≤s ())

  no3 : ∀ {a b c : Fin 2} → .(a < b) → .(b < c) → ⊥
  no3 {a} {b} {c} p q = helper a b c (lt p) (lt q)
    where
    helper : ∀ (a b c : Fin 2) → a < b → b < c → ⊥
    helper zero zero c () q
    helper zero (suc zero) zero p ()
    helper zero (suc zero) (suc zero) p (s≤s ())
    helper (suc zero) zero c () q
    helper (suc zero) (suc zero) c (s≤s ()) q

  table1 : ∀ {u v} → u U.=== v → Old.Rules.D T.⌊ u ⌋ʷ ≈ Old.Rules.D T.⌊ v ⌋ʷ
  table1 (U.r1a p) = empty-relator Eq.refl
  table1 (U.r1b {a = zero}) = empty-relator Eq.refl
  table1 (U.r1b {a = suc zero}) = empty-relator Eq.refl
  table1 (U.r1c p q r) = ⊥-elim (no3 p q)
  table1 (U.r2a {a = a} {b = b} {c = c} {d = d} p q ac ad bc bd)
    with full2 a b (lt p) | full2 c d (lt q)
  ... | Eq.refl , Eq.refl | Eq.refl , Eq.refl = ⊥-elim (ac Eq.refl)
  table1 (U.r2b {a = a} {b = b} {c = c} p ca cb) with full2 a b (lt p)
  table1 (U.r2b {c = zero} p ca cb) | Eq.refl , Eq.refl = ⊥-elim (ca Eq.refl)
  table1 (U.r2b {c = suc zero} p ca cb) | Eq.refl , Eq.refl = ⊥-elim (cb Eq.refl)
  table1 (U.r2c p q r s _ _ _ _ _ _ _ _) = ⊥-elim (no3 q r)
  table1 (U.r2d {a = zero} {b = zero} ne) = ⊥-elim (ne Eq.refl)
  table1 (U.r2d {a = zero} {b = suc zero} ne) =
    Calc.derive-equation {selected = cycle} (R.certificate [] 0 false Eq.refl) cycle-trivial
  table1 (U.r2d {a = suc zero} {b = zero} ne) =
    Calc.derive-equation {selected = cycle} (R.certificate [] 1 false Eq.refl) cycle-trivial
  table1 (U.r2d {a = suc zero} {b = suc zero} ne) = ⊥-elim (ne Eq.refl)
  table1 (U.r2e p q r _ _ _ _) = ⊥-elim (no3 p q)
  table1 (U.r2f p q r s t u _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = ⊥-elim (no3 p q)
  table1 (U.r3a p q r) = ⊥-elim (no3 p q)
  table1 (U.r3b p q r) = ⊥-elim (no3 p q)
  table1 (U.r3c {a = a} {b = b} p) with full2 a b (lt p)
  ... | Eq.refl , Eq.refl = empty-relator Eq.refl
  table1 (U.r3d p q r s t) = ⊥-elim (no3 p q)
  table1 (U.r3e p q r s t u) = ⊥-elim (no3 p q)
  table1 (U.r3f p q r s t u) = ⊥-elim (no3 p q)
  table1 (U.r3g p q r s t) = ⊥-elim (no3 p q)
  table1 (U.r4a p q r s) = ⊥-elim (no3 p q)
  table1 (U.r4b p q r) = ⊥-elim (no3 p q)
  table1 (U.r4c p q r s) = ⊥-elim (no3 p q)
  table1 (U.r5a p q r s t u v) = ⊥-elim (no3 p q)
  table1 (U.r6a p q r s t u v w) = ⊥-elim (no3 p q)

  table2 : ∀ {u v} → u T.===ᴸ v → Old.Rules.D u ≈ Old.Rules.D v
  table2 (T.table1 ax) = table1 ax
  table2 T.r7a = empty-relator Eq.refl
  table2 (T.r7b p q r _ _ _ _) = ⊥-elim (no3 p q)
  table2 (T.r7c {a = a} {b = b} p _ _) with full2 a b (lt p)
  ... | Eq.refl , Eq.refl = Calc.derive-equation {selected = cycle}
    (R.certificate [] 1 false Eq.refl) cycle-trivial
  table2 (T.r7d₀ {x = a} {y = b} p _ _) with full2 a b (lt p)
  ... | Eq.refl , Eq.refl = empty-relator Eq.refl
  table2 (T.r7d₁ p q r _ _ _ _) = ⊥-elim (no3 p q)

translated-axiom : ∀ {u v} → Old._===_ u v → u ≈ v
translated-axiom (Old.decoded ax) = table2 ax
translated-axiom (Old.recover X-gen) = empty-relator Eq.refl
translated-axiom (Old.recover H-gen) = empty-relator Eq.refl
translated-axiom (Old.recover (gate₀ ()))
translated-axiom (Old.recover ((gate₀ ()) ↥))

from-translated : ∀ {u v} → u Old.Circuit.≈ v → u ≈ v
from-translated PB.refl = refl
from-translated (PB.sym p) = sym (from-translated p)
from-translated (PB.trans p q) = trans (from-translated p) (from-translated q)
from-translated (PB.cong p q) = cong (from-translated p) (from-translated q)
from-translated PB.assoc = assoc
from-translated PB.left-unit = left-unit
from-translated PB.right-unit = right-unit
from-translated (PB.axiom ax) = translated-axiom ax

opaque
  unfolding Ring._+ᴰ_ Ring._*ᴰ_ Ring.-ᴰ_

  to-translated-axiom : ∀ {u v} → Relations u v → u Old.Circuit.≈ v
  to-translated-axiom x-square = Old.complete Eq.refl
  to-translated-axiom h-square = Old.complete Eq.refl
  to-translated-axiom period = Old.complete Eq.refl

to-translated : ∀ {u v} → u ≈ v → u Old.Circuit.≈ v
to-translated refl = PB.refl
to-translated (sym p) = PB.sym (to-translated p)
to-translated (trans p q) = PB.trans (to-translated p) (to-translated q)
to-translated (cong p q) = PB.cong (to-translated p) (to-translated q)
to-translated assoc = PB.assoc
to-translated left-unit = PB.left-unit
to-translated right-unit = PB.right-unit
to-translated (axiom ax) = to-translated-axiom ax

sound : ∀ {u v} → u ≈ v → interpret u ≡ interpret v
sound = Old.sound ∘ to-translated
  where open import Function.Base using (_∘_)

complete : ∀ {u v} → interpret u ≡ interpret v → u ≈ v
complete eq = from-translated (Old.complete eq)

physical-sound : ∀ {u v} → u ≈ v → Physical.interpret u ≡ Physical.interpret v
physical-sound {u} {v} eq = Eq.trans (Bridge.one u)
  (Eq.trans (sound eq) (Eq.sym (Bridge.one v)))

physical-complete : ∀ {u v : Circuit 1} → Physical.interpret u ≡ Physical.interpret v → u ≈ v
physical-complete {u} {v} eq = complete
  (Eq.trans (Eq.sym (Bridge.one u)) (Eq.trans eq (Bridge.one v)))
