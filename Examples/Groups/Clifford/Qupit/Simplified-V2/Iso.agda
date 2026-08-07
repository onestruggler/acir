{-# OPTIONS --cubical-compatible --termination-depth=20 #-}
{-# OPTIONS --inversion-max-depth=1000 #-}

------------------------------------------------------------------------
-- The id-isomorphism  Clifford-Relations ≅ Simplified-Relations.
-- f-well-defined: every Clifford relation holds in Simplified
--                 (selinger via completeness; rest via axiom).
-- g-well-defined: every Simplified relation holds in Clifford
--                 (selinger via soundness; rest via axiom).
-- Fully machine-checked — NO termination pragma (route (B)).
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (id)
open import Data.Product using (_,_ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
open import Presentation.Construct.Base hiding (_*_)
open import Presentation.GroupLike
open import Data.Nat.Primality
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open GroupMorphisms

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem
open import Notations

module Examples.Groups.Clifford.Qupit.Simplified-V2.Iso
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.Clifford.Qupit.Simplified-V1.Syntactics
  p-3 p-prime g* g-gen
open import Examples.Groups.Clifford.Qupit.Simplified-V1.Lemmas
  p-3 p-prime g* g-gen
  using (module Clifford-GroupLike)
import Examples.Groups.Clifford.Qupit.Simplified-V2.Syntactics p-3 p-prime g* g-gen as Sim
import Examples.Groups.Clifford.Qupit.Simplified-V1.Soundness p-3 p-prime g* g-gen as Snd
import Examples.Groups.Clifford.Qupit.Simplified-V2.Lemmas p-3 p-prime g* g-gen as Cmp
-- semi-M bridges: soundness (simplified holds in Clifford) and
-- completeness (original holds in Simplified) of the simplified semi-M relations.
import Examples.Groups.Clifford.Qupit.Simplified-V1.SemiM   p-3 p-prime g* g-gen as MgC
import Examples.Groups.Clifford.Qupit.Simplified-V2.SemiM p-3 p-prime g* g-gen as MgS
-- Clifford-side proofs of Z↔CZ (the new comm-Z-CZ / comm-Z↑-CZ axioms).
import Examples.Groups.Clifford.Qupit.Simplified-V1.LemmasCZ p-3 p-prime g* g-gen as CliL

open import Algebra.Bundles using (Group)

module CliR = Clifford-Relations
module SimR = Sim.Simplified-Relations

-- f : Clifford → Simplified  (every Clifford relation holds in Simplified)
f-well-defined : ∀ {n} → let open PB (SimR._QRel,_===_ n) renaming (_≈_ to _≈₂_) in
    ∀ {w v} -> CliR._QRel,_===_ n w v -> id w ≈₂ id v
f-well-defined CliR.order-S        = PB.axiom SimR.order-S
f-well-defined CliR.order-H        = PB.axiom SimR.order-H
f-well-defined (CliR.M-power k)    = PB.axiom (SimR.M-power k)
f-well-defined CliR.semi-MR        = MgS.SemiS.completeness-semi-MR _
f-well-defined CliR.order-SH       = PB.axiom SimR.order-SH
f-well-defined CliR.comm-HHSHHS    = PB.axiom SimR.comm-HHSHHS
f-well-defined CliR.semi-M↑CZ      = MgS.SemiCZ.completeness-semi-M↑CZ _
f-well-defined CliR.semi-M↓CZ      = MgS.SemiCZ↓.completeness-semi-M↓CZ _
f-well-defined CliR.rel-X↑-CZ      = PB.axiom SimR.rel-X↑-CZ
f-well-defined CliR.rel-X↓-CZ      = PB.axiom SimR.rel-X↓-CZ
f-well-defined CliR.order-CZ       = PB.axiom SimR.order-CZ
f-well-defined CliR.comm-CZ-S↓     = PB.axiom SimR.comm-CZ-S↓
f-well-defined CliR.comm-CZ-S↑     = PB.axiom SimR.comm-CZ-S↑
f-well-defined CliR.selinger-c10   = Cmp.Completeness-S.completeness-c10 _
f-well-defined CliR.selinger-c11   = Cmp.Completeness-S.completeness-c11 _
f-well-defined CliR.selinger-c12   = PB.axiom SimR.selinger-c12
f-well-defined CliR.selinger-c13   = PB.axiom SimR.selinger-c13
f-well-defined CliR.selinger-c14   = PB.axiom SimR.selinger-c14
f-well-defined CliR.selinger-c15   = PB.axiom SimR.selinger-c15
-- Matched through comm₁/comm₂: on the Clifford side these three are now
-- instances of the framework's structural rules, so there is no
-- constructor named comm-H to match on any more.
f-well-defined {₂₊ n} (CliR.comm₁ H-gate _)  = PB.axiom SimR.comm-H
f-well-defined {₂₊ n} (CliR.comm₁ S-gate _)  = PB.axiom SimR.comm-S
f-well-defined {₃₊ n} (CliR.comm₂ CZ-gate _) = PB.axiom SimR.comm-CZ
f-well-defined (CliR.cong↑ eq)     = SimR.lemma-cong↑ _ _ (f-well-defined eq)

-- g : Simplified → Clifford  (every Simplified relation holds in Clifford)
g-well-defined : ∀ {n} → let open PB (CliR._QRel,_===_ n) renaming (_≈_ to _≈₁_) in
  ∀ {u t} -> SimR._QRel,_===_ n u t -> id u ≈₁ id t
g-well-defined SimR.order-S        = PB.axiom CliR.order-S
g-well-defined SimR.order-H        = PB.axiom CliR.order-H
g-well-defined (SimR.M-power k)    = PB.axiom (CliR.M-power k)
g-well-defined SimR.semi-MR        = MgC.SemiS-collected.final-semi-MR _
g-well-defined SimR.order-SH       = PB.axiom CliR.order-SH
g-well-defined SimR.comm-HHSHHS    = PB.axiom CliR.comm-HHSHHS
-- comm-X-Z is no longer a Clifford axiom; it is derived there.
g-well-defined SimR.comm-X-Z       = CliL.CLb.lemma-comm-X-Z _
g-well-defined SimR.semi-M↑CZ      = MgC.SemiCZ.final-semi-M↑CZ _
g-well-defined SimR.semi-M↓CZ      = MgC.SemiCZ↓.final-semi-M↓CZ _
g-well-defined SimR.rel-X↑-CZ      = PB.axiom CliR.rel-X↑-CZ
g-well-defined SimR.rel-X↓-CZ      = PB.axiom CliR.rel-X↓-CZ
g-well-defined SimR.comm-Z-CZ      = CliL.lemma-comm-Z-CZ
g-well-defined SimR.comm-Z↑-CZ     = CliL.lemma-comm-Z↑-CZ
g-well-defined SimR.order-CZ       = PB.axiom CliR.order-CZ
g-well-defined SimR.comm-CZ-S↓     = PB.axiom CliR.comm-CZ-S↓
g-well-defined SimR.comm-CZ-S↑     = PB.axiom CliR.comm-CZ-S↑
g-well-defined SimR.selinger-c10   = Snd.C10.soundness-c10 _
g-well-defined SimR.selinger-c11   = Snd.C11.soundness-c11 _
g-well-defined SimR.selinger-c12   = PB.axiom CliR.selinger-c12
g-well-defined SimR.selinger-c13   = PB.axiom CliR.selinger-c13
g-well-defined SimR.selinger-c14   = PB.axiom CliR.selinger-c14
g-well-defined SimR.selinger-c15   = PB.axiom CliR.selinger-c15
-- Both sides are on the framework now, so these match comm₁/comm₂ here too.
g-well-defined {₂₊ n} (SimR.comm₁ H-gate _)  = PB.axiom CliR.comm-H
g-well-defined {₂₊ n} (SimR.comm₁ S-gate _)  = PB.axiom CliR.comm-S
g-well-defined {₃₊ n} (SimR.comm₂ CZ-gate _) = PB.axiom CliR.comm-CZ
g-well-defined (SimR.cong↑ eq)     = Clifford-Relations.lemma-cong↑ _ _ (g-well-defined eq)

module M (n : ℕ) where
  module G1 = Group-Lemmas (CliR._QRel,_===_ n) (Clifford-GroupLike.grouplike {n})
  module G2 = Group-Lemmas (SimR._QRel,_===_ n) (Cmp.Simplified-GroupLike-S.grouplike {n})

  open import Presentation.MorphismId (CliR._QRel,_===_ n) (SimR._QRel,_===_ n)
  open GroupMorphs (Clifford-GroupLike.grouplike {n}) (Cmp.Simplified-GroupLike-S.grouplike {n})

  Theorem-Clifford-iso-Simplified :
    IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) id
  Theorem-Clifford-iso-Simplified =
    StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
