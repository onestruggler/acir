------------------------------------------------------------------------
-- Presentations of groups
--
-- Every compact stabilizer equation is derived from Table 1.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Compact.Soundness where

open import Data.Vec.Base using (Vec ; lookup)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_ʷ)
open import Examples.Groups.CCX+HH.ThreeQubit.Compact.Syntactics
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (b)
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerAction as Action
import Examples.Groups.CCX+HH.ThreeQubit.Compact.SourceChecks as Check
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as Main
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
import Examples.Groups.Symmetric.Syntactics as Sym
import Examples.Groups.Symmetric.SubPresentation.Interpretation as SymSound
import Presentation.Base as PB
import Presentation.Properties as PP

private module A = PB (T._===_ {8})

private
  vec-ext : ∀ {n} {u v : Vec D n} → (∀ i → lookup u i ≡ lookup v i) → u ≡ v
  vec-ext {u = u} {v} eq = Eq.trans (Eq.sym (VP.tabulate∘lookup u))
    (Eq.trans (VP.tabulate-cong eq) (VP.tabulate∘lookup v))

  permutation-vectors : ∀ {u v} → Sym._VRel,_===_ 8 u v → ∀ z →
    S.actVʷ ((b ʷ) (permutation u)) z ≡ S.actVʷ ((b ʷ) (permutation v)) z
  permutation-vectors {u} {v} ax z = vec-ext λ i →
    Eq.trans (Action.permutation-action u z i)
      (Eq.trans (Eq.cong (lookup z) (SymSound.sound-ax ax i))
        (Eq.sym (Action.permutation-action v z i)))

encode-axiom : ∀ {u v} → u === v → (b ʷ) u A.≈ (b ʷ) v
encode-axiom (phase-square i) = Main.completeness (Check.square i)
encode-axiom (phase-commute i j p) = Main.completeness (Check.commute i j)
encode-axiom (cross i j) = Main.completeness (Check.crossing i j)
encode-axiom (symmetric {u} {v} ax) = Main.completeness (S.col-ext λ j →
  Eq.trans (S.col-actMʷ ((b ʷ) (permutation u)) S.𝕀 j)
    (Eq.trans (permutation-vectors ax (S.col S.𝕀 j))
      (Eq.sym (S.col-actMʷ ((b ʷ) (permutation v)) S.𝕀 j))))

encode-cong : ∀ {u v} → u ≈ v → (b ʷ) u A.≈ (b ʷ) v
encode-cong = PP.StarCongruence.fʷ-cong _===_ (T._===_ {8}) b encode-axiom
