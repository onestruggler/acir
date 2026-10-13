------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément translation for three-wire X,CX,CCX,HH circuits.
-- The finite auxiliary normal form has 135 frame representatives and
-- an even signed-permutation base with 105 equations.  The resulting
-- 1185 circuit equations have no parameters or semantic-equality axioms.
-- Their transition and base equations
-- are derived in the existing two-level Table 1 presentation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Presentation where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Data.Product.Base using (_,_)
open import Word.Base using ([_]ʷ)
open import Presentation.GroupLike using (Grouplike)
open import Examples.Groups.CCX+HH.Syntactics using (Circuit)
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Derived {8} as Source
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as Main
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Reduction
import Examples.Groups.CCX+HH.ThreeQubit.FiniteExtension as Extension
import Examples.Groups.CCX+HH.ThreeQubit.Compact.Presentation as Base
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators
  using (b ; d ; d-correct)
open import Examples.Groups.CCX+HH.ThreeQubit.Cosets using (c000 ; rep)
open import Examples.Groups.CCX+HH.ThreeQubit.Table using (h)
open import Examples.Groups.CCX+HH.ThreeQubit.Factorizations using (factor)
open import Examples.Groups.CCX+HH.ThreeQubit.Separation using (separate)
open import Examples.Groups.CCX+HH.ThreeQubit.Involutions using (source-involution)

module Theory = Extension (T._===_ {8}) Source.grouplike Base._===_
  E.e b d d-correct Base.encode-axiom Base.encode-injective
  c000 rep refl h factor separate

open Theory public using (_===_ ; _≈_ ; table ; stabilizer ; normalization)

soundness : ∀ {u v : Circuit 3} → u ≈ v → C.interpret u ≡ C.interpret v
soundness {u} {v} proof = Eq.trans (Eq.sym (C.encoding-correct u))
  (Eq.trans (Reduction.sound-act (Theory.encode-cong proof) S.𝕀)
    (C.encoding-correct v))

completeness : ∀ {u v : Circuit 3} → C.interpret u ≡ C.interpret v → u ≈ v
completeness {u} {v} equality = Theory.encode-injective (Main.completeness
  (Eq.trans (C.encoding-correct u)
    (Eq.trans equality (Eq.sym (C.encoding-correct v)))))

grouplike : Grouplike _===_
grouplike g = [ g ]ʷ , Theory.encode-injective (source-involution g)
