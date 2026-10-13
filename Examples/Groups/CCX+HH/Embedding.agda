------------------------------------------------------------------------
-- Presentations of groups
--
-- Expanding each HH gate into its two H gates embeds the complete
-- circuit theory into the H theory, at every width.  Equality is both
-- preserved and reflected, so the presented groups embed as well.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Embedding where

open import Data.Nat.Base using (ℕ)
open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Presentation.GroupLike using (module Group-Lemmas)
import Presentation.Base as PB
import Presentation.Morphism as Morphism
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+HH.Presentation as HH
import Examples.Groups.CCX+H.Presentation as H
import Examples.Groups.CCX+H.Orthogonal as HO
import Examples.Groups.CCX+HH.GeneralN.HadamardEmbedding as Physical
open Physical public using (e ; embed ; embed-shift ; physical-correct)

preserves : ∀ {n} {u v : HH.Circuit n} → u HH.≈ v → H._⊢_≈_ n (embed u) (embed v)
preserves {n} {u} {v} eq = H.complete n
  (Physical.preserve {u = u} {v = v} (HH.soundness eq))

reflects : ∀ {n} {u v : HH.Circuit n} → H._⊢_≈_ n (embed u) (embed v) → u HH.≈ v
reflects {n} {u} {v} eq = HH.completeness
  (Physical.reflect {u = u} {v = v} (H.sound n eq))

module At (n : ℕ) where
  module Source = Group-Lemmas (HH._===_ {n}) (HH.grouplike n)
  module Target = Group-Lemmas (H.Relations n) (HO.grouplike n)
  module Builder = Morphism.GroupMorphism (HH._===_ {n}) (H.Relations n)
    (HH.grouplike n) (HO.grouplike n)
  module Hom = Builder.StarGroupHomomorphism e (λ ax → preserves (PB.axiom ax))
  open GroupMorphisms (Group.rawGroup Source.•-ε-group) (Group.rawGroup Target.•-ε-group)

  monomorphism : IsGroupMonomorphism (embed {n})
  monomorphism = record
    { isGroupHomomorphism = Hom.isGroupHomomorphism
    ; injective = reflects
    }
