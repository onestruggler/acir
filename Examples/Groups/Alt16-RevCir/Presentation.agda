------------------------------------------------------------------------
-- Presentations of groups
--
-- The circuits on four wires over X, CX, CCX and Ex present 𝔄₁₆
--
-- Iso makes the translation f ʷ of circuits into words in Lafont's
-- cycles an isomorphism of the two word groups, and Lafont's Theorem 4
-- (Examples.Groups.Alternating.Presentation) makes the reading of
-- those words as even permutations of sixteen points an isomorphism
-- onto 𝔄₁₆.  Their composite is the presentation: a circuit is read as
-- the even permutation of its word, ⟦_⟧ᴬ.
--
-- That permutation is the circuit's own action: along the Gray-code
-- numbering of the sixteen states it permutes the positions as the
-- circuit maps the states (⟦⟧ᴬ-sem).  So the rules are sound and
-- complete for the functions on states, too: two circuits are equal by
-- the rules exactly when they are the same function (sound, complete).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Presentation where

open import Algebra.Bundles using (Group)
import Algebra.Morphism.Construct.Composition as Compose
open import Data.Fin using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; sym ; trans ; cong)

open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.Embedding using (module Pres)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Word.Base using (_ʷ)

open import Examples.Groups.Alternating.Interpretation
  using () renaming (⟦_⟧ to L⟦_⟧)
open import Examples.Groups.Alternating.Presentation as LA using ()
open import Examples.Groups.Alternating.Semantics
  using (Alt ; Alt-group ; perm)

open import Examples.Groups.Alt16-RevCir.Bridge using (f-sem)
open import Examples.Groups.Alt16-RevCir.Iso using (module Theorem)
open import Examples.Groups.Alt16-RevCir.Numbering using (enc ; dec)
open import Examples.Groups.Alt16-RevCir.Semantics as S using (⟦_⟧ ; _≐_)
open import Examples.Groups.Alt16-RevCir.Syntactics
open import Examples.Groups.Alt16-RevCir.Translation using (f)

open Theorem using (grouplike ; Theorem-Circuits-iso-Cycles)

private
  module LP = _IsPresentationOf_ (LA.presentation {16})
  module G₁ = Group-Lemmas (4 VRel,_===_) grouplike

------------------------------------------------------------------------
-- A circuit as an even permutation

-- The permutation of the circuit's word in the cycles.
⟦_⟧ᴬ : Circuit 4 → Alt 16
⟦ w ⟧ᴬ = L⟦ (f ʷ) w ⟧

-- It carries the position of a state to the position of the state the
-- circuit sends it to.
⟦⟧ᴬ-sem : (w : Circuit 4) (i : Fin 16) →
          perm ⟦ w ⟧ᴬ ⟨$⟩ʳ i ≡ dec (⟦ w ⟧ (enc i))
⟦⟧ᴬ-sem = f-sem

------------------------------------------------------------------------
-- The presentation

-- The isomorphism of Iso, followed by Lafont's.
presentation : (4 VRel,_===_) IsPresentationOf (Alt-group 16)
presentation = record
  { gl  = grouplike
  ; ⟦_⟧ = ⟦_⟧ᴬ
  ; iso = Compose.isGroupIsomorphism
            {G₁ = Group.rawGroup G₁.•-ε-group}
            {G₂ = Group.rawGroup LP.GL.•-ε-group}
            {G₃ = Group.rawGroup (Alt-group 16)}
            (λ {x} {y} {z} → Group.trans (Alt-group 16) {x} {y} {z})
            {f = f ʷ} {g = LP.⟦_⟧}
            Theorem-Circuits-iso-Cycles LP.iso
  }

------------------------------------------------------------------------
-- Soundness and completeness for the functions on states

sound : ∀ {w v : Circuit 4} → 4 ⊢ w ≈ v → ⟦ w ⟧ ≐ ⟦ v ⟧
sound = S.sound

-- Two circuits with the same function have the same permutation, and
-- the presentation's reading is injective.
complete : ∀ {w v : Circuit 4} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 4 ⊢ w ≈ v
complete {w} {v} e = Pres.complete presentation {w} {v} λ i →
  trans (⟦⟧ᴬ-sem w i)
        (trans (cong dec (e (enc i))) (sym (⟦⟧ᴬ-sem v i)))
