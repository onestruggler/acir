------------------------------------------------------------------------
-- Presentations of groups
--
-- The complete circuit calculus as a group sub-presentation of the
-- ordinary orthogonal group over Z[1/sqrt(2)], at every width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Orthogonal where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _*_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_)
open import Algebra.Bundles using (Group)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Presentation.GroupLike using (Grouplike)
open import Presentation.Definitions
  using (_IsSubMonoidPresentationOf_ ; _IsSubPresentationOf_
        ; subMonoidPresentation⇒subPresentation)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; RingD ; AdjointD)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics as O
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as M
open import Examples.Groups.CCX+H.Syntactics using (Gen ; Circuit ; gate₀)
open import Examples.Groups.CCX+H.Presentation using (Relations ; sound ; complete)
import Examples.Groups.CCX+H.GeneralN.Semantics as S
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as C
open import Examples.Groups.CCX+H.GeneralN.GateInvolutions using (matrix-involutive)

private
  cast-unitary : ∀ {j k} (p : j ≡ k) {A : Matrix j j D} →
    M.Unitary A → M.Unitary (C.cast-matrix p A)
  cast-unitary refl u = u

  empty-unitary : ∀ (w : Circuit 0) → M.Unitary (C.interpret w)
  empty-unitary [ gate₀ () ]ʷ
  empty-unitary ε = M.Unitary-𝕀
  empty-unitary (u • v) = M.Unitary-·*· (empty-unitary u) (empty-unitary v)

unitary : ∀ {n} (w : Circuit n) → O.Unitary (C.interpret w)
unitary {zero} = empty-unitary
unitary {suc n} w = Eq.subst M.Unitary (C.At.correct n w)
  (cast-unitary (Eq.sym (NP.*-comm 2 (2 ^ℕ n)))
    (Eq.subst M.Unitary (S.At.encoding-correct n w)
      (M.Dim.Unitary-⟦⟧ᴸ (2 ^ℕ n) (S.At.compile n w))))

⟦_⟧ᴼ : ∀ {n} → Circuit n → O.OMat (2 ^ℕ n)
⟦ w ⟧ᴼ = C.interpret w , unitary w

grouplike : ∀ n → Grouplike (Relations n)
grouplike n g = [ g ]ʷ , complete n (matrix-involutive g)

submonoidPresentation : ∀ n →
  Relations n IsSubMonoidPresentationOf (Group.monoid (O.O (2 ^ℕ n)))
submonoidPresentation n = record
  { ⟦_⟧ = ⟦_⟧ᴼ
  ; mono = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = sound n }
        ; homo = λ u v → refl
        }
      ; ε-homo = refl
      }
    ; injective = complete n
    }
  }

subpresentationᴼ : ∀ n → Relations n IsSubPresentationOf (O.O (2 ^ℕ n))
subpresentationᴼ n = subMonoidPresentation⇒subPresentation
  (submonoidPresentation n) (grouplike n)
