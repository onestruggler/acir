------------------------------------------------------------------------
-- Presentations of groups
--
-- The Clifford+CS circuits on 4 + m wires present their unitaries
--
-- The theory of Stable.Rules presents the submonoid of U (2^(4 + m))
-- that the circuits on 4 + m wires generate, for every m, as Clifford+CS-
-- 3qubit's Presentation and Unitary.presentation≤₃ do on three wires and
-- fewer: a circuit is read as the two-level matrix of its encoding into
-- P′ (`⟦_⟧ᵁ`, through Auxiliary.P.asG and Clifford+CS-TwoLevel's
-- unitary reading), a monoid homomorphism; it respects the theory,
-- which is sound (Stable.Soundness), the encoding having the circuit's
-- matrix (Section8.e-sem) and the Gray-numbered reading Φ of BridgeGray
-- taking a two-level word's scaled operator to its matrix (`Φ-Y`); and
-- it is injective because Φ is (`Φ-inj`) and the theory is complete
-- (on four wires by `Four.Complete`, given here as `c4`, from five on by
-- Stable.Theorem).  It is stated as a monoid sub-presentation, every
-- gate having a left inverse (`grouplikeᵧ`), so that the submonoid is
-- the subgroup the gates generate: the group form, through ForStdlib's
-- isMonoidHomomorphism⇒isGroupHomomorphism, compares U's inverses at a
-- symbolic size and exhausted 10 GB.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)

module Examples.Groups.Clifford+CS.Stable.Presentation (c4 : Complete 4) (c₅ : Completeᵧ 5) where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_ ; proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₄₊)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubMonoidPresentationOf_)
open import Presentation.GroupLike using (Grouplike)

open import Examples.Groups.Clifford+CS.Semantics using (_~_ ; _∙_ ; ε∙ ; ~-sym ; ~-trans ; ~-reflexive ; ∙-cong ; Idₒ)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; grouplike)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; ⟦⟧ₒ-ε)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using () renaming (hom to ⟦hom⟧)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_YVRel,_===_ ; _⊢ᵧ_≈_ ; embed)
open import Examples.Groups.Clifford+CS.Stable.Soundness using (soundᵧ)
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics using (UMat ; U ; ⟦_⟧ᵐ ; ⟦•⟧ᵐ)
import Examples.Groups.Clifford+CS-TwoLevel.Presentation as TLP
import Examples.Groups.Clifford+CS.Encoding as Encoding
import Examples.Groups.Clifford+CS.Section8 as Section8
import Examples.Groups.Clifford+CS.BridgeGray as BridgeGray
open import Examples.Groups.Clifford+CS.Stable.Theorem c4 c₅ using (completeᵧ)

------------------------------------------------------------------------
-- Inverses, and completeness from four wires on

-- Every generator has a left inverse (the old theory's, embedded).
grouplikeᵧ : ∀ {n} → Grouplike (n YVRel,_===_)
grouplikeᵧ g with grouplike g
... | ig , prf = ig , embed prf

completeᵧ₄ : ∀ m → Completeᵧ (₄₊ m)
completeᵧ₄ zero    e = embed (c4 e)
completeᵧ₄ (suc m) e = completeᵧ m e

------------------------------------------------------------------------
-- The presentation on 4 + m wires

module _ (m : ℕ) where
  private
    module E  = Encoding m
    module S8 = Section8 m
    module BG = BridgeGray (₄₊ m)

    n : ℕ
    n = ₄₊ m

    -- The encoding of a circuit has the circuit's reading.
    eʷ-sem : (w : Circuit n) → BG.⟦ (E.e ʷ) w ⟧PY ~ ⟦ w ⟧
    eʷ-sem [ g ]ʷ  = S8.e-sem g
    eʷ-sem ε       = ~-sym {s = ⟦_⟧ {n} ε} {t = ε∙} (~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {n} ε} {Idₒ} Eq.refl ⟦⟧ₒ-ε)
    eʷ-sem (u • v) =
      ~-trans {s = BG.⟦ (E.e ʷ) u ⟧PY ∙ BG.⟦ (E.e ʷ) v ⟧PY} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} {u = ⟦ u • v ⟧}
        (∙-cong {s = BG.⟦ (E.e ʷ) u ⟧PY} {s' = ⟦ u ⟧} {t = BG.⟦ (E.e ʷ) v ⟧PY} {t' = ⟦ v ⟧} (eʷ-sem u) (eʷ-sem v))
        (~-sym {s = ⟦ u • v ⟧} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} (⟦hom⟧ u v))

    -- The two-level word of a circuit.
    tw : Circuit n → Word _
    tw w = (asG ʷ) ((E.e ʷ) w)

    -- Its scaled operator is the circuit's.
    tw-sem : (w : Circuit n) → BG.⟦ tw w ⟧Y ~ ⟦ w ⟧
    tw-sem w = ~-trans {s = BG.⟦ tw w ⟧Y} {BG.⟦ (E.e ʷ) w ⟧PY} {⟦ w ⟧}
                 (~-sym {s = BG.⟦ (E.e ʷ) w ⟧PY} {BG.⟦ tw w ⟧Y} (BG.PY-asG ((E.e ʷ) w))) (eʷ-sem w)

  -- A circuit's unitary: the two-level matrix of its encoding.
  ⟦_⟧ᵁ : Circuit n → UMat E.N
  ⟦ w ⟧ᵁ = TLP.⟦_⟧ᵘ {E.N} (tw w)

  private
    -- Equal readings, equal matrices, and back.
    sem⇒mat : ∀ {w v : Circuit n} → ⟦ w ⟧ ~ ⟦ v ⟧ → proj₁ ⟦ w ⟧ᵁ ≡ proj₁ ⟦ v ⟧ᵁ
    sem⇒mat {w} {v} eq =
      Eq.trans (Eq.sym (BG.Φ-Y (tw w)))
        (Eq.trans (BG.Φ-cong {s = BG.⟦ tw w ⟧Y} {BG.⟦ tw v ⟧Y} same) (BG.Φ-Y (tw v)))
      where
      same : BG.⟦ tw w ⟧Y ~ BG.⟦ tw v ⟧Y
      same = ~-trans {s = BG.⟦ tw w ⟧Y} {⟦ w ⟧} {BG.⟦ tw v ⟧Y} (tw-sem w)
               (~-trans {s = ⟦ w ⟧} {⟦ v ⟧} {BG.⟦ tw v ⟧Y} eq (~-sym {s = BG.⟦ tw v ⟧Y} {⟦ v ⟧} (tw-sem v)))

    mat⇒sem : ∀ {w v : Circuit n} → proj₁ ⟦ w ⟧ᵁ ≡ proj₁ ⟦ v ⟧ᵁ → ⟦ w ⟧ ~ ⟦ v ⟧
    mat⇒sem {w} {v} eq =
      ~-trans {s = ⟦ w ⟧} {BG.⟦ tw w ⟧Y} {⟦ v ⟧} (~-sym {s = BG.⟦ tw w ⟧Y} {⟦ w ⟧} (tw-sem w))
        (~-trans {s = BG.⟦ tw w ⟧Y} {BG.⟦ tw v ⟧Y} {⟦ v ⟧}
          (BG.Φ-inj {s = BG.⟦ tw w ⟧Y} {BG.⟦ tw v ⟧Y}
            (Eq.trans (BG.Φ-Y (tw w)) (Eq.trans eq (Eq.sym (BG.Φ-Y (tw v))))))
          (tw-sem v))



  -- The rules on 4 + m wires present the submonoid of U (2^(4 + m)) the
  -- gates generate, which is the subgroup they generate: every gate has
  -- a left inverse (`grouplikeᵧ`).
  presentation : (n YVRel,_===_) IsSubMonoidPresentationOf (Group.monoid (U E.N))
  presentation = record
    { ⟦_⟧  = ⟦_⟧ᵁ
    ; mono = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = λ eq → sem⇒mat (soundᵧ eq) }
          ; homo = λ w v → ⟦•⟧ᵐ (tw w) (tw v)
          }
        ; ε-homo = Eq.refl
        }
      ; injective = λ {w} {v} eq → completeᵧ₄ m (mat⇒sem {w} {v} eq)
      }
    }
