------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness for affine circuits, given completeness on at most
-- eight wires, in the calculus with the schema.
--
-- An affine circuit is a word in X, CX and the swap
-- (`AffineWords.AGen`).  Two affine circuits with the same matrix are
-- equal (`affine-complete`).
-- The proof borrows the completeness of Amy, Chen and Ross's
-- CNOT-dihedral relations (`CNOT+Dihedral.Completeness`): erasing T
-- and ω (`E`) carries their derivations into this calculus, since every
-- one of their relations, erased, is an equation of affine circuits on
-- at most four wires (proved here by evaluation), a swap rule, or a
-- structural rule.  Their CNOT is our CX (control on wire 1), and both
-- developments read wire 0 as the first bit.  An affine word read in
-- their semantics picks up no phase, and its permutation is the
-- classical action of GeneralN/Classical, which the matrix determines
-- column by column.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.Affine
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (Bool ; true ; false ; T ; not ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (zero ; suc ; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; _∷_ ; lookup ; tabulate)
open import Data.Vec.Properties using (tabulate∘lookup ; tabulate-cong)
open import Relation.Binary.PropositionalEquality as Eq
  using (refl ; sym ; trans ; cong ; cong₂ ; subst₂ ; _≢_)
open import Relation.Nullary.Decidable using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap ; _^_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.Decide using (by-eq)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; δ-refl ; δ-≢ ; _!_)
import Examples.Groups.CCX+HH.Semantics as Sem
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (ket ; physical-column)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (idx ; bits ; bits-idx ; idx-injective)
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis ; basis-!)

import Examples.Groups.CNOT+Dihedral.Syntactics as CD
import Examples.Groups.CNOT+Dihedral.Semantics as CDS
import Examples.Groups.CNOT+Dihedral.Evaluation as CDE
import Examples.Groups.CNOT+Dihedral.Interpretation as CDI
open import Examples.Groups.CCX+HH.NaturalP.AffineWords public
open import Examples.Groups.CNOT+Dihedral.Completeness using () renaming (complete to cd-complete)

private
  variable
    n : ℕ

  le : ∀ a → T (a ≤ᵇ 8) → a ≤ 8
  le a p = ≤ᵇ⇒≤ a 8 p

------------------------------------------------------------------------
-- The erased relations

-- The relations of Amy, Chen and Ross, erased, on their own wires.
private
  opaque
    unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

    R₂₀ : 2 ⊢ (E ʷ) (CD.CNOT • CD.X • CD.CNOT) ≈ (E ʷ) CD.X
    R₂₀ = complete≤ (le 2 tt) {u = (E ʷ) (CD.CNOT • CD.X • CD.CNOT)} {v = (E ʷ) CD.X}
      (by-eq tt)

    R₃₀ : 2 ⊢ (E ʷ) (CD.CNOT • CD.X CD.↑ • CD.CNOT) ≈ (E ʷ) (CD.X CD.↑ • CD.X)
    R₃₀ = complete≤ (le 2 tt) {u = (E ʷ) (CD.CNOT • CD.X CD.↑ • CD.CNOT)}
      {v = (E ʷ) (CD.X CD.↑ • CD.X)} (by-eq tt)

    R₅₀ : 2 ⊢ (E ʷ) CD.SWAP ≈ (E ʷ) (CD.CNOT • CD.SWAP • CD.CNOT • CD.SWAP • CD.CNOT)
    R₅₀ = complete≤ (le 2 tt) {u = (E ʷ) CD.SWAP}
      {v = (E ʷ) (CD.CNOT • CD.SWAP • CD.CNOT • CD.SWAP • CD.CNOT)} (by-eq tt)

    R₆₀ : 3 ⊢ (E ʷ) CD.CNOT₂₀ ≈ (E ʷ) (CD.CNOT • CD.CNOT CD.↑ • CD.CNOT • CD.CNOT CD.↑)
    R₆₀ = complete≤ (le 3 tt) {u = (E ʷ) CD.CNOT₂₀}
      {v = (E ʷ) (CD.CNOT • CD.CNOT CD.↑ • CD.CNOT • CD.CNOT CD.↑)} (by-eq tt)

    R₇₀ : 1 ⊢ (E ʷ) (CD.T ^ 8) ≈ ε
    R₇₀ = complete≤ (le 1 tt) {u = (E ʷ) (CD.T ^ 8)} {v = ε} (by-eq tt)

    R₈₀ : 2 ⊢ (E ʷ) (CD.U ^ 4) ≈ (E ʷ) (CD.T ^ 4 • (CD.T CD.↑) ^ 4)
    R₈₀ = complete≤ (le 2 tt) {u = (E ʷ) (CD.U ^ 4)}
      {v = (E ʷ) (CD.T ^ 4 • (CD.T CD.↑) ^ 4)} (by-eq tt)

    R₉₀ : 3 ⊢ (E ʷ) (CD.V ^ 2) ≈
      (E ʷ) (CD.T ^ 6 • (CD.T CD.↑) ^ 6 • (CD.T CD.↑ CD.↑) ^ 6 • (CD.U CD.↑) ^ 2 •
             CD.U₀₂ ^ 2 • CD.U ^ 2)
    R₉₀ = complete≤ (le 3 tt) {u = (E ʷ) (CD.V ^ 2)}
      {v = (E ʷ) (CD.T ^ 6 • (CD.T CD.↑) ^ 6 • (CD.T CD.↑ CD.↑) ^ 6 • (CD.U CD.↑) ^ 2 •
             CD.U₀₂ ^ 2 • CD.U ^ 2)} (by-eq tt)

    R₁₀₀ : 0 ⊢ (E ʷ) (CD.ω ^ 8) ≈ ε
    R₁₀₀ = complete≤ (le 0 tt) {u = (E ʷ) (CD.ω ^ 8)} {v = ε} (by-eq tt)

    R₁₁₀ : 1 ⊢ (E ʷ) (CD.X • CD.T • CD.X) ≈ (E ʷ) (CD.ω • CD.T ^ 7)
    R₁₁₀ = complete≤ (le 1 tt) {u = (E ʷ) (CD.X • CD.T • CD.X)}
      {v = (E ʷ) (CD.ω • CD.T ^ 7)} (by-eq tt)

    R₁₂₀ : 2 ⊢ (E ʷ) (CD.CNOT • CD.T CD.↑ • CD.CNOT) ≈ (E ʷ) (CD.T CD.↑)
    R₁₂₀ = complete≤ (le 2 tt) {u = (E ʷ) (CD.CNOT • CD.T CD.↑ • CD.CNOT)}
      {v = (E ʷ) (CD.T CD.↑)} (by-eq tt)

    R₁₃₀ : 4 ⊢ (E ʷ) (CD.CNOT CD.↑ CD.↑ • CD.V • CD.CNOT CD.↑ CD.↑) ≈
      (E ʷ) (CD.T ^ 5 • (CD.T CD.↑) ^ 5 • (CD.T CD.↑ CD.↑) ^ 5 • (CD.T CD.↑ CD.↑ CD.↑) ^ 5 •
        (CD.U CD.↑ CD.↑) ^ 3 • CD.U₁₃ ^ 3 • CD.U₀₃ ^ 3 • (CD.U CD.↑) ^ 3 • CD.U₀₂ ^ 3 •
        CD.U ^ 3 • CD.V CD.↑ • CD.V₀₂₃ • CD.V₀₁₃ • CD.V)
    R₁₃₀ = complete≤ (le 4 tt)
      {u = (E ʷ) (CD.CNOT CD.↑ CD.↑ • CD.V • CD.CNOT CD.↑ CD.↑)}
      {v = (E ʷ) (CD.T ^ 5 • (CD.T CD.↑) ^ 5 • (CD.T CD.↑ CD.↑) ^ 5 • (CD.T CD.↑ CD.↑ CD.↑) ^ 5 •
        (CD.U CD.↑ CD.↑) ^ 3 • CD.U₁₃ ^ 3 • CD.U₀₃ ^ 3 • (CD.U CD.↑) ^ 3 • CD.U₀₂ ^ 3 •
        CD.U ^ 3 • CD.V CD.↑ • CD.V₀₂₃ • CD.V₀₁₃ • CD.V)} (by-eq tt)

erase-ax : ∀ {w v} → n CD.VRel, w === v → n ⊢ (E ʷ) w ≈ (E ʷ) v
erase-ax (CD.srel (CD.σrel CD.σ-inv))                  = PB.axiom (srel (σrel σ-inv))
erase-ax (CD.srel (CD.σrel (CD.σ-nat₁ CD.X-gate)))     = PB.axiom (srel (σrel (σ-nat₁ X-gate)))
erase-ax (CD.srel (CD.σrel (CD.σ-nat₁ CD.T-gate)))     = PB.sym unit-comm
erase-ax (CD.srel (CD.σrel (CD.σ-nat₂ CD.CNOT-gate)))  = PB.axiom (srel (σrel (σ-nat₂ CX-gate)))
erase-ax (CD.srel (CD.σrel (CD.σ-nat₂ CD.SWAP-gate)))  = PB.axiom (srel (σrel (σ-nat₂ SW-gate)))
erase-ax (CD.srel (CD.srel CD.R₁))                     = XX
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₂))              = widen m R₂₀
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₃))              = widen m R₃₀
erase-ax (CD.srel (CD.srel CD.R₄))                     = CXCX
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₅))              = widen m R₅₀
erase-ax {₃₊ m} (CD.srel (CD.srel CD.R₆))              = widen m R₆₀
erase-ax {₁₊ m} (CD.srel (CD.srel CD.R₇))              = widen m R₇₀
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₈))              = widen m R₈₀
erase-ax {₃₊ m} (CD.srel (CD.srel CD.R₉))              = widen m R₉₀
erase-ax {m} (CD.srel (CD.srel CD.R₁₀))                = widen m R₁₀₀
erase-ax {₁₊ m} (CD.srel (CD.srel CD.R₁₁))             = widen m R₁₁₀
erase-ax {₂₊ m} (CD.srel (CD.srel CD.R₁₂))             = widen m R₁₂₀
erase-ax {₄₊ m} (CD.srel (CD.srel CD.R₁₃))             = widen m R₁₃₀
erase-ax (CD.cong↑ {w = w} {v = v} x) =
  subst₂ (λ x y → _ ⊢ x ≈ y) (sym (E-↑ w)) (sym (E-↑ v)) (lemma-cong↑ _ _ (erase-ax x))
erase-ax (CD.comm₁ CD.X-gate g)    = comm-gate₁-w↑ X-gate (E g)
erase-ax (CD.comm₁ CD.T-gate g)    = unit-comm
erase-ax (CD.comm₂ CD.CNOT-gate g) = comm-gate₂-w↑↑ CX-gate (E g)
erase-ax (CD.comm₂ CD.SWAP-gate g) = comm-gate₂-w↑↑ SW-gate (E g)
erase-ax (CD.ω↑=ω CD.ω-gate)       = PB.refl

erase : ∀ {w v} → n CD.⊢ w ≈ v → n ⊢ (E ʷ) w ≈ (E ʷ) v
erase PB.refl        = PB.refl
erase (PB.sym p)     = PB.sym (erase p)
erase (PB.trans p q) = PB.trans (erase p) (erase q)
erase (PB.cong p q)  = PB.cong (erase p) (erase q)
erase PB.assoc       = PB.assoc
erase PB.left-unit   = PB.left-unit
erase PB.right-unit  = PB.right-unit
erase (PB.axiom x)   = erase-ax x

------------------------------------------------------------------------
-- Completeness

affine-complete : (a a′ : Word (AGen n)) → interpret ⌈ a ⌉ ≡ interpret ⌈ a′ ⌉ →
  n ⊢ ⌈ a ⌉ ≈ ⌈ a′ ⌉
affine-complete a a′ e =
  subst₂ (λ x y → _ ⊢ x ≈ y) (E-ι a) (E-ι a′) (erase (cd-complete (cd-same a a′ e)))
