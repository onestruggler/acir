------------------------------------------------------------------------
-- Presentations of groups
--
-- Two two-level words act alike when they agree on every basis column.
--
-- The matrix of a word is its action on the columns of the identity, so
-- agreement there is agreement everywhere (`cols⇒action`).  The check is
-- one boolean (`agree`), each side computed as a vector action letter by
-- letter: for a word of many letters on a few wires that is far cheaper
-- than a product of dense matrices.  `ctrl-by-columns` puts it to the
-- use NaturalP.CtrlSem makes of it: a circuit acts as another one
-- controlled by wire 0.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Columns where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; T)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; ε)

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (D ; isCommutativeRing-D ; adj-D ; ½ᴰ)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-cong ; encode-parallel ; encode-parallel-correct)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating)
open import Examples.Groups.CCX+HH.Decide using (eqVec ; eqVec-sound ; eqD ; eqD-sound)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.StructuralEncoding as E
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics
  using (quantum ; encoding-action)
open import Examples.Groups.CCX+HH.NaturalP.Blocks2 using (ctrlA)

private
  variable
    n N : ℕ

  T-∧ : ∀ {x y} → T (x ∧ y) → T x × T y
  T-∧ {true} {true} _ = tt , tt

allFin : (Fin N → Bool) → Bool
allFin {zero}  f = true
allFin {suc N} f = f zero ∧ allFin (λ i → f (suc i))

allFin-sound : (f : Fin N → Bool) → T (allFin f) → ∀ i → T (f i)
allFin-sound {suc N} f p zero    = proj₁ (T-∧ {f zero} p)
allFin-sound {suc N} f p (suc i) = allFin-sound (λ i → f (suc i)) (proj₂ (T-∧ {f zero} p)) i

-- The two words agree on every column of the identity.
agree : (w v : Word (TL.Gen N)) → Bool
agree w v = allFin λ i → eqVec eqD (A.actVʷ w (A.col A.𝕀 i)) (A.actVʷ v (A.col A.𝕀 i))

cols⇒action : (w v : Word (TL.Gen N)) → T (agree w v) → ∀ x → A.actVʷ w x ≡ A.actVʷ v x
cols⇒action w v p = A.same-action w v (A.col-ext λ i →
  trans (A.col-actMʷ w A.𝕀 i)
  (trans (eqVec-sound eqD eqD-sound _ _ (allFin-sound _ p i))
    (sym (A.col-actMʷ v A.𝕀 i))))

-- The encoding of g on the odd coordinates acts as g controlled by
-- wire 0.
ctrl-word : (g : H.Circuit n) → ∀ x →
  A.actVʷ (encode-parallel (alternating (2 ^ n)) ε (E.encode g)) x ≡ ctrlA (2 ^ n) (quantum g) x
ctrl-word {n} g x =
  trans (encode-parallel-correct (alternating (2 ^ n)) ε (E.encode g) x)
    (parallel-cong (alternating (2 ^ n))
      {f = A.actVʷ ε} {f′ = λ y → y} {g = A.actVʷ (E.encode g)} {g′ = quantum g}
      (λ _ → refl) (encoding-action g) x)

-- w acts as g controlled by wire 0.
ctrl-by-columns : (w : H.Circuit (suc n)) (g : H.Circuit n) →
  T (agree (E.encode w) (encode-parallel (alternating (2 ^ n)) ε (E.encode g))) →
  ∀ x → quantum w x ≡ ctrlA (2 ^ n) (quantum g) x
ctrl-by-columns {n} w g p x =
  trans (sym (encoding-action w x))
  (trans (cols⇒action (E.encode w) (encode-parallel (alternating (2 ^ n)) ε (E.encode g)) p x)
    (ctrl-word g x))
