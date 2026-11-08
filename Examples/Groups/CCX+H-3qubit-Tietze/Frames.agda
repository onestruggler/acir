------------------------------------------------------------------------
-- Concrete permutation frames for the one- and four-level matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Frames where

open import Data.Fin.Base using (Fin ; zero ; suc)
import Relation.Binary.PropositionalEquality as Eq
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Examples.Groups.Symmetric.Syntactics as S
import Examples.Groups.Symmetric.SubPresentation.Semantics as SS
open import Examples.Groups.CCX+HH-3qubit.Syntactics hiding (Gen)
open import Examples.Groups.CCX+HH-3qubit.Permutation using (decode ; permutation-complete)
open import Presentation.Base _===_ hiding (_===_ ; _≈_)

PWord : Set
PWord = Word (S.Gen 8)

s0 s1 s2 s3 s4 s5 s6 : PWord
s0 = [ S.gate₂ S.σ-gate ]ʷ
s1 = [ (S.gate₂ S.σ-gate) S.↥ ]ʷ
s2 = [ ((S.gate₂ S.σ-gate) S.↥) S.↥ ]ʷ
s3 = [ (((S.gate₂ S.σ-gate) S.↥) S.↥) S.↥ ]ʷ
s4 = [ ((((S.gate₂ S.σ-gate) S.↥) S.↥) S.↥) S.↥ ]ʷ
s5 = [ (((((S.gate₂ S.σ-gate) S.↥) S.↥) S.↥) S.↥) S.↥ ]ʷ
s6 = [ ((((((S.gate₂ S.σ-gate) S.↥) S.↥) S.↥) S.↥) S.↥) S.↥ ]ʷ

p : PWord → Word Examples.Groups.CCX+HH-3qubit.Syntactics.Gen
p = (decode 0) ʷ

checked : (u v : PWord) → (∀ i → SS.⟦ u ⟧ i Eq.≡ SS.⟦ v ⟧ i) → p u ≈ p v
checked = permutation-complete

commute-product : ∀ {q a b} → a • q ≈ q • a → b • q ≈ q • b →
                  (a • b) • q ≈ q • (a • b)
commute-product ea eb = trans assoc
  (trans (cong refl eb) (trans (sym assoc) (trans (cong ea refl) assoc)))

forget-frame : ∀ {a b c i} → a • b ≈ c • a → a • i ≈ ε →
               a • b • i ≈ c
forget-frame e inverse = trans (sym assoc)
  (trans (cong e refl)
    (trans assoc (trans (cong refl inverse) right-unit)))

move-product : ∀ {q a a′ b b′} → q • a ≈ a′ • q → q • b ≈ b′ • q →
               q • (a • b) ≈ (a′ • b′) • q
move-product ea eb = trans (sym assoc)
  (trans (cong ea refl) (trans assoc (trans (cong refl eb) (sym assoc))))

move-compose : ∀ {a b x y z} → a • y ≈ z • a → b • x ≈ y • b →
               (a • b) • x ≈ z • (a • b)
move-compose ea eb = trans assoc
  (trans (cong refl eb) (trans (sym assoc) (trans (cong ea refl) assoc)))
