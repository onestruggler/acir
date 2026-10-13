------------------------------------------------------------------------
-- Presentations of groups
--
-- A canonical circuit normalizer at every width at least four.
-- Algorithm 1 of the two-level development supplies a canonical source
-- word from the matrix; the proved Clément decoder turns it into an
-- actual circuit.  Equal matrices produce literally equal output words.
-- No additional circuit equations are introduced.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+HH.GeneralN.Normalization (n : ℕ) where

open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.GeneralN.Generation as Generation
import Examples.Groups.CCX+HH.GeneralN.Presentation as Presentation
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Presentation as Source

width = 4 + n
N = 2 ^ width
private
  module P = Presentation n
  module G = Generation n

source-normal : H.Circuit width → Word (T.Gen N)
source-normal w = Source.word-of (S.⟦ E.encode w ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode w))

source-correct : ∀ w → S.⟦ source-normal w ⟧ᵐ ≡ C.interpret w
source-correct w = Eq.trans
  (Source.word-of-correct (S.⟦ E.encode w ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode w)))
  (C.encoding-correct w)

private
  -- The orthogonality proof is irrelevant to Algorithm 1's output.
  source-cong : ∀ {A B : S.OMat N} → Data.Product.Base.proj₁ A ≡ Data.Product.Base.proj₁ B →
    Source.word-of A ≡ Source.word-of B
  source-cong {A , a} {.A , b} Eq.refl = Eq.refl

source-normal-cong : ∀ {u v} → C.interpret u ≡ C.interpret v → source-normal u ≡ source-normal v
source-normal-cong {u} {v} eq = source-cong
  {A = S.⟦ E.encode u ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode u)}
  {B = S.⟦ E.encode v ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode v)}
  (Eq.trans (C.encoding-correct u) (Eq.trans eq (Eq.sym (C.encoding-correct v))))

nf : H.Circuit width → H.Circuit width
nf w = G.synthesize (source-normal w)

correct : ∀ w → C.interpret (nf w) ≡ C.interpret w
correct w = Eq.trans
  (G.correct (source-normal w) (G.necessary (source-normal w) w (Eq.sym (source-correct w))))
  (source-correct w)

normalize : ∀ w → w P.≈ nf w
normalize w = P.complete {u = w} {v = nf w} (Eq.sym (correct w))

semantic-cong : ∀ {u v} → C.interpret u ≡ C.interpret v → nf u ≡ nf v
semantic-cong eq = Eq.cong G.synthesize (source-normal-cong eq)

cong : ∀ {u v} → u P.≈ v → nf u ≡ nf v
cong eq = semantic-cong (P.sound eq)

complete : ∀ {u v} → nf u ≡ nf v → u P.≈ v
complete {u} {v} eq = P.complete {u = u} {v = v}
  (Eq.trans (Eq.sym (correct u))
    (Eq.trans (Eq.cong C.interpret eq) (correct v)))

idempotent : ∀ w → nf (nf w) ≡ nf w
idempotent w = semantic-cong (correct w)
