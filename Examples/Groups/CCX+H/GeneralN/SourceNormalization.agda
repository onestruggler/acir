------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical words in the scaled auxiliary group: Algorithm 1 applied
-- to the dyadic factor, followed by the unique IH parity bit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; suc ; _*_)

module Examples.Groups.CCX+H.GeneralN.SourceNormalization (k : ℕ) where

open import Data.Bool.Base using (Bool)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; _•_)
import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as UD
import Examples.Groups.CCX+HH-TwoLevel.Semantics as US
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as UC
import Examples.Groups.CCX+HH-TwoLevel.Presentation as UP
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as M
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring as R
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Normal as Normal
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity

N = suc k * 2

private
  module A = PB (T._===ᴸ_ {N})
  module S = M.Dim (suc k)
  module D = Normal k

  gl : Grouplike (T._===ᴸ_ {N})
  gl T.⌊ g ⌋ = [ T.⌊ g ⌋ ]ʷ , T.⌊⌋-cong (UD.gen-gen g)
  gl T.IH = T.H , A.axiom T.r7a

  module G = Group-Lemmas (T._===ᴸ_ {N}) gl

  canonical : Word (U.Gen N) → Word (U.Gen N)
  canonical w = UP.word-of (US.⟦ w ⟧ᵐ , US.Unitary-⟦⟧ᵐ w)

  canonical-correct : ∀ w → US.⟦ canonical w ⟧ᵐ ≡ US.⟦ w ⟧ᵐ
  canonical-correct w = UP.word-of-correct (US.⟦ w ⟧ᵐ , US.Unitary-⟦⟧ᵐ w)

  word-of-cong : ∀ {A B : US.OMat N} → proj₁ A ≡ proj₁ B → UP.word-of A ≡ UP.word-of B
  word-of-cong {A , a} {.A , b} Eq.refl = Eq.refl

  canonical-cong : ∀ {u v} → US.⟦ u ⟧ᵐ ≡ US.⟦ v ⟧ᵐ → canonical u ≡ canonical v
  canonical-cong {u} {v} = word-of-cong
    {A = US.⟦ u ⟧ᵐ , US.Unitary-⟦⟧ᵐ u} {B = US.⟦ v ⟧ᵐ , US.Unitary-⟦⟧ᵐ v}

  dyadic : Word (T.Genᴸ N) → Word (U.Gen N)
  dyadic w = proj₁ (D.nf w)

  bit : Word (T.Genᴸ N) → Bool
  bit w = proj₁ (proj₂ (D.nf w))

  form : ∀ w → w A.≈ T.⌊ dyadic w ⌋ʷ • D.Hᵇ (bit w)
  form w = proj₂ (proj₂ (D.nf w))

nf : Word (T.Genᴸ N) → Word (T.Genᴸ N)
nf w = T.⌊ canonical (dyadic w) ⌋ʷ • D.Hᵇ (bit w)

normalize : ∀ w → w A.≈ nf w
normalize w = A.trans (form w)
  (A.cong (T.⌊⌋-cong (UC.completeness {u = dyadic w} {v = canonical (dyadic w)}
    (Eq.sym (canonical-correct (dyadic w))))) A.refl)

correct : ∀ w → S.⟦ nf w ⟧ᴸ ≡ S.⟦ w ⟧ᴸ
correct w = Eq.sym (M.soundness (suc k) (normalize w))

private
  same : ∀ {u v} → u A.≈ v → nf u ≡ nf v
  same {u} {v} eq = Eq.cong₂ (λ d b → T.⌊ d ⌋ʷ • D.Hᵇ b) canonical-equal bit-equal
    where
    forms : T.⌊ dyadic u ⌋ʷ • D.Hᵇ (bit u) A.≈ T.⌊ dyadic v ⌋ʷ • D.Hᵇ (bit v)
    forms = A.trans (A.sym (form u)) (A.trans eq (form v))

    bit-equal : bit u ≡ bit v
    bit-equal = Eq.trans (Eq.sym (Parity.normal-parity k (dyadic u) (bit u)))
      (Eq.trans (Parity.source-sound forms) (Parity.normal-parity k (dyadic v) (bit v)))

    same-tail : T.⌊ dyadic u ⌋ʷ • D.Hᵇ (bit u) A.≈ T.⌊ dyadic v ⌋ʷ • D.Hᵇ (bit u)
    same-tail = A.trans forms (A.refl'
      (Eq.cong (λ b → T.⌊ dyadic v ⌋ʷ • D.Hᵇ b) (Eq.sym bit-equal)))

    same-dyadic : T.⌊ dyadic u ⌋ʷ A.≈ T.⌊ dyadic v ⌋ʷ
    same-dyadic = G.•-cancelʳ {g = T.⌊ dyadic u ⌋ʷ} {g' = T.⌊ dyadic v ⌋ʷ}
      {h = D.Hᵇ (bit u)} same-tail

    same-matrix : US.⟦ dyadic u ⟧ᵐ ≡ US.⟦ dyadic v ⟧ᵐ
    same-matrix = M.Tr.mapM-injective R.e-injective
      (Eq.trans (Eq.sym (M.⟦⌊⌋⟧ (suc k) (dyadic u)))
        (Eq.trans (M.soundness (suc k) same-dyadic) (M.⟦⌊⌋⟧ (suc k) (dyadic v))))

    canonical-equal : canonical (dyadic u) ≡ canonical (dyadic v)
    canonical-equal = canonical-cong {u = dyadic u} {v = dyadic v} same-matrix

cong : ∀ {u v} → u A.≈ v → nf u ≡ nf v
cong = same

semantic-cong : ∀ {u v} → S.⟦ u ⟧ᴸ ≡ S.⟦ v ⟧ᴸ → nf u ≡ nf v
semantic-cong {u} {v} eq = same (Complete.completeness k {u = u} {v = v} eq)

idempotent : ∀ w → nf (nf w) ≡ nf w
idempotent w = semantic-cong {u = nf w} {v = w} (correct w)
