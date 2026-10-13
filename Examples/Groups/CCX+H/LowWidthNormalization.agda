------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical physical circuit normalizers on zero, one, two and three
-- wires.  The positive cases decode the canonical scaled source word.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.LowWidthNormalization where

open import Data.Nat.Base using (ℕ ; suc ; _*_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.Encoding as Encoding
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as C
import Examples.Groups.CCX+H.GeneralN.SmallPhysicalSemantics as Small
import Examples.Groups.CCX+H.GeneralN.SourceNormalization as Source
import Examples.Groups.CCX+H.OneQubit as Q1
import Examples.Groups.CCX+H.TwoQubit as Q2
import Examples.Groups.CCX+H.TwoQubit.Decoding as D2
import Examples.Groups.CCX+H.TwoQubit.Semantics as S2
import Examples.Groups.CCX+H.ThreeQubit.Decoding as D3
import Examples.Groups.CCX+H.ThreeQubit.DecodingSoundness as Check3
import Examples.Groups.CCX+H.ThreeQubit.Semantics as S3
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as M

private
  module Transfer (width k : ℕ)
    (e : H.Gen width → Word (T.Genᴸ (suc k * 2)))
    (d : T.Genᴸ (suc k * 2) → H.Circuit width)
    (section : ∀ g → M.Dim.⟦_⟧ᴸ (suc k) ((e ʷ) (d g)) ≡ M.Dim.⟦_⟧ᴸ (suc k) [ g ]ʷ)
    where

    private
      module S = M.Dim (suc k)
      module N = Source k

    decode = d ʷ
    encode = e ʷ

    decode-correct : ∀ w → S.⟦ encode (decode w) ⟧ᴸ ≡ S.⟦ w ⟧ᴸ
    decode-correct [ g ]ʷ = section g
    decode-correct ε = Eq.refl
    decode-correct (u • v) = Eq.trans
      (S.⟦•⟧ᴸ (encode (decode u)) (encode (decode v)))
      (Eq.trans (Eq.cong₂ _·*·_ (decode-correct u) (decode-correct v))
        (Eq.sym (S.⟦•⟧ᴸ u v)))

    nf : H.Circuit width → H.Circuit width
    nf w = decode (N.nf (encode w))

    correct : ∀ w → S.⟦ encode (nf w) ⟧ᴸ ≡ S.⟦ encode w ⟧ᴸ
    correct w = Eq.trans (decode-correct (N.nf (encode w))) (N.correct (encode w))

    semantic-cong : ∀ {u v} → S.⟦ encode u ⟧ᴸ ≡ S.⟦ encode v ⟧ᴸ → nf u ≡ nf v
    semantic-cong {u} {v} eq = Eq.cong decode
      (N.semantic-cong {u = encode u} {v = encode v} eq)

module Zero where
  nf : H.Circuit 0 → H.Circuit 0
  nf w = ε

  correct : ∀ w → C.interpret (nf w) ≡ C.interpret w
  correct w = Eq.sym (Small.zero-identity w)

  semantic-cong : ∀ {u v : H.Circuit 0} → C.interpret u ≡ C.interpret v → nf u ≡ nf v
  semantic-cong eq = Eq.refl

module One where
  private module F = Transfer 1 0 Encoding.e Q1.d Q1.d-correct
  open F public using (nf)

  correct : ∀ w → C.interpret (nf w) ≡ C.interpret w
  correct w = Eq.trans (Small.one (nf w))
    (Eq.trans (Eq.sym (Q1.bridge (nf w)))
      (Eq.trans (F.correct w) (Eq.trans (Q1.bridge w) (Eq.sym (Small.one w)))))

  semantic-cong : ∀ {u v : H.Circuit 1} → C.interpret u ≡ C.interpret v → nf u ≡ nf v
  semantic-cong {u} {v} eq = F.semantic-cong {u} {v}
    (Eq.trans (Q1.bridge u) (Eq.trans (Eq.sym (Small.one u))
      (Eq.trans eq (Eq.trans (Small.one v) (Eq.sym (Q1.bridge v))))))

module Two where
  private module F = Transfer 2 1 Encoding.e D2.d Q2.d-correct
  open F public using (nf)

  correct : ∀ w → C.interpret (nf w) ≡ C.interpret w
  correct w = Eq.trans (Small.two (nf w))
    (Eq.trans (Eq.sym (S2.bridge (nf w)))
      (Eq.trans (F.correct w) (Eq.trans (S2.bridge w) (Eq.sym (Small.two w)))))

  semantic-cong : ∀ {u v : H.Circuit 2} → C.interpret u ≡ C.interpret v → nf u ≡ nf v
  semantic-cong {u} {v} eq = F.semantic-cong {u} {v}
    (Eq.trans (S2.bridge u) (Eq.trans (Eq.sym (Small.two u))
      (Eq.trans eq (Eq.trans (Small.two v) (Eq.sym (S2.bridge v))))))

module Three where
  private module F = Transfer 3 3 Encoding.e D3.d Check3.d-correct
  open F public using (nf)

  correct : ∀ w → C.interpret (nf w) ≡ C.interpret w
  correct w = Eq.trans (Small.three (nf w))
    (Eq.trans (Eq.sym (S3.bridge (nf w)))
      (Eq.trans (F.correct w) (Eq.trans (S3.bridge w) (Eq.sym (Small.three w)))))

  semantic-cong : ∀ {u v : H.Circuit 3} → C.interpret u ≡ C.interpret v → nf u ≡ nf v
  semantic-cong {u} {v} eq = F.semantic-cong {u} {v}
    (Eq.trans (S3.bridge u) (Eq.trans (Eq.sym (Small.three u))
      (Eq.trans eq (Eq.trans (Small.three v) (Eq.sym (S3.bridge v))))))
