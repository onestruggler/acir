------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical two-wire circuits, obtained by Algorithm 1 followed by the
-- already verified three-coset Clément decoder.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.TwoQubit.Normalization where

open import Data.Product.Base using (_,_ ; proj₁)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; inspect)
  renaming ([_] to [_]ᵢ)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ᵗ)
import Presentation.Base as PB
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH.Encoding as E
import Examples.Groups.CCX+HH.LowWidth as Low
import Examples.Groups.CCX+HH.TwoQubit.Table as Table
import Examples.Groups.CCX+HH.TwoQubit.Semantics as Physical
import Examples.Groups.CCX+HH.TwoQubit.Soundness as Factor
import Examples.Groups.CCX+HH.Subgroup.State as State
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Presentation as Source
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as Main
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red

private
  module A = PB (T._===_ {4})
  module Fold = State Table.step
  open Table using (c0 ; state ; decode ; h)

  state-product : ∀ c u v → state c (u • v) ≡ state (state c u) v
  state-product c u v with (h ᵗ) c u | inspect ((h ᵗ) c) u
  ... | (u′ , c′) | [ Eq.refl ]ᵢ with (h ᵗ) c′ v
  ... | (v′ , c″) = Eq.refl

  state-fold : ∀ c w → state c w ≡ Fold.state c w
  state-fold c [ g ]ʷ = Eq.refl
  state-fold c ε = Eq.refl
  state-fold c (u • v) = Eq.trans (state-product c u v)
    (Eq.trans (state-fold (state c u) v)
      (Eq.cong (λ d → Fold.state d v) (state-fold c u)))

  fold-relations : ∀ c {u v} → u T.=== v → Fold.state c u ≡ Fold.state c v
  fold-relations c {u} {v} ax = Eq.trans (Eq.sym (state-fold c u))
    (Eq.trans (Table.state-relations c ax) (state-fold c v))

  module Model = Fold.Congruence (T._===_ {4}) fold-relations

  state-cong : ∀ c {u v} → u A.≈ v → state c u ≡ state c v
  state-cong c {u} {v} eq = Eq.trans (state-fold c u)
    (Eq.trans (Model.state-cong c eq) (Eq.sym (state-fold c v)))

  encoded-closed : ∀ w → state c0 (E.encode w) ≡ c0
  encoded-closed [ g ]ʷ = Eq.sym (Table.state-roundtrip g)
  encoded-closed ε = Eq.refl
  encoded-closed (u • v) = Eq.trans (state-product c0 (E.encode u) (E.encode v))
    (Eq.trans (Eq.cong (λ d → state d (E.encode v)) (encoded-closed u)) (encoded-closed v))

  physical-encoding : ∀ w → S.⟦ E.encode w ⟧ᵐ ≡ C.interpret w
  physical-encoding w = Eq.trans (Physical.encoding-correct w) (Eq.sym (Low.Two.semantics w))

  source-cong : ∀ {A B : S.OMat 4} → proj₁ A ≡ proj₁ B → Source.word-of A ≡ Source.word-of B
  source-cong {A , a} {.A , b} Eq.refl = Eq.refl

source-normal : H.Circuit 2 → Word (T.Gen 4)
source-normal w = Source.word-of (S.⟦ E.encode w ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode w))

private
  source-correct : ∀ w → S.⟦ source-normal w ⟧ᵐ ≡ S.⟦ E.encode w ⟧ᵐ
  source-correct w = Source.word-of-correct (S.⟦ E.encode w ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode w))

  source-closed : ∀ w → state c0 (source-normal w) ≡ c0
  source-closed w = Eq.trans
    (state-cong c0 {u = source-normal w} {v = E.encode w}
      (Main.completeness {u = source-normal w} {v = E.encode w} (source-correct w)))
    (encoded-closed w)

  decode-closed : ∀ w → state c0 w ≡ c0 → w A.≈ E.encode (decode c0 w)
  decode-closed w closed = A.trans (A.sym A.left-unit)
    (A.trans (Factor.Proven.factor-word c0 w)
      (A.trans (A.cong A.refl (A.refl' (Eq.cong Factor.rep closed))) A.right-unit))

nf : H.Circuit 2 → H.Circuit 2
nf w = decode c0 (source-normal w)

correct : ∀ w → C.interpret (nf w) ≡ C.interpret w
correct w = Eq.trans (Eq.sym (physical-encoding (nf w)))
  (Eq.trans (Eq.sym (Red.sound-act (decode-closed (source-normal w) (source-closed w)) S.𝕀))
    (Eq.trans (source-correct w) (physical-encoding w)))

semantic-cong : ∀ {u v} → C.interpret u ≡ C.interpret v → nf u ≡ nf v
semantic-cong {u} {v} eq = Eq.cong (decode c0)
  (source-cong
    {A = S.⟦ E.encode u ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode u)}
    {B = S.⟦ E.encode v ⟧ᵐ , S.Unitary-⟦⟧ᵐ (E.encode v)}
    (Eq.trans (physical-encoding u) (Eq.trans eq (Eq.sym (physical-encoding v)))))
