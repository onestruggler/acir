------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical H-circuit normal forms on at least four wires: normalize
-- the dyadic component and append its unique Hadamard parity bit.
-- Equal physical matrices have literally equal output circuit words.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.Normalization (n : ℕ) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)
import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.Orthogonal as O
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as C
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity
import Examples.Groups.CCX+H.GeneralN.HadamardDecomposition as Decomposition
import Examples.Groups.CCX+HH.Embedding as Embed
import Examples.Groups.CCX+HH.GeneralN.Normalization as DyadicNormal

width = 4 + n

private
  module D = Decomposition n
  module DN = DyadicNormal n
  module A = PB (P.Relations width)
  module G = Group-Lemmas (P.Relations width) (O.grouplike width)
  open D.Decomposition using (body ; bit)

nf : H.Circuit width → H.Circuit width
nf w = Embed.embed (DN.nf (body (D.decompose w))) • D.tail (bit (D.decompose w))

normalize : ∀ w → width P.⊢ w ≈ nf w
normalize w = A.trans (D.Decomposition.correct (D.decompose w))
  (A.cong (Embed.preserves (DN.normalize (body (D.decompose w)))) A.refl)

correct : ∀ w → C.interpret (nf w) ≡ C.interpret w
correct w = Eq.sym (P.sound width (normalize w))

private
  same : ∀ {u v} → width P.⊢ u ≈ v →
    (du : D.Decomposition u) (dv : D.Decomposition v) →
    Embed.embed (DN.nf (body du)) • D.tail (bit du) ≡
    Embed.embed (DN.nf (body dv)) • D.tail (bit dv)
  same {u} {v} eq du dv = Eq.cong₂ (λ a b → Embed.embed a • D.tail b) body-equal bit-equal
    where
    forms : width P.⊢ Embed.embed (body du) • D.tail (bit du) ≈
      Embed.embed (body dv) • D.tail (bit dv)
    forms = A.trans (A.sym (D.Decomposition.correct du))
      (A.trans eq (D.Decomposition.correct dv))

    bit-equal : bit du ≡ bit dv
    bit-equal = Parity.factor-bit-unique (body du) (body dv) (bit du) (bit dv)
      (P.sound width forms)

    same-tail : width P.⊢ Embed.embed (body du) • D.tail (bit du) ≈
      Embed.embed (body dv) • D.tail (bit du)
    same-tail = A.trans forms (A.refl'
      (Eq.cong (λ b → Embed.embed (body dv) • D.tail b) (Eq.sym bit-equal)))

    body-equal : DN.nf (body du) ≡ DN.nf (body dv)
    body-equal = DN.cong {u = body du} {v = body dv}
      (Embed.reflects {u = body du} {v = body dv}
        (G.•-cancelʳ {g = Embed.embed (body du)} {g' = Embed.embed (body dv)}
          {h = D.tail (bit du)} same-tail))

cong : ∀ {u v} → width P.⊢ u ≈ v → nf u ≡ nf v
cong {u} {v} eq = same eq (D.decompose u) (D.decompose v)

semantic-cong : ∀ {u v} → C.interpret u ≡ C.interpret v → nf u ≡ nf v
semantic-cong {u} {v} eq = cong (P.complete width {u = u} {v = v} eq)

complete : ∀ {u v} → nf u ≡ nf v → width P.⊢ u ≈ v
complete {u} {v} eq = P.complete width {u = u} {v = v}
  (Eq.trans (Eq.sym (correct u))
    (Eq.trans (Eq.cong C.interpret eq) (correct v)))

idempotent : ∀ w → nf (nf w) ≡ nf w
idempotent w = semantic-cong {u = nf w} {v = w} (correct w)
