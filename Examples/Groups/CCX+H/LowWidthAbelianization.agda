------------------------------------------------------------------------
-- Presentations of groups
--
-- The physical H circuit groups on one, two and three wires all have
-- abelianization C2 x C2.  The verified full-source decoders transport
-- the scaled source's two characters and its four representatives.
-- At width zero the abelianization is trivial.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.LowWidthAbelianization where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Nat.Base using (ℕ ; suc ; _*_)
open import Data.Product.Base using (_,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)
import Presentation.Base as PB
import Presentation.GroupLike as GL
open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.Abelianization as Abel
import Examples.Groups.CCX+H.Encoding as Encoding
import Examples.Groups.CCX+H.Zero as Q0
import Examples.Groups.CCX+H.OneQubit as Q1
import Examples.Groups.CCX+H.TwoQubit as Q2
import Examples.Groups.CCX+H.TwoQubit.Decoding as D2
import Examples.Groups.CCX+H.ThreeQubit.Presentation as Q3
import Examples.Groups.CCX+H.ThreeQubit.Decoding as D3
import Examples.Groups.CCX+H.ThreeQubit.DecodingSoundness as Check3
import Examples.Groups.CCX+H.GeneralN.ScaledAbelianization as SourceAbel
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness as Complete

module Transfer (width k : ℕ)
  (e : H.Gen width → Word (T.Genᴸ (suc k * 2)))
  (d : T.Genᴸ (suc k * 2) → H.Circuit width)
  (section : ∀ g → S.Dim.⟦_⟧ᴸ (suc k) ((e ʷ) (d g)) ≡ S.Dim.⟦_⟧ᴸ (suc k) [ g ]ʷ)
  (encoded-sound : ∀ {u v} → width P.⊢ u ≈ v →
    S.Dim.⟦_⟧ᴸ (suc k) ((e ʷ) u) ≡ S.Dim.⟦_⟧ᴸ (suc k) ((e ʷ) v))
  (encoded-complete : ∀ {u v} →
    S.Dim.⟦_⟧ᴸ (suc k) ((e ʷ) u) ≡ S.Dim.⟦_⟧ᴸ (suc k) ((e ʷ) v) → width P.⊢ u ≈ v)
  where

  module A = Abel.At width
  module B = SourceAbel (k * 2)
  private module M = S.Dim (suc k)
  private module SC = Complete k

  open A public using (_≈_ ; Derived)
  open B public using (Character ; C₂×C₂ ; neutral ; _⊕_)

  encode = e ʷ
  decode = d ʷ

  character : H.Circuit width → Character
  character w = B.character (encode w)

  private
    decode-correct : ∀ w → M.⟦ encode (decode w) ⟧ᴸ ≡ M.⟦ w ⟧ᴸ
    decode-correct [ g ]ʷ = section g
    decode-correct ε = Eq.refl
    decode-correct (u • v) = Eq.trans
      (M.⟦•⟧ᴸ (encode (decode u)) (encode (decode v)))
      (Eq.trans (Eq.cong₂ _·*·_ (decode-correct u) (decode-correct v))
        (Eq.sym (M.⟦•⟧ᴸ u v)))

    recovery : ∀ w → width P.⊢ decode (encode w) ≈ w
    recovery w = encoded-complete {u = decode (encode w)} {v = w} (decode-correct (encode w))

    encode-raw : ∀ {u v} → P.Relations width u v → encode u B.≈ encode v
    encode-raw {u} {v} ax = B.source-cong
      (SC.completeness {u = encode u} {v = encode v} (encoded-sound (PB.axiom ax)))

    decode-raw : ∀ {u v} → u T.===ᴸ v → decode u A.≈ decode v
    decode-raw {u} {v} ax = A.source-cong
      (encoded-complete {u = decode u} {v = decode v}
        (Eq.trans (decode-correct u)
          (Eq.trans (S.soundness (suc k) (PB.axiom ax)) (Eq.sym (decode-correct v)))))

    module Forward = A.Universal B.Relations e encode-raw
      (λ u v → B.axiom (B.commute u v))
    module Backward = B.Universal (Abel.Relations width) d decode-raw
      (λ u v → A.axiom (Abel.commute u v))

  sound : ∀ {u v} → u ≈ v → character u ≡ character v
  sound eq = B.sound (Forward.factor eq)

  complete : ∀ {u v} → character u ≡ character v → u ≈ v
  complete {u} {v} eq = A.trans (A.sym (A.source-cong (recovery u)))
    (A.trans (Backward.factor (B.complete {u = encode u} {v = encode v} eq))
      (A.source-cong (recovery v)))

  rep : Character → H.Circuit width
  rep c = decode (B.rep c)

  representatives : ∀ c → character (rep c) ≡ c
  representatives c = Eq.trans
    (B.sound (B.source-cong (SC.completeness
      {u = encode (decode (B.rep c))} {v = B.rep c} (decode-correct (B.rep c)))))
    (B.representatives c)

  normalize : ∀ w → w ≈ rep (character w)
  normalize w = complete {u = w} {v = rep (character w)} (Eq.sym (representatives (character w)))

  kernel : ∀ {w} → character w ≡ neutral → Derived w
  kernel {w} = complete {u = w} {v = ε}

  kernel-only : ∀ {w} → Derived w → character w ≡ neutral
  kernel-only = sound

  private module G = GL.Group-Lemmas (Abel.Relations width) A.grouplike

  abelian-group : Group 0ℓ 0ℓ
  abelian-group = G.•-ε-group

  private
    module Mono = MonoidMorphisms (Group.rawMonoid abelian-group) (Group.rawMonoid C₂×C₂)
    module Maps = GroupMorphisms (Group.rawGroup abelian-group) (Group.rawGroup C₂×C₂)

    monoid-homomorphism : Mono.IsMonoidHomomorphism character
    monoid-homomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = sound }
        ; homo = λ u v → B.character-product (encode u) (encode v)
        }
      ; ε-homo = Eq.refl
      }

  isomorphism : Maps.IsGroupIsomorphism character
  isomorphism = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
          abelian-group C₂×C₂ monoid-homomorphism
      ; injective = complete
      }
    ; surjective = λ c → rep c , λ eq → Eq.trans (sound eq) (representatives c)
    }

module Zero where
  trivial : ∀ (w : H.Circuit 0) → Abel.At._≈_ 0 w ε
  trivial w = Abel.At.source-cong 0 (Q0.complete w ε)

private
  one-sound : ∀ {u v} → 1 P.⊢ u ≈ v →
    S.Dim.⟦_⟧ᴸ 1 (Encoding.encode u) ≡ S.Dim.⟦_⟧ᴸ 1 (Encoding.encode v)
  one-sound {u} {v} eq = Eq.trans (Q1.bridge u)
    (Eq.trans (Q1.sound eq) (Eq.sym (Q1.bridge v)))

  one-complete : ∀ {u v} →
    S.Dim.⟦_⟧ᴸ 1 (Encoding.encode u) ≡ S.Dim.⟦_⟧ᴸ 1 (Encoding.encode v) → 1 P.⊢ u ≈ v
  one-complete {u} {v} eq = Q1.Rules.encode-injective
    (Complete.completeness 0 {u = Encoding.encode u} {v = Encoding.encode v} eq)

module One = Transfer 1 0 Encoding.e Q1.d Q1.d-correct one-sound one-complete
module Two = Transfer 2 1 Encoding.e D2.d Q2.d-correct Q2.encoded-sound Q2.encoded-complete
module Three = Transfer 3 3 Encoding.e D3.d Check3.d-correct Q3.encoded-sound Q3.encoded-complete
