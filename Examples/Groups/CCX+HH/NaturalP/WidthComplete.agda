------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness at every width from completeness on a few wires.
--
-- On 4 + k + c wires (c at least 8) the rules with the schema are
-- complete, given that they are complete on at most eight wires and
-- on 4 + c wires (`complete`).  It is Clément's argument with the
-- natural decoder: every gate is the decoding of an auxiliary word
-- (`recover`: Merge.recover-win and GateDecoded.piece-decoded), the
-- decoder respects the auxiliary presentation (`D-cong`, from
-- Decoded.decoded), and the auxiliary presentation is complete
-- (Subgroup/PresentationAt.completeness).  So two circuits with the
-- same matrix decode words that are equal in the auxiliary
-- presentation, and are equal to those decodings.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_ ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Notations using (₄₊)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S

module Examples.Groups.CCX+HH.NaturalP.WidthComplete
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  (k c : ℕ) (big : 8 ≤ c)
  (complete-top : ∀ {u v : P.Circuit (₄₊ (c + 0))} → interpret u ≡ interpret v →
     (₄₊ (c + 0)) S.⊢ u ≈ v)
  where

open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (refl ; sym ; trans ; cong ; cong₂ ; subst)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB

import Examples.Groups.CCX+HH-TwoLevel.Semantics as TS
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.Semantics as Q
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (encoding-action)
open import Examples.Groups.CCX+HH.NaturalP.Schema using (Circuit ; Gen ; _⊢_≈_)
open import Examples.Groups.CCX+HH.NaturalP.SchemaSound using (sound)
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.NaturalP.Merge complete≤ using (recover-win ; pairs ; gate′ ; trW)
open import Examples.Groups.CCX+HH.NaturalP.AtomDecoder k c using (W)
open import Examples.Groups.CCX+HH.NaturalP.Decoded complete≤ k c big complete-top
  using (module Aux ; D ; D-act ; decoded)
open import Examples.Groups.CCX+HH.NaturalP.GateDecoded complete≤ k c big complete-top
  using (piece-word ; piece-decoded)

------------------------------------------------------------------------
-- Gates decoded

-- The auxiliary word of a gate: its pieces' words, colouring by
-- colouring.
E′ : Gen W → Word Aux.Edge
E′ x = ((λ p → piece-word x (proj₁ p) (proj₂ p)) ʷ) (pairs k c)

private
  ʷ-cong : ∀ {A : Set} {f g : A → Circuit W} → (∀ a → W ⊢ f a ≈ g a) → (w : Word A) →
    W ⊢ (f ʷ) w ≈ (g ʷ) w
  ʷ-cong e [ a ]ʷ  = e a
  ʷ-cong e ε       = PB.refl
  ʷ-cong e (u • v) = PB.cong (ʷ-cong e u) (ʷ-cong e v)

  D-ʷ : ∀ {A : Set} (f : A → Word Aux.Edge) (w : Word A) → D ((f ʷ) w) ≡ ((λ a → D (f a)) ʷ) w
  D-ʷ f [ a ]ʷ  = refl
  D-ʷ f ε       = refl
  D-ʷ f (u • v) = cong₂ _•_ (D-ʷ f u) (D-ʷ f v)

recover : ∀ x → W ⊢ [ x ]ʷ ≈ D (E′ x)
recover x =
  PB.trans (proj₂ (proj₂ (recover-win k c x)))
  (PB.trans (ʷ-cong (λ p → piece-decoded x (proj₁ p) (proj₂ p)) (pairs k c))
    (subst (λ z → W ⊢ z ≈ D (E′ x)) (D-ʷ (λ p → piece-word x (proj₁ p) (proj₂ p)) (pairs k c)) PB.refl))

-- Every circuit is the decoding of its auxiliary word.
recover-w : ∀ (u : Circuit W) → W ⊢ u ≈ D ((E′ ʷ) u)
recover-w [ x ]ʷ  = recover x
recover-w ε       = PB.refl
recover-w (u • v) = PB.cong (recover-w u) (recover-w v)

------------------------------------------------------------------------
-- The decoder respects the auxiliary presentation

D-cong : ∀ {u v} → u Aux.≈ v → W ⊢ D u ≈ D v
D-cong PB.refl        = PB.refl
D-cong (PB.sym p)     = PB.sym (D-cong p)
D-cong (PB.trans p q) = PB.trans (D-cong p) (D-cong q)
D-cong (PB.cong p q)  = PB.cong (D-cong p) (D-cong q)
D-cong PB.assoc       = PB.assoc
D-cong PB.left-unit   = PB.left-unit
D-cong PB.right-unit  = PB.right-unit
D-cong (PB.axiom a)   = decoded a

------------------------------------------------------------------------
-- Completeness

private
  enc-interp : ∀ w → TS.⟦ Aux.encode w ⟧ᵐ ≡ interpret (D w)
  enc-interp w =
    trans (TS.same-matrix (Aux.encode w) (E.encode (τ (D w)))
            (λ x → trans (sym (D-act w x)) (sym (encoding-action (τ (D w)) x))))
      (Q.encoding-correct (τ (D w)))

complete : ∀ {u v : Circuit W} → interpret u ≡ interpret v → W ⊢ u ≈ v
complete {u} {v} eq =
  PB.trans (recover-w u)
  (PB.trans (D-cong (Aux.completeness {u = (E′ ʷ) u} {v = (E′ ʷ) v}
      (trans (enc-interp ((E′ ʷ) u))
      (trans (sym (sound (recover-w u)))
      (trans eq
      (trans (sound (recover-w v)) (sym (enc-interp ((E′ ʷ) v)))))))))
    (PB.sym (recover-w v)))
