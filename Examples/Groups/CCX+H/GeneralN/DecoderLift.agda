------------------------------------------------------------------------
-- Presentations of groups
--
-- Lift a physical dyadic decoder through HH = H on each of two wires.
-- The four extra scaled edges are realized by H or a sign pair then H.
-- Dimension transport changes only the spelling of the matrix size.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.DecoderLift (n : ℕ) where

open import Data.Nat.Base using (_*_ ; _<_ ; s≤s ; z≤n) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Fin.Base using (Fin ; fromℕ< ; toℕ)
import Data.Fin.Properties as FP
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)
import Presentation.Base as PB
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.CircuitTranslation as Transfer
import Examples.Groups.CCX+H.GeneralN.Semantics as Sem
import Examples.Groups.CCX+H.GeneralN.HadamardEmbedding as Embed
import Examples.Groups.CCX+H.GeneralN.HadamardSchreierAt as HEdges
import Examples.Groups.CCX+H.GeneralN.SignPair as Sign
import Examples.Groups.CCX+HH.CircuitTranslation as DyadicTransfer
import Examples.Groups.CCX+HH.Subgroup.PresentationAt as Dyadic
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
open import Examples.Groups.CCX+H.GeneralN.Action using (c00 ; c10 ; c11 ; c01)

module C = Sem.At (3 + n)
module Translation = Transfer n
module D = DyadicTransfer n
module Auxiliary = Translation.Auxiliary

private
  k = 2 ^ℕ (3 + n)
  N = k * 2
  dimension : 2 ^ℕ (4 + n) ≡ N
  dimension = NP.*-comm 2 k
  p₀ : 0 < 2 ^ℕ (4 + n)
  p₀ = NP.m^n>0 2 (4 + n)
  p₁ : 1 < 2 ^ℕ (4 + n)
  p₁ = NP.^-monoʳ-≤ 2 {1} {4 + n} (s≤s z≤n)
  q₀ = Eq.subst (0 <_) dimension p₀
  q₁ = Eq.subst (1 <_) dimension p₁
  a b : Fin N
  a = fromℕ< q₀
  b = fromℕ< q₁
  ab : toℕ a < toℕ b
  ab = Eq.subst₂ _<_ (Eq.sym (FP.toℕ-fromℕ< q₀))
    (Eq.sym (FP.toℕ-fromℕ< q₁)) (s≤s z≤n)
  module M = S.Dim k
  module A = PB (T._===ᴸ_ {N})
  module DE = Dyadic N a b ab
  module HE = HEdges N a b ab (FP.toℕ-fromℕ< q₀) (FP.toℕ-fromℕ< q₁)

  cast-gen : ∀ {j l} → j ≡ l → U.Gen j → U.Gen l
  cast-gen Eq.refl g = g

  module Canonical (j : ℕ) (r₀ : 0 < j) (r₁ : 1 < j) where
    i₀ i₁ : Fin j
    i₀ = fromℕ< r₀
    i₁ = fromℕ< r₁
    ordered : toℕ i₀ < toℕ i₁
    ordered = Eq.subst₂ _<_ (Eq.sym (FP.toℕ-fromℕ< r₀))
      (Eq.sym (FP.toℕ-fromℕ< r₁)) (s≤s z≤n)
    module P = Dyadic j i₀ i₁ ordered
    open P public using (e)

  cast-edge : ∀ {j l} (p : j ≡ l) r₀ r₁ s₀ s₁ q g →
    Sem.cast-word p T.⌊ Canonical.e j r₀ r₁ (q , cast-gen (Eq.sym p) g) ⌋ʷ ≡
    T.⌊ Canonical.e l s₀ s₁ (q , g) ⌋ʷ
  cast-edge Eq.refl r₀ r₁ s₀ s₁ q g = Eq.refl

  lift-edge : ∀ q g → Auxiliary.e (q , T.⌊ g ⌋) ≡ T.⌊ DE.e (q , g) ⌋ʷ
  lift-edge c00 (U.M-gen a) = Eq.refl
  lift-edge c10 (U.M-gen a) = Eq.refl
  lift-edge c11 (U.M-gen a) = Eq.refl
  lift-edge c01 (U.M-gen a) = Eq.refl
  lift-edge c00 (U.X-gen a b ab) = Eq.refl
  lift-edge c10 (U.X-gen a b ab) = Eq.refl
  lift-edge c11 (U.X-gen a b ab) = Eq.refl
  lift-edge c01 (U.X-gen a b ab) = Eq.refl
  lift-edge c00 (U.K-gen a b c d ab bc cd) = Eq.refl
  lift-edge c10 (U.K-gen a b c d ab bc cd) = Eq.refl
  lift-edge c11 (U.K-gen a b c d ab bc cd) = Eq.refl
  lift-edge c01 (U.K-gen a b c d ab bc cd) = Eq.refl

  cast-H : ∀ {j l} (p : j ≡ l) → Sem.cast-word p (ε • T.H) ≡ ε • T.H
  cast-H Eq.refl = Eq.refl

  H-correct : C.interpret H.H ≡ M.⟦ T.H ⟧ᴸ
  H-correct = Eq.trans (Eq.sym (C.encoding-correct H.H))
    (Eq.trans (Eq.cong M.⟦_⟧ᴸ (cast-H dimension))
      (S.soundness k {w = ε • T.H} {v = T.H} A.left-unit))

  cast-pair : ∀ {j l} (p : j ≡ l) (r₀ : 0 < j) (r₁ : 1 < j)
    (s₀ : 0 < l) (s₁ : 1 < l) →
    Sem.cast-word p T.⌊ U.M (fromℕ< r₀) • U.M (fromℕ< r₁) ⌋ʷ ≡
    T.Mᴸ (fromℕ< s₀) • T.Mᴸ (fromℕ< s₁)
  cast-pair Eq.refl r₀ r₁ s₀ s₁ = Eq.refl

  pair : H.Circuit (4 + n)
  pair = Embed.embed (Sign.circuit n (fromℕ< p₀) (fromℕ< p₁))

  pair-correct : C.interpret pair ≡ M.⟦ HE.pair ⟧ᴸ
  pair-correct = Eq.trans (Embed.At.realises (3 + n)
    (Sign.circuit n (fromℕ< p₀) (fromℕ< p₁))
    (U.M (fromℕ< p₀) • U.M (fromℕ< p₁)) (Sign.correct n _ _))
    (Eq.cong M.⟦_⟧ᴸ (cast-pair dimension p₀ p₁ q₀ q₁))

  pair-H-correct : C.interpret (pair • H.H) ≡ M.⟦ HE.pair • T.H ⟧ᴸ
  pair-H-correct = Eq.trans (Eq.cong₂ _·*·_ pair-correct H-correct)
    (Eq.sym (M.⟦•⟧ᴸ HE.pair T.H))

module Lift (decoder : D.Decoder) where
  private module DD = D.Decoder decoder

  d : Auxiliary.Edge → H.Circuit (4 + n)
  d (q , T.⌊ g ⌋) = Embed.embed (DD.d (q , cast-gen (Eq.sym dimension) g))
  d (c00 , T.IH) = H.H
  d (c10 , T.IH) = pair • H.H
  d (c11 , T.IH) = pair • H.H
  d (c01 , T.IH) = pair • H.H

  correct : ∀ y → C.interpret (d y) ≡ M.⟦ Auxiliary.e y ⟧ᴸ
  correct (q , T.⌊ g ⌋) = Eq.trans
    (Embed.At.realises (3 + n) (DD.d (q , cast-gen (Eq.sym dimension) g))
      (D.Auxiliary.e (q , cast-gen (Eq.sym dimension) g))
      (DD.correct (q , cast-gen (Eq.sym dimension) g)))
    (Eq.cong M.⟦_⟧ᴸ (Eq.trans (cast-edge dimension p₀ p₁ q₀ q₁ q g)
      (Eq.sym (lift-edge q g))))
  correct (c00 , T.IH) = Eq.trans H-correct
    (S.soundness k (A.sym (A.trans A.assoc HE.edge00)))
  correct (c10 , T.IH) = Eq.trans pair-H-correct
    (S.soundness k (A.sym (A.trans A.assoc HE.edge10)))
  correct (c11 , T.IH) = Eq.trans pair-H-correct
    (S.soundness k (A.sym (A.trans A.assoc HE.edge11)))
  correct (c01 , T.IH) = Eq.trans pair-H-correct
    (S.soundness k (A.sym (A.trans A.assoc HE.edge01)))

  lifted : Translation.Decoder
  lifted = record { d = d ; correct = correct }
