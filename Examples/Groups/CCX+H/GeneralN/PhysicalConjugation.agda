------------------------------------------------------------------------
-- Presentations of groups
--
-- Every classical routing circuit induces a permutation of ordinary
-- matrix indices.  Its physical conjugation transports a sign pair to
-- the images of its two levels, with every other matrix entry fixed.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _^_)
import Examples.Groups.CCX+HH.GeneralN.Classical as C

module Examples.Groups.CCX+H.GeneralN.PhysicalConjugation
  {n : ℕ} (w : C.Circuit n) where

open import Data.Fin.Base using (Fin ; _<_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; _•_)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (M ; M-gen ; K ; K-gen)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties
  using (inverse ; inverse-correct ; inverse-correctʳ)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis
  using (bits ; idx ; bits-idx ; idx-bits ; idx-cong)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (physical-column)
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis-!)
import Examples.Groups.CCX+H.GeneralN.PermutationConjugation as Perm

index : C.Circuit n → Fin (2 ^ n) → Fin (2 ^ n)
index v i = idx n (C.act v (bits n i))

forward backward : Fin (2 ^ n) → Fin (2 ^ n)
forward = index w
backward = index (inverse w)

private
  compose-index : ∀ u v i → index u (index v i) ≡ index (u • v) i
  compose-index u v i = idx-cong n
    (C.act-cong u (bits-idx n (C.act v (bits n i))))

forward-backward : ∀ i → forward (backward i) ≡ i
forward-backward i = trans (compose-index w (inverse w) i)
  (trans (idx-cong n (inverse-correctʳ w (bits n i))) (idx-bits n i))

backward-forward : ∀ i → backward (forward i) ≡ i
backward-forward i = trans (compose-index (inverse w) w i)
  (trans (idx-cong n (inverse-correct w (bits n i))) (idx-bits n i))

matrix inverse-matrix : Matrix (2 ^ n) (2 ^ n) D
matrix = Q.interpret (C.physical w)
inverse-matrix = Q.interpret (C.physical (inverse w))

private
  entries : ∀ v r c → A.ent (Q.interpret (C.physical v)) r c ≡ A.δ r (index v c)
  entries v r c = trans (cong (A._! r) (physical-column v c)) (basis-! (index v c) r)

module Transport = Perm.Permutation forward backward forward-backward backward-forward
  matrix inverse-matrix (entries w) (entries (inverse w))

route : H.Circuit n → H.Circuit n
route v = C.physical w • v • C.physical (inverse w)

interpret-route : ∀ v → Q.interpret (route v) ≡ matrix ·*· Q.interpret v ·*· inverse-matrix
interpret-route v = sym (A.·*·-assoc matrix (Q.interpret v) inverse-matrix)

route-matrix : ∀ v (A B : Matrix (2 ^ n) (2 ^ n) D) →
  Q.interpret v ≡ A →
  (∀ r c → A.ent B (forward r) (forward c) ≡ A.ent A r c) →
  Q.interpret (route v) ≡ B
route-matrix v old new base image = trans (interpret-route v)
  (trans (cong (λ M → matrix ·*· M ·*· inverse-matrix) base)
    (Transport.conjugate old new image))

private
  pair-reading : ∀ (a b : Fin (2 ^ n)) → A.⟦ M a • M b ⟧ᵐ ≡ A.gmat (M-gen a) ·*· A.gmat (M-gen b)
  pair-reading a b = trans (A.⟦•⟧ᵐ (M a) (M b))
    (cong₂ _·*·_ (A.⟦g⟧ᵐ≡ (M-gen a)) (A.⟦g⟧ᵐ≡ (M-gen b)))

sign-pair : ∀ v a b → Q.interpret v ≡ A.⟦ M a • M b ⟧ᵐ →
  Q.interpret (route v) ≡ A.⟦ M (forward a) • M (forward b) ⟧ᵐ
sign-pair v a b base = trans (interpret-route v)
  (trans (cong (λ M → matrix ·*· M ·*· inverse-matrix)
      (trans base (pair-reading a b)))
    (trans (Transport.product (A.gmat (M-gen a)) (A.gmat (M-gen b)))
      (trans (cong₂ _·*·_ (Transport.sign a) (Transport.sign b))
        (sym (pair-reading (forward a) (forward b))))))

module KPair (a b c d e f g h : Fin (2 ^ n))
  .(ab : a < b) .(bc : b < c) .(cd : c < d)
  .(ef : e < f) .(fg : f < g) .(gh : g < h)
  .(fab : forward a < forward b) .(fbc : forward b < forward c) .(fcd : forward c < forward d)
  .(fef : forward e < forward f) .(ffg : forward f < forward g) .(fgh : forward g < forward h) where

  private
    module First = Transport.Block a b c d ab bc cd fab fbc fcd
    module Second = Transport.Block e f g h ef fg gh fef ffg fgh
    old₁ = K-gen a b c d ab bc cd
    old₂ = K-gen e f g h ef fg gh
    new₁ = K-gen (forward a) (forward b) (forward c) (forward d) fab fbc fcd
    new₂ = K-gen (forward e) (forward f) (forward g) (forward h) fef ffg fgh

  auxiliary = K a b c d ab bc cd • K e f g h ef fg gh
  target = K (forward a) (forward b) (forward c) (forward d) fab fbc fcd •
    K (forward e) (forward f) (forward g) (forward h) fef ffg fgh

  correct : ∀ v → Q.interpret v ≡ A.⟦ auxiliary ⟧ᵐ →
    Q.interpret (route v) ≡ A.⟦ target ⟧ᵐ
  correct v base = trans (interpret-route v)
    (trans (cong (λ M → matrix ·*· M ·*· inverse-matrix)
        (trans base (trans (A.⟦•⟧ᵐ [ old₁ ]ʷ [ old₂ ]ʷ)
          (cong₂ _·*·_ (A.⟦g⟧ᵐ≡ old₁) (A.⟦g⟧ᵐ≡ old₂)))))
      (trans (Transport.product (A.gmat old₁) (A.gmat old₂))
        (trans (cong₂ _·*·_ First.block Second.block)
          (sym (trans (A.⟦•⟧ᵐ [ new₁ ]ʷ [ new₂ ]ʷ)
            (cong₂ _·*·_ (A.⟦g⟧ᵐ≡ new₁) (A.⟦g⟧ᵐ≡ new₂)))))))
