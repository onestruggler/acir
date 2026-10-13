------------------------------------------------------------------------
-- Exact 8 × 8 matrices over ℤ[1/√2], in matrix-product order.
-- A pair (d , M) denotes M / √2ᵈ. Stored matrices avoid expanding
-- a long matrix product into exponentially many intermediate indices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Interpretation where

open import Data.Nat.Base using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.GateMatrices
open import Examples.Groups.Real-Clifford+CH.Semantics.Scaled public
  using (Scaled ; _~_ ; Scaled-monoid ; scaleM ; ix-scaleM)
import Normalization.StarInterp as SI

len : Word Gen → ℕ
len [ g ]ʷ = degree g
len ε = 0
len (w • v) = len w +ℕ len v

abstract
  readM : Word Gen → Mat 3
  readM [ g ]ʷ = gateM g
  readM ε = idM
  readM (w • v) = mulM (readM w) (readM v)

  readM-gen : (g : Gen) → readM [ g ]ʷ ≡ gateM g
  readM-gen g = Eq.refl

  readM-ε : readM ε ≡ idM
  readM-ε = Eq.refl

  readM-• : (w v : Word Gen) →
            readM (w • v) ≡ mulM (readM w) (readM v)
  readM-• w v = Eq.refl

⟦_⟧ : Word Gen → Scaled 3
⟦ w ⟧ = len w , ix (readM w)

-- Cross multiplication is exact, including the global scalar.
scaledM : Word Gen → Word Gen → Mat 3
scaledM w v = scaleM (√2^ len v) (readM w)

by-matrix : ∀ {w v} → scaledM w v ≡ scaledM v w → ⟦ w ⟧ ~ ⟦ v ⟧
by-matrix {w} {v} e = ≐-trans
  (≐-sym (ix-scaleM (√2^ len v) (readM w)))
  (≐-trans (λ x y → Eq.cong (λ M → ix M x y) e)
    (ix-scaleM (√2^ len w) (readM v)))

-- The library's free-monoid interpretation and the stored reading agree.
module Ext = SI.Extend _===_ (Scaled-monoid 3)
  (λ g → degree g , ix (gateM g))

⟦⟧-Ext : (w : Word Gen) → ⟦ w ⟧ ~ Ext.⟦ w ⟧
⟦⟧-Ext [ g ]ʷ = S.~-reflexive {l = degree g} {l' = degree g}
  {M = ix (readM [ g ]ʷ)} {M' = ix (gateM g)} Eq.refl
  (λ x y → Eq.cong (λ M → ix M x y) (readM-gen g))
  where import Examples.Groups.Real-Clifford+CH.Semantics.Scaled as S
⟦⟧-Ext ε = S.~-reflexive {l = 0} {l' = 0}
  {M = ix (readM ε)} {M' = Idₒ {3}} Eq.refl
  (λ x y → Eq.trans (Eq.cong (λ M → ix M x y) readM-ε) (ix-id x y))
  where import Examples.Groups.Real-Clifford+CH.Semantics.Scaled as S
⟦⟧-Ext (w • v) = S.~-trans
  {s = ⟦ w • v ⟧} {t = ⟦ w ⟧ S.∙ ⟦ v ⟧}
  {u = Ext.⟦ w • v ⟧}
  (S.~-reflexive {l = len (w • v)} {l' = len (w • v)}
    {M = ix (readM (w • v))} {M' = ix (readM w) ⊙ ix (readM v)}
    Eq.refl (λ x y → Eq.trans
      (Eq.cong (λ M → ix M x y) (readM-• w v))
      (ix-mul (readM w) (readM v) x y)))
  (S.∙-cong {s = ⟦ w ⟧} {s' = Ext.⟦ w ⟧}
    {t = ⟦ v ⟧} {t' = Ext.⟦ v ⟧} (⟦⟧-Ext w) (⟦⟧-Ext v))
  where import Examples.Groups.Real-Clifford+CH.Semantics.Scaled as S

sound-from : (∀ {w v} → w === v → ⟦ w ⟧ ~ ⟦ v ⟧) →
             ∀ {w v} → w ≈ v → ⟦ w ⟧ ~ ⟦ v ⟧
sound-from ax {w} {v} e = S.~-trans
  {s = ⟦ w ⟧} {t = Ext.⟦ w ⟧} {u = ⟦ v ⟧} (⟦⟧-Ext w)
  (S.~-trans {s = Ext.⟦ w ⟧} {t = Ext.⟦ v ⟧} {u = ⟦ v ⟧}
    (C.fʷ-cong e) (S.~-sym {s = ⟦ v ⟧} {t = Ext.⟦ v ⟧} (⟦⟧-Ext v)))
  where
  import Examples.Groups.Real-Clifford+CH.Semantics.Scaled as S
  ax′ : ∀ {u z} → u === z → Ext.⟦ u ⟧ ~ Ext.⟦ z ⟧
  ax′ {u} {z} h = S.~-trans
    {s = Ext.⟦ u ⟧} {t = ⟦ u ⟧} {u = Ext.⟦ z ⟧}
    (S.~-sym {s = ⟦ u ⟧} {t = Ext.⟦ u ⟧} (⟦⟧-Ext u))
    (S.~-trans {s = ⟦ u ⟧} {t = ⟦ z ⟧} {u = Ext.⟦ z ⟧}
      (ax h) (⟦⟧-Ext z))
  module C = Ext.Cong ax′
