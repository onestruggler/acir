------------------------------------------------------------------------
-- Presentations of groups
--
-- A five-wire gadget denotes its block
--
-- The gadget of the affine decoding on p ≠ q, λ⁰ of a four-wire gadget
-- conjugated by an affine circuit sending 0 and e₀ to p and q, denotes
-- the two-level block on p and q: as Five.Sem.Gad4 one wire up, the
-- four-wire gadget's block on 0 and e₀ (a module parameter) becoming,
-- under the control λ⁰ (Five.Sem.Lam), the block on the same vectors
-- with wire 4 at 0 (Five.Sem.TL.tl-ctrl).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List using ([] ; _∷_)
open import Word.Base using (ε)
open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Five.Chain using (⟪_⟫ʷ ; _≈_ ; X4)
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁ ; λᵈ)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; blkOf ; o₄ ; e₄)

module Examples.Groups.Clifford+CS.Five.Sem.Gad5
  (F4ᵍ : ∀ g h → ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ h ∷ [] ⟫ʷ ≈ ⟪ λ₁ h ∷ X4 ∷ λ₁ g ∷ X4 ∷ [] ⟫ʷ)
  (F5ᵍ : ∀ g → ⟪ λᵈ g ∷ [] ⟫ʷ ≈ ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ g ∷ [] ⟫ʷ)
  (x4x4 : ⟪ X4 ∷ X4 ∷ [] ⟫ʷ ≈ ε)
  (G : Kind → Circuit 4) (g4 : ∀ V → ⟦ G V ⟧ ~ tl (blkOf V) o₄ e₄)
  where

open import Data.Bool using (true)
open import Data.Nat.Primality using (prime[2])
open import Data.Product using (_,_)
open import Data.Vec using () renaming (_∷_ to _∷ᵥ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_)
open import Word.Base using (_•_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; _~_)
open import Examples.Groups.Clifford+CS.Five.Affine using (τ)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (perm ; ctrl ; tl-ctrl ; module Bij)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff using (bm ; bm-inv ; bm-inv′)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff5 using (aff5)
open import Examples.Groups.Clifford+CS.Five.Sem.Build using (α ; α-o ; α-e ; ze)
import Examples.Groups.Clifford+CS.Five.Calc as Calc
import Examples.Groups.Clifford+CS.Five.Sem.Lam as Lam

import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹)

open Calc F4ᵍ F5ᵍ x4x4 using (Λ⁰)
open Lam F4ᵍ F5ᵍ x4x4 using (Λ⁰-sem ; ctrl-cong)

-- λ⁰ of the four-wire gadget: the block on 0 and e₀ with wire 4 at 0.
Λ⁰G-sem : (V : Kind) → ⟦ Λ⁰ (G V) ⟧ ~ tl (blkOf V) ze (true ∷ᵥ ze)
Λ⁰G-sem V =
  ~-trans {s = ⟦ Λ⁰ (G V) ⟧} {t = ctrl ⟦ G V ⟧} {u = tl (blkOf V) ze (true ∷ᵥ ze)} (Λ⁰-sem (G V))
    (~-trans {s = ctrl ⟦ G V ⟧} {t = ctrl (tl (blkOf V) o₄ e₄)} {u = tl (blkOf V) ze (true ∷ᵥ ze)}
      (ctrl-cong {s = ⟦ G V ⟧} {t = tl (blkOf V) o₄ e₄} (g4 V))
      (~-sym {s = tl (blkOf V) ze (true ∷ᵥ ze)} {t = ctrl (tl (blkOf V) o₄ e₄)} (tl-ctrl (blkOf V) o₄ e₄)))

gad₅-sem : (V : Kind) (p q : Bits 5) → p ≢ q →
           ⟦ τ (α p q) • Λ⁰ (G V) • τ (α p q ⁻¹) ⟧ ~ tl (blkOf V) p q
gad₅-sem V p q ne =
  Eq.subst₂ (λ x y → ⟦ a • (g • a′) ⟧ ~ tl (blkOf V) x y) (α-o p q) (α-e p q ne) main
  where
  a g a′ : Circuit 5
  a  = τ (α p q)
  g  = Λ⁰ (G V)
  a′ = τ (α p q ⁻¹)

  f f′ : Bits 5 → Bits 5
  f  = bm (α p q)
  f′ = bm (α p q ⁻¹)

  Pf Pg Bl Tl : Scaled 5
  Pf = 0 , perm f
  Pg = 0 , perm f′
  Bl = tl (blkOf V) ze (true ∷ᵥ ze)
  Tl = tl (blkOf V) (f ze) (f (true ∷ᵥ ze))

  main : ⟦ a • (g • a′) ⟧ ~ Tl
  main =
    ~-trans {s = ⟦ a • (g • a′) ⟧} {t = ⟦ a ⟧ ∙ (⟦ g ⟧ ∙ ⟦ a′ ⟧)} {u = Tl}
      (~-trans {s = ⟦ a • (g • a′) ⟧} {t = ⟦ a ⟧ ∙ ⟦ g • a′ ⟧} {u = ⟦ a ⟧ ∙ (⟦ g ⟧ ∙ ⟦ a′ ⟧)}
        (hom a (g • a′))
        (∙-cong {s = ⟦ a ⟧} {s' = ⟦ a ⟧} {t = ⟦ g • a′ ⟧} {t' = ⟦ g ⟧ ∙ ⟦ a′ ⟧} (~-refl ⟦ a ⟧) (hom g a′)))
      (~-trans {s = ⟦ a ⟧ ∙ (⟦ g ⟧ ∙ ⟦ a′ ⟧)} {t = Pf ∙ (Bl ∙ Pg)} {u = Tl}
        (∙-cong {s = ⟦ a ⟧} {s' = Pf} {t = ⟦ g ⟧ ∙ ⟦ a′ ⟧} {t' = Bl ∙ Pg}
          (aff5 (α p q)) (∙-cong {s = ⟦ g ⟧} {s' = Bl} {t = ⟦ a′ ⟧} {t' = Pg} (Λ⁰G-sem V) (aff5 (α p q ⁻¹))))
        (~-trans {s = Pf ∙ (Bl ∙ Pg)} {t = (Pf ∙ Bl) ∙ Pg} {u = Tl}
          (~-sym {s = (Pf ∙ Bl) ∙ Pg} {t = Pf ∙ (Bl ∙ Pg)} (∙-assoc Pf Bl Pg))
          (Bij.conj-tl f f′ (bm-inv′ (α p q)) (bm-inv (α p q)) (blkOf V) ze (true ∷ᵥ ze))))
