------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport of two-wire derivations on five wires
--
-- The de-borrowing of the joint paper (its λ-images of rel-269, rel-272
-- and ck-tct) replaces λ(el) by λ(er) for equations el = er on at most
-- two wires: the transport of a two-wire derivation.  Placed on the
-- wires 0 1 of the domain, a two-wire derivation uses only rules on at
-- most two wires and the structural rules, so it needs the λ-images of
-- those instances only (`Ok₂`), which the joint run derives; the rules
-- whose λ-images it does not derive, being on three or four wires, do
-- not occur (`transport₂`, by induction on the derivation, as
-- Five.Transport.transport).  λ⁰ is λ¹ between two X on wire 4 (`lam⁰`,
-- as Five.Calc.Λ⁰-X, given that X on wire 4 is an involution).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Transport2 where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.List.Properties using (++-assoc ; ++-identityʳ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Syntactics as Syn using (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁)
open import Examples.Groups.Clifford+CS.Five.Transport using (λʷ)

private
  refl≡ : ∀ {xs ys : List Mac} → xs ≡ ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
  refl≡ Eq.refl = refl

------------------------------------------------------------------------
-- λ¹

-- The λ-images of the instances on two wires, placed on the wires 0 1.
Ok₂ : Set
Ok₂ = ∀ {w v : Circuit 2} → 2 VRel, w === v → ⟪ λʷ (w ↓ᵏ 2) ⟫ʷ ≈ ⟪ λʷ (v ↓ᵏ 2) ⟫ʷ

transport₂ : Ok₂ → ∀ {u v : Circuit 2} → 2 Syn.⊢ u ≈ v → ⟪ λʷ (u ↓ᵏ 2) ⟫ʷ ≈ ⟪ λʷ (v ↓ᵏ 2) ⟫ʷ
transport₂ ok PB.refl         = refl
transport₂ ok (PB.sym e)      = sym (transport₂ ok e)
transport₂ ok (PB.trans e f)  = trans (transport₂ ok e) (transport₂ ok f)
transport₂ ok (PB.cong {w} {w′} {v} {v′} e f) =
  trans (⟪⟫-++ (λʷ (w ↓ᵏ 2)) (λʷ (v ↓ᵏ 2)))
    (trans (cong (transport₂ ok e) (transport₂ ok f)) (sym (⟪⟫-++ (λʷ (w′ ↓ᵏ 2)) (λʷ (v′ ↓ᵏ 2)))))
transport₂ ok (PB.assoc {w} {v} {u}) = refl≡ (++-assoc (λʷ (w ↓ᵏ 2)) (λʷ (v ↓ᵏ 2)) (λʷ (u ↓ᵏ 2)))
transport₂ ok PB.left-unit    = refl
transport₂ ok (PB.right-unit {w}) = refl≡ (++-identityʳ (λʷ (w ↓ᵏ 2)))
transport₂ ok (PB.axiom a)    = ok a

------------------------------------------------------------------------
-- λ⁰

λ⁰ʷ : Circuit 4 → List Mac
λ⁰ʷ [ g ]ʷ  = X4 ∷ λ₁ g ∷ X4 ∷ []
λ⁰ʷ ε       = []
λ⁰ʷ (u • v) = λ⁰ʷ u ++ λ⁰ʷ v

module _ (x4x4 : ⟪ X4 ∷ X4 ∷ [] ⟫ʷ ≈ ε) where

  private
    X4w : Circuit 5
    X4w = ⟪ X4 ∷ [] ⟫ʷ

  Λ⁰-X : ∀ w → ⟪ λ⁰ʷ w ⟫ʷ ≈ X4w • ⟪ λʷ w ⟫ʷ • X4w
  Λ⁰-X [ g ]ʷ  = refl
  Λ⁰-X ε       = sym (trans (back _ left-unit) x4x4)
  Λ⁰-X (u • v) = begin
    ⟪ λ⁰ʷ u ++ λ⁰ʷ v ⟫ʷ                                       ≈⟨ ⟪⟫-++ (λ⁰ʷ u) (λ⁰ʷ v) ⟩
    ⟪ λ⁰ʷ u ⟫ʷ • ⟪ λ⁰ʷ v ⟫ʷ                                   ≈⟨ cong (Λ⁰-X u) (Λ⁰-X v) ⟩
    (X4w • ⟪ λʷ u ⟫ʷ • X4w) • (X4w • ⟪ λʷ v ⟫ʷ • X4w)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    X4w • ⟪ λʷ u ⟫ʷ • (X4w • X4w) • ⟪ λʷ v ⟫ʷ • X4w          ≈⟨ back _ (back _ (front _ x4x4)) ⟩
    X4w • ⟪ λʷ u ⟫ʷ • ε • ⟪ λʷ v ⟫ʷ • X4w                     ≈⟨ back _ (back _ left-unit) ⟩
    X4w • ⟪ λʷ u ⟫ʷ • ⟪ λʷ v ⟫ʷ • X4w                         ≈⟨ back _ (sym assoc) ⟩
    X4w • (⟪ λʷ u ⟫ʷ • ⟪ λʷ v ⟫ʷ) • X4w                       ≈⟨ back _ (front _ (sym (⟪⟫-++ (λʷ u) (λʷ v)))) ⟩
    X4w • ⟪ λʷ u ++ λʷ v ⟫ʷ • X4w                             ∎

  lam⁰ : ∀ {u v : Circuit 4} → ⟪ λʷ u ⟫ʷ ≈ ⟪ λʷ v ⟫ʷ → ⟪ λ⁰ʷ u ⟫ʷ ≈ ⟪ λ⁰ʷ v ⟫ʷ
  lam⁰ {u} {v} e = trans (Λ⁰-X u) (trans (back _ (front _ e)) (sym (Λ⁰-X v)))

  -- The same for two-wire circuits on the wires 0 1, given explicitly:
  -- ⟪ λʷ ?u ⟫ʷ does not determine ?u, and in a literal `w ↓ᵏ 2` the
  -- width of w is not solved from its sum with 2.
  lam⁰₂ : ∀ (u v : Circuit 2) → ⟪ λʷ (u ↓ᵏ 2) ⟫ʷ ≈ ⟪ λʷ (v ↓ᵏ 2) ⟫ʷ →
          ⟪ λ⁰ʷ (u ↓ᵏ 2) ⟫ʷ ≈ ⟪ λ⁰ʷ (v ↓ᵏ 2) ⟫ʷ
  lam⁰₂ u v = lam⁰ {u ↓ᵏ 2} {v ↓ᵏ 2}
