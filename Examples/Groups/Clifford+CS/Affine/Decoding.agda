------------------------------------------------------------------------
-- Presentations of groups
--
-- The affine decoding of a gate, and its equivariance
--
-- For a gate G on 4 + m wires that commutes with every CX whose control
-- is off wire 0, `d p q = α p q • G • (α p q)⁻¹` is G carried from the
-- basis states 0, e₀ to p, q.  Conjugating it by any affine word τ gives
-- the decoding at the images of p and q under τ's bit map (`eqvʷ`): a
-- letter passes α leaving only CX that commute with G (Affine.Alpha),
-- and affine words are circuits (Affine.Circuits).  Stated over any
-- theory Γ of circuits containing the old one (the rules of Syntactics),
-- since from five wires on G lives in the new theory.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (WRel)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Gen ; Circuit ; _⊢_≈_)
open import Notations using (₄₊)
import Presentation.Base as PB

module Examples.Groups.Clifford+CS.Affine.Decoding
  (m : ℕ) (c4 : Complete 4)
  (Γ : WRel (Gen (₄₊ m)))
  (emb : ∀ {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ u ≈ v → PB._≈_ Γ u v)
  where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥-elim)
import Data.Empty.Irrelevant as Irr
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Product using (Σ ; _×_ ; _,_)
open import Data.Vec using (Vec ; lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₃₊)

open import Examples.Groups.Clifford+CS.Tools using (module Tools)
import Examples.Groups.Clifford+CS.Affine.Theory (₃₊ m) as A
open A using (Lt ; xL ; tL ; Wire ; toggle)
open import Examples.Groups.Clifford+CS.Affine.Equivariance (₃₊ m) using (Ctl ; tmap)
open import Examples.Groups.Clifford+CS.Affine.Alpha (₃₊ m) using (α ; amap ; eqv-α ; amapʷ ; amapʷ-inj)
open import Examples.Groups.Clifford+CS.Affine.Circuits m c4 using (⟪_⟫ ; ⟪_⟫ʷ ; ⟪⟫-cong)

open Tools Γ

private
  W : ℕ
  W = ₄₊ m

  St : Set
  St = Vec Bool W

------------------------------------------------------------------------
-- The decoding of a gate

module Gate
  (G : Circuit W)
  (indep : ∀ (u : Fin (₃₊ m)) (v : Wire) .(p : sF u ≢ v) → PB._≈_ Γ (⟪ tL (sF u) v p ⟫ • G) (G • ⟪ tL (sF u) v p ⟫))
  where

  -- CX with their controls off wire 0 pass G.
  ctl-comm : ∀ (h : Word Lt) → Ctl h → ⟪ h ⟫ʷ • G ≈ G • ⟪ h ⟫ʷ
  ctl-comm [ xL _ ]ʷ          ()
  ctl-comm [ tL 0F _ _ ]ʷ     ()
  ctl-comm [ tL (sF u) v p ]ʷ _ = indep u v p
  ctl-comm ε _ = trans left-unit (sym right-unit)
  ctl-comm (a • b) (ca , cb) = begin
    (⟪ a ⟫ʷ • ⟪ b ⟫ʷ) • G   ≈⟨ assoc ⟩
    ⟪ a ⟫ʷ • (⟪ b ⟫ʷ • G)   ≈⟨ back _ (ctl-comm b cb) ⟩
    ⟪ a ⟫ʷ • (G • ⟪ b ⟫ʷ)   ≈⟨ sym assoc ⟩
    (⟪ a ⟫ʷ • G) • ⟪ b ⟫ʷ   ≈⟨ front _ (ctl-comm a ca) ⟩
    (G • ⟪ a ⟫ʷ) • ⟪ b ⟫ʷ   ≈⟨ assoc ⟩
    G • ⟪ a ⟫ʷ • ⟪ b ⟫ʷ ∎

  d : St → St → Circuit W
  d p q = ⟪ α p q ⟫ʷ • G • ⟪ A.rev (α p q) ⟫ʷ

  private
    cancel-h : ∀ (h : Word Lt) → ⟪ h ⟫ʷ • ⟪ A.rev h ⟫ʷ ≈ ε
    cancel-h h = emb (⟪⟫-cong (A.rev-inv h))

  -- One letter.
  eqv : ∀ (a : Lt) (p q : St) → p ≢ q → ⟪ a ⟫ • d p q • ⟪ a ⟫ ≈ d (amap a p) (amap a q)
  eqv a p q ne with eqv-α a p q ne
  ... | h , ch , e = begin
    ⟪ a ⟫ • (⟪ α p q ⟫ʷ • G • ⟪ A.rev (α p q) ⟫ʷ) • ⟪ a ⟫
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    ⟪ [ a ]ʷ • α p q ⟫ʷ • G • ⟪ A.rev ([ a ]ʷ • α p q) ⟫ʷ
      ≈⟨ cong (emb (⟪⟫-cong e)) (back _ (emb (⟪⟫-cong (A.rev-cong e)))) ⟩
    ⟪ α′ • h ⟫ʷ • G • ⟪ A.rev (α′ • h) ⟫ʷ
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
    ⟪ α′ ⟫ʷ • (⟪ h ⟫ʷ • G) • ⟪ A.rev h ⟫ʷ • ⟪ A.rev α′ ⟫ʷ
      ≈⟨ back _ (front _ (ctl-comm h ch)) ⟩
    ⟪ α′ ⟫ʷ • (G • ⟪ h ⟫ʷ) • ⟪ A.rev h ⟫ʷ • ⟪ A.rev α′ ⟫ʷ
      ≈⟨ back _ (trans assoc (back _ (trans (sym assoc) (trans (front _ (cancel-h h)) left-unit)))) ⟩
    ⟪ α′ ⟫ʷ • G • ⟪ A.rev α′ ⟫ʷ ∎
    where α′ = α (amap a p) (amap a q)

  -- Any affine word.
  eqvʷ : ∀ (τ : Word Lt) (p q : St) → p ≢ q → ⟪ τ ⟫ʷ • d p q • ⟪ A.rev τ ⟫ʷ ≈ d (amapʷ τ p) (amapʷ τ q)
  eqvʷ [ a ]ʷ  p q ne = eqv a p q ne
  eqvʷ ε       p q ne = trans left-unit right-unit
  eqvʷ (u • v) p q ne = begin
    (⟪ u ⟫ʷ • ⟪ v ⟫ʷ) • d p q • (⟪ A.rev v ⟫ʷ • ⟪ A.rev u ⟫ʷ)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    ⟪ u ⟫ʷ • (⟪ v ⟫ʷ • d p q • ⟪ A.rev v ⟫ʷ) • ⟪ A.rev u ⟫ʷ
      ≈⟨ back _ (front _ (eqvʷ v p q ne)) ⟩
    ⟪ u ⟫ʷ • d (amapʷ v p) (amapʷ v q) • ⟪ A.rev u ⟫ʷ
      ≈⟨ eqvʷ u (amapʷ v p) (amapʷ v q) (λ e → ne (amapʷ-inj v e)) ⟩
    d (amapʷ u (amapʷ v p)) (amapʷ u (amapʷ v q)) ∎
