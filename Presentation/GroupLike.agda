------------------------------------------------------------------------
-- Presentations of groups
--
-- Group-like presentations: inverses, cancellation, and the group of
-- words modulo the congruence
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Presentation.GroupLike where

open import Algebra.Bundles using (Group)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Level using (0ℓ)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base

import Presentation.Base as PB
import Presentation.Properties as PP

------------------------------------------------------------------------
-- Group-like presentations

-- A presentation is group-like if every generator has a left inverse.
Grouplike : {Y : Set} → (Γ : WRel Y) → Set
Grouplike {Y} Γ = ∀ (x : Y) →  ∃ λ (x' : Word Y) → x' • [ x ]ʷ ≈ ε
  where open PB Γ

------------------------------------------------------------------------
-- Basic group lemmas

module Group-Lemmas
  {Y : Set}
  (Γ : WRel Y)
  (group-like : Grouplike Γ)
  where

  infix 8 _⁻¹

  open PP Γ
  open PB Γ
  open SR word-setoid

  -- Syntactic inverse: invert generators via the group-like structure
  -- and reverse products.
  _⁻¹ : Word Y → Word Y
  [ x ]ʷ ⁻¹  = proj₁ (group-like x)
  ε ⁻¹        = ε
  (u • v) ⁻¹  = v ⁻¹ • u ⁻¹

  -- g ⁻¹ is a left inverse.
  inverseˡ : {g : Word Y} → g ⁻¹ • g ≈ ε
  inverseˡ {[ x ]ʷ} = proj₂ (group-like x)
  inverseˡ {ε}       = left-unit
  inverseˡ {u • v}   = begin
      (v ⁻¹ • u ⁻¹) • (u • v)     ≈⟨ assoc ⟩
      v ⁻¹ • (u ⁻¹ • (u • v))     ≈⟨ cright assoc reversed ⟩
      v ⁻¹ • ((u ⁻¹ • u) • v)     ≈⟨ cright cleft inverseˡ ⟩
      v ⁻¹ • ε • v                ≈⟨ cright left-unit ⟩
      v ⁻¹ • v                    ≈⟨ inverseˡ ⟩
      ε ∎

  -- g ⁻¹ is a right inverse.
  inverseʳ : {g : Word Y} → g • g ⁻¹ ≈ ε
  inverseʳ {g} = begin
      g • (g ⁻¹)                        ≈⟨ left-unit reversed ⟩
      ε • (g • (g ⁻¹))                  ≈⟨ cleft inverseˡ reversed ⟩
      ((g ⁻¹) ⁻¹ • g ⁻¹) • (g • (g ⁻¹)) ≈⟨ assoc ⟩
      (g ⁻¹) ⁻¹ • (g ⁻¹ • (g • (g ⁻¹))) ≈⟨ cright assoc reversed ⟩
      (g ⁻¹) ⁻¹ • ((g ⁻¹ • g) • g ⁻¹)   ≈⟨ cright cleft inverseˡ ⟩
      (g ⁻¹) ⁻¹ • (ε • g ⁻¹)            ≈⟨ cright left-unit ⟩
      (g ⁻¹) ⁻¹ • g ⁻¹                  ≈⟨ inverseˡ ⟩
      ε ∎

  -- Left cancellation.
  •-cancelˡ : {g h h' : Word Y} → g • h ≈ g • h' → h ≈ h'
  •-cancelˡ {g} {h} {h'} p = begin
      h               ≈⟨ left-unit reversed ⟩
      ε • h           ≈⟨ cleft inverseˡ reversed ⟩
      (g ⁻¹ • g) • h  ≈⟨ assoc ⟩
      g ⁻¹ • (g • h)  ≈⟨ cright p ⟩
      g ⁻¹ • (g • h') ≈⟨ assoc reversed ⟩
      (g ⁻¹ • g) • h' ≈⟨ cleft inverseˡ ⟩
      ε • h'          ≈⟨ left-unit ⟩
      h' ∎

  -- Right cancellation.
  •-cancelʳ : {g g' h : Word Y} → g • h ≈ g' • h → g ≈ g'
  •-cancelʳ {g} {g'} {h} p = begin
      g               ≈⟨ right-unit reversed ⟩
      g • ε           ≈⟨ cright inverseʳ reversed ⟩
      g • (h • h ⁻¹)  ≈⟨ assoc reversed ⟩
      (g • h) • h ⁻¹  ≈⟨ cleft p ⟩
      (g' • h) • h ⁻¹ ≈⟨ assoc ⟩
      g' • (h • h ⁻¹) ≈⟨ cright inverseʳ ⟩
      g' • ε          ≈⟨ right-unit ⟩
      g' ∎

  -- Left inverses are unique.
  inverseˡ-unique : {g h : Word Y} → h • g ≈ ε → h ≈ g ⁻¹
  inverseˡ-unique {g} {h} p = begin
      h              ≈⟨ right-unit reversed ⟩
      h • ε          ≈⟨ cright inverseʳ reversed ⟩
      h • (g • g ⁻¹) ≈⟨ assoc reversed ⟩
      (h • g) • g ⁻¹ ≈⟨ cleft p ⟩
      ε • g ⁻¹       ≈⟨ left-unit ⟩
      g ⁻¹ ∎

  -- Right inverses are unique.
  inverseʳ-unique : {g h : Word Y} → g • h ≈ ε → h ≈ g ⁻¹
  inverseʳ-unique {g} {h} p = begin
      h              ≈⟨ left-unit reversed ⟩
      ε • h          ≈⟨ cleft inverseˡ reversed ⟩
      (g ⁻¹ • g) • h ≈⟨ assoc ⟩
      g ⁻¹ • (g • h) ≈⟨ cright p ⟩
      g ⁻¹ • ε       ≈⟨ right-unit ⟩
      g ⁻¹ ∎

  -- Congruence for inverses.
  ⁻¹-cong : {g h : Word Y} → g ≈ h → g ⁻¹ ≈ h ⁻¹
  ⁻¹-cong {g} {h} p = inverseʳ-unique claim
    where
    claim : h • g ⁻¹ ≈ ε
    claim = begin
      h • g ⁻¹       ≈⟨ cleft p reversed ⟩
      g • g ⁻¹       ≈⟨ inverseʳ ⟩
      ε ∎

  -- The inverse is involutive.
  ⁻¹-involutive : {g : Word Y} → (g ⁻¹) ⁻¹ ≈ g
  ⁻¹-involutive {g} =
    inverseʳ-unique inverseˡ reversed

  -- The inverse of ε.
  ⁻¹-ε : ε ⁻¹ ≈ ε
  ⁻¹-ε = refl

  -- The inverse of a product.
  ⁻¹-anti-homo-• : ∀ {g h : Word Y} → (g • h) ⁻¹ ≈ h ⁻¹ • g ⁻¹
  ⁻¹-anti-homo-• = refl

  -- Inverses reflect equality.
  ⁻¹-injective : ∀ {u v : Word Y} → u ⁻¹ ≈ v ⁻¹ → u ≈ v
  ⁻¹-injective {u} {v} hyp = begin
      u              ≈⟨ right-unit reversed ⟩
      u • ε          ≈⟨ cright (inverseˡ reversed) ⟩
      u • (v ⁻¹ • v) ≈⟨ assoc reversed ⟩
      (u • v ⁻¹) • v ≈⟨ cleft (cright (hyp reversed)) ⟩
      (u • u ⁻¹) • v ≈⟨ cleft inverseʳ ⟩
      ε • v          ≈⟨ left-unit ⟩
      v ∎

  -- Commutativity of inverses.
  comm-⁻¹ : ∀ {v v' w w'} → v • w ≈ w' • v' → v' • w ⁻¹ ≈ w' ⁻¹ • v
  comm-⁻¹ {v} {v'} {w} {w'} hyp = begin
      v' • w ⁻¹                  ≈⟨ left-unit reversed ⟩
      ε • (v' • w ⁻¹)            ≈⟨ cleft inverseˡ reversed ⟩
      (w' ⁻¹ • w') • (v' • w ⁻¹) ≈⟨ assoc ⟩
      w' ⁻¹ • (w' • (v' • w ⁻¹)) ≈⟨ cright assoc reversed ⟩
      w' ⁻¹ • (w' • v') • w ⁻¹   ≈⟨ cright cleft hyp reversed ⟩
      w' ⁻¹ • (v • w) • w ⁻¹     ≈⟨ cright assoc ⟩
      w' ⁻¹ • v • (w • w ⁻¹)     ≈⟨ assoc reversed ⟩
      (w' ⁻¹ • v) • (w • w ⁻¹)   ≈⟨ cright inverseʳ ⟩
      (w' ⁻¹ • v) • ε            ≈⟨ right-unit ⟩
      w' ⁻¹ • v ∎

  -- Any equation can be reduced to a one-sided equation.
  one-sided : ∀ {w u} → w • u ⁻¹ ≈ ε → w ≈ u
  one-sided {w} {u} hyp = begin
      w              ≈⟨ right-unit reversed ⟩
      w • ε          ≈⟨ cright inverseˡ reversed ⟩
      w • (u ⁻¹ • u) ≈⟨ assoc reversed ⟩
      (w • u ⁻¹) • u ≈⟨ cleft hyp ⟩
      ε • u          ≈⟨ left-unit ⟩
      u ∎

  -- The group of words modulo the congruence.
  •-ε-group : Group 0ℓ 0ℓ
  •-ε-group = record
    { Carrier  = Word Y
    ; _≈_      = _≈_
    ; _∙_      = _•_
    ; ε        = ε
    ; _⁻¹      = _⁻¹
    ; isGroup  = record
      { isMonoid = •-ε-isMonoid
      ; inverse  = (λ x → inverseˡ) , (λ x → inverseʳ)
      ; ⁻¹-cong  = ⁻¹-cong
      }
    }
