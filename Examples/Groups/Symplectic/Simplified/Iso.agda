------------------------------------------------------------------------
-- Presentations of groups
--
-- The simplified rule set is equivalent to the original
--
-- Each axiom of Examples.Groups.Symplectic.Syntactics is derivable
-- from the simplified ones (f-well-defined) and conversely
-- (g-well-defined).  Since both presentations have the same generators,
-- the identity on words is the isomorphism, in both directions.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR


open import Function using (id)

open import Data.Product using (_,_ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)



open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



open import Presentation.GroupLike
open import Data.Nat.Primality
open import Data.Nat.GCD
open Bézout
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Symplectic.Simplified.Iso
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime as NSym
open Symplectic hiding (_QRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑ ; order-S ; order-H ; semi-MS ; semi-M↑CZ ; semi-M↓CZ ; order-CZ ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11 ; selinger-c12 ; selinger-c13 ; selinger-c14 ; selinger-c15)

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
open import Examples.Groups.Symplectic.Simplified.Lemmas p-2 p-prime g* g-gen
open import Examples.Groups.Symplectic.Simplified.LemmasCZ p-2 p-prime g* g-gen

private
  variable
    n : ℕ

module Sym  = NSym.Symplectic
module Sim  = Simplified-Relations
open Sym renaming (Gen to Gen₁ ; _QRel,_===_ to _QRel,_===₁_) using ()
Gen₂ = Gen₁
open Sim renaming (_QRel,_===_ to _QRel,_===₂_) using ()
open Symplectic-GroupLike renaming (grouplike to grouplike₁) using ()
open Symplectic-Sim-GroupLike renaming (grouplike to grouplike₂) using ()


f-well-defined : let open PB (n QRel,_===₂_) renaming (_≈_ to _≈₂_) in
  ∀ {w v} → n QRel, w ===₁ v → id w ≈₂ id v
f-well-defined {n} (Sym.srel Sym.Base.order-S) = PB.axiom (Sim.srel Sim.order-S)
f-well-defined {₁₊ n} (Sym.srel Sym.Base.order-H) = lemma-order-H
  where
  open Lemmas1 n
f-well-defined {₁₊ n} (Sym.srel Sym.Base.order-SH) = lemma-order-SH
  where
  open Lemmas1 n
f-well-defined {₁₊ n} (Sym.srel Sym.Base.comm-HHS) = lemma-comm-HHS
  where
  open Lemmas1b n
f-well-defined {₁₊ n} (Sym.srel (Sym.Base.M-mul x y)) = lemma-M-mul x y
  where
  open Lemmas1 n
f-well-defined {₁₊ n} (Sym.srel (Sym.Base.semi-MS x)) = lemma-semi-MS x
  where
  open Lemmas1 n
f-well-defined {₂₊ n} (Sym.srel (Sym.Base.semi-M↑CZ x)) = lemma-semi-M↑CZ x
  where
  open Lemmas2 n
f-well-defined {₂₊ n} (Sym.srel (Sym.Base.semi-M↓CZ x)) = lemma-semi-M↓CZ x
  where
  open Lemmas2 n
f-well-defined {n} (Sym.srel Sym.Base.order-CZ) = PB.axiom (Sim.srel Sim.order-CZ)
f-well-defined {n} (Sym.srel Sym.Base.comm-CZ-S↓) = PB.axiom (Sim.srel Sim.comm-CZ-S↓)
f-well-defined {n} (Sym.srel Sym.Base.comm-CZ-S↑) = PB.axiom (Sim.srel Sim.comm-CZ-S↑)
f-well-defined {n} (Sym.srel Sym.Base.selinger-c10) = PB.axiom (Sim.srel Sim.selinger-c10)
f-well-defined {n} (Sym.srel Sym.Base.selinger-c11) = PB.axiom (Sim.srel Sim.selinger-c11)
f-well-defined {n} (Sym.srel Sym.Base.selinger-c12) = PB.axiom (Sim.srel Sim.selinger-c12)
f-well-defined {n} (Sym.srel Sym.Base.selinger-c13) = PB.axiom (Sim.srel Sim.selinger-c13)
f-well-defined {n} (Sym.srel Sym.Base.selinger-c14) = PB.axiom (Sim.srel Sim.selinger-c14)
f-well-defined {n} (Sym.srel Sym.Base.selinger-c15) = PB.axiom (Sim.srel Sim.selinger-c15)
f-well-defined {n} (Sym.comm₁ h g) = PB.axiom (Sim.comm₁ h g)
f-well-defined {n} (Sym.comm₂ h g) = PB.axiom (Sim.comm₂ h g)
f-well-defined {n} (Sym.cong↑ eq) = Sim.lemma-cong↑ _ _ (f-well-defined eq)

g-well-defined : let open PB (n QRel,_===₁_) renaming (_≈_ to _≈₁_) in
  ∀ {u t} → n QRel, u ===₂ t → id u ≈₁ id t
g-well-defined (Sim.srel Sim.order-S) = PB.axiom (Sym.srel Sym.Base.order-S)
g-well-defined {₁₊ n} (Sim.srel Sim.order-H) = lemma-HH-M-1
  where
  open Lemmas0 n
g-well-defined {₁₊ n} (Sim.srel (Sim.M-power k)) = begin
  (Mg^ k) ≡⟨ auto ⟩
  Mg ^ toℕ k ≈⟨ ^-cong (Mg) (M g′) (toℕ k) (refl) ⟩
  M g′ ^ toℕ k ≈⟨ lemma-M-power g′ (toℕ k) ⟩
  M (g^ k) ≈⟨ refl ⟩
  (M (g^ k)) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid
  open Lemmas0 n
  open Sim


g-well-defined {₁₊ n} (Sim.srel Sim.semi-MS) = PB.axiom (Sym.srel (Sym.Base.semi-MS ((g , g≠0))))
g-well-defined (Sim.srel Sim.semi-M↑CZ) = PB.axiom (Sym.srel (Sym.Base.semi-M↑CZ ((g , g≠0))))
g-well-defined (Sim.srel Sim.semi-M↓CZ) = PB.axiom (Sym.srel (Sym.Base.semi-M↓CZ ((g , g≠0))))
g-well-defined (Sim.srel Sim.order-CZ) = PB.axiom (Sym.srel Sym.Base.order-CZ)
g-well-defined (Sim.srel Sim.comm-CZ-S↓) = PB.axiom (Sym.srel Sym.Base.comm-CZ-S↓)
g-well-defined (Sim.srel Sim.comm-CZ-S↑) = PB.axiom (Sym.srel Sym.Base.comm-CZ-S↑)
g-well-defined (Sim.srel Sim.selinger-c10) = PB.axiom (Sym.srel Sym.Base.selinger-c10)
g-well-defined (Sim.srel Sim.selinger-c11) = PB.axiom (Sym.srel Sym.Base.selinger-c11)
g-well-defined (Sim.srel Sim.selinger-c12) = PB.axiom (Sym.srel Sym.Base.selinger-c12)
g-well-defined (Sim.srel Sim.selinger-c13) = PB.axiom (Sym.srel Sym.Base.selinger-c13)
g-well-defined (Sim.srel Sim.selinger-c14) = PB.axiom (Sym.srel Sym.Base.selinger-c14)
g-well-defined (Sim.srel Sim.selinger-c15) = PB.axiom (Sym.srel Sym.Base.selinger-c15)
g-well-defined (Sim.comm₁ h g) = PB.axiom (Sym.comm₁ h g)
g-well-defined (Sim.comm₂ h g) = PB.axiom (Sym.comm₂ h g)
g-well-defined (Sim.cong↑ eq) = Sym.lemma-cong↑ _ _ (g-well-defined eq)


open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)

open GroupMorphisms


Theorem-Sym-iso-Sim : ∀ {n} →
  let
  module G1 = Group-Lemmas (n QRel,_===₁_) grouplike₁
  module G2 = Group-Lemmas (n QRel,_===₂_) grouplike₂
  in
  IsGroupIsomorphism (Group.rawGroup G1.•-ε-group) (Group.rawGroup G2.•-ε-group) id
Theorem-Sym-iso-Sim {n}  = StarGroupIsomorphism.isGroupIsomorphism f-well-defined g-well-defined
  where
  open import Presentation.MorphismId (n QRel,_===₁_) (n QRel,_===₂_)
  open GroupMorphs (grouplike₁ {n}) (grouplike₂ {n})



Theorem-Sym-iso-Sim' : ∀ {n} →
  let
  module G1 = Group-Lemmas (n QRel,_===₁_) grouplike₁
  module G2 = Group-Lemmas (n QRel,_===₂_) grouplike₂
  in
  IsGroupIsomorphism (Group.rawGroup G2.•-ε-group) (Group.rawGroup G1.•-ε-group)  id
Theorem-Sym-iso-Sim' {n} = StarGroupIsomorphism.isGroupIsomorphism g-well-defined f-well-defined
  where
  open import Presentation.MorphismId  (n QRel,_===₂_) (n QRel,_===₁_)
  open GroupMorphs (grouplike₂ {n}) (grouplike₁ {n})
