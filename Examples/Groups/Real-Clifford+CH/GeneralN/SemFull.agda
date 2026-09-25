------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic steps of Equations (297)–(299), one width down
--
-- One width down, with the wire 2 of the full width removed, the
-- multi-controlled H of (284) is HG₀₁ (SemZX): H on wire 0 controlled
-- by the wires 2 …, its box wire on wire 1.  It passes the CH from
-- wire 1 onto wire 0, with either colour of control: all three are H
-- on wire 0 under disjoint controls.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.SemFull where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (HG₀₁ ; module Forms)

module _ (k : ℕ) where
  open Forms k

  private
    wch : CF {3} {k} °CH
    wch = cf-loc °CH

  sem-HG-CH : ⟦ HG₀₁ k • CH ⟧ ~ ⟦ CH • HG₀₁ k ⟧
  sem-HG-CH = cf-~ (cf-• hg₀₁ ch) (cf-• ch hg₀₁) Eq.refl Eq.refl

  sem-HG-°CH : ⟦ HG₀₁ k • °CH ⟧ ~ ⟦ °CH • HG₀₁ k ⟧
  sem-HG-°CH = cf-~ (cf-• hg₀₁ wch) (cf-• wch hg₀₁) Eq.refl Eq.refl
