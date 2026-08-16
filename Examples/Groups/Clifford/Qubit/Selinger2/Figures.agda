------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Figures 3-7, replayed from the supplement (GENERATED).
--
-- Produced by emit2.py from the machine-readable proof file of
-- arXiv:1310.6813.  Do not edit by hand.  The generator, the extracted
-- rule tables and the paper's own source all live untracked in
-- local/qubit-clifford/, tools in local/qubit-clifford/tools/.
--
-- Every link is one congruence step: `by-assoc` for a bracketing, `at`
-- for a rule inside an explicit context, and `swap1` under some crights
-- for a transposition of gates on disjoint wires -- which Selinger never
-- writes down, working in a strict spatial monoidal groupoid.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger2.Figures where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations
open import Word.Base using (ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford.Qubit.Selinger2.Figure8
open import Examples.Groups.Clifford.Qubit.Selinger2.Boxes
open import Examples.Groups.Clifford.Qubit.Selinger2.Wires
import Examples.Groups.Clifford.Qubit.Selinger2.Lemmas as L

-- Equation 3.1   (2 steps)
module M-3-1 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-1 : (ε) ≈ ([ a₁ ]ᴬ • [ c₁ ]ᶜ • [ e₁ ]ᴱ)
  eq-3-1 = begin
    ε
      ≈⟨ by-assoc Eq.refl ⟩
    ε
      ≈⟨ by-assoc Eq.refl ⟩
    [ a₁ ]ᴬ • [ c₁ ]ᶜ • [ e₁ ]ᴱ
      ∎

-- Equation 3.3   (2 steps)
module M-3-3 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-3 : (H • [ a₁ ]ᴬ) ≈ ([ a₂ ]ᴬ)
  eq-3-3 = begin
    H • [ a₁ ]ᴬ
      ≈⟨ by-assoc Eq.refl ⟩
    H
      ≈⟨ by-assoc Eq.refl ⟩
    [ a₂ ]ᴬ
      ∎

-- Equation 3.4   (3 steps)
module M-3-4 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-4 : (H • [ a₂ ]ᴬ) ≈ ([ a₁ ]ᴬ)
  eq-3-4 = begin
    H • [ a₂ ]ᴬ
      ≈⟨ by-assoc Eq.refl ⟩
    H • H
      ≈⟨ by-assoc-and (at (ε) (ε) L.OneQubit.HH) Eq.refl Eq.refl ⟩
    ε
      ≈⟨ by-assoc Eq.refl ⟩
    [ a₁ ]ᴬ
      ∎

-- Equation 3.5   (6 steps)
module M-3-5 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-5 : (H • [ a₃ ]ᴬ) ≈ ([ a₃ ]ᴬ • X • S • S • S • ω)
  eq-3-5 = begin
    H • [ a₃ ]ᴬ
      ≈⟨ by-assoc Eq.refl ⟩
    H • H • S • H
      ≈⟨ by-assoc-and (at (ε) (S • H) L.OneQubit.HH) Eq.refl Eq.refl ⟩
    S • H
      ≈⟨ by-assoc-and (at (S • H) (ε) (L.OneQubit.SSSS reversed)) Eq.refl Eq.refl ⟩
    S • H • S • S • S • S
      ≈⟨ by-assoc-and (at (ε) (S • S • S) L.OneQubit.SHS) Eq.refl Eq.refl ⟩
    H • S • S • S • H • ω • S • S • S
      ≈⟨ by-assoc-and (at (H • S • S • S • H) (ε) (ω^-central 1 (S • S • S))) Eq.refl Eq.refl ⟩
    H • S • S • S • H • S • S • S • ω
      ≈⟨ by-assoc-and (at (H • S) (S • S • H • S • S • S • ω) (L.OneQubit.HH reversed)) Eq.refl Eq.refl ⟩
    H • S • H • H • S • S • H • S • S • S • ω
      ≈⟨ by-assoc Eq.refl ⟩
    [ a₃ ]ᴬ • X • S • S • S • ω
      ∎

-- Equation 3.6   (2 steps)
module M-3-6 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-6 : (S • [ a₁ ]ᴬ) ≈ ([ a₁ ]ᴬ • S)
  eq-3-6 = begin
    S • [ a₁ ]ᴬ
      ≈⟨ by-assoc Eq.refl ⟩
    S
      ≈⟨ by-assoc Eq.refl ⟩
    [ a₁ ]ᴬ • S
      ∎

-- Equation 3.7   (5 steps)
module M-3-7 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-7 : (S • [ a₂ ]ᴬ) ≈ ([ a₃ ]ᴬ • X • S • S • S • ω)
  eq-3-7 = begin
    S • [ a₂ ]ᴬ
      ≈⟨ by-assoc Eq.refl ⟩
    S • H
      ≈⟨ by-assoc-and (at (S • H) (ε) (L.OneQubit.SSSS reversed)) Eq.refl Eq.refl ⟩
    S • H • S • S • S • S
      ≈⟨ by-assoc-and (at (ε) (S • S • S) L.OneQubit.SHS) Eq.refl Eq.refl ⟩
    H • S • S • S • H • ω • S • S • S
      ≈⟨ by-assoc-and (at (H • S • S • S • H) (ε) (ω^-central 1 (S • S • S))) Eq.refl Eq.refl ⟩
    H • S • S • S • H • S • S • S • ω
      ≈⟨ by-assoc-and (at (H • S) (S • S • H • S • S • S • ω) (L.OneQubit.HH reversed)) Eq.refl Eq.refl ⟩
    H • S • H • H • S • S • H • S • S • S • ω
      ≈⟨ by-assoc Eq.refl ⟩
    [ a₃ ]ᴬ • X • S • S • S • ω
      ∎

-- Equation 3.8   (3 steps)
module M-3-8 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-8 : (S • [ a₃ ]ᴬ) ≈ ([ a₂ ]ᴬ • S • S • S • ω)
  eq-3-8 = begin
    S • [ a₃ ]ᴬ
      ≈⟨ by-assoc Eq.refl ⟩
    S • H • S • H
      ≈⟨ by-assoc-and (at (ε) (ε) L.OneQubit.SHSH) Eq.refl Eq.refl ⟩
    H • S • S • S • ω
      ≈⟨ by-assoc-and (at (H • S • S • S) (ε) (ω^-central 1 (ε))) Eq.refl Eq.refl ⟩
    H • S • S • S • ω
      ≈⟨ by-assoc Eq.refl ⟩
    [ a₂ ]ᴬ • S • S • S • ω
      ∎

-- Equation 3.9   (2 steps)
module M-3-9 {n : ℕ} where
  private Γ = (₂₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-9 : (CZ • [ a₁ ]ᴬ) ≈ ([ a₁ ]ᴬ • CZ)
  eq-3-9 = begin
    CZ • [ a₁ ]ᴬ
      ≈⟨ by-assoc Eq.refl ⟩
    CZ
      ≈⟨ by-assoc Eq.refl ⟩
    [ a₁ ]ᴬ • CZ
      ∎

-- Equation 3.44   (2 steps)
module M-3-44 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-44 : (X • [ c₁ ]ᶜ) ≈ ([ c₂ ]ᶜ)
  eq-3-44 = begin
    X • [ c₁ ]ᶜ
      ≈⟨ by-assoc Eq.refl ⟩
    H • S • S • H
      ≈⟨ by-assoc Eq.refl ⟩
    [ c₂ ]ᶜ
      ∎

-- Equation 3.45   (5 steps)
module M-3-45 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-45 : (X • [ c₂ ]ᶜ) ≈ ([ c₁ ]ᶜ)
  eq-3-45 = begin
    X • [ c₂ ]ᶜ
      ≈⟨ by-assoc Eq.refl ⟩
    H • S • S • H • H • S • S • H
      ≈⟨ by-assoc-and (at (H • S • S) (S • S • H) L.OneQubit.HH) Eq.refl Eq.refl ⟩
    H • S • S • S • S • H
      ≈⟨ by-assoc-and (at (H) (H) L.OneQubit.SSSS) Eq.refl Eq.refl ⟩
    H • H
      ≈⟨ by-assoc-and (at (ε) (ε) L.OneQubit.HH) Eq.refl Eq.refl ⟩
    ε
      ≈⟨ by-assoc Eq.refl ⟩
    [ c₁ ]ᶜ
      ∎

-- Equation 3.46   (2 steps)
module M-3-46 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-46 : (S • [ c₁ ]ᶜ) ≈ ([ c₁ ]ᶜ • S)
  eq-3-46 = begin
    S • [ c₁ ]ᶜ
      ≈⟨ by-assoc Eq.refl ⟩
    S
      ≈⟨ by-assoc Eq.refl ⟩
    [ c₁ ]ᶜ • S
      ∎

-- Equation 3.48   (2 steps)
module M-3-48 {n : ℕ} where
  private Γ = (₂₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-48 : (CZ • [ c₁ ]ᶜ) ≈ ([ c₁ ]ᶜ • CZ)
  eq-3-48 = begin
    CZ • [ c₁ ]ᶜ
      ≈⟨ by-assoc Eq.refl ⟩
    CZ
      ≈⟨ by-assoc Eq.refl ⟩
    [ c₁ ]ᶜ • CZ
      ∎

-- Equation 3.82   (2 steps)
module M-3-82 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-82 : (S • [ e₁ ]ᴱ) ≈ ([ e₂ ]ᴱ)
  eq-3-82 = begin
    S • [ e₁ ]ᴱ
      ≈⟨ by-assoc Eq.refl ⟩
    S
      ≈⟨ by-assoc Eq.refl ⟩
    [ e₂ ]ᴱ
      ∎

-- Equation 3.83   (2 steps)
module M-3-83 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-83 : (S • [ e₂ ]ᴱ) ≈ ([ e₃ ]ᴱ)
  eq-3-83 = begin
    S • [ e₂ ]ᴱ
      ≈⟨ by-assoc Eq.refl ⟩
    S • S
      ≈⟨ by-assoc Eq.refl ⟩
    [ e₃ ]ᴱ
      ∎

-- Equation 3.84   (2 steps)
module M-3-84 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-84 : (S • [ e₃ ]ᴱ) ≈ ([ e₄ ]ᴱ)
  eq-3-84 = begin
    S • [ e₃ ]ᴱ
      ≈⟨ by-assoc Eq.refl ⟩
    S • S • S
      ≈⟨ by-assoc Eq.refl ⟩
    [ e₄ ]ᴱ
      ∎

-- Equation 3.85   (3 steps)
module M-3-85 {n : ℕ} where
  private Γ = (₁₊ n) CRel,_===_
  open PB Γ
  open PP Γ using (word-setoid)
  open Assoc Γ using (by-assoc ; by-assoc-and)
  open SR word-setoid

  eq-3-85 : (S • [ e₄ ]ᴱ) ≈ ([ e₁ ]ᴱ)
  eq-3-85 = begin
    S • [ e₄ ]ᴱ
      ≈⟨ by-assoc Eq.refl ⟩
    S • S • S • S
      ≈⟨ by-assoc-and (at (ε) (ε) L.OneQubit.SSSS) Eq.refl Eq.refl ⟩
    ε
      ≈⟨ by-assoc Eq.refl ⟩
    [ e₁ ]ᴱ
      ∎

