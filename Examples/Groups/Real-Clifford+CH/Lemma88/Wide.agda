------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 at width 5 + k, from completeness at every smaller width
-- (Clément, Appendix E.5)
--
-- The rules of Figure 8 whose decodings are proved so far with the
-- general-width machinery of GeneralN: (22), from (335) and (336)
-- (BoxComm); (23), from (355) in both signs (ZX355); (24), from (358)
-- placed (BraidAnywhere); (31), from (355), (351)/(352) and the pair
-- step of RotPair; (32), from (351)/(352) placed (RotAnywhere); (38),
-- from (348)–(350) placed (HGAnywhere, Canon38); (39),
-- from (338) with x = y (Box338Eq); (40),
-- from (353) and (339) (Canon40); (43), from (361), (360) and the
-- D-trick (Canon43); (44), from (361) — Lemma 8.5, (354)
-- and (355) (Canon361) — and (338) (Canon44); (45), from (333) and
-- the three-qubit proof of (146) (Canon45); and (46), from (337) and
-- the D-trick, (338) and (339) under relabellings and (335), (336)
-- (Canon46a, Canon46b).  Completeness below the
-- width is the paper's own induction (CompletenessInduction).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Notations using (₁₊ ; ₂₊ ; ₄₊)

module Examples.Groups.Real-Clifford+CH.Lemma88.Wide
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (s≤s)

open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (eq335 ; eq336ᶜ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HGAnywhere complete₂ complete₃ using (hgrot)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule38 as Rule38
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule22 as Rule22
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX355 complete₂ complete₃ using (eq355 ; eq355′)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule23 as Rule23
open import Examples.Groups.Real-Clifford+CH.GeneralN.BraidAnywhere complete₂ complete₃ using (braid)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule24 as Rule24
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotPair complete₂ complete₃ using (pair-step)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule31 as Rule31
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhere complete₂ complete₃ using (rot-comm)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule32 as Rule32
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon40 complete₂ complete₃ using (core40)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon43 complete₂ complete₃ using (core43)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule43 as Rule43
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule39 as Rule39
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule40 as Rule40
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon44 complete₂ complete₃ using (core44)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule44 as Rule44
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon45 complete₂ complete₃ using (core45)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule45 as Rule45
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon46b complete₂ complete₃ using (core46)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule46 as Rule46

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

  -- (22)
  open Rule22 (canonN k completes) (eq335 k below) (eq336ᶜ k below) public using (e22)

  -- (23)
  open Rule23 {₂₊ k} (eq355 k below) (eq355′ k below) public using (e23)

  -- (24)
  open Rule24 {₂₊ k} (braid k below) public using (e24)

  -- (31)
  open Rule31 (canonN k completes) complete₂ (eq355 k below) (eq355′ k below) (rot-comm k below) (pair-step k below)
    public using (e31)

  -- (32)
  open Rule32 {₂₊ k} (rot-comm k below) public using (e32)

  -- (38)
  open Rule38 {₂₊ k} (hgrot k below) public using (e38)

  -- (39)
  open Rule39 {₂₊ k} (XY.core39 k below) public using (e39)

  -- (40)
  open Rule40 {₂₊ k} (core40 k below) public using (e40)

  -- (43)
  open Rule43 {₂₊ k} (core43 k below) public using (e43)

  -- (44)
  open Rule44 {₂₊ k} (core44 k below) public using (e44)

  -- (45)
  open Rule45 {₂₊ k} (core45 k below) public using (e45)

  -- (46)
  open Rule46 {₂₊ k} (core46 k below) public using (e46)
