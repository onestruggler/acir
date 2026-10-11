------------------------------------------------------------------------
-- Presentations of groups
--
-- The pair step placed anywhere, at any width with its canonical case
-- given (Clément, Appendix E.5, the proof of rule (31))
--
-- A placed rotation against a placed box whose colouring agrees with
-- the rotation's off the two targets is turned over by it.  A network
-- bringing the two targets to the wires 0 1 (Placed.bring₂) makes them
-- the canonical rotation and the box on wire 1, coloured relatively on
-- the wires 0 1 only (PlaceFrames.frame-agree, col-rel′), which is the
-- canonical pair step `k1`.  The parameters are the rigidity on wire 0
-- of the box and of the rotations, and `k1`; RotPair supplies them from
-- five wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Notations using (₂₊)
open import Examples.Groups.Real-Clifford+CH.Syntactics using (Λ□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (Rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; PairCanon)

module Examples.Groups.Real-Clifford+CH.GeneralN.PairFrom
  {m : ℕ} (rigΛ : Rigid 1 (Λ□ (₂₊ m))) (rig : ∀ β → Rigid 1 (rot {m} β)) (k1 : PairCanon m)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (s≤s ; z≤n)
open import Data.Product using (_,_)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)

open import Notations using (₁₊ ; ₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swW ; combine)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place ; bring₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (PairStep)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames
  using (reflect′ ; col-rel′ ; frame-0 ; frame-1 ; frame-agree)

private
  N : ℕ
  N = ₃₊ m

  Λ B : Circuit N
  Λ = Λ□ (₂₊ m)
  B = Ex ↓ • Λ • Ex ↓

open Tools (N VRel,_===_)

pair-step : PairStep m
pair-step β u u′ t t′ t′t pu pu′ s s′ agree with bring₂ t t′ t′t
... | σ , σt , σt′ = reflect′ σ (begin
  pl (revS σ) (place u s (rot β)) • pl (revS σ) (place u′ s′ Λ)
    ≈⟨ cong (frame-0 (rig β) σ u t pu σt s) (frame-1 rigΛ σ u′ t′ pu′ σt′ s′) ⟩
  col x (rot β) • col y B
    ≈⟨ col-rel′ x y (Eq.subst (λ w → rot β • col w B ≈ col w B • rot (not β)) (Eq.sym zs)
                              (k1 β (lookupℕ 0 z) (lookupℕ 1 z))) ⟩
  col y B • col x (rot (not β))
    ≈⟨ sym (cong (frame-1 rigΛ σ u′ t′ pu′ σt′ s′) (frame-0 (rig (not β)) σ u t pu σt s)) ⟩
  pl (revS σ) (place u′ s′ Λ) • pl (revS σ) (place u s (rot (not β))) ∎)
  where
  x y z : Bits N
  x = swW (revS σ) s
  y = swW (revS σ) s′
  z = combine x y
  zs : z ≡ lookupℕ 0 z ∷ lookupℕ 1 z ∷ replicate (₁₊ m) true
  zs = frame-agree σ t t′ σt σt′ s s′ agree
