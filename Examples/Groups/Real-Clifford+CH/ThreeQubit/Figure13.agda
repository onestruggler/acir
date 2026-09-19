------------------------------------------------------------------------
-- Presentations of groups
--
-- More auxiliary equations on two qubits (Clément, Figure 13, Lemma
-- D.1)
--
-- The paper's proof is one line: "this follows directly from Lemma
-- 7.6", completeness on two qubits.  So is each proof here: the two
-- sides have the same stored matrix, by evaluation, and SemanticSteps
-- turns that into a derivation on the bottom two wires of any circuit.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₂₊)

open import Examples.Groups.Real-Clifford+CH.SemanticSteps

open Below 2 (s≤s (s≤s z≤n)) complete₂

private
  variable
    n : ℕ

-- The controlled ZX and XZ gates of Definition 2.4 on two wires, with
-- the control above (as Syntactics defines them) and below.
CZX CXZ ZXC XZC : Circuit (₂₊ n)
CZX {n} = ΛZX 1 ↓ᵏ n
CXZ {n} = ΛXZ 1 ↓ᵏ n
ZXC {n} = Ex • (ΛZX 1 ↓ᵏ n) • Ex
XZC {n} = Ex • (ΛXZ 1 ↓ᵏ n) • Ex

-- (111): P ⊗ P is an involution.
eq111 : (₂₊ n) ⊢ PP • PP ≈ ε
eq111 = by-sem (PP • PP) ε Eq.refl

-- (112): P ⊗ P commutes with the swap.
eq112 : (₂₊ n) ⊢ PP • Ex ≈ Ex • PP
eq112 = by-sem (PP • Ex) (Ex • PP) Eq.refl

-- (113): P carries H to Z.
eq113 : (₂₊ n) ⊢ H ↑ • PP ≈ PP • Z ↑
eq113 = by-sem (H ↑ • PP) (PP • Z ↑) Eq.refl

-- (114): P ⊗ P turns the controlled H upside down.
eq114 : (₂₊ n) ⊢ CH • PP ≈ PP • HC
eq114 = by-sem (CH • PP) (PP • HC) Eq.refl

-- (115), (116): the swap from three controlled ZX and XZ gates.
eq115 : (₂₊ n) ⊢ CXZ • ZXC • CXZ ≈ CZ • Ex
eq115 = by-sem (ΛXZ 1 • (Ex • ΛZX 1 • Ex) • ΛXZ 1) (CZ • Ex) Eq.refl

eq116 : (₂₊ n) ⊢ CZX • XZC • CZX ≈ Ex • CZ
eq116 = by-sem (ΛZX 1 • (Ex • ΛXZ 1 • Ex) • ΛZX 1) (Ex • CZ) Eq.refl
