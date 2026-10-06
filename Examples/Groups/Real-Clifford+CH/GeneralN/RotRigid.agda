------------------------------------------------------------------------
-- Presentations of groups
--
-- The rotations are rigid on wire 0, at any width with the swap of the
-- wires 1 2 given (Clément, Appendix E.5)
--
-- A network on the controls of `rot β` passes it: the swap of the wires
-- 1 2 by the module's parameter `s12` ((353) from five wires on, (127)
-- and Lemma D.5's (215) below), and every higher swap by disjointness
-- from CH and by the box's rigidity, `Canon.swaps` — the rotation being
-- CH B CH B, resp. B CH B CH, with B the box on wire 1.  Canon32 is the
-- instance from five wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Notations using (₃₊)
open import Word.Base using (_•_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)

module Examples.Groups.Real-Clifford+CH.GeneralN.RotRigid
  {m : ℕ} (C : Canon m) (s12 : ∀ β → (₃₊ m) ⊢ Ex ↑ • rot {m} β ≈ rot β • Ex ↑)
  where

open import Data.Bool using (true ; false)
open import Word.Base using ([_]ʷ ; ε)

open import Notations using (₂₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (φ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (Rigid)

private
  N : ℕ
  N = ₃₊ m

  B : Circuit N
  B = Ex ↓ • Λ□ (₂₊ m) • Ex ↓

open Tools (N VRel,_===_)

private
  pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  passL : ∀ {a b y : Circuit N} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
  passL ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

  R-gen : ∀ β (g : S.Gen (₂₊ m)) → φ g ↑ • rot β ≈ rot β • φ g ↑
  R-gen β     (S.gate₀ ())
  R-gen β     (S.gate₁ ())
  R-gen β     (S.gate₂ S.σ-gate) = s12 β
  R-gen true  (g S.↥) = pass₂ sCH (pass₂ sB (pass₂ sCH sB))
    where
    sCH : φ g ↑ ↑ • CH ≈ CH • φ g ↑ ↑
    sCH = sym (low-comm CH (φ g))
    sB : φ g ↑ ↑ • B ≈ B • φ g ↑ ↑
    sB = pass₂ (sym (low-comm Ex (φ g))) (pass₂ (Canon.swaps C [ g S.↥ ]ʷ) (sym (low-comm Ex (φ g))))
  R-gen false (g S.↥) = pass₂ sB (pass₂ sCH (pass₂ sB sCH))
    where
    sCH : φ g ↑ ↑ • CH ≈ CH • φ g ↑ ↑
    sCH = sym (low-comm CH (φ g))
    sB : φ g ↑ ↑ • B ≈ B • φ g ↑ ↑
    sB = pass₂ (sym (low-comm Ex (φ g))) (pass₂ (Canon.swaps C [ g S.↥ ]ʷ) (sym (low-comm Ex (φ g))))

rot-rigid : ∀ β → Rigid 1 (rot {m} β)
rot-rigid β [ g ]ʷ  = R-gen β g
rot-rigid β ε       = trans left-unit (sym right-unit)
rot-rigid β (u • v) = passL (rot-rigid β u) (rot-rigid β v)
