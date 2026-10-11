------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 at every width from five (Clément, Appendix E.5)
--
-- Every rule of Figure 8, decoded, on 5 + k qubits given completeness
-- on fewer: the rules that decode by definition (Easy), the two
-- involutions (Invol), the rules proved in Wide from the equations of
-- Appendix D, and (36), (37) (Rule3637).  With it, Theorem 8.9 asks
-- for Lemma 8.8 only on three and four qubits
-- (CompletenessInduction.Theorem-8-9‴).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.All
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; s≤s)

open import Notations using (₁₊ ; ₂₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Section8 using (Lemma-8-8)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Wide complete₂ complete₃
  using (e22 ; e23 ; e24 ; e31 ; e32 ; e38 ; e39 ; e40 ; e43 ; e44 ; e45 ; e46)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Rule3637 using (e36 ; e37)
open import Examples.Groups.Real-Clifford+CH.Lemma88.KitN complete₂ complete₃ using (kitN)
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

  open Easy (₂₊ k) using (e20 ; e21 ; e25 ; e26 ; e27 ; e28 ; e30 ; e33 ; e34 ; e35 ; e42)
  open Invol (canonN k completes) complete₂ using (e29 ; e41)

  lemma-8-8 : Lemma-8-8 (₂₊ k)
  lemma-8-8 (r20 a)                  = e20 a
  lemma-8-8 (r21 a b)                = e21 a b
  lemma-8-8 (r22 a b c)              = e22 k below a b c
  lemma-8-8 (r23 a a′ s)             = e23 k below a a′ s
  lemma-8-8 (r24 a a′ a″ s s′)       = e24 k below a a′ a″ s s′
  lemma-8-8 (r25 a a′ c s lt p)      = e25 a a′ c s lt p
  lemma-8-8 (r26 a a′ c s lt p)      = e26 a a′ c s lt p
  lemma-8-8 (r27 a c′ c s lt p)      = e27 a c′ c s lt p
  lemma-8-8 (r28 a c′ c s lt p)      = e28 a c′ c s lt p
  lemma-8-8 (r29 a a′ s)             = e29 a a′ s
  lemma-8-8 (r30 c a b ab ca cb)     = e30 c a b ab ca cb
  lemma-8-8 (r31 a a′ c s ca ca′)    = e31 k below a a′ c s ca ca′
  lemma-8-8 (r32 a a′ b b′ s s′ lt)  = e32 k below a a′ b b′ s s′ lt
  lemma-8-8 (r33 b a)                = e33 b a
  lemma-8-8 (r34 a b c e ab ce)      = e34 a b c e ab ce
  lemma-8-8 (r35 a b c e dist np)    = e35 a b c e dist np
  lemma-8-8 (r36 a b c e pb pc hp lt) = e36 (kitN k below) a b c e pb pc hp lt
  lemma-8-8 (r37 a b c e pb pc hp lt) = e37 (kitN k below) a b c e pb pc hp lt
  lemma-8-8 (r38 a a′ s le)          = e38 k below a a′ s le
  lemma-8-8 r39                      = e39 k below
  lemma-8-8 r40                      = e40 k below
  lemma-8-8 r41                      = e41
  lemma-8-8 (r42 a b c e ab ce nd)   = e42 a b c e ab ce nd
  lemma-8-8 r43                      = e43 k below
  lemma-8-8 r44                      = e44 k below
  lemma-8-8 r45                      = e45 k below
  lemma-8-8 r46                      = e46 k below
