------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on four qubits (Clément, Appendix E.5 at n = 4)
--
-- Every rule of Figure 8 on four qubits, decoded, is an equation of the
-- circuit theory, from completeness on two and three qubits and Lemma
-- D.5: the rules that decode by definition (Easy, Invol), the generic
-- rule modules at m = 1 with the canonical facts of W4 — the box family
-- (Box), the rotation family (Rot), the gadget (HG), the closed cores
-- (Cores, Eq361, Core45, Core46) — and (36), (37) over the kit of
-- W4.Frag.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.All
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Section8 using (Lemma-8-8)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Rule3637 using (e36 ; e37)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Frag complete₂ complete₃ using (e22 ; e23 ; e24 ; e31 ; e32 ; kit₄)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.HG complete₂ complete₃ using (hgrot₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Cores complete₂ complete₃ using (core39₁ ; core40₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Eq361 complete₂ complete₃ using (core43₁ ; core44₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Core45 complete₂ complete₃ using (core45₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Core46 complete₂ complete₃ using (core46₁)
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule38 as Rule38
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule39 as Rule39
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule40 as Rule40
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule43 as Rule43
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule44 as Rule44
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule45 as Rule45
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule46 as Rule46

open Easy 1 using (e20 ; e21 ; e25 ; e26 ; e27 ; e28 ; e30 ; e33 ; e34 ; e35 ; e42)
open Invol canon4 complete₂ using (e29 ; e41)
open Rule38 {1} hgrot₁ using (e38)
open Rule39 {1} core39₁ using (e39)
open Rule40 {1} core40₁ using (e40)
open Rule43 {1} core43₁ using (e43)
open Rule44 {1} core44₁ using (e44)
open Rule45 {1} core45₁ using (e45)
open Rule46 {1} core46₁ using (e46)

lemma-8-8₄ : Lemma-8-8 1
lemma-8-8₄ (r20 a)                  = e20 a
lemma-8-8₄ (r21 a b)                = e21 a b
lemma-8-8₄ (r22 a b c)              = e22 a b c
lemma-8-8₄ (r23 a a′ s)             = e23 a a′ s
lemma-8-8₄ (r24 a a′ a″ s s′)       = e24 a a′ a″ s s′
lemma-8-8₄ (r25 a a′ c s lt p)      = e25 a a′ c s lt p
lemma-8-8₄ (r26 a a′ c s lt p)      = e26 a a′ c s lt p
lemma-8-8₄ (r27 a c′ c s lt p)      = e27 a c′ c s lt p
lemma-8-8₄ (r28 a c′ c s lt p)      = e28 a c′ c s lt p
lemma-8-8₄ (r29 a a′ s)             = e29 a a′ s
lemma-8-8₄ (r30 c a b ab ca cb)     = e30 c a b ab ca cb
lemma-8-8₄ (r31 a a′ c s ca ca′)    = e31 a a′ c s ca ca′
lemma-8-8₄ (r32 a a′ b b′ s s′ lt)  = e32 a a′ b b′ s s′ lt
lemma-8-8₄ (r33 b a)                = e33 b a
lemma-8-8₄ (r34 a b c e ab ce)      = e34 a b c e ab ce
lemma-8-8₄ (r35 a b c e dist np)    = e35 a b c e dist np
lemma-8-8₄ (r36 a b c e pb pc hp lt) = e36 kit₄ a b c e pb pc hp lt
lemma-8-8₄ (r37 a b c e pb pc hp lt) = e37 kit₄ a b c e pb pc hp lt
lemma-8-8₄ (r38 a a′ s le)          = e38 a a′ s le
lemma-8-8₄ r39                      = e39
lemma-8-8₄ r40                      = e40
lemma-8-8₄ r41                      = e41
lemma-8-8₄ (r42 a b c e ab ce nd)   = e42 a b c e ab ce nd
lemma-8-8₄ r43                      = e43
lemma-8-8₄ r44                      = e44
lemma-8-8₄ r45                      = e45
lemma-8-8₄ r46                      = e46
