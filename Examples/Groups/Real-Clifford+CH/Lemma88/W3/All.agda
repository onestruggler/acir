------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on three qubits (Clément, Appendix E.5 at n = 3)
--
-- Every rule of Figure 8 on three qubits, decoded, is an equation of
-- the circuit theory, from completeness on two qubits and Lemma D.2:
-- the rules that decode by definition (Easy, Invol), the generic rule
-- modules at m = 0 with the canonical facts of W3 — the box family
-- (Box), the rotation family (Rot), the gadget (HG), the closed cores
-- (Cores, Eq361) — and (36), (37) over the kit of W3.Frag.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W3.All
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Section8 using (Lemma-8-8)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon3 complete₂ using (canon3)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Rule3637 using (e36 ; e37)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Frag complete₂ using (e22 ; e23 ; e24 ; e31 ; e32 ; kit₃)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.HG complete₂ using (hgrot₀)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Cores complete₂ using (core39₀ ; core40₀ ; core45₀ ; core46₀)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Eq361 complete₂ using (core43₀ ; core44₀)
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule38 as Rule38
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule39 as Rule39
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule40 as Rule40
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule43 as Rule43
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule44 as Rule44
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule45 as Rule45
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule46 as Rule46

open Easy 0 using (e20 ; e21 ; e25 ; e26 ; e27 ; e28 ; e30 ; e33 ; e34 ; e35 ; e42)
open Invol canon3 complete₂ using (e29 ; e41)
open Rule38 {0} hgrot₀ using (e38)
open Rule39 {0} core39₀ using (e39)
open Rule40 {0} core40₀ using (e40)
open Rule43 {0} core43₀ using (e43)
open Rule44 {0} core44₀ using (e44)
open Rule45 {0} core45₀ using (e45)
open Rule46 {0} core46₀ using (e46)

lemma-8-8₃ : Lemma-8-8 0
lemma-8-8₃ (r20 a)                  = e20 a
lemma-8-8₃ (r21 a b)                = e21 a b
lemma-8-8₃ (r22 a b c)              = e22 a b c
lemma-8-8₃ (r23 a a′ s)             = e23 a a′ s
lemma-8-8₃ (r24 a a′ a″ s s′)       = e24 a a′ a″ s s′
lemma-8-8₃ (r25 a a′ c s lt p)      = e25 a a′ c s lt p
lemma-8-8₃ (r26 a a′ c s lt p)      = e26 a a′ c s lt p
lemma-8-8₃ (r27 a c′ c s lt p)      = e27 a c′ c s lt p
lemma-8-8₃ (r28 a c′ c s lt p)      = e28 a c′ c s lt p
lemma-8-8₃ (r29 a a′ s)             = e29 a a′ s
lemma-8-8₃ (r30 c a b ab ca cb)     = e30 c a b ab ca cb
lemma-8-8₃ (r31 a a′ c s ca ca′)    = e31 a a′ c s ca ca′
lemma-8-8₃ (r32 a a′ b b′ s s′ lt)  = e32 a a′ b b′ s s′ lt
lemma-8-8₃ (r33 b a)                = e33 b a
lemma-8-8₃ (r34 a b c e ab ce)      = e34 a b c e ab ce
lemma-8-8₃ (r35 a b c e dist np)    = e35 a b c e dist np
lemma-8-8₃ (r36 a b c e pb pc hp lt) = e36 kit₃ a b c e pb pc hp lt
lemma-8-8₃ (r37 a b c e pb pc hp lt) = e37 kit₃ a b c e pb pc hp lt
lemma-8-8₃ (r38 a a′ s le)          = e38 a a′ s le
lemma-8-8₃ r39                      = e39
lemma-8-8₃ r40                      = e40
lemma-8-8₃ r41                      = e41
lemma-8-8₃ (r42 a b c e ab ce nd)   = e42 a b c e ab ce nd
lemma-8-8₃ r43                      = e43
lemma-8-8₃ r44                      = e44
lemma-8-8₃ r45                      = e45
lemma-8-8₃ r46                      = e46
