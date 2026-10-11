------------------------------------------------------------------------
-- Presentations of groups
--
-- The Hadamard-free fragment of Figure 8 decoded on four qubits, and
-- the kit of the Hadamard-free decoding there (Clément, Appendix E.5 at
-- n = 4)
--
-- Rules (20)–(34) on four qubits: the generic rule modules at m = 1,
-- with the box family of W4.Box and the rotation family of W4.Rot.  With
-- the canonical box (Canon4), its merges (Lemma87All) and W4.Kit's
-- rigidity and top merges, that is the kit Rule3637 and Letter85 take.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.Frag
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Word.Base using (Word ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free
open import Examples.Groups.Real-Clifford+CH.Decoding using (d)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (merges₂)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Kit using (Kit)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Kit complete₂ complete₃ using (rig₄ ; tm₄)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Box complete₂ complete₃ using (c335₁ ; c336₁ ; core₁ ; core′₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Rot complete₂ complete₃ using (rotcomm₁ ; braid₁ ; pairstep₁)
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule22 as Rule22
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule23 as Rule23
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule24 as Rule24
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule31 as Rule31
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule32 as Rule32

open Easy 1 using (e20 ; e21 ; e25 ; e26 ; e27 ; e28 ; e30 ; e33 ; e34)
open Invol canon4 complete₂ using (e29)
open Rule22 canon4 c335₁ c336₁ public using (e22)
open Rule23 {1} core₁ core′₁ public using (e23)
open Rule24 {1} braid₁ public using (e24)
open Rule31 canon4 complete₂ core₁ core′₁ rotcomm₁ pairstep₁ public using (e31)
open Rule32 {1} rotcomm₁ public using (e32)

-- Each rule of the fragment, decoded.
d-ax₄ : ∀ {u t : Word (GenP 4)} → 1 PF, u === t → 4 ⊢ (d ʷ) u ≈ (d ʷ) t
d-ax₄ (r20 a)                 = e20 a
d-ax₄ (r21 a b)               = e21 a b
d-ax₄ (r22 a b c)             = e22 a b c
d-ax₄ (r23 a a′ s)            = e23 a a′ s
d-ax₄ (r24 a a′ a″ s s′)      = e24 a a′ a″ s s′
d-ax₄ (r25 a a′ c s lt p)     = e25 a a′ c s lt p
d-ax₄ (r26 a a′ c s lt p)     = e26 a a′ c s lt p
d-ax₄ (r27 a c′ c s lt p)     = e27 a c′ c s lt p
d-ax₄ (r28 a c′ c s lt p)     = e28 a c′ c s lt p
d-ax₄ (r29 a a′ s)            = e29 a a′ s
d-ax₄ (r30 c a b ab ca cb)    = e30 c a b ab ca cb
d-ax₄ (r31 a a′ c s ca ca′)   = e31 a a′ c s ca ca′
d-ax₄ (r32 a a′ b b′ s s′ lt) = e32 a a′ b b′ s s′ lt
d-ax₄ (r33 b a)               = e33 b a
d-ax₄ (r34 a b c e ab ce)     = e34 a b c e ab ce

kit₄ : Kit 1
kit₄ = record
  { complete₂ = complete₂
  ; canon     = canon4
  ; merges    = merges₂
  ; tm        = tm₄
  ; rig       = rig₄
  ; d-ax      = d-ax₄
  }
