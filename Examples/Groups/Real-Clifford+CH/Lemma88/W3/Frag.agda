------------------------------------------------------------------------
-- Presentations of groups
--
-- The Hadamard-free fragment of Figure 8 decoded on three qubits, and
-- the kit of the Hadamard-free decoding there (Clément, Appendix E.5 at
-- n = 3)
--
-- Rules (20)–(34) on three qubits: the generic rule modules at m = 0,
-- with the box family of W3.Box and the rotation family of W3.Rot.  With
-- the canonical box (Canon3), its merges (Lemma87Three) and W3.Kit's
-- rigidity and top merges, that is the kit Rule3637 and Letter85 take.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W3.Frag
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Word.Base using (Word ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free
open import Examples.Groups.Real-Clifford+CH.Decoding using (d)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon3 complete₂ using (canon3)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Three complete₂ using (merges₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Kit using (Kit)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Kit complete₂ using (rig₃ ; tm₃)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Box complete₂ using (c335₀ ; c336₀ ; core₀ ; core′₀)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Rot complete₂ using (rotcomm₀ ; braid₀ ; pairstep₀)
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule22 as Rule22
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule23 as Rule23
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule24 as Rule24
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule31 as Rule31
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule32 as Rule32

open Easy 0 using (e20 ; e21 ; e25 ; e26 ; e27 ; e28 ; e30 ; e33 ; e34)
open Invol canon3 complete₂ using (e29)
open Rule22 canon3 c335₀ c336₀ public using (e22)
open Rule23 {0} core₀ core′₀ public using (e23)
open Rule24 {0} braid₀ public using (e24)
open Rule31 canon3 complete₂ core₀ core′₀ rotcomm₀ pairstep₀ public using (e31)
open Rule32 {0} rotcomm₀ public using (e32)

-- Each rule of the fragment, decoded.
d-ax₃ : ∀ {u t : Word (GenP 3)} → 0 PF, u === t → 3 ⊢ (d ʷ) u ≈ (d ʷ) t
d-ax₃ (r20 a)                 = e20 a
d-ax₃ (r21 a b)               = e21 a b
d-ax₃ (r22 a b c)             = e22 a b c
d-ax₃ (r23 a a′ s)            = e23 a a′ s
d-ax₃ (r24 a a′ a″ s s′)      = e24 a a′ a″ s s′
d-ax₃ (r25 a a′ c s lt p)     = e25 a a′ c s lt p
d-ax₃ (r26 a a′ c s lt p)     = e26 a a′ c s lt p
d-ax₃ (r27 a c′ c s lt p)     = e27 a c′ c s lt p
d-ax₃ (r28 a c′ c s lt p)     = e28 a c′ c s lt p
d-ax₃ (r29 a a′ s)            = e29 a a′ s
d-ax₃ (r30 c a b ab ca cb)    = e30 c a b ab ca cb
d-ax₃ (r31 a a′ c s ca ca′)   = e31 a a′ c s ca ca′
d-ax₃ (r32 a a′ b b′ s s′ lt) = e32 a a′ b b′ s s′ lt
d-ax₃ (r33 b a)               = e33 b a
d-ax₃ (r34 a b c e ab ce)     = e34 a b c e ab ce

kit₃ : Kit 0
kit₃ = record
  { complete₂ = complete₂
  ; canon     = canon3
  ; merges    = merges₁
  ; tm        = tm₃
  ; rig       = rig₃
  ; d-ax      = d-ax₃
  }
