------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on the Hadamard-free fragment, and Corollary A.5 decoded
-- (Clément, Appendix E.5)
--
-- At width 5 + k every rule (20)–(34) of the fragment is decoded to an
-- equation (Easy, Invol, and Wide's (22), (23), (24), (31), (32)), so the
-- decoding respects the fragment's congruence (`d-≈`; `d ʷ` is a monoid
-- map by definition).  With Corollary A.5 (Auxiliary/Unique.A5), two
-- Hadamard-free words with the same signed permutation have equivalent
-- decodings (`dA5`): any Hadamard-free identity of P-words that holds
-- on signed permutations holds of the decoded circuits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.Free
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; s≤s)
open import Word.Base using (Word ; _ʷ)
import Presentation.Base as PB

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free
open import Examples.Groups.Real-Clifford+CH.Decoding using (d)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Wide complete₂ complete₃ using (e22 ; e23 ; e24 ; e31 ; e32)
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol
import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique as Unique
import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm as SignedPerm
import Examples.Groups.Real-Clifford+CH.Auxiliary.NF as NF
import Examples.Groups.Real-Clifford+CH.Lemma88.FreeGen as FreeGen

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    m N : ℕ
    m = ₂₊ k
    N = ₃₊ m

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

  open Tools (N VRel,_===_)
  open Easy m using (e20 ; e21 ; e25 ; e26 ; e27 ; e28 ; e30 ; e33 ; e34)
  open Invol (canonN k completes) complete₂ using (e29)

  -- Each rule of the fragment, decoded.
  d-ax : ∀ {u t : Word (GenP N)} → m PF, u === t → (d ʷ) u ≈ (d ʷ) t
  d-ax (r20 a)                 = e20 a
  d-ax (r21 a b)               = e21 a b
  d-ax (r22 a b c)             = e22 k below a b c
  d-ax (r23 a a′ s)            = e23 k below a a′ s
  d-ax (r24 a a′ a″ s s′)      = e24 k below a a′ a″ s s′
  d-ax (r25 a a′ c s lt p)     = e25 a a′ c s lt p
  d-ax (r26 a a′ c s lt p)     = e26 a a′ c s lt p
  d-ax (r27 a c′ c s lt p)     = e27 a c′ c s lt p
  d-ax (r28 a c′ c s lt p)     = e28 a c′ c s lt p
  d-ax (r29 a a′ s)            = e29 a a′ s
  d-ax (r30 c a b ab ca cb)    = e30 c a b ab ca cb
  d-ax (r31 a a′ c s ca ca′)   = e31 k below a a′ c s ca ca′
  d-ax (r32 a a′ b b′ s s′ lt) = e32 k below a a′ b b′ s s′ lt
  d-ax (r33 b a)               = e33 b a
  d-ax (r34 a b c e ab ce)     = e34 a b c e ab ce

  open FreeGen {m} d-ax public using (d-≈ ; dA5)
