------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing a no-↥ Word (Gen 2) (only wire-0 gates gate₁ x and the wire-0,1
-- gate CZ — exactly the shape of every L2-CZ residual) through a lifted
-- B-vector:
--
--   [ vb ]ᵛᵇ ↑ • (W ↓ᵏ m) ≈ res • [ vb ]ᵛᵇ ↑
--
-- The vector is left unchanged: wire-0 letters commute past the lift
-- (lemma-comm-{H,S}-w↑), and CZ letters cross via PushBvcz.bvec↑-cz
-- (residual Wof vb).  This generalises bvec↑-cz from a single CZ to an
-- arbitrary no-↥ residual word, by structural recursion on the word.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushBword (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (∃ ; _,_)
open import Data.Vec using (Vec)
open import Data.Fin using (toℕ)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open Lemmas-Sym using (lemma-comm-H-w↑ ; lemma-comm-S-w↑)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBvcz p-2 p-prime
  using (bvec↑-cz ; Wof)

open import Notations
open import Word.Base using (Word ; _•_ ; ε ; [_]ʷ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- Generators / words with no top (↥) component: wire-0 unary gates and CZ.

NoTopGen : Gen 2 → Set
NoTopGen (gate₁ x) = ⊤
NoTopGen (gate₂ x) = ⊤
NoTopGen (g ↥)     = ⊥

data No-Top : Word (Gen 2) → Set where
  sg   : ∀ {g} → NoTopGen g → No-Top [ g ]ʷ
  εⁿ   : No-Top ε
  _•ⁿ_ : ∀ {u v} → No-Top u → No-Top v → No-Top (u • v)

-- No-Top closure for the box-word vocabulary (wire-0 S powers and CZ powers).
nt-S : No-Top S
nt-S = sg tt
nt-CZ : No-Top CZ
nt-CZ = sg tt
nt-^ : ∀ {w} → No-Top w → (k : ℕ) → No-Top (w ^ k)
nt-^ nw ₀        = εⁿ
nt-^ nw (₁₊ ₀)   = nw
nt-^ nw (₂₊ k)   = nw •ⁿ nt-^ nw (₁₊ k)
nt-S^ : (k : ℤ ₚ) → No-Top (S^ k)
nt-S^ k = nt-^ nt-S (toℕ k)
nt-CZ^ : (k : ℤ ₚ) → No-Top (CZ^ k)
nt-CZ^ k = nt-^ nt-CZ (toℕ k)

------------------------------------------------------------------------
-- The push.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid

  bvec-word : (W : Word (Gen 2)) → No-Top W → (vb : Vec B m) →
    ∃ λ res → [ vb ]ᵛᵇ ↑ • (W ↓ᵏ m) ≈ res • [ vb ]ᵛᵇ ↑
  bvec-word ε                   εⁿ            vb = ε , trans right-unit (sym left-unit)
  bvec-word [ gate₁ H-gate ]ʷ   _             vb = H     , sym (lemma-comm-H-w↑ [ vb ]ᵛᵇ)
  bvec-word [ gate₁ S-gate ]ʷ   _             vb = S     , sym (lemma-comm-S-w↑ [ vb ]ᵛᵇ)
  bvec-word [ gate₂ CZ-gate ]ʷ  _             vb = Wof vb , bvec↑-cz vb
  bvec-word [ g ↥ ]ʷ            (sg ())       vb
  bvec-word (u • v)             (ntu •ⁿ ntv)  vb =
    let (ru , equ) = bvec-word u ntu vb
        (rv , eqv) = bvec-word v ntv vb
    in (ru • rv) , (begin
      [ vb ]ᵛᵇ ↑ • ((u ↓ᵏ m) • (v ↓ᵏ m))   ≈⟨ sym assoc ⟩
      ([ vb ]ᵛᵇ ↑ • (u ↓ᵏ m)) • (v ↓ᵏ m)   ≈⟨ cleft equ ⟩
      (ru • [ vb ]ᵛᵇ ↑) • (v ↓ᵏ m)         ≈⟨ assoc ⟩
      ru • ([ vb ]ᵛᵇ ↑ • (v ↓ᵏ m))         ≈⟨ cright eqv ⟩
      ru • (rv • [ vb ]ᵛᵇ ↑)               ≈⟨ sym assoc ⟩
      (ru • rv) • [ vb ]ᵛᵇ ↑               ∎)
