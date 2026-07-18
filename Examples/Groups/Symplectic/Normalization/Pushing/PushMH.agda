------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing a "dirty" H-gate through an M box (the X-normal column
-- M = E · [Vec D]).  Companion to Examples.Groups.Symplectic.PushM,
-- which does the same for an S-gate.
--
--   [ m ]ᵐ • H  ≈  dir ↑ • [ m' ]ᵐ
--
-- As with S, the pushed H lives on the *bottom* wire only: it commutes
-- freely past every ↑-lifted upper D box (lemma-comm-H-w↑), so it only
-- ever meets the bottom D box.  There it turns into a direction gate on
-- the wires above (dirDH x ↑) plus an updated box (d'DH x); the freed
-- direction then commutes back left past the bottom E box E = S^(−e)
-- (lemma-comm-Sᵏ-w↑, which holds for an arbitrary lifted word).
--
-- The bottom-box push itself — [ d ]ᵈ • H ≈ dirDH d ↑ • [ d'DH d ]ᵈ — is
-- taken as a parameter (auxDH).  Its S-counterpart aux-DS is complete in
-- Pushing.DS, but the H-counterpart in Pushing.DH is presently
-- commented-out scaffold (its four cases still contain holes), so this
-- file proves the *assembly* unconditionally and leaves auxDH abstract.
-- Once auxDH is discharged the M-box H-push becomes concrete with no
-- further work.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushMH (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; ∃)
open import Data.Vec using (Vec ; _∷_)
open import Data.Fin using (toℕ)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-comm-H-w↑ ; lemma-comm-Sᵏ-w↑)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open import Notations
open import Word.Base using (Word ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- Pushing an H-gate through an M box, given the bottom-box push auxDH.

module _ {n : ℕ}
  (dirDH : D → Word (Gen (₁₊ n)))
  (d'DH  : D → D)
  (auxDH : (d : D) → let open PB ((₂₊ n) QRel,_===_) in
                     [ d ]ᵈ • H ≈ dirDH d ↑ • [ d'DH d ]ᵈ)
  where

  push-M-H : (m : M (₂₊ n)) →
    let open PB ((₂₊ n) QRel,_===_) in
    ∃ λ (dir : Word (Gen (₂₊ n))) → ∃ λ (m' : M (₂₊ n)) → [ m ]ᵐ • H ≈ dir • [ m' ]ᵐ
  push-M-H (e , x ∷ v) = dirDH x ↑ , (e , d'DH x ∷ v) , claim
    where
    open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
    claim : ([ e ]ᵉ • ([ x ]ᵈ • [ v ]ᵛᵈ ↑)) • H
          ≈ dirDH x ↑ • ([ e ]ᵉ • ([ d'DH x ]ᵈ • [ v ]ᵛᵈ ↑))
    claim = begin
      ([ e ]ᵉ • ([ x ]ᵈ • [ v ]ᵛᵈ ↑)) • H              ≈⟨ assoc ⟩
      [ e ]ᵉ • (([ x ]ᵈ • [ v ]ᵛᵈ ↑) • H)              ≈⟨ cright assoc ⟩
      [ e ]ᵉ • ([ x ]ᵈ • ([ v ]ᵛᵈ ↑ • H))              ≈⟨ cright (cright (sym (lemma-comm-H-w↑ [ v ]ᵛᵈ))) ⟩
      [ e ]ᵉ • ([ x ]ᵈ • (H • [ v ]ᵛᵈ ↑))              ≈⟨ cright (sym assoc) ⟩
      [ e ]ᵉ • (([ x ]ᵈ • H) • [ v ]ᵛᵈ ↑)              ≈⟨ cright (cleft (auxDH x)) ⟩
      [ e ]ᵉ • ((dirDH x ↑ • [ d'DH x ]ᵈ) • [ v ]ᵛᵈ ↑) ≈⟨ cright assoc ⟩
      [ e ]ᵉ • (dirDH x ↑ • ([ d'DH x ]ᵈ • [ v ]ᵛᵈ ↑)) ≈⟨ sym assoc ⟩
      ([ e ]ᵉ • dirDH x ↑) • ([ d'DH x ]ᵈ • [ v ]ᵛᵈ ↑) ≈⟨ cleft (lemma-comm-Sᵏ-w↑ (toℕ (- e)) (dirDH x)) ⟩
      (dirDH x ↑ • [ e ]ᵉ) • ([ d'DH x ]ᵈ • [ v ]ᵛᵈ ↑) ≈⟨ assoc ⟩
      dirDH x ↑ • ([ e ]ᵉ • ([ d'DH x ]ᵈ • [ v ]ᵛᵈ ↑)) ∎
