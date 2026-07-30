------------------------------------------------------------------------
-- Presentations of groups
--
-- General-width bottom-CZ push through an M box.  Companion to
-- PushMScz.push-M-CZ (fixed at M 3), using the general-width D-vector
-- CZ push BR.Three.DD-CZ-n.gen-dd-cz in place of DD←CZ.
--
--   push-M-CZ-n :  [ m ]ᵐ • CZ ≈ dir ↑ • [ m' ]ᵐ    (M (₃₊ n))
--
-- Same shape as PushMScz: flatten M to E · Vec-D, run the D-vector CZ
-- push, commute the escaping direction out past the E box.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushMCZn (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_)
open import Data.Vec using (Vec ; _∷_ ; [])
open import Data.Fin using (toℕ)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-comm-Sᵏ-w↑)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime using (lemma-ᵐ-flat)
open import Examples.Groups.Symplectic.BR.Three.DD-CZ-n p-2 p-prime
  using (gen-dd-cz ; gen-dir-of ; gen-vd'-of)

open import Notations
open import Word.Base using (Word ; _•_ ; ε)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

  push-M-CZ-n : (m : M (₃₊ n)) →
    let (vd , e) = m in
    [ m ]ᵐ • CZ ≈ (gen-dir-of vd ↑) • [ (gen-vd'-of vd , e) ]ᵐ
  push-M-CZ-n (vd , e) = begin
    [ (vd , e) ]ᵐ • CZ                                     ≈⟨ cleft (lemma-ᵐ-flat vd e) ⟩
    ([ e ]ᵉ • [ vd ]ᵛᵈ) • CZ                              ≈⟨ assoc ⟩
    [ e ]ᵉ • ([ vd ]ᵛᵈ • CZ)                              ≈⟨ cright (gen-dd-cz vd) ⟩
    [ e ]ᵉ • ((gen-dir-of vd ↑) • [ gen-vd'-of vd ]ᵛᵈ)    ≈⟨ sym assoc ⟩
    ([ e ]ᵉ • (gen-dir-of vd ↑)) • [ gen-vd'-of vd ]ᵛᵈ    ≈⟨ cleft (lemma-comm-Sᵏ-w↑ (toℕ (- e)) (gen-dir-of vd)) ⟩
    ((gen-dir-of vd ↑) • [ e ]ᵉ) • [ gen-vd'-of vd ]ᵛᵈ    ≈⟨ assoc ⟩
    (gen-dir-of vd ↑) • ([ e ]ᵉ • [ gen-vd'-of vd ]ᵛᵈ)    ≈⟨ cright (sym (lemma-ᵐ-flat (gen-vd'-of vd) e)) ⟩
    (gen-dir-of vd ↑) • [ (gen-vd'-of vd , e) ]ᵐ          ∎
