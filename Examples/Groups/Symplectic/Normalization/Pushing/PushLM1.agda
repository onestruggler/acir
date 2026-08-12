------------------------------------------------------------------------
-- Presentations of groups
--
-- The LM-box push at width 1 — the end-to-end base case of the coset
-- update, exercising the whole "push through L, then push the dirty gate
-- through M" pipeline in miniature.
--
--   [ lm ]ᵐˡ • [ g ]ʷ  ≈  [ lm' ]ᵐˡ
--
-- At width 1, ML 1 = M 1 × L' 1 = E × A, so [ lm ]ᵐˡ = [ e ]ᵉ • [ a ]ᵃ.
-- The generator g first goes through the A box (single-qupit box
-- relation), which — crucially — emits only a *power of S* as its dirty
-- gate (A-dir-S-power).  That S^k is then swallowed by the E box
-- (push-E-S^, e ↦ e − k).  There is no escaping direction.
--
-- Stated over the E · A box product at arbitrary width (₁₊ n) — at width
-- 1 this is exactly [ (e , a) ]ᵐˡ • [ g ]ʷ.  g is a bottom-wire single
-- gate (S or H); the hypothesis Bottom-Wire-Single rules out CZ and any
-- lifted gate, which never enter the single-qupit A box.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushLM1 (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Empty using (⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.BR.One.A p-2 p-prime
  using (dir-and-A'-of ; lemma-single-qupit-br-A ; Bottom-Wire-Single)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMScz p-2 p-prime using (push-E-S^)

open import Notations
open import Word.Base using (_•_ ; [_]ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- Every A-box push emits a power of S (ε = S^ ₀ included).

A-dir-S-power : ∀ {n} (a : A) (g : Gen (₁₊ n)) (bws : Bottom-Wire-Single n g) →
  ∃ λ k → dir-and-A'-of n a g bws .proj₁ ≡ S^ k
A-dir-S-power ((₀ , ₀) , nz)     _     bws = ⊥-elim (nz auto)
A-dir-S-power ((₀ , ₁₊ _) , nz)  H-gen bws = ₀ , Eq.refl
A-dir-S-power ((₁₊ _ , ₀) , nz)  H-gen bws = ₀ , Eq.refl
A-dir-S-power ((₁₊ _ , ₁₊ _) , nz) H-gen bws = _ , Eq.refl
A-dir-S-power ((₀ , ₁₊ _) , nz)  S-gen bws = _ , Eq.refl
A-dir-S-power ((₁₊ _ , ₀) , nz)  S-gen bws = ₀ , Eq.refl
A-dir-S-power ((₁₊ _ , ₁₊ _) , nz) S-gen bws = ₀ , Eq.refl
A-dir-S-power _ CZ-gen ()
A-dir-S-power _ (_ ↥)  ()

------------------------------------------------------------------------
-- The E · A push at width (₁₊ n).

push-LM1 : ∀ {n} (e : E) (a : A) (g : Gen (₁₊ n)) (bws : Bottom-Wire-Single n g) →
  let open PB ((₁₊ n) QRel,_===_)
      a' = dir-and-A'-of n a g bws .proj₂
      k  = A-dir-S-power a g bws .proj₁
  in ([ e ]ᵉ • [ a ]ᵃ) • [ g ]ʷ ≈ [ e + - k ]ᵉ • [ a' ]ᵃ
push-LM1 {n} e a g bws = begin
  ([ e ]ᵉ • [ a ]ᵃ) • [ g ]ʷ   ≈⟨ assoc ⟩
  [ e ]ᵉ • ([ a ]ᵃ • [ g ]ʷ)   ≈⟨ cright (lemma-single-qupit-br-A n a g bws) ⟩
  [ e ]ᵉ • (dir • [ a' ]ᵃ)     ≈⟨ sym assoc ⟩
  ([ e ]ᵉ • dir) • [ a' ]ᵃ     ≈⟨ cleft (trans (refl' (Eq.cong ([ e ]ᵉ •_) dir≡)) (push-E-S^ e k)) ⟩
  [ e + - k ]ᵉ • [ a' ]ᵃ       ∎
  where
  open PB ((₁₊ n) QRel,_===_) ; open PP ((₁₊ n) QRel,_===_) ; open SR word-setoid
  dir  = dir-and-A'-of n a g bws .proj₁
  a'   = dir-and-A'-of n a g bws .proj₂
  k    = A-dir-S-power a g bws .proj₁
  dir≡ = A-dir-S-power a g bws .proj₂
