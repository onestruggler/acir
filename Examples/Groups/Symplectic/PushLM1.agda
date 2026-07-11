------------------------------------------------------------------------
-- Presentations of groups
--
-- The LM-box push at width 1 — the end-to-end base case of the coset
-- update, exercising the whole "push through L, then push the dirty gate
-- through M" pipeline in miniature.
--
--   [ lm ]ˡᵐ • [ g ]ʷ  ≈  [ lm' ]ˡᵐ
--
-- At width 1, LM 1 = M 1 × L' 1 = E × A, so [ lm ]ˡᵐ = [ e ]ᵉ • [ a ]ᵃ.
-- The generator g first goes through the A box (single-qupit box
-- relation), which — crucially — emits only a *power of S* as its dirty
-- gate (A-dir-S-power).  That S^k is then swallowed by the E box
-- (push-E-S^, e ↦ e − k).  There is no escaping direction: width 1 has
-- no wire above to carry one.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.PushLM1 (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Empty using (⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.BR.OneQupit p-2 p-prime
  using (dir-and-A'-of ; lemma-single-qupit-br-A)
open import Examples.Groups.Symplectic.PushMScz p-2 p-prime using (push-E-S^)

open import Notations
open import Word.Base using (Word ; _•_ ; [_]ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- Every A-box push emits a power of S (ε = S^ ₀ included).

A-dir-S-power : ∀ (a : A) (g : Gen 1) →
  ∃ λ k → dir-and-A'-of a g .proj₁ ≡ S^ k
A-dir-S-power ((₀ , ₀) , nz)     _     = ⊥-elim (nz auto)
A-dir-S-power ((₀ , ₁₊ _) , nz)  H-gen = ₀ , Eq.refl
A-dir-S-power ((₁₊ _ , ₀) , nz)  H-gen = ₀ , Eq.refl
A-dir-S-power ((₁₊ _ , ₁₊ _) , nz) H-gen = _ , Eq.refl
A-dir-S-power ((₀ , ₁₊ _) , nz)  S-gen = _ , Eq.refl
A-dir-S-power ((₁₊ _ , ₀) , nz)  S-gen = ₀ , Eq.refl
A-dir-S-power ((₁₊ _ , ₁₊ _) , nz) S-gen = ₀ , Eq.refl

------------------------------------------------------------------------
-- The width-1 LM push.

push-LM1 : ∀ (e : E) (a : A) (g : Gen 1) →
  let open PB (1 QRel,_===_)
      a' = dir-and-A'-of a g .proj₂
      k  = A-dir-S-power a g .proj₁
  in [ (e , a) ]ˡᵐ • [ g ]ʷ ≈ [ (e + - k , a') ]ˡᵐ
push-LM1 e a g = begin
  ([ e ]ᵉ • [ a ]ᵃ) • [ g ]ʷ   ≈⟨ assoc ⟩
  [ e ]ᵉ • ([ a ]ᵃ • [ g ]ʷ)   ≈⟨ cright (lemma-single-qupit-br-A a g) ⟩
  [ e ]ᵉ • (dir • [ a' ]ᵃ)     ≈⟨ sym assoc ⟩
  ([ e ]ᵉ • dir) • [ a' ]ᵃ     ≈⟨ cleft (trans (refl' (Eq.cong ([ e ]ᵉ •_) dir≡)) (push-E-S^ e k)) ⟩
  [ e + - k ]ᵉ • [ a' ]ᵃ       ∎
  where
  open PB (1 QRel,_===_) ; open PP (1 QRel,_===_) ; open SR word-setoid
  dir  = dir-and-A'-of a g .proj₁
  a'   = dir-and-A'-of a g .proj₂
  k    = A-dir-S-power a g .proj₁
  dir≡ = A-dir-S-power a g .proj₂
