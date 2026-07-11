------------------------------------------------------------------------
-- Presentations of groups
--
-- The LM-box push at width 2, the inj₂ shape: LM = M · A (an M column
-- followed by a single A box, no B boxes).  This is the first case where
-- the dirty gate genuinely *escapes upward* (rather than being absorbed
-- as at width 1), exercising the general-n M-side machinery.
--
--   [ (m , inj₂ a) ]ˡᵐ • S  ≈  dir ↑…  • [ (m' , inj₂ a') ]ˡᵐ
--
-- S goes through the A box (width-2 single-qupit relation), emitting a
-- power of S as its dirty gate (A-dir-S-power-S).  That S^k is then sent
-- through the whole M column by push-M-Sⁿ, escaping as its direction.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.PushLM2 (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (toℕ)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.BR.One.A p-2 p-prime
  using (dir-and-A'-of ; lemma-single-qupit-br-A)
open import Examples.Groups.Symplectic.PushMSn p-2 p-prime using (push-M-Sⁿ)

open import Notations
open import Word.Base using (Word ; _•_ ; _^_ ; [_]ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- The A-box direction for an S-gen push is always a power of S.

A-dir-S-power-S : ∀ {n} (a : A) →
  ∃ λ k → dir-and-A'-of n a S-gen tt .proj₁ ≡ S^ k
A-dir-S-power-S ((₀ , ₀) , nz)     = ⊥-elim (nz auto)
A-dir-S-power-S ((₀ , ₁₊ _) , nz)  = _ , Eq.refl
A-dir-S-power-S ((₁₊ _ , ₀) , nz)  = ₀ , Eq.refl
A-dir-S-power-S ((₁₊ _ , ₁₊ _) , nz) = ₀ , Eq.refl

------------------------------------------------------------------------
-- Pushing S through the width-2 inj₂ LM box.

push-LM2-inj₂-S : ∀ (m : M 2) (a : A) →
  let open PB (2 QRel,_===_)
      a'    = dir-and-A'-of 1 a S-gen tt .proj₂
      pr    = push-M-Sⁿ (toℕ (A-dir-S-power-S {1} a .proj₁)) m
      dir-M = proj₁ pr
      m'    = proj₁ (proj₂ pr)
  in [ (m , inj₂ a) ]ˡᵐ • S ≈ dir-M • [ (m' , inj₂ a') ]ˡᵐ
push-LM2-inj₂-S m a = begin
  ([ m ]ᵐ • [ a ]ᵃ) • S       ≈⟨ assoc ⟩
  [ m ]ᵐ • ([ a ]ᵃ • S)       ≈⟨ cright (lemma-single-qupit-br-A 1 a S-gen tt) ⟩
  [ m ]ᵐ • (dir • [ a' ]ᵃ)    ≈⟨ sym assoc ⟩
  ([ m ]ᵐ • dir) • [ a' ]ᵃ    ≈⟨ cleft (trans (refl' (Eq.cong ([ m ]ᵐ •_) dir≡)) push-Sᵏ) ⟩
  (dir-M • [ m' ]ᵐ) • [ a' ]ᵃ ≈⟨ assoc ⟩
  dir-M • ([ m' ]ᵐ • [ a' ]ᵃ) ∎
  where
  open PB (2 QRel,_===_) ; open PP (2 QRel,_===_) ; open SR word-setoid
  dir     = dir-and-A'-of 1 a S-gen tt .proj₁
  a'      = dir-and-A'-of 1 a S-gen tt .proj₂
  k       = A-dir-S-power-S {1} a .proj₁
  dir≡    = A-dir-S-power-S {1} a .proj₂
  pr      = push-M-Sⁿ (toℕ k) m
  dir-M   = proj₁ pr
  m'      = proj₁ (proj₂ pr)
  push-Sᵏ = proj₂ (proj₂ pr)

------------------------------------------------------------------------
-- The same for H: the A-box direction for an H-gen push is also a power
-- of S, so H through the inj₂ LM box goes exactly as S does.

A-dir-S-power-H : ∀ {n} (a : A) →
  ∃ λ k → dir-and-A'-of n a H-gen tt .proj₁ ≡ S^ k
A-dir-S-power-H ((₀ , ₀) , nz)     = ⊥-elim (nz auto)
A-dir-S-power-H ((₀ , ₁₊ _) , nz)  = ₀ , Eq.refl
A-dir-S-power-H ((₁₊ _ , ₀) , nz)  = ₀ , Eq.refl
A-dir-S-power-H ((₁₊ _ , ₁₊ _) , nz) = _ , Eq.refl

push-LM2-inj₂-H : ∀ (m : M 2) (a : A) →
  let open PB (2 QRel,_===_)
      a'    = dir-and-A'-of 1 a H-gen tt .proj₂
      pr    = push-M-Sⁿ (toℕ (A-dir-S-power-H {1} a .proj₁)) m
      dir-M = proj₁ pr
      m'    = proj₁ (proj₂ pr)
  in [ (m , inj₂ a) ]ˡᵐ • H ≈ dir-M • [ (m' , inj₂ a') ]ˡᵐ
push-LM2-inj₂-H m a = begin
  ([ m ]ᵐ • [ a ]ᵃ) • H       ≈⟨ assoc ⟩
  [ m ]ᵐ • ([ a ]ᵃ • H)       ≈⟨ cright (lemma-single-qupit-br-A 1 a H-gen tt) ⟩
  [ m ]ᵐ • (dir • [ a' ]ᵃ)    ≈⟨ sym assoc ⟩
  ([ m ]ᵐ • dir) • [ a' ]ᵃ    ≈⟨ cleft (trans (refl' (Eq.cong ([ m ]ᵐ •_) dir≡)) push-Sᵏ) ⟩
  (dir-M • [ m' ]ᵐ) • [ a' ]ᵃ ≈⟨ assoc ⟩
  dir-M • ([ m' ]ᵐ • [ a' ]ᵃ) ∎
  where
  open PB (2 QRel,_===_) ; open PP (2 QRel,_===_) ; open SR word-setoid
  dir     = dir-and-A'-of 1 a H-gen tt .proj₁
  a'      = dir-and-A'-of 1 a H-gen tt .proj₂
  k       = A-dir-S-power-H {1} a .proj₁
  dir≡    = A-dir-S-power-H {1} a .proj₂
  pr      = push-M-Sⁿ (toℕ k) m
  dir-M   = proj₁ pr
  m'      = proj₁ (proj₂ pr)
  push-Sᵏ = proj₂ (proj₂ pr)
