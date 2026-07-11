------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing the remaining dirty gates — S↑ and CZ — through an M box.
-- Companions to PushM (S) and PushMSn (S^j).  Together with those, the
-- M column can absorb every dirty gate an L-push can produce
-- ({S, S↑, CZ}), so the hard H-through-M rule is never needed.
--
--   push-M-S↑ :  [ m ]ᵐ • S ↑ ≈ S • [ m ]ᵐ           (M 2 base)
--   push-M-CZ :  [ m ]ᵐ • CZ  ≈ dir ↑ • [ m' ]ᵐ       (M 3, via DD←CZ)
--
-- S↑ descends past the bottom D box to a plain S (aux-DS↑, box
-- unchanged) and commutes out past the E box.  CZ is handled by the
-- complete Vec-D-2 relation DD←CZ, its escaping direction then commuting
-- out past E.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.PushMScz (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; ∃)
open import Data.Vec using (_∷_ ; [])
open import Data.Fin using (toℕ)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Symplectic p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-comm-Sᵏ-w↑)
open import Examples.Groups.Symplectic.LM-Sym p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.Pushing.DS p-2 p-prime using (aux-DS↑)
open import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime
  using (lemma-dir-and-vd') renaming (dir-of to ddcz-dir ; vd'-of to ddcz-vd')
open import Examples.Groups.Symplectic.BoxRelations p-2 p-prime
open Two using (D←H-S↑-S-CZ)

open import Notations
open import Word.Base using (Word ; _•_ ; ε)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- Pushing S ↑ through the base M box (M 2 = E × one D box).
-- S ↑ descends to a plain S; the box is unchanged.

push-M-S↑ : (m : M 2) →
  let open PB (2 QRel,_===_) in
  ∃ λ (dir : Word (Gen 2)) → ∃ λ (m' : M 2) → [ m ]ᵐ • S ↑ ≈ dir • [ m' ]ᵐ
push-M-S↑ (e , x ∷ []) = S , (e , x ∷ []) , claim
  where
  open PB (2 QRel,_===_) ; open PP (2 QRel,_===_) ; open SR word-setoid
  open Lemmas0 1
  comm-e-S : [ e ]ᵉ • S ≈ S • [ e ]ᵉ
  comm-e-S = begin
    [ e ]ᵉ • S      ≈⟨ lemma-S^k+l (- e) ₁ ⟩
    S^ (- e + ₁)    ≈⟨ refl' (Eq.cong S^ (+-comm (- e) ₁)) ⟩
    S^ (₁ + - e)    ≈⟨ sym (lemma-S^k+l ₁ (- e)) ⟩
    S • [ e ]ᵉ      ∎
  claim : ([ e ]ᵉ • ([ x ]ᵈ • ε)) • S ↑ ≈ S • ([ e ]ᵉ • ([ x ]ᵈ • ε))
  claim = begin
    ([ e ]ᵉ • ([ x ]ᵈ • ε)) • S ↑   ≈⟨ cong (cright right-unit) refl ⟩
    ([ e ]ᵉ • [ x ]ᵈ) • S ↑         ≈⟨ assoc ⟩
    [ e ]ᵉ • ([ x ]ᵈ • S ↑)         ≈⟨ cright (aux-DS↑ x) ⟩
    [ e ]ᵉ • (S • [ x ]ᵈ)           ≈⟨ sym assoc ⟩
    ([ e ]ᵉ • S) • [ x ]ᵈ           ≈⟨ cleft comm-e-S ⟩
    (S • [ e ]ᵉ) • [ x ]ᵈ           ≈⟨ assoc ⟩
    S • ([ e ]ᵉ • [ x ]ᵈ)           ≈⟨ cright (sym (cright right-unit)) ⟩
    S • ([ e ]ᵉ • ([ x ]ᵈ • ε))     ∎

------------------------------------------------------------------------
-- Pushing CZ through the M box M 3 = E × Vec D 2, via DD←CZ.

push-M-CZ : (m : M 3) →
  let open PB (3 QRel,_===_) in
  ∃ λ (dir : Word (Gen 3)) → ∃ λ (m' : M 3) → [ m ]ᵐ • CZ ≈ dir • [ m' ]ᵐ
push-M-CZ (e , vd) = ddcz-dir vd ↑ , (e , ddcz-vd' vd) , claim
  where
  open PB (3 QRel,_===_) ; open PP (3 QRel,_===_) ; open SR word-setoid
  claim : ([ e ]ᵉ • [ vd ]ᵛᵈ) • CZ
        ≈ ddcz-dir vd ↑ • ([ e ]ᵉ • [ ddcz-vd' vd ]ᵛᵈ)
  claim = begin
    ([ e ]ᵉ • [ vd ]ᵛᵈ) • CZ                       ≈⟨ assoc ⟩
    [ e ]ᵉ • ([ vd ]ᵛᵈ • CZ)                       ≈⟨ cright (lemma-dir-and-vd' vd) ⟩
    [ e ]ᵉ • (ddcz-dir vd ↑ • [ ddcz-vd' vd ]ᵛᵈ)   ≈⟨ sym assoc ⟩
    ([ e ]ᵉ • ddcz-dir vd ↑) • [ ddcz-vd' vd ]ᵛᵈ   ≈⟨ cleft (lemma-comm-Sᵏ-w↑ (toℕ (- e)) (ddcz-dir vd)) ⟩
    (ddcz-dir vd ↑ • [ e ]ᵉ) • [ ddcz-vd' vd ]ᵛᵈ   ≈⟨ assoc ⟩
    ddcz-dir vd ↑ • ([ e ]ᵉ • [ ddcz-vd' vd ]ᵛᵈ)   ∎

------------------------------------------------------------------------
-- The E box absorbs an S-power: this is how the M column (at its base)
-- swallows the S^k dirty an A-box push emits.  e ↦ e − k, no direction.

push-E-S^ : ∀ {n} (e k : ℤ ₚ) →
  let open PB ((₁₊ n) QRel,_===_) in
  [ e ]ᵉ • S^ k ≈ [ e + - k ]ᵉ
push-E-S^ {n} e k = begin
  [ e ]ᵉ • S^ k      ≈⟨ lemma-S^k+l (- e) k ⟩
  S^ (- e + k)       ≈⟨ refl' (Eq.cong S^ pf) ⟩
  S^ (- (e + - k))   ∎
  where
  open PB ((₁₊ n) QRel,_===_) ; open PP ((₁₊ n) QRel,_===_) ; open SR word-setoid
  open Lemmas0 n
  pf : - e + k ≡ - (e + - k)
  pf = Eq.trans (Eq.cong (- e +_) (Eq.sym (-‿involutive k))) (-‿+-comm e (- k))

------------------------------------------------------------------------
-- CZ through a single a = 0 D box: absorbed, b ↦ b − 1, no direction.
-- (b is split only to force dir-of/d'-of of the unified D relation to
-- reduce.)

D-CZ-a0 : ∀ (b : ℤ ₚ) →
  let open PB (2 QRel,_===_) in [ (₀ , b) ]ᵈ • CZ ≈ [ (₀ , b + - ₁) ]ᵈ
D-CZ-a0 ₀        = trans (D←H-S↑-S-CZ (₀ , ₀) CZ-gen (λ ())) simp
  where open PB (2 QRel,_===_) ; open PP (2 QRel,_===_)
        simp = trans (cright left-unit) left-unit
D-CZ-a0 (₁₊ b') = trans (D←H-S↑-S-CZ (₀ , ₁₊ b') CZ-gen (λ ())) simp
  where open PB (2 QRel,_===_) ; open PP (2 QRel,_===_)
        simp = trans (cright left-unit) left-unit

-- CZ through the width-2 M box M 2 = E × one (a = 0) D box.
push-M-CZ-M2-a0 : ∀ (e : E) (b : ℤ ₚ) →
  let open PB (2 QRel,_===_) in
  [ (e , (₀ , b) ∷ []) ]ᵐ • CZ ≈ [ (e , (₀ , b + - ₁) ∷ []) ]ᵐ
push-M-CZ-M2-a0 e b = begin
  ([ e ]ᵉ • ([ (₀ , b) ]ᵈ • ε)) • CZ    ≈⟨ cong (cright right-unit) refl ⟩
  ([ e ]ᵉ • [ (₀ , b) ]ᵈ) • CZ          ≈⟨ assoc ⟩
  [ e ]ᵉ • ([ (₀ , b) ]ᵈ • CZ)          ≈⟨ cright (D-CZ-a0 b) ⟩
  [ e ]ᵉ • [ (₀ , b + - ₁) ]ᵈ           ≈⟨ cright (sym right-unit) ⟩
  [ e ]ᵉ • ([ (₀ , b + - ₁) ]ᵈ • ε)     ∎
  where open PB (2 QRel,_===_) ; open PP (2 QRel,_===_) ; open SR word-setoid
