------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing a top-H-free bottom word W (a Word (Gen 2)) through an M box.
-- Companion to PushMCZn.push-M-CZ-n, but for an arbitrary word instead
-- of a single CZ.
--
--   * push-Mʷ2   : width 2 (single D box).  Flatten M to E · (one D box),
--                  run the word-level single-box push D-w.lemma-D-w-br,
--                  fold the emitted bottom S-power into the E box, commute
--                  the escaping residual out past E.
--   * push-Mʷ-suc: width (₃₊ n) (≥ 2 D boxes).  Flatten and run the whole
--                  word through the D-vector via DVecPush.dvec-word (whose
--                  residual is already a clean dir ↑ — no bottom S-power),
--                  then commute out past E.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushMword (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃ ; ∃-syntax)
open import Data.Vec using (Vec ; _∷_ ; [])
open import Data.Fin using (toℕ)
import Relation.Binary.PropositionalEquality as Eq

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-comm-Sᵏ-w↑)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime using (lemma-ᵐ-flat)
open import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime using (push-D-w ; lemma-D-w-br ; No-Top-H)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime using (dvec-word)
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Notations
open import Word.Base using (Word ; _•_ ; ε)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

-- Fold the bottom S-power e' emitted by the D-box push into the E box:
-- [ e ]ᵉ • S^ e' ≈ [ e + - e' ]ᵉ, using -e + e' ≡ - (e + - e').
private
  eqE : ∀ (e e' : ℤ ₚ) → - e + e' Eq.≡ - (e + - e')
  eqE e e' = Eq.trans (Eq.cong (- e +_) (Eq.sym (-‿involutive e'))) (-‿+-comm e (- e'))

------------------------------------------------------------------------
-- Width-2 base case (single D box).

module _ where
  open PB (2 QRel,_===_)
  open PP (2 QRel,_===_)
  open SR word-setoid
  open Lemmas0 1

  private
    fold-E : ∀ (e e' : ℤ ₚ) → [ e ]ᵉ • S^ e' ≈ [ e + - e' ]ᵉ
    fold-E e e' = trans (lemma-S^k+l (- e) e') (refl' (Eq.cong S^ (eqE e e')))

  push-Mʷ2 : (d₀ : D) (e : E) (W : Word (Gen 2)) (ntW : No-Top-H W) →
    let (e' , dir , d₀') = push-D-w d₀ W ntW in
    [ (d₀ ∷ [] , e) ]ᵐ • W ≈ dir ↑ • [ (d₀' ∷ [] , e + - e') ]ᵐ
  push-Mʷ2 d₀ e W ntW = begin
    [ (d₀ ∷ [] , e) ]ᵐ • W                            ≈⟨ cleft (lemma-ᵐ-flat (d₀ ∷ []) e) ⟩
    ([ e ]ᵉ • ([ d₀ ]ᵈ • ε)) • W                      ≈⟨ cleft (cright right-unit) ⟩
    ([ e ]ᵉ • [ d₀ ]ᵈ) • W                            ≈⟨ assoc ⟩
    [ e ]ᵉ • ([ d₀ ]ᵈ • W)                            ≈⟨ cright (lemma-D-w-br d₀ W ntW) ⟩
    [ e ]ᵉ • (S^ e' ↓ • (dir ↑ • [ d₀' ]ᵈ))          ≈⟨ sym assoc ⟩
    ([ e ]ᵉ • S^ e' ↓) • (dir ↑ • [ d₀' ]ᵈ)          ≈⟨ cleft (fold-E e e') ⟩
    [ e + - e' ]ᵉ • (dir ↑ • [ d₀' ]ᵈ)               ≈⟨ sym assoc ⟩
    ([ e + - e' ]ᵉ • dir ↑) • [ d₀' ]ᵈ               ≈⟨ cleft (lemma-comm-Sᵏ-w↑ (toℕ (- (e + - e'))) dir) ⟩
    (dir ↑ • [ e + - e' ]ᵉ) • [ d₀' ]ᵈ               ≈⟨ assoc ⟩
    dir ↑ • ([ e + - e' ]ᵉ • [ d₀' ]ᵈ)               ≈⟨ cright (sym (trans (lemma-ᵐ-flat (d₀' ∷ []) (e + - e')) (cright right-unit))) ⟩
    dir ↑ • [ (d₀' ∷ [] , e + - e') ]ᵐ               ∎
    where
    e'  = push-D-w d₀ W ntW .proj₁
    dir = push-D-w d₀ W ntW .proj₂ .proj₁
    d₀' = push-D-w d₀ W ntW .proj₂ .proj₂

------------------------------------------------------------------------
-- General width (M (₃₊ n), i.e. ≥ 2 D boxes): flatten, push the whole
-- word through the D-vector via DVecPush.dvec-word (clean dir ↑ residual,
-- no bottom S-power to absorb), commute the residual out past the E box.

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

  push-Mʷ-suc : (m : M (₃₊ n)) (W : Word (Gen 2)) →
    let (vd , e) = m in
    ∃[ dir ] ∃[ m' ] ([ m ]ᵐ • (W ↓ᵏ (₁₊ n)) ≈ (dir ↑) • [ m' ]ᵐ)
  push-Mʷ-suc (vd , e) W =
    let (dir , vd' , eq) = dvec-word W vd
    in dir , (vd' , e) , (begin
      [ (vd , e) ]ᵐ • (W ↓ᵏ (₁₊ n))              ≈⟨ cleft (lemma-ᵐ-flat vd e) ⟩
      ([ e ]ᵉ • [ vd ]ᵛᵈ) • (W ↓ᵏ (₁₊ n))        ≈⟨ assoc ⟩
      [ e ]ᵉ • ([ vd ]ᵛᵈ • (W ↓ᵏ (₁₊ n)))        ≈⟨ cright eq ⟩
      [ e ]ᵉ • ((dir ↑) • [ vd' ]ᵛᵈ)             ≈⟨ sym assoc ⟩
      ([ e ]ᵉ • (dir ↑)) • [ vd' ]ᵛᵈ             ≈⟨ cleft (lemma-comm-Sᵏ-w↑ (toℕ (- e)) dir) ⟩
      ((dir ↑) • [ e ]ᵉ) • [ vd' ]ᵛᵈ             ≈⟨ assoc ⟩
      (dir ↑) • ([ e ]ᵉ • [ vd' ]ᵛᵈ)             ≈⟨ cright (sym (lemma-ᵐ-flat vd' e)) ⟩
      (dir ↑) • [ (vd' , e) ]ᵐ                   ∎)
