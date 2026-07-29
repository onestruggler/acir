{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Pushing a top gate through a D-box · B-box pair.
--
-- Chains BR.Two.B-Top.lemma-B-br (top gate through a B box) with
-- BR.Two.D-Bot.lemma-D-br (bottom gate through a D box):
--
--   [ d ]ᵈ • [ b ]ᵇ • [ gate₁ x₁ ↥ ]ʷ
--
-- B-Top sends the top gate through the B box, leaving a bottom-wire
-- residual (dir ↓ᵏ 1) and an updated box b'.  That bottom residual is a
-- Gen-1 word; D-Bot pushes a single bottom gate through a D box, so we
-- iterate it letter by letter (lemmaᵈ-w) to carry the whole residual
-- through the D box, ending with a top-wire residual and updated d'.
------------------------------------------------------------------------

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Nat.Primality
open import Notations

module Examples.Groups.Symplectic.BR.Two.BD-Top (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
import Examples.Groups.Symplectic.BR.Two.B-Top p-2 p-prime as BT
import Examples.Groups.Symplectic.BR.Two.D-Bot p-2 p-prime as DB

open PB (₂ QRel,_===_)
open PP (₂ QRel,_===_)
open SR word-setoid

------------------------------------------------------------------------
-- Word-level D-box push (iterate D-Bot.lemma-D-br over a bottom word).

-- pushᵈ d w = (DIR , d'): sending the bottom Gen-1 word w through the D
-- box d leaves the top residual DIR (the D-Bot residuals concatenated)
-- and the updated box d' (threaded left to right).
pushᵈ : D → Word (Gen 1) → Word (Gen 1) × D
pushᵈ d [ gate₁ H-gate ]ʷ = DB.dir-of d H-gate , DB.d'-of d H-gate
pushᵈ d [ gate₁ S-gate ]ʷ = DB.dir-of d S-gate , DB.d'-of d S-gate
pushᵈ d ε                 = ε , d
pushᵈ d (w • v)           = proj₁ r₁ • proj₁ r₂ , proj₂ r₂
  where
  r₁ = pushᵈ d w
  r₂ = pushᵈ (proj₂ r₁) v

-- [ d ]ᵈ • (w ↓ᵏ 1) ≈ (DIR ↑) • [ d' ]ᵈ, the word analogue of
-- D-Bot.lemma-D-br.  Singletons are D-Bot.lemma-D-br; a concatenation
-- threads the box and fuses the residuals (both distributions of ↓ᵏ 1
-- and ↑ over • are definitional).
lemmaᵈ-w : (d : D) (w : Word (Gen 1)) ->
  [ d ]ᵈ • (w ↓ᵏ 1) ≈ (proj₁ (pushᵈ d w) ↑) • [ proj₂ (pushᵈ d w) ]ᵈ
lemmaᵈ-w d [ gate₁ H-gate ]ʷ = DB.lemma-D-br d H-gate
lemmaᵈ-w d [ gate₁ S-gate ]ʷ = DB.lemma-D-br d S-gate
lemmaᵈ-w d ε = begin
  [ d ]ᵈ • ε ≈⟨ right-unit ⟩
  [ d ]ᵈ     ≈⟨ sym left-unit ⟩
  ε • [ d ]ᵈ ∎
lemmaᵈ-w d (w • v) = begin
  [ d ]ᵈ • ((w ↓ᵏ 1) • (v ↓ᵏ 1))   ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • (w ↓ᵏ 1)) • (v ↓ᵏ 1)   ≈⟨ cleft (lemmaᵈ-w d w) ⟩
  ((dw ↑) • [ d₁ ]ᵈ) • (v ↓ᵏ 1)    ≈⟨ assoc ⟩
  (dw ↑) • ([ d₁ ]ᵈ • (v ↓ᵏ 1))    ≈⟨ cright (lemmaᵈ-w d₁ v) ⟩
  (dw ↑) • ((dv ↑) • [ d₂ ]ᵈ)      ≈⟨ sym assoc ⟩
  ((dw ↑) • (dv ↑)) • [ d₂ ]ᵈ      ∎
  where
  r₁ = pushᵈ d w
  dw = proj₁ r₁
  d₁ = proj₂ r₁
  r₂ = pushᵈ d₁ v
  dv = proj₁ r₂
  d₂ = proj₂ r₂

------------------------------------------------------------------------
-- The chained push.

lemma-BD-Top : (d : D) (b : B) (x₁ : SympGate 1) ->
  let
  dir = BT.dir-of b x₁
  b'  = BT.b'-of b x₁
  in

  [ d ]ᵈ • [ b ]ᵇ • [ gate₁ x₁ ↥ ]ʷ ≈
    (proj₁ (pushᵈ d dir) ↑) • [ proj₂ (pushᵈ d dir) ]ᵈ • [ b' ]ᵇ
lemma-BD-Top d b x₁ = begin
  [ d ]ᵈ • [ b ]ᵇ • [ gate₁ x₁ ↥ ]ʷ         ≈⟨ cright (BT.lemma-B-br b x₁) ⟩
  [ d ]ᵈ • ((dir ↓ᵏ 1) • [ b' ]ᵇ)           ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • (dir ↓ᵏ 1)) • [ b' ]ᵇ           ≈⟨ cleft (lemmaᵈ-w d dir) ⟩
  ((DIR ↑) • [ d' ]ᵈ) • [ b' ]ᵇ             ≈⟨ assoc ⟩
  (DIR ↑) • [ d' ]ᵈ • [ b' ]ᵇ               ∎
  where
  dir = BT.dir-of b x₁
  b'  = BT.b'-of b x₁
  DIR = proj₁ (pushᵈ d dir)
  d'  = proj₂ (pushᵈ d dir)
