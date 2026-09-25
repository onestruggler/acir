------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding of Definition 8.3 on three qubits: checks that a decoded
-- letter has the matrix of the letter
--
-- D(p) is a circuit of multi-controlled gates read off the Gray codes
-- of the indices of p (Decoding, MultiControlled).  Here its stored
-- matrix is compared with that of p: for every sign pair and every
-- signed exchange on eight indices (`zz-all`, `zx-all`), and on samples
-- of the exchange pairs and of the Hadamard pairs, on and off the
-- H-pattern and with repeated indices.  The circuit is read by row
-- operations and compared by one boolean (Evaluation, Semantics.Decide);
-- read as a dense product and compared by `mat-dec`, as this module
-- first did, a decoded letter cost about 1.27ⁿ in its n gates and only
-- the five letters under 43 gates were within reach, where a Hadamard
-- pair off the H-pattern has some 1800.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks where

open import Data.Bool using (Bool ; true)
open import Data.Bool.ListAction using (all)
open import Data.List using (allFin)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧ ; len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R ; ⟦⟧R-ix)
open import Examples.Groups.Real-Clifford+CH.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (⟦_⟧ᴳ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx ; xx ; hh)
open import Examples.Groups.Real-Clifford+CH.Decoding using () renaming (d to D)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])
import Examples.Groups.Real-Clifford+CH.BackAndForth as BackAndForth

module BF = BackAndForth 3 (0 P,_===_) ⟦_⟧ᴾ
open BF using (⟦_⟧Y)

------------------------------------------------------------------------
-- The stored reading of a word over P, and the decision

private
  ⟦_⟧GM : G.Gen 8 → Mat 3
  ⟦ g ⟧GM = matOf (proj₂ ⟦ g ⟧ᴳ)

  ⟦_⟧PM : Word (GenP 3) → Mat 3
  ⟦ [ −1−1 a b ]ʷ ⟧PM       = mulM ⟦ −1[ a ] ⟧GM ⟦ −1[ b ] ⟧GM
  ⟦ [ −1X c a b _ ]ʷ ⟧PM    = mulM ⟦ −1[ c ] ⟧GM ⟦ X[ a , b ] ⟧GM
  ⟦ [ XX a b c d _ _ ]ʷ ⟧PM = mulM ⟦ X[ a , b ] ⟧GM ⟦ X[ c , d ] ⟧GM
  ⟦ [ HH a b c d _ _ ]ʷ ⟧PM = mulM ⟦ H[ a , b ] ⟧GM ⟦ H[ c , d ] ⟧GM
  ⟦ ε ⟧PM                   = idM
  ⟦ u • t ⟧PM               = mulM ⟦ u ⟧PM ⟦ t ⟧PM

  pair-ix : (g h : G.Gen 8) → (proj₂ ⟦ g ⟧ᴳ ⊙ proj₂ ⟦ h ⟧ᴳ) ≐ ix (mulM ⟦ g ⟧GM ⟦ h ⟧GM)
  pair-ix g h = ≐-trans (⊙-cong (≐-sym (ix-matOf (proj₂ ⟦ g ⟧ᴳ))) (≐-sym (ix-matOf (proj₂ ⟦ h ⟧ᴳ)))) (≐-sym (ix-mul ⟦ g ⟧GM ⟦ h ⟧GM))

  Y-ix : (u : Word (GenP 3)) → proj₂ ⟦ u ⟧Y ≐ ix ⟦ u ⟧PM
  Y-ix [ −1−1 a b ]ʷ       = pair-ix −1[ a ] −1[ b ]
  Y-ix [ −1X c a b _ ]ʷ    = pair-ix −1[ c ] X[ a , b ]
  Y-ix [ XX a b c d _ _ ]ʷ = pair-ix X[ a , b ] X[ c , d ]
  Y-ix [ HH a b c d _ _ ]ʷ = pair-ix H[ a , b ] H[ c , d ]
  Y-ix ε                   = ≐-sym ix-id
  Y-ix (u • t)             = ≐-trans (⊙-cong (Y-ix u) (Y-ix t)) (≐-sym (ix-mul ⟦ u ⟧PM ⟦ t ⟧PM))

-- A circuit and a word over P with the same matrix, decided.
decideD : Circuit 3 → Word (GenP 3) → Bool
decideD w u = eqM (scaleM (√2^ proj₁ ⟦ u ⟧Y) ⟦ w ⟧R) (scaleM (√2^ len w) ⟦ u ⟧PM)

decideD-sound : (w : Circuit 3) (u : Word (GenP 3)) → decideD w u ≡ true → ⟦ w ⟧ ~ ⟦ u ⟧Y
decideD-sound w u eq =
  ≐-trans (·-cong Eq.refl (⟦⟧R-ix w))
    (≐-trans (≐-sym (ix-scaleM _ _))
      (≐-trans (ix-≡ (eqM-sound _ _ eq))
        (≐-trans (ix-scaleM _ _) (·-cong Eq.refl (≐-sym (Y-ix u))))))

------------------------------------------------------------------------
-- The letters checked
--
-- The Gray codes of 0 … 7, top wire first: 000, 001, 011, 010, 110,
-- 111, 101, 100.

private
  check : Word (GenP 3) → Bool
  check u = decideD ((D ʷ) u) u

-- Every sign pair (−1)_[a] (−1)_[b]: boxes on every wire, and chains of
-- up to seven of them.
zz-all : all (λ a → all (λ b → check (zz a b)) (allFin 8)) (allFin 8) ≡ true
zz-all = Eq.refl

-- Every signed exchange (−1)_[c] X_[a,b]: on its own pair, in either
-- order of the pair, and with the sign elsewhere.
zx-all : all (λ c → all (λ a → all (λ b → check (zx c a b)) (allFin 8)) (allFin 8)) (allFin 8) ≡ true
zx-all = Eq.refl

-- Exchange pairs X_[a,b] X_[c,d].
xx-0123 : check (xx ₀ ₁ ₂ ₃) ≡ true
xx-0123 = Eq.refl

xx-0725 : check (xx ₀ ₇ ₂ ₅) ≡ true
xx-0725 = Eq.refl

xx-6134 : check (xx ₆ ₁ ₃ ₄) ≡ true
xx-6134 = Eq.refl

-- Hadamard pairs of the H-pattern: the all-white gate, a black
-- control, and the other order of the two varying wires.
hh-0132 : check (hh ₀ ₁ ₃ ₂) ≡ true
hh-0132 = Eq.refl

hh-7645 : check (hh ₇ ₆ ₄ ₅) ≡ true
hh-7645 = Eq.refl

hh-0312 : check (hh ₀ ₃ ₁ ₂) ≡ true
hh-0312 = Eq.refl

-- Off the H-pattern: Definition E.1's words around the gadget.
hh-0246 : check (hh ₀ ₂ ₄ ₆) ≡ true
hh-0246 = Eq.refl

hh-1527 : check (hh ₁ ₅ ₂ ₇) ≡ true
hh-1527 = Eq.refl

-- Repeated indices: the pair is split over two fresh ones.
hh-0102 : check (hh ₀ ₁ ₀ ₂) ≡ true
hh-0102 = Eq.refl

-- As statements about the semantics.
D-zz-01 : ⟦ (D ʷ) (zz ₀ ₁) ⟧ ~ ⟦ zz ₀ ₁ ⟧Y
D-zz-01 = decideD-sound ((D ʷ) (zz ₀ ₁)) (zz ₀ ₁) Eq.refl

D-hh-0132 : ⟦ (D ʷ) (hh ₀ ₁ ₃ ₂) ⟧ ~ ⟦ hh ₀ ₁ ₃ ₂ ⟧Y
D-hh-0132 = decideD-sound ((D ʷ) (hh ₀ ₁ ₃ ₂)) (hh ₀ ₁ ₃ ₂) hh-0132
