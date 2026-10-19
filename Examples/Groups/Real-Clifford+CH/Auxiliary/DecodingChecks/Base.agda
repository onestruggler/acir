------------------------------------------------------------------------
-- Presentations of groups
--
-- The decision behind DecodingChecks: a decoded letter against the
-- letter, by their stored matrices
--
-- The circuit is read by row operations and compared by one boolean
-- (Evaluation, Semantics.Decide).  The checks themselves are in
-- DecodingChecks and, eight modules for the 512 signed exchanges,
-- DecodingChecks.ZX0 … ZX7: each check is evaluated where it is stated,
-- so a module of its own is what keeps each file short.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.Base where

open import Data.Bool using (Bool ; true)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧ ; len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R ; ⟦⟧R-ix)
open import Examples.Groups.Real-Clifford+CH.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (⟦_⟧ᴳ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Decoding using () renaming (d to D)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])
import Examples.Groups.Real-Clifford+CH.BackAndForth as BackAndForth

module BF = BackAndForth 3 (0 P,_===_) ⟦_⟧ᴾ
open BF public using (⟦_⟧Y)

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

-- A letter of P against its decoding.
check : Word (GenP 3) → Bool
check u = decideD ((D ʷ) u) u
