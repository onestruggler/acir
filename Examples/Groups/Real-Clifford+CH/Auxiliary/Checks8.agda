------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 8 on three qubits, decided on tries: every rule of Figure 8
-- is sound for the 8 × 8 matrices (and Checks8.Base: the encoding
-- preserves the semantics of every generator)
--
-- These are the checks that pin down the transcriptions of Figure 8
-- (with its words W₁, W₂ and Σ), of the encoding of Definition 8.2
-- and of the swap and X encodings of Appendix A.4.1.  Each generic
-- rule is checked at every choice of indices satisfying its side
-- conditions, by one Boolean decision evaluated at typechecking time;
-- the evaluations are in Checks8/R* and Checks8/H*, a few thousand
-- instances per module, and this module assembles them into `sound`.
-- Every word is written out: a decision left to unification is
-- evaluated again, with free indices, at each use; and the cases are
-- stated through the abstract Sound (Checks8.Sound), so that Agda
-- compares words, not their operators.  For the same reason a word
-- mentioning toℕ pins its implicit to 8, as the evaluation modules
-- elaborate it: the rule's index has type Fin (2 ^ ₃₊ 0), and two
-- decisions that differ in that implicit are compared by unfolding.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8 where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (suc ; _∸_ ; _≤ᵇ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (code ; parity)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Encoding
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.Base
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.Sound
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R20
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R24
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R30
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R32
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R34
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R38
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.R42
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.H01
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.H23
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.H45
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.H67

open BF using (⟦_⟧Y)

------------------------------------------------------------------------
-- The rules with a free first index, assembled

private
  ok32 : ∀ a a′ b b′ → (succᵇ a a′ ⇒ succᵇ b b′ ⇒ ltᵇ (toℕ a′) (toℕ b) ⇒ decide (zx a a a′ • zx b b b′) (zx b b b′ • zx a a a′)) ≡ true
  ok32 ₀ = okR32₀
  ok32 ₁ = okR32₁
  ok32 ₂ = okR32₂
  ok32 ₃ = okR32₃
  ok32 ₄ = okR32₄
  ok32 ₅ = okR32₅
  ok32 ₆ = okR32₆
  ok32 ₇ = okR32₇
  ok34 : ∀ a b c d → (neqᵇ a b ⇒ neqᵇ c d ⇒ decide (xx a b c d) (zx a a b • zx b c d)) ≡ true
  ok34 ₀ = okR34₀
  ok34 ₁ = okR34₁
  ok34 ₂ = okR34₂
  ok34 ₃ = okR34₃
  ok34 ₄ = okR34₄
  ok34 ₅ = okR34₅
  ok34 ₆ = okR34₆
  ok34 ₇ = okR34₇
  ok42 : ∀ a b c d → (neqᵇ a b ⇒ neqᵇ c d ⇒ not (distinct4 (toℕ a) (toℕ b) (toℕ c) (toℕ d)) ⇒ decide (hhℕ (toℕ a) (toℕ b) (proj₁ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d))) • hhℕ (proj₁ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d))) (proj₂ (twoSmallest (toℕ a) (toℕ b) (toℕ c) (toℕ d))) (toℕ c) (toℕ d)) (hh a b c d)) ≡ true
  ok42 ₀ = okR42₀
  ok42 ₁ = okR42₁
  ok42 ₂ = okR42₂
  ok42 ₃ = okR42₃
  ok42 ₄ = okR42₄
  ok42 ₅ = okR42₅
  ok42 ₆ = okR42₆
  ok42 ₇ = okR42₇
  okH : ∀ a b c d → (chkH′ (hpat (code₃ a) (code₃ b) (code₃ c) (code₃ d)) a b c d) ≡ true
  okH ₀ = okRH₀
  okH ₁ = okRH₁
  okH ₂ = okRH₂
  okH ₃ = okRH₃
  okH ₄ = okRH₄
  okH ₅ = okRH₅
  okH ₆ = okRH₆
  okH ₇ = okRH₇

------------------------------------------------------------------------
-- Soundness of Figure 8 at n = 3

sound : ∀ {u t} → 0 P, u === t → Sound u t
sound (r20 a)       = sound-by (zz a a) ε (ok20 a)
sound (r21 a b)     = sound-by (zz a b) (zz b a) (ok21 a b)
sound (r22 a b c)   = sound-by (zz a b • zz b c) (zz a c) (ok22 a b c)
sound (r23 a a′ s)  = sound-by (zz a a′) (zx a a a′ • zx a a a′) (⇒-true (ok23 a a′) (succ-true s))
sound (r24 a a′ a″ s s′) =
  sound-by (zx a a a′ • zx a′ a′ a″ • zx a a a′) (zx a′ a′ a″ • zx a a a′ • zx a′ a′ a″)
    (⇒-true (⇒-true (ok24 a a′ a″) (succ-true s)) (succ-true s′))
sound (r25 a a′ c s lt odd) =
  sound-by (zx a a c) (zx a′ a a′ • zx a′ a′ c • zx a a a′)
    (⇒-true (⇒-true (⇒-true (ok25 a a′ c) (succ-true s)) (lt-true lt)) (bool-true odd))
sound (r26 a a′ c s lt odd) =
  sound-by (zx c a c) (zx a′ a a′ • zx c a′ c • zx a a a′)
    (⇒-true (⇒-true (⇒-true (ok26 a a′ c) (succ-true s)) (lt-true lt)) (bool-true odd))
sound (r27 a c′ c s lt ev) =
  sound-by (zx a a c) (zx c′ c′ c • zx a a c′ • zx c c′ c)
    (⇒-true (⇒-true (⇒-true (ok27 a c′ c) (succ-true s)) (lt-true lt)) (bool-true ev))
sound (r28 a c′ c s lt ev) =
  sound-by (zx c a c) (zx c′ c′ c • zx c′ a c′ • zx c c′ c)
    (⇒-true (⇒-true (⇒-true (ok28 a c′ c) (succ-true s)) (lt-true lt)) (bool-true ev))
sound (r29 a a′ s)  = sound-by (zx a a a′ • zx a′ a a′) ε (⇒-true (ok29 a a′) (succ-true s))
sound (r30 c a b ab p q) =
  sound-by (zx c a b) (zz c a • zx a a b)
    (⇒-true (⇒-true (⇒-true (ok30 c a b) (neq-true ab)) (neq-true p)) (neq-true q))
sound (r31 a a′ c s p q) =
  sound-by (zz a′ c • zx a a a′) (zx a a a′ • zz a c)
    (⇒-true (⇒-true (⇒-true (ok31 a a′ c) (succ-true s)) (neq-true p)) (neq-true q))
sound (r32 a a′ b b′ s s′ lt) =
  sound-by (zx a a a′ • zx b b b′) (zx b b b′ • zx a a a′)
    (⇒-true (⇒-true (⇒-true (ok32 a a′ b b′) (succ-true s)) (succ-true s′)) (lt-true lt))
sound (r33 b a)     = sound-by (zx b a b) (zx b b a) (ok33 b a)
sound (r34 a b c d ab cd) =
  sound-by (xx a b c d) (zx a a b • zx b c d)
    (⇒-true (⇒-true (ok34 a b c d) (neq-true ab)) (neq-true cd))
sound (r35 a b c d dist pat) =
  sound-by (hh a b c d) (Σ (toℕ {8} a) (toℕ {8} b) (toℕ {8} c) (toℕ {8} d) • hh₀₁₃₂ • Σ′ (toℕ {8} a) (toℕ {8} b) (toℕ {8} c) (toℕ {8} d))
    (⇒-true (Eq.subst (λ v → chkH′ v a b c d ≡ true) pat (okH a b c d)) dist)
sound (r36 a b c d pb pc pat lt) =
  sound-by (hh a b c d) (W₁ (code₃ a) pc pb)
    (⇒-true (∧-left (Eq.subst (λ v → chkH′ v a b c d ≡ true) pat (okH a b c d))) (lt-true lt))
sound (r37 a b c d pb pc pat lt) =
  sound-by (hh a b c d) (W₂ (code₃ a) pb pc)
    (⇒-true (∧-right (Eq.subst (λ v → chkH′ v a b c d ≡ true) pat (okH a b c d))) (lt-true lt))
sound (r38 a a′ s ge) =
  sound-by (zx a a a′ • hh₀₁₃₂) (hh₀₁₃₂ • zx a a a′) (⇒-true (⇒-true (ok38 a a′) (succ-true s)) (le-true ge))
sound r39 = sound-by (zzℕ 0 1 • hh₀₁₃₂) (hh₀₁₃₂ • zzℕ 0 1) ok39
sound r40 = sound-by (zzℕ 3 4 • hh₀₁₃₂) (hh₀₁₃₂ • zzℕ 3 4 • zxℕ 2 2 3) ok40
sound r41 = sound-by (hh₀₁₃₂ • hh₀₁₃₂) ε ok41
sound (r42 a b c d ab cd nd) =
  sound-by (hhℕ (toℕ {8} a) (toℕ {8} b) (proj₁ (twoSmallest (toℕ {8} a) (toℕ {8} b) (toℕ {8} c) (toℕ {8} d))) (proj₂ (twoSmallest (toℕ {8} a) (toℕ {8} b) (toℕ {8} c) (toℕ {8} d))) • hhℕ (proj₁ (twoSmallest (toℕ {8} a) (toℕ {8} b) (toℕ {8} c) (toℕ {8} d))) (proj₂ (twoSmallest (toℕ {8} a) (toℕ {8} b) (toℕ {8} c) (toℕ {8} d))) (toℕ {8} c) (toℕ {8} d)) (hh a b c d)
    (⇒-true (⇒-true (⇒-true (ok42 a b c d) (neq-true ab)) (neq-true cd)) (Eq.cong not nd))
sound r43 = sound-by (hhℕ 0 1 3 2 • hhℕ 3 2 4 5) (xxℕ 0 3 1 2 • hhℕ 3 2 4 5 • xxℕ 0 3 1 2) ok43
sound r44 = sound-by (xxℕ 0 3 1 2 • hhℕ 0 1 3 2) (hhℕ 0 1 3 2 • xxℕ 0 3 1 2) ok44
sound r45 =
  sound-by (hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6 • zzℕ 0 1 • hhℕ 0 3 1 2)
               (hhℕ 0 3 1 2 • zzℕ 0 1 • hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6) ok45
sound r46 =
  sound-by (hhℕ 0 1 7 6 • hhℕ 0 3 1 2 • hhℕ 3 4 2 5 • hhℕ 3 2 4 5 • hhℕ 7 6 4 5 • zzℕ 2 3 • hhℕ 3 4 2 5 • hhℕ 0 3 1 2)
               (hhℕ 0 3 1 2 • hhℕ 3 4 2 5 • zzℕ 2 3 • hhℕ 7 6 4 5 • hhℕ 3 2 4 5 • hhℕ 3 4 2 5 • hhℕ 0 3 1 2 • hhℕ 0 1 7 6) ok46

-- Every rule of Figure 8 is sound for the 8 × 8 matrices.
sound-Figure8 : ∀ {u t} → 0 P, u === t → ⟦ u ⟧Y ~ ⟦ t ⟧Y
sound-Figure8 r = unSound (sound r)
