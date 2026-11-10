------------------------------------------------------------------------
-- Presentations of groups
--
-- Letter lists written as strings, for the generated derivations
--
-- The four-wire derivations are long lists of steps on long lists of
-- letters.  As in Qutrit-Clifford's Letters, a letter list is written
-- as a string, ℓ "suT…", one character per letter:
--
--     a b d f     X on the wires 0, 1, 2, 3
--     c e g       CX with target 0, 1, 2 and the control one wire up
--     s t u       Ex on the wires 0 1, 1 2, 2 3
--     T U         CCX with target 0, 1 and the controls above it
--
-- ℓ₃ reads the letters of three wires (a b d, c e, s t, T) and ℓʰ the
-- NOT gates and swaps of Frames.  The steps of a derivation are
-- functions of an index and strings, without parentheses, and the
-- evidence of a step that evaluation decides is a hidden argument of
-- type T …, which is ⊤ once evaluated and solved by eta.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Letters where

open import Data.Bool.Base using (Bool ; true ; false ; T)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String ; toList)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Examples.Groups.Alt16-RevCir.Semantics using (same)
open import Examples.Groups.Alt16-RevCir.Syntactics
  using (Gen ; X-gen ; CX-gen ; Ex-gen ; CCX-gen ; _↥)
open import Examples.Groups.Alt16-RevCir.FourWire
open import Examples.Groups.Alt16-RevCir.Frames

------------------------------------------------------------------------
-- Decoding

private
  decode : {A : Set} → (Char → Maybe A) → List Char → List A
  decode f []       = []
  decode f (c ∷ cs) = add (f c) (decode f cs)
    where
    add : Maybe _ → List _ → List _
    add (just g) xs = g ∷ xs
    add nothing  xs = xs

  l4 : Char → Maybe (Gen 4)
  l4 'a' = just x0
  l4 'b' = just x1
  l4 'd' = just x2
  l4 'f' = just x3
  l4 'c' = just cx0
  l4 'e' = just cx1
  l4 'g' = just cx2
  l4 's' = just ex0
  l4 't' = just ex1
  l4 'u' = just ex2
  l4 'T' = just ccx0
  l4 'U' = just ccx1
  l4 _   = nothing

  l3 : Char → Maybe (Gen 3)
  l3 'a' = just X-gen
  l3 'b' = just (X-gen ↥)
  l3 'd' = just (X-gen ↥ ↥)
  l3 'c' = just CX-gen
  l3 'e' = just (CX-gen ↥)
  l3 's' = just Ex-gen
  l3 't' = just (Ex-gen ↥)
  l3 'T' = just CCX-gen
  l3 _   = nothing

  lh : Char → Maybe HL
  lh 'a' = just hx0
  lh 'b' = just hx1
  lh 'd' = just hx2
  lh 'f' = just hx3
  lh 's' = just he0
  lh 't' = just he1
  lh 'u' = just he2
  lh _   = nothing

ℓ : String → List (Gen 4)
ℓ s = decode l4 (toList s)

ℓ₃ : String → List (Gen 3)
ℓ₃ s = decode l3 (toList s)

ℓʰ : String → List HL
ℓʰ s = decode lh (toList s)

------------------------------------------------------------------------
-- Steps

private
  T→≡ : {b : Bool} → T b → b ≡ true
  T→≡ {true} _ = refl

-- A step on the bottom three wires, and on the top three.
bo : ℕ → (l r : String) {_ : T (same 3 ⟪ ℓ₃ l ⟫ ⟪ ℓ₃ r ⟫)} → Step 4
bo i l r {h} = rw i (bot (ℓ₃ l) (ℓ₃ r) (T→≡ h))

to : ℕ → (l r : String) {_ : T (same 3 ⟪ ℓ₃ l ⟫ ⟪ ℓ₃ r ⟫)} → Step 4
to i l r {h} = rw i (top (ℓ₃ l) (ℓ₃ r) (T→≡ h))

-- Two words in the NOT gates and swaps.
hs : ℕ → (u v : String)
     {_ : T (okSt (hnorm₀ (ℓʰ u)) (hnorm₀ (ℓʰ v)))} → Step 4
hs i u v {h} = rw i (hstep (ℓʰ u) (ℓʰ v) (T→≡ h))

-- A change of frame.
fr : ℕ → (p p′ b b′ : String)
     {_ : T (frame-ok (ℓʰ p) (ℓʰ p′) (ℓ₃ b) (ℓ₃ b′))} → Step 4
fr i p p′ b b′ {h} = rw i (frame (ℓʰ p) (ℓʰ p′) (ℓ₃ b) (ℓ₃ b′) (T→≡ h))

-- An equation backwards.
rwˢ : ℕ → Eqn 4 → Step 4
rwˢ i e = rw i (sym⁼ e)

-- A derivation between two strings.
deriveℓ : (l r : String) (ss : List (Step 4)) →
          run ss (ℓ l) ≡ just (ℓ r) → Eqn 4
deriveℓ l r = derive (ℓ l) (ℓ r)
