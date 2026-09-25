------------------------------------------------------------------------
-- Presentations of groups
--
-- Colours of controls as conjugations, wire by wire
--
-- A colouring s of the wires is X on the wires where s is false,
-- `col s w = negsB s • w • negsB s`.  On the four bottom wires it comes
-- apart into one conjugation per wire (`peel`) — X on wire 0, 1, 2, 3
-- or not — around the colouring of the top wires, `colT`, which a
-- circuit on the bottom four wires does not see (`colT-local`).  These
-- conjugations commute with each other (X on different wires), with
-- the swap of the wires 0 1 up to renaming (X on wire 1 through it is X
-- on wire 0), and X on the target of a triply controlled rotation turns
-- it over ((238)).  So a coloured rotation of wire 0 or 1 from the
-- wires 0–3, white on wire 2, is one of the gates of (241) or (240)
-- (`norm-ZX`, `norm-K`), whose commutations Lemma D.5 proves in every
-- colour.  A colouring passes `place 3` with its bit on wire 3 dropped
-- (`col-place`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Colours
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; s≤s ; z≤n)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₁ ; module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃ using (ZX₃ ; XZ₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations5 complete₂ complete₃ using (eq238)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; N₃ᵇ ; rot ; C₂₄₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃
  using (module N₀ ; N₀ᵇ ; D₂₄₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs² ; negs-flip ; negs-flip′ ; X-negs ; swB ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (insertℕ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑ ; swapX ; swapX′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (up ; local-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place ; place-• ; low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget319 complete₂ complete₃ using (N₂ᵇ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc
  using (placeAt-• ; placeAt-X-lo ; placeAt-zero ; placeAt-↑)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- A colouring

col : Bits n → Circuit n → Circuit n
col s w = negsB s • w • negsB s

-- The colouring of the wires above the bottom four.
colT : Bits n → Circuit (₄₊ n) → Circuit (₄₊ n)
colT x w = up 4 (negsB x) • w • up 4 (negsB x)

-- A colouring is a conjugation by an involution.
module Col {n : ℕ} (s : Bits n) = Conj {n} (negsB s) (negs² s)

------------------------------------------------------------------------
-- Word algebra: conjugations by involutions

module _ {m : ℕ} where
  open Tools (m VRel,_===_)

  -- Conjugating by commuting involutions in either order.
  conj-swap : ∀ {c d : Circuit m} → c • d ≈ d • c → (w : Circuit m) →
              c • (d • w • d) • c ≈ d • (c • w • c) • d
  conj-swap {c} {d} cd w = begin
    c • (d • w • d) • c        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (c • d) • w • (d • c)      ≈⟨ cong cd (back _ (sym cd)) ⟩
    (d • c) • w • (c • d)      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    d • (c • w • c) • d ∎

  -- Conjugating by c • r where c commutes with r.
  conj-split : ∀ {c r : Circuit m} → c • r ≈ r • c → (w : Circuit m) →
               (c • r) • w • (c • r) ≈ c • (r • w • r) • c
  conj-split {c} {r} cr w = begin
    (c • r) • w • (c • r)      ≈⟨ back _ (back _ cr) ⟩
    (c • r) • w • (r • c)      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    c • (r • w • r) • c ∎

------------------------------------------------------------------------
-- X on the bottom four wires, and the colourings on them

module _ {n : ℕ} where
  open Tools ((₄₊ n) VRel,_===_)

  private
    X₀₁ : X • X ↑ ≈ X ↑ • X
    X₀₁ = X-↑ X
    X₀₂ : X • X ↑ ↑ ≈ X ↑ ↑ • X
    X₀₂ = X-↑ (X ↑)
    X₀₃ : X • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • X
    X₀₃ = X-↑ (X ↑ ↑)
    X₁₂ : X ↑ • X ↑ ↑ ≈ X ↑ ↑ • X ↑
    X₁₂ = lemma-cong↑ _ _ (X-↑ X)
    X₁₃ : X ↑ • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • X ↑
    X₁₃ = lemma-cong↑ _ _ (X-↑ (X ↑))
    X₂₃ : X ↑ ↑ • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • X ↑ ↑
    X₂₃ = lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ X))

  -- The conjugations respect ≈.
  N₀ᵇ-cong : ∀ a {u v : Circuit (₄₊ n)} → u ≈ v → N₀ᵇ a u ≈ N₀ᵇ a v
  N₀ᵇ-cong true  e = e
  N₀ᵇ-cong false e = N₀.⟪⟫-cong e

  N₁ᵇ-cong : ∀ a {u v : Circuit (₄₊ n)} → u ≈ v → N₁ᵇ a u ≈ N₁ᵇ a v
  N₁ᵇ-cong true  e = e
  N₁ᵇ-cong false e = N₁.⟪⟫-cong e

  N₂ᵇ-cong : ∀ a {u v : Circuit (₄₊ n)} → u ≈ v → N₂ᵇ a u ≈ N₂ᵇ a v
  N₂ᵇ-cong true  e = e
  N₂ᵇ-cong false e = N₂.⟪⟫-cong e

  N₃ᵇ-cong : ∀ a {u v : Circuit (₄₊ n)} → u ≈ v → N₃ᵇ a u ≈ N₃ᵇ a v
  N₃ᵇ-cong true  e = e
  N₃ᵇ-cong false e = N₃.⟪⟫-cong e

  -- The conjugations on different wires commute.
  N₀₁ : ∀ a b w → N₀ᵇ a (N₁ᵇ b w) ≈ N₁ᵇ b (N₀ᵇ a w)
  N₀₁ true  b     w = refl
  N₀₁ false true  w = refl
  N₀₁ false false w = conj-swap X₀₁ w

  N₀₂ : ∀ a b w → N₀ᵇ a (N₂ᵇ b w) ≈ N₂ᵇ b (N₀ᵇ a w)
  N₀₂ true  b     w = refl
  N₀₂ false true  w = refl
  N₀₂ false false w = conj-swap X₀₂ w

  N₀₃ : ∀ a b w → N₀ᵇ a (N₃ᵇ b w) ≈ N₃ᵇ b (N₀ᵇ a w)
  N₀₃ true  b     w = refl
  N₀₃ false true  w = refl
  N₀₃ false false w = conj-swap X₀₃ w

  N₁₂ : ∀ a b w → N₁ᵇ a (N₂ᵇ b w) ≈ N₂ᵇ b (N₁ᵇ a w)
  N₁₂ true  b     w = refl
  N₁₂ false true  w = refl
  N₁₂ false false w = conj-swap X₁₂ w

  N₁₃ : ∀ a b w → N₁ᵇ a (N₃ᵇ b w) ≈ N₃ᵇ b (N₁ᵇ a w)
  N₁₃ true  b     w = refl
  N₁₃ false true  w = refl
  N₁₃ false false w = conj-swap X₁₃ w

  N₂₃ : ∀ a b w → N₂ᵇ a (N₃ᵇ b w) ≈ N₃ᵇ b (N₂ᵇ a w)
  N₂₃ true  b     w = refl
  N₂₃ false true  w = refl
  N₂₃ false false w = conj-swap X₂₃ w

  -- Through the swap of the wires 0 1: X on wire 1 becomes X on wire
  -- 0 and back, X on the wires 2 3 stays.
  N₀-S₀₁ : ∀ a w → N₀ᵇ a (S₀₁.⟪ w ⟫) ≈ S₀₁.⟪ N₁ᵇ a w ⟫
  N₀-S₀₁ true  w = refl
  N₀-S₀₁ false w = begin
    X • (Ex ↓ • w • Ex ↓) • X
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (X • Ex ↓) • w • (Ex ↓ • X)
      ≈⟨ cong (sym swapX′) (back _ (sym swapX)) ⟩
    (Ex ↓ • X ↑) • w • (X ↑ • Ex ↓)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Ex ↓ • (X ↑ • w • X ↑) • Ex ↓ ∎

  N₁-S₀₁ : ∀ a w → N₁ᵇ a (S₀₁.⟪ w ⟫) ≈ S₀₁.⟪ N₀ᵇ a w ⟫
  N₁-S₀₁ true  w = refl
  N₁-S₀₁ false w = begin
    X ↑ • (Ex ↓ • w • Ex ↓) • X ↑
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (X ↑ • Ex ↓) • w • (Ex ↓ • X ↑)
      ≈⟨ cong swapX (back _ swapX′) ⟩
    (Ex ↓ • X ↓) • w • (X ↓ • Ex ↓)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Ex ↓ • (X ↓ • w • X ↓) • Ex ↓ ∎

  N₂-S₀₁ : ∀ a w → N₂ᵇ a (S₀₁.⟪ w ⟫) ≈ S₀₁.⟪ N₂ᵇ a w ⟫
  N₂-S₀₁ true  w = refl
  N₂-S₀₁ false w = conj-swap (sym (low-comm (Ex {0}) (X {₁₊ n}))) w

  N₃-S₀₁ : ∀ a w → N₃ᵇ a (S₀₁.⟪ w ⟫) ≈ S₀₁.⟪ N₃ᵇ a w ⟫
  N₃-S₀₁ true  w = refl
  N₃-S₀₁ false w = conj-swap (sym (low-comm (Ex {0}) (X {n} ↑))) w

  -- X on the target turns the rotation over, (238).
  N₀-rot : ∀ a → N₀ᵇ a ZX₃ ≈ rot a
  N₀-rot true  = refl
  N₀-rot false = trans (sym assoc) (trans (front _ eq238) (cancelʳ _ X²))

  -- X on the bottom four wires passes the colouring of the top ones.
  N₀-colT : ∀ a (x : Bits n) w → N₀ᵇ a (colT x w) ≈ colT x (N₀ᵇ a w)
  N₀-colT true  x w = refl
  N₀-colT false x w = conj-swap (X-↑ (up 3 (negsB x))) w

  N₁-colT : ∀ a (x : Bits n) w → N₁ᵇ a (colT x w) ≈ colT x (N₁ᵇ a w)
  N₁-colT true  x w = refl
  N₁-colT false x w = conj-swap (lemma-cong↑ _ _ (X-↑ (up 2 (negsB x)))) w

  N₂-colT : ∀ a (x : Bits n) w → N₂ᵇ a (colT x w) ≈ colT x (N₂ᵇ a w)
  N₂-colT true  x w = refl
  N₂-colT false x w = conj-swap (lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ (up 1 (negsB x))))) w

  N₃-colT : ∀ a (x : Bits n) w → N₃ᵇ a (colT x w) ≈ colT x (N₃ᵇ a w)
  N₃-colT true  x w = refl
  N₃-colT false x w = conj-swap (lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ (negsB x))))) w

  -- A circuit on the bottom four wires passes a top colouring.
  colT-pass : ∀ (u : Circuit 4) (x : Bits n) {w : Circuit (₄₊ n)} →
              (u ↓ᵏ n) • w ≈ w • (u ↓ᵏ n) → (u ↓ᵏ n) • colT x w ≈ colT x w • (u ↓ᵏ n)
  colT-pass u x {w} e = begin
    U • T • w • T          ≈⟨ trans (sym assoc) (front _ (local-comm u (negsB x))) ⟩
    (T • U) • w • T        ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ e))) ⟩
    T • (w • U) • T        ≈⟨ back _ (trans assoc (back _ (local-comm u (negsB x)))) ⟩
    T • w • T • U          ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
    (T • w • T) • U ∎
    where
    U T : Circuit (₄₊ n)
    U = u ↓ᵏ n
    T = up 4 (negsB x)

  ----------------------------------------------------------------------
  -- Peeling a colouring, one wire at a time

  private
    peel₀ : ∀ a (r : Bits (₃₊ n)) (w : Circuit (₄₊ n)) →
            col (a ∷ r) w ≈ N₀ᵇ a (negsB r ↑ • w • negsB r ↑)
    peel₀ true  r w = refl
    peel₀ false r w = conj-split (X-↑ (negsB r)) w

    peel₁ : ∀ b (r : Bits (₂₊ n)) (w : Circuit (₄₊ n)) →
            negsB (b ∷ r) ↑ • w • negsB (b ∷ r) ↑ ≈ N₁ᵇ b (negsB r ↑ ↑ • w • negsB r ↑ ↑)
    peel₁ true  r w = refl
    peel₁ false r w = conj-split (lemma-cong↑ _ _ (X-↑ (negsB r))) w

    peel₂ : ∀ c (r : Bits (₁₊ n)) (w : Circuit (₄₊ n)) →
            negsB (c ∷ r) ↑ ↑ • w • negsB (c ∷ r) ↑ ↑ ≈ N₂ᵇ c (negsB r ↑ ↑ ↑ • w • negsB r ↑ ↑ ↑)
    peel₂ true  r w = refl
    peel₂ false r w = conj-split (lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ (negsB r)))) w

    peel₃ : ∀ d (x : Bits n) (w : Circuit (₄₊ n)) →
            negsB (d ∷ x) ↑ ↑ ↑ • w • negsB (d ∷ x) ↑ ↑ ↑ ≈ N₃ᵇ d (colT x w)
    peel₃ true  x w = refl
    peel₃ false x w = conj-split (lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ (X-↑ (negsB x))))) w

  peel : ∀ a b c d (x : Bits n) (w : Circuit (₄₊ n)) →
         col (a ∷ b ∷ c ∷ d ∷ x) w ≈ N₀ᵇ a (N₁ᵇ b (N₂ᵇ c (N₃ᵇ d (colT x w))))
  peel a b c d x w =
    trans (peel₀ a (b ∷ c ∷ d ∷ x) w)
      (N₀ᵇ-cong a (trans (peel₁ b (c ∷ d ∷ x) w)
        (N₁ᵇ-cong b (trans (peel₂ c (d ∷ x) w) (N₂ᵇ-cong c (peel₃ d x w))))))

  -- A circuit on the bottom four wires does not see the top colours.
  colT-local : ∀ (u : Circuit 4) (x : Bits n) → colT x (u ↓ᵏ n) ≈ u ↓ᵏ n
  colT-local u x = begin
    T • (u ↓ᵏ n) • T      ≈⟨ trans (sym assoc) (front _ (sym (local-comm u (negsB x)))) ⟩
    ((u ↓ᵏ n) • T) • T    ≈⟨ cancelʳ _ TT ⟩
    u ↓ᵏ n ∎
    where
    T : Circuit (₄₊ n)
    T = up 4 (negsB x)
    TT : T • T ≈ ε
    TT = lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ (negs² x))))

  ----------------------------------------------------------------------
  -- The coloured rotations, white on wire 2, as gates of (241), (240)

  norm-ZX : ∀ a b d (x : Bits n) → col (a ∷ b ∷ false ∷ d ∷ x) ZX₃ ≈ C₂₄₁ d b a
  norm-ZX a b d x = begin
    col (a ∷ b ∷ false ∷ d ∷ x) ZX₃
      ≈⟨ peel a b false d x ZX₃ ⟩
    N₀ᵇ a (N₁ᵇ b (N₂.⟪ N₃ᵇ d (colT x ZX₃) ⟫))
      ≈⟨ N₀ᵇ-cong a (N₁ᵇ-cong b (N₂.⟪⟫-cong (N₃ᵇ-cong d (colT-local (ΛZX 3) x)))) ⟩
    N₀ᵇ a (N₁ᵇ b (N₂.⟪ N₃ᵇ d ZX₃ ⟫))
      ≈⟨ trans (N₀₁ a b _) (N₁ᵇ-cong b (trans (N₀₂ a false _) (N₂.⟪⟫-cong (N₀₃ a d _)))) ⟩
    N₁ᵇ b (N₂.⟪ N₃ᵇ d (N₀ᵇ a ZX₃) ⟫)
      ≈⟨ N₁ᵇ-cong b (N₂.⟪⟫-cong (N₃ᵇ-cong d (N₀-rot a))) ⟩
    N₁ᵇ b (N₂.⟪ N₃ᵇ d (rot a) ⟫)
      ≈⟨ trans (N₁ᵇ-cong b (N₂₃ false d _)) (N₁₃ b d _) ⟩
    N₃ᵇ d (N₁ᵇ b (N₂.⟪ rot a ⟫)) ∎

  -- The rotation on wire 1 from the wires 0 2 3.
  norm-K : ∀ a b d (x : Bits n) → col (a ∷ b ∷ false ∷ d ∷ x) (S₀₁.⟪ ZX₃ ⟫) ≈ D₂₄₀ d a b
  norm-K a b d x = begin
    col (a ∷ b ∷ false ∷ d ∷ x) K
      ≈⟨ peel a b false d x K ⟩
    N₀ᵇ a (N₁ᵇ b (N₂.⟪ N₃ᵇ d (colT x K) ⟫))
      ≈⟨ N₀ᵇ-cong a (N₁ᵇ-cong b (N₂.⟪⟫-cong (N₃ᵇ-cong d (colT-local (Ex • ΛZX 3 • Ex) x)))) ⟩
    N₀ᵇ a (N₁ᵇ b (N₂.⟪ N₃ᵇ d K ⟫))
      ≈⟨ N₀ᵇ-cong a (N₁ᵇ-cong b (trans (N₂ᵇ-cong false (N₃-S₀₁ d ZX₃)) (N₂-S₀₁ false _))) ⟩
    N₀ᵇ a (N₁ᵇ b (S₀₁.⟪ N₂.⟪ N₃ᵇ d ZX₃ ⟫ ⟫))
      ≈⟨ N₀ᵇ-cong a (N₁-S₀₁ b _) ⟩
    N₀ᵇ a (S₀₁.⟪ N₀ᵇ b (N₂.⟪ N₃ᵇ d ZX₃ ⟫) ⟫)
      ≈⟨ N₀-S₀₁ a _ ⟩
    S₀₁.⟪ N₁ᵇ a (N₀ᵇ b (N₂.⟪ N₃ᵇ d ZX₃ ⟫)) ⟫
      ≈⟨ S₀₁.⟪⟫-cong (N₁ᵇ-cong a (trans (N₀₂ b false _) (N₂.⟪⟫-cong (trans (N₀₃ b d _) (N₃ᵇ-cong d (N₀-rot b)))))) ⟩
    S₀₁.⟪ N₁ᵇ a (N₂.⟪ N₃ᵇ d (rot b) ⟫) ⟫
      ≈⟨ S₀₁.⟪⟫-cong (trans (N₁ᵇ-cong a (N₂₃ false d _)) (N₁₃ a d _)) ⟩
    S₀₁.⟪ N₃ᵇ d (N₁ᵇ a (N₂.⟪ rot b ⟫)) ⟫
      ≈⟨ sym (trans (N₃ᵇ-cong d (N₀-S₀₁ a _)) (N₃-S₀₁ d _)) ⟩
    N₃ᵇ d (N₀ᵇ a (S₀₁.⟪ N₂.⟪ rot b ⟫ ⟫)) ∎
    where
    K : Circuit (₄₊ n)
    K = S₀₁.⟪ ZX₃ ⟫

------------------------------------------------------------------------
-- A colouring through the swap of the wires 0 1

col-Ex : ∀ (s : Bits (₂₊ n)) (w : Circuit (₂₊ n)) → (₂₊ n) ⊢ Ex • col s w • Ex ≈ col (swB 0 s) (Ex • w • Ex)
col-Ex {n} s w = begin
  Ex • (N • w • N) • Ex
    ≈⟨ SW.⟪⟫-•₃ (swapAt-negsB 0 s) refl (swapAt-negsB 0 s) ⟩
  negsB (swB 0 s) • (Ex • w • Ex) • negsB (swB 0 s) ∎
  where
  open Tools ((₂₊ n) VRel,_===_)
  module SW = Conj {₂₊ n} Ex Ex²
  N : Circuit (₂₊ n)
  N = negsB s

------------------------------------------------------------------------
-- An idle wire inserted at p is a black bit inserted there (MergeAll
-- has the same, privately)

placeAt-negsB : ∀ p (W : Bits n) → p ≤ n → (₁₊ n) ⊢ placeAt p (negsB W) ≈ negsB (insertℕ p true W)
placeAt-negsB {n} zero    W _ = placeAt-zero (negsB W)
placeAt-negsB {suc n} (suc p) (true ∷ W) (s≤s p≤) =
  trans (placeAt-↑ p (negsB W)) (lemma-cong↑ _ _ (placeAt-negsB p W p≤))
  where open Tools ((₂₊ n) VRel,_===_)
placeAt-negsB {suc n} (suc p) (false ∷ W) (s≤s p≤) = begin
  placeAt (suc p) (X • negsB W ↑)                     ≈⟨ placeAt-• (suc p) X (negsB W ↑) ⟩
  placeAt (suc p) X • placeAt (suc p) (negsB W ↑)     ≈⟨ cong (placeAt-X-lo (suc p) 0 (s≤s z≤n) (s≤s p≤)) (placeAt-↑ p (negsB W)) ⟩
  X • placeAt p (negsB W) ↑                           ≈⟨ back _ (lemma-cong↑ _ _ (placeAt-negsB p W p≤)) ⟩
  X • negsB (insertℕ p true W) ↑ ∎
  where open Tools ((₂₊ n) VRel,_===_)

------------------------------------------------------------------------
-- A colouring through place 3: its bit on wire 3 is dropped

module _ {r : ℕ} where
  open Tools ((₄₊ r) VRel,_===_)

  private
    X₃ : Circuit (₄₊ r)
    X₃ = X ↑ ↑ ↑

  col-place : ∀ a b c d (x : Bits r) (u : Circuit (₃₊ r)) →
              col (a ∷ b ∷ c ∷ d ∷ x) (place 3 u) ≈ place 3 (col (a ∷ b ∷ c ∷ x) u)
  col-place a b c d x u = trans (drop d) put
    where
    s′ : Bits (₃₊ r)
    s′ = a ∷ b ∷ c ∷ x

    ≡→≈ : ∀ {p q : Circuit (₄₊ r)} → p ≡ q → p ≈ q
    ≡→≈ Eq.refl = refl

    -- X on wire 3 passes the placed circuit.
    drop : ∀ d → col (a ∷ b ∷ c ∷ d ∷ x) (place 3 u) ≈ col (a ∷ b ∷ c ∷ true ∷ x) (place 3 u)
    drop true  = refl
    drop false = begin
      negsB (flipAt 3 M-bits) • place 3 u • negsB (flipAt 3 M-bits)
        ≈⟨ cong (negs-flip i₃ M-bits) (back _ (negs-flip′ i₃ M-bits)) ⟩
      (X₃ • M) • place 3 u • (M • X₃)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      X₃ • (M • place 3 u • M) • X₃
        ≈⟨ trans (sym assoc) (trans (front _ (pass XM (pass (X-place 3 u) XM))) (cancelʳ′ X₃²)) ⟩
      M • place 3 u • M ∎
      where
      i₃ : Fin (₄₊ r)
      i₃ = sF (sF (sF 0F))
      M-bits : Bits (₄₊ r)
      M-bits = a ∷ b ∷ c ∷ true ∷ x
      M : Circuit (₄₊ r)
      M = negsB M-bits
      XM : X₃ • M ≈ M • X₃
      XM = X-negs i₃ M-bits
      X₃² : X₃ • X₃ ≈ ε
      X₃² = lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ X²))
      pass : ∀ {p q : Circuit (₄₊ r)} → X₃ • p ≈ p • X₃ → X₃ • q ≈ q • X₃ → X₃ • (p • q) ≈ (p • q) • X₃
      pass {p} {q} ep eq = trans (sym assoc) (trans (front _ ep) (trans assoc (trans (back _ eq) (sym assoc))))
      cancelʳ′ : ∀ {p : Circuit (₄₊ r)} → X₃ • X₃ ≈ ε → (p • X₃) • X₃ ≈ p
      cancelʳ′ {p} e = trans assoc (trans (back _ e) right-unit)

    -- The other bits go inside.
    put : col (a ∷ b ∷ c ∷ true ∷ x) (place 3 u) ≈ place 3 (col s′ u)
    put = begin
      negsB (a ∷ b ∷ c ∷ true ∷ x) • place 3 u • negsB (a ∷ b ∷ c ∷ true ∷ x)
        ≈⟨ cong (sym N≈) (back _ (sym N≈)) ⟩
      place 3 (negsB s′) • place 3 u • place 3 (negsB s′)
        ≈⟨ sym (trans (place-• 3 (negsB s′) (u • negsB s′)) (back _ (place-• 3 u (negsB s′)))) ⟩
      place 3 (col s′ u) ∎
      where
      N≈ : place 3 (negsB s′) ≈ negsB (a ∷ b ∷ c ∷ true ∷ x)
      N≈ = trans (≡→≈ (Eq.sym (placeAt-place 3 (negsB s′))))
                 (placeAt-negsB 3 s′ (s≤s (s≤s (s≤s z≤n))))
