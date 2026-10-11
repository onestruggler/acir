------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding of words over P into n-qubit circuits (Clément,
-- Definition 8.3)
--
-- Each letter of P becomes a circuit of multi-controlled gates whose
-- controls are read off the Gray codes of its indices: (−1)_[a] (−1)_[a+1]
-- is the box on the wire where the codes of a and a + 1 differ,
-- controlled by their common bits; the other letters are built from
-- these by the recursions of the definition.
--
-- The paper composes circuits with ∘, the right one first; a
-- composition A ∘ B is here the word B • A.  D on a word is a monoid
-- homomorphism for ∘, D(p₁ … p_r) = D(p₁) ∘ … ∘ D(p_r), so on our
-- words it reverses the letters: `dPʷ`.  BackAndForth needs a
-- homomorphism of time-ordered words, which is D with every letter's
-- circuit reversed: `d`, with (d ʷ) u = rev (dPʷ u).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Decoding where

open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _xor_ ; not ; _∧_)
open import Data.Fin using (Fin ; toℕ)
open import Data.List using (List ; [] ; _∷_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _<ᵇ_ ; _≡ᵇ_)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec ; [] ; _∷_ ; zipWith)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (gray ; toBits ; parity)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Encoding using (Σ ; Σ′ ; hpat ; distinct4 ; twoSmallest)

------------------------------------------------------------------------
-- The decoding, on n = m + 3 wires, with indices as naturals

module _ {m : ℕ} where
  private
    n : ℕ
    n = ₃₊ m

    -- The Gray code of an index.
    gcode : ℕ → Bits n
    gcode k = gray (toBits n k)

    -- The layout of the gate for a and a + 1: the target where the
    -- codes differ, the common bits as controls.
    slot : Bool → Bool → Slot
    slot b b′ = if b xor b′ then tgt else ctrl b

    layout□ : ℕ → Layout n
    layout□ a = zipWith slot (gcode a) (gcode (suc a))

    -- β: the bit of the code of a on the target wire.
    βof : ℕ → Bool
    βof a = lookupℕ (tgtWire (layout□ a)) (gcode a)

  ----------------------------------------------------------------------
  -- (−1)_[a] (−1)_[b]

  -- The box for a and a + 1.
  dZZ₁ : ℕ → Circuit n
  dZZ₁ a = mc□ (layout□ a)

  private
    -- D((−1)_[a] (−1)_[a+d]) for a ≤ a + d: the boxes for a, …, a + d − 1,
    -- the one for a first (the ∘-product runs from the right).
    chain : ℕ → ℕ → Circuit n
    chain a zero    = ε
    chain a (suc d) = dZZ₁ a • chain (suc a) d

  dZZ : ℕ → ℕ → Circuit n
  dZZ a b = if a <ᵇ b then chain a (b ∸ a) else chain b (a ∸ b)

  ----------------------------------------------------------------------
  -- (−1)_[c] X_[a,b]

  -- The base cases: (−1)_[a] X_[a,a+1] and (−1)_[a+1] X_[a,a+1].
  dZXlo₁ dZXhi₁ : ℕ → Circuit n
  dZXlo₁ a = mc±XZ (βof a) (layout□ a)
  dZXhi₁ a = mc±ZX (βof a) (layout□ a)

  -- (−1)_[a] X_[a,b] and (−1)_[b] X_[a,b] for b = a + d, d ≥ 1, by
  -- induction on d; the parity of d decides the recursion.
  dZXlo dZXhi : ℕ → ℕ → Circuit n
  dZXlo a zero          = ε
  dZXlo a (suc zero)    = dZXlo₁ a
  dZXlo a (suc (suc d)) =
    if parity d
    then dZXlo₁ a • dZXlo (suc a) (suc d) • dZXhi₁ a
    else dZXhi₁ (a + suc d) • dZXlo a (suc d) • dZXlo₁ (a + suc d)
  dZXhi a zero          = ε
  dZXhi a (suc zero)    = dZXhi₁ a
  dZXhi a (suc (suc d)) =
    if parity d
    then dZXlo₁ a • dZXhi (suc a) (suc d) • dZXhi₁ a
    else dZXhi₁ (a + suc d) • dZXhi a (suc d) • dZXlo₁ (a + suc d)

  private
    -- (−1)_[a] X_[a,b] for any a ≠ b, through X_[a,b] = X_[b,a].
    dZXself : ℕ → ℕ → Circuit n
    dZXself a b = if a <ᵇ b then dZXlo a (b ∸ a) else dZXhi b (a ∸ b)

  dZX : ℕ → ℕ → ℕ → Circuit n
  dZX c a b =
    let lo = if a <ᵇ b then a else b
        hi = if a <ᵇ b then b else a
    in if c ≡ᵇ lo then dZXlo lo (hi ∸ lo)
       else if c ≡ᵇ hi then dZXhi lo (hi ∸ lo)
       else dZXself a b • dZZ c a

  ----------------------------------------------------------------------
  -- X_[a,b] X_[c,d]

  dXX : ℕ → ℕ → ℕ → ℕ → Circuit n
  dXX a b c d = dZX b c d • dZX a a b

  ----------------------------------------------------------------------
  -- H_[a,b] H_[c,d]

  private
    -- The layout with the H on wire h, the box on wire q and the bits
    -- of a as controls elsewhere.
    layoutH : Bits n → ℕ → ℕ → Layout n
    layoutH a h q = go 0 a
      where
      go : ∀ {k} → ℕ → Bits k → Layout k
      go w []       = []
      go w (b ∷ bs) = (if w ≡ᵇ h then tgtH else if w ≡ᵇ q then tgt else ctrl b) ∷ go (suc w) bs

    -- D(H_[0,1] H_[3,2]): white controls everywhere, the box on wire 1,
    -- the H on wire 0.
    gadget : Circuit n
    gadget = mcH (layoutH (gcode 0) 0 1)

    -- The decoding of a word of (−1) X letters, the last letter first.
    dΣ : Word (GenP n) → Circuit n
    dΣ [ −1X c a b _ ]ʷ = dZX (toℕ c) (toℕ a) (toℕ b)
    dΣ [ _ ]ʷ           = ε
    dΣ ε                = ε
    dΣ (u • v)          = dΣ v • dΣ u

    -- Four distinct indices.
    dHH₄ : ℕ → ℕ → ℕ → ℕ → Circuit n
    dHH₄ a b c d with hpat (gcode a) (gcode b) (gcode c) (gcode d)
    ... | just (pb , pc) = mcH (layoutH (gcode a) pb pc)
    ... | nothing        = dΣ (Σ′ a b c d) • gadget • dΣ (Σ a b c d)

  dHH : ℕ → ℕ → ℕ → ℕ → Circuit n
  dHH a b c d =
    if distinct4 a b c d then dHH₄ a b c d
    else let (e , f) = twoSmallest a b c d in dHH₄ e f c d • dHH₄ a b e f

  ----------------------------------------------------------------------
  -- The decoding

  -- Definition 8.3 on a letter.
  dP : GenP n → Circuit n
  dP (−1−1 a b)       = dZZ (toℕ a) (toℕ b)
  dP (−1X c a b _)    = dZX (toℕ c) (toℕ a) (toℕ b)
  dP (XX a b c d _ _) = dXX (toℕ a) (toℕ b) (toℕ c) (toℕ d)
  dP (HH a b c d _ _) = dHH (toℕ a) (toℕ b) (toℕ c) (toℕ d)

  -- On a word, the paper's homomorphism for ∘: the last letter first.
  dPʷ : Word (GenP n) → Circuit n
  dPʷ [ p ]ʷ  = dP p
  dPʷ ε       = ε
  dPʷ (u • v) = dPʷ v • dPʷ u

  -- The letter-wise decoding whose extension to time-ordered words is
  -- the reverse of dPʷ.
  d : GenP n → Circuit n
  d p = rev (dP p)
