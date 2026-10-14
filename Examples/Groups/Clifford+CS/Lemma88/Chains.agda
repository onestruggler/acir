------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's chains over arbitrary consecutive letters
--
-- Decoding defines a letter of P′ on any indices as a word in the
-- letters on consecutive indices: phase pairs as chains of consecutive
-- phase pairs, signed exchanges by shrinking from the bottom, the
-- hybrid's pair closed by consecutive rotations.  Those definitions
-- are given here once, over any five families of consecutive letters
-- (the phase pair and its flip, the two rotations, the hybrid), so
-- that the facts the rules of P′ ask of them (Lemma88.Fragment) are
-- proved once for every width.  Decoding instantiates them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Word.Base using (Word)

module Examples.Groups.Clifford+CS.Lemma88.Chains
  {X : Set} (p p′ l h k : ℕ → Word X) where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (zero ; suc ; _∸_ ; _<ᵇ_ ; _≡ᵇ_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)

------------------------------------------------------------------------
-- i_a i_b⁻¹

-- The chain from a up d steps, and the inverse chain.
pp-up pp-dn : ℕ → ℕ → Word X
pp-up a zero    = ε
pp-up a (suc d) = p a • pp-up (suc a) d
pp-dn a zero    = ε
pp-dn a (suc d) = p′ a • pp-dn (suc a) d

dPP : ℕ → ℕ → Word X
dPP a b = if a <ᵇ b then pp-up a (b ∸ a) else pp-dn b (a ∸ b)

------------------------------------------------------------------------
-- (−1)_c X_[a,b]

-- (−1)_a X_{a,a+d} and (−1)_{a+d} X_{a,a+d}, shrinking from the bottom.
dLo dHi : ℕ → ℕ → Word X
dLo a zero             = ε
dLo a (suc zero)       = l a
dLo a (suc (suc d))    = h a • dLo (suc a) (suc d) • l a
dHi a zero             = ε
dHi a (suc zero)       = h a
dHi a (suc (suc d))    = h a • dHi (suc a) (suc d) • l a

-- (−1)_c X_[a,b] for a < b, its tests passed as arguments so that proofs
-- can rewrite them: whether c is a, b, or neither.
dPXs : Bool → Bool → ℕ → ℕ → ℕ → Word X
dPXs true  _     c a b = dLo a (b ∸ a)
dPXs false true  c a b = dHi a (b ∸ a)
dPXs false false c a b = dPP c a • dPP c a • dLo a (b ∸ a)

dPX : ℕ → ℕ → ℕ → Word X
dPX c a b = dPXs (c ≡ᵇ a) (c ≡ᵇ b) c a b

------------------------------------------------------------------------
-- X_[a,b] X_[c,d]

dDX : ℕ → ℕ → ℕ → ℕ → Word X
dDX a b c d = dPX a a b • dPX b c d

------------------------------------------------------------------------
-- K_[a,b] i_s⁻¹

-- K_[a,a+d] i_a⁻¹: the pair closed by consecutive rotations.
dKIa : ℕ → ℕ → Word X
dKIa a zero          = ε
dKIa a (suc zero)    = k a
dKIa a (suc (suc d)) = h a • dKIa (suc a) (suc d) • l a

dKI : ℕ → ℕ → ℕ → Word X
dKI a b s = dKIa a (b ∸ a) • dPP a s

------------------------------------------------------------------------
-- The decoding of a letter of P′ on N indices

d : ∀ {N} → GenP N → Word X
d (pp a b)         = dPP (toℕ a) (toℕ b)
d (px c a b _)     = dPX (toℕ c) (toℕ a) (toℕ b)
d (dx a b c e _ _) = dDX (toℕ a) (toℕ b) (toℕ c) (toℕ e)
d (ki a b s _)     = dKI (toℕ a) (toℕ b) (toℕ s)
