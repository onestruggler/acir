------------------------------------------------------------------------
-- Presentations of groups
--
-- The translations, in both directions, between Lafont's cycles on
-- sixteen points and the gates on four wires
--
-- The generators of the alternating group on sixteen points are
-- Lafont's cycles ω₀, …, ω₁₃ (Examples.Groups.Alternating at width
-- 16), and those of the circuits the gates X, CX, CCX and Ex on four
-- wires (Syntactics).  This module translates each set of generators
-- into words in the other:
--
-- * f reads a gate as a word in the cycles: the permutation of the
--   sixteen states that the gate carries out;
--
-- * g reads a cycle as a circuit: g ωᵢ is Ω i.
--
-- Iso proves that the two are inverse to each other on generators, and
-- that each carries the relations of its source to consequences of the
-- relations of its target.
--
-- The six gates on their own wires go to the words that the rules
-- gate-X, …, gate-Ex₂ of Syntactics name.  A gate on other wires goes
-- to the word of that gate between the words of the swaps that carry
-- it there: NOT one wire up is Ex • X • Ex, and CX and CCX one wire up
-- are CX and CCX between the cycles σ⁻[ 2 ], σ[ 2 ] and σ⁻[ 3 ],
-- σ[ 3 ] of Circuit.Prop, and f is bracketed as those are.
--
-- A cycle of Lafont's is the generator ω under some number of shifts,
-- so g is defined with that number as a parameter: gᵈ d reads a
-- generator at any width as the cycle d points further up.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Translation where

open import Data.Nat using (ℕ ; suc)
open import Word.Base using (_•_)

import Examples.Groups.Alternating.Syntactics as L

open import Examples.Groups.Alt16-RevCir.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Lafont's cycles on sixteen points

-- ωᵢ sends i to i + 1, i + 1 to i + 2 and i + 2 to i.
ω₀ ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ ω₇ ω₈ ω₉ ω₁₀ ω₁₁ ω₁₂ ω₁₃ : L.Circuit 16
ω₀  = L.ω {13}
ω₁  = L.ω {12} L.↑ᵏ 1
ω₂  = L.ω {11} L.↑ᵏ 2
ω₃  = L.ω {10} L.↑ᵏ 3
ω₄  = L.ω {9} L.↑ᵏ 4
ω₅  = L.ω {8} L.↑ᵏ 5
ω₆  = L.ω {7} L.↑ᵏ 6
ω₇  = L.ω {6} L.↑ᵏ 7
ω₈  = L.ω {5} L.↑ᵏ 8
ω₉  = L.ω {4} L.↑ᵏ 9
ω₁₀ = L.ω {3} L.↑ᵏ 10
ω₁₁ = L.ω {2} L.↑ᵏ 11
ω₁₂ = L.ω {1} L.↑ᵏ 12
ω₁₃ = L.ω {0} L.↑ᵏ 13

------------------------------------------------------------------------
-- The gates as words in the cycles

-- The gates on their own wires.
fX fCX fCCX fEx₀ fEx₁ fEx₂ : L.Circuit 16
fX   = ω₁ • ω₀ • ω₅ • ω₄ • ω₉ • ω₈ • ω₁₃ • ω₁₂
fCX  = ω₃ • ω₂ • ω₁₁ • ω₁₀
fCCX = ω₅ • ω₄ • ω₇ • ω₆ • ω₉ • ω₈
fEx₀ = ω₁ • ω₃ • ω₂ • ω₄ • ω₉ • ω₁₁ • ω₁₀ • ω₁₂
fEx₁ = ω₂ • ω₃ • ω₄ • ω₂ • ω₅ • ω₃ • ω₈ • ω₉ • ω₁₀ • ω₈ • ω₁₁ • ω₉
fEx₂ = ω₆ • ω₇ • ω₈ • ω₉ • ω₁₀ • ω₁₁ • ω₁₂ • ω₁₃ •
       ω₄ • ω₅ • ω₆ • ω₇ • ω₈ • ω₉ • ω₁₀ • ω₁₁ •
       ω₆ • ω₇ • ω₈ • ω₉ • ω₄ • ω₅ • ω₆ • ω₇

-- NOT, CX and CCX further up, between the swaps.
fX₁ fX₂ fX₃ fCX₁ fCX₂ fCCX₁ : L.Circuit 16
fX₁   = fEx₀ • fX • fEx₀
fX₂   = fEx₁ • fX₁ • fEx₁
fX₃   = fEx₂ • fX₂ • fEx₂
fCX₁  = (fEx₀ • fEx₁) • fCX • (fEx₁ • fEx₀)
fCX₂  = (fEx₁ • fEx₂) • fCX₁ • (fEx₂ • fEx₁)
fCCX₁ = (fEx₀ • fEx₁ • fEx₂) • fCCX • ((fEx₂ • fEx₁) • fEx₀)

f : Gen 4 → L.Circuit 16
f X-gen             = fX
f CX-gen            = fCX
f Ex-gen            = fEx₀
f CCX-gen           = fCCX
f (X-gen ↥)         = fX₁
f (CX-gen ↥)        = fCX₁
f (Ex-gen ↥)        = fEx₁
f (CCX-gen ↥)       = fCCX₁
f (X-gen ↥ ↥)       = fX₂
f (CX-gen ↥ ↥)      = fCX₂
f (Ex-gen ↥ ↥)      = fEx₂
f (X-gen ↥ ↥ ↥)     = fX₃
f (gate₀ ())
f (gate₀ () ↥)
f (gate₀ () ↥ ↥)
f (gate₀ () ↥ ↥ ↥)
f (gate₀ () ↥ ↥ ↥ ↥)

------------------------------------------------------------------------
-- The cycles as circuits

-- The generator y, d points further up, as a circuit.
gᵈ : ℕ → L.Gen n → Circuit 4
gᵈ d L.ω-gen   = Ω d
gᵈ d (y L.↥)   = gᵈ (suc d) y

g : L.Gen 16 → Circuit 4
g = gᵈ 0
