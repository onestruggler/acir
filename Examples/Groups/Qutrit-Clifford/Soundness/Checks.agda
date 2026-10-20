------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules of Figure 1, each checked by evaluation on its own wires
--
-- Each rule's two sides are named (lᵢ, rᵢ) and its soundness on its
-- own wires is decided once by Evaluation's row operations (soundᵢ);
-- Soundness carries it to every width.  The names matter: Soundness
-- refers to the very terms the evaluation was stated for.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qutrit-Clifford.Soundness.Checks where


open import Word.Base using (ε ; _•_ ; _^_)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Semantics using (⟦_⟧ ; _≈_)
open import Examples.Groups.Qutrit-Clifford.Evaluation using (checked)

l₁ r₁ : Circuit 0
l₁ = (ν ^ 6)
r₁ = ε

sound₁ : ⟦ l₁ ⟧ ≈ ⟦ r₁ ⟧
sound₁ = checked l₁ r₁ _

l₂ r₂ : Circuit 1
l₂ = (H ^ 4)
r₂ = ε

sound₂ : ⟦ l₂ ⟧ ≈ ⟦ r₂ ⟧
sound₂ = checked l₂ r₂ _

l₃ r₃ : Circuit 1
l₃ = (S ^ 3)
r₃ = ε

sound₃ : ⟦ l₃ ⟧ ≈ ⟦ r₃ ⟧
sound₃ = checked l₃ r₃ _

l₄ r₄ : Circuit 1
l₄ = (H • S • S • H • S • S • H • S • S)
r₄ = ν

sound₄ : ⟦ l₄ ⟧ ≈ ⟦ r₄ ⟧
sound₄ = checked l₄ r₄ _

l₅ r₅ : Circuit 1
l₅ = (S′ • S)
r₅ = (S • S′)

sound₅ : ⟦ l₅ ⟧ ≈ ⟦ r₅ ⟧
sound₅ = checked l₅ r₅ _

l₆ r₆ : Circuit 2
l₆ = (CZ ^ 3)
r₆ = ε

sound₆ : ⟦ l₆ ⟧ ≈ ⟦ r₆ ⟧
sound₆ = checked l₆ r₆ _

l₇ r₇ : Circuit 2
l₇ = (SWAP • SWAP)
r₇ = ε

sound₇ : ⟦ l₇ ⟧ ≈ ⟦ r₇ ⟧
sound₇ = checked l₇ r₇ _

l₈ r₈ : Circuit 2
l₈ = (CZ • S ↑)
r₈ = (S ↑ • CZ)

sound₈ : ⟦ l₈ ⟧ ≈ ⟦ r₈ ⟧
sound₈ = checked l₈ r₈ _

l₉ r₉ : Circuit 2
l₉ = (CZ • CZ • H ↑ • H ↑)
r₉ = (H ↑ • H ↑ • CZ)

sound₉ : ⟦ l₉ ⟧ ≈ ⟦ r₉ ⟧
sound₉ = checked l₉ r₉ _

l₁₀ r₁₀ : Circuit 2
l₁₀ = (SWAP • S ↑)
r₁₀ = (S • SWAP)

sound₁₀ : ⟦ l₁₀ ⟧ ≈ ⟦ r₁₀ ⟧
sound₁₀ = checked l₁₀ r₁₀ _

l₁₁ r₁₁ : Circuit 2
l₁₁ = (SWAP • H ↑)
r₁₁ = (H • SWAP)

sound₁₁ : ⟦ l₁₁ ⟧ ≈ ⟦ r₁₁ ⟧
sound₁₁ = checked l₁₁ r₁₁ _

l₁₂ r₁₂ : Circuit 2
l₁₂ = (SWAP • CZ)
r₁₂ = (CZ • SWAP)

sound₁₂ : ⟦ l₁₂ ⟧ ≈ ⟦ r₁₂ ⟧
sound₁₂ = checked l₁₂ r₁₂ _

l₁₃ r₁₃ : Circuit 2
l₁₃ = (XC • S ↑)
r₁₃ = (ωˢ • ωˢ • S′ • S ↑ • CZ • XC)

sound₁₃ : ⟦ l₁₃ ⟧ ≈ ⟦ r₁₃ ⟧
sound₁₃ = checked l₁₃ r₁₃ _

l₁₄ r₁₄ : Circuit 2
l₁₄ = (XC • CZ)
r₁₄ = (ωˢ • S • S′ • CZ • XC)

sound₁₄ : ⟦ l₁₄ ⟧ ≈ ⟦ r₁₄ ⟧
sound₁₄ = checked l₁₄ r₁₄ _

l₁₅ r₁₅ : Circuit 3
l₁₅ = (CZ ↑ • CZ)
r₁₅ = (CZ • CZ ↑)

sound₁₅ : ⟦ l₁₅ ⟧ ≈ ⟦ r₁₅ ⟧
sound₁₅ = checked l₁₅ r₁₅ _

l₁₆ r₁₆ : Circuit 3
l₁₆ = (SWAP ↑ • SWAP • SWAP ↑)
r₁₆ = (SWAP • SWAP ↑ • SWAP)

sound₁₆ : ⟦ l₁₆ ⟧ ≈ ⟦ r₁₆ ⟧
sound₁₆ = checked l₁₆ r₁₆ _

l₁₇ r₁₇ : Circuit 3
l₁₇ = (SWAP • SWAP ↑ • CZ)
r₁₇ = (CZ ↑ • SWAP • SWAP ↑)

sound₁₇ : ⟦ l₁₇ ⟧ ≈ ⟦ r₁₇ ⟧
sound₁₇ = checked l₁₇ r₁₇ _

l₁₈ r₁₈ : Circuit 3
l₁₈ = (CZ • CX ↑)
r₁₈ = (CZ₀₂ • CX ↑ • CZ)

sound₁₈ : ⟦ l₁₈ ⟧ ≈ ⟦ r₁₈ ⟧
sound₁₈ = checked l₁₈ r₁₈ _

