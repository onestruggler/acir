------------------------------------------------------------------------
-- Presentations of groups
--
-- What the five-wire development needs of the four-wire gadgets
--
-- The gadgets G V (V the phase pair, the signed exchange or the hybrid)
-- with their inverses, their blocks on 0 and e₀, the letters of the
-- independence they commute with, and the twisted-commutator
-- decompositions behind (F6).  The five-wire modules take this record
-- as a parameter, so that no concrete gadget — some thousands of gates —
-- ever meets another spelling of itself under λ⁰, where the comparison
-- would unfold its five-wire spelling; Five.Facts4Inst fills it from
-- Five.Gadgets and Five.Sem.G4.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Facts4 where

open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; S ; CS ; CX₁₀ ; Swap ; _↑ ; _⊢_≈_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; kpp ; krot ; kki ; blkOf ; o₄ ; e₄)

record Facts4 : Set where
  field
    G G⁻ : Kind → Circuit 4

    -- The inverses.
    inv  : ∀ V → 4 ⊢ G V • G⁻ V ≈ ε
    inv′ : ∀ V → 4 ⊢ G⁻ V • G V ≈ ε

    -- The block on 0 and e₀.
    sem : ∀ V → ⟦ G V ⟧ ~ tl (blkOf V) o₄ e₄

    -- The letters of the independence on the wires 0 … 3.
    cx₀ : ∀ V → 4 ⊢ CX₁₀ • G V ≈ G V • CX₁₀
    cx₁ : ∀ V → 4 ⊢ CX₁₀ ↑ • G V ≈ G V • CX₁₀ ↑
    cx₂ : ∀ V → 4 ⊢ CX₁₀ ↑ ↑ • G V ≈ G V • CX₁₀ ↑ ↑
    sw₁ : ∀ V → 4 ⊢ Swap ↑ • G V ≈ G V • Swap ↑
    sw₂ : ∀ V → 4 ⊢ Swap ↑ ↑ • G V ≈ G V • Swap ↑ ↑

    -- S on wire 1 and CS on the wires 0 1 pass the gadgets of the
    -- twisted commutators (they act on 0 and e₀ alone).
    s₁-rot : 4 ⊢ S ↑ • G krot ≈ G krot • S ↑
    s₁-ki  : 4 ⊢ S ↑ • G kki ≈ G kki • S ↑
    cs-rot : 4 ⊢ CS • G krot ≈ G krot • CS
    cs-ki  : 4 ⊢ CS • G kki ≈ G kki • CS

    -- (F6): iZ⁻¹ is a twisted commutator, the hybrid's inverse one times
    -- iZ⁻¹, and XZ the conjugate of iZ by the hybrid.
    dec-pp⁻ : 4 ⊢ G⁻ kpp ≈ G⁻ krot • (S • S • S) • G krot • S
    dec-ki⁻ : 4 ⊢ G⁻ kki ≈ (G kki • (S • S • S) • G⁻ kki • S) • G⁻ kpp
    dec-rot : 4 ⊢ G krot ≈ G⁻ kki • G kpp • G kki
