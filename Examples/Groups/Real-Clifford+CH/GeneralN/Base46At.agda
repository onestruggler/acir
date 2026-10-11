------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-wire steps of rule (46) at width 4 + n, as a record
-- (Clément, Lemma 8.8)
--
-- The words of Base46 — the box on wire 3 of the bottom four wires and
-- its colourings, the relabellings πa, πb and the splitting of ζ η over
-- the colour of wire 0 — on the bottom four wires of a circuit of width
-- 4 + n, with the equations Canon46bGen needs between them.  From five
-- wires on they are Base46's evaluations under completeness on four
-- qubits (Canon46b); on four wires they are derived from Lemma D.5
-- (Lemma88.W4.Core46).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base46At where

open import Data.Nat using (ℕ)
open import Word.Base using (ε ; _•_)

open import Notations using (₄₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (P₁₃)
import Examples.Groups.Real-Clifford+CH.GeneralN.Base46 as B46

-- A word on four wires, on the bottom four of 4 + n.
lift : Circuit 4 → ∀ n → Circuit (₄₊ n)
lift w n = w ↓ᵏ n

record Base46At (n : ℕ) : Set where
  field
    ea₁   : (₄₊ n) ⊢ lift (B46.πa • B46.πa′) n ≈ lift ε n
    ea₂   : (₄₊ n) ⊢ lift (B46.πa′ • B46.πa) n ≈ lift ε n
    eb₁   : (₄₊ n) ⊢ lift (B46.πb • B46.πb′) n ≈ lift ε n
    eb₂   : (₄₊ n) ⊢ lift (B46.πb′ • B46.πb) n ≈ lift ε n
    ea-bb : (₄₊ n) ⊢ lift (B46.πa • B46.bb • B46.πa′) n ≈ lift (Λ□ 3) n
    eb-bb : (₄₊ n) ⊢ lift (B46.πb • B46.bb • B46.πb′) n ≈ lift (Λ□ 3) n
    ea-X  : (₄₊ n) ⊢ lift (B46.πa • X • B46.πa′) n ≈ lift (X ↑ ↑) n
    ea-X₁ : (₄₊ n) ⊢ lift (B46.πa • X ↑ • B46.πa′) n ≈ lift (X ↑ ↑ ↑) n
    ea-P  : (₄₊ n) ⊢ lift (B46.πa • PP ↑ • B46.πa′) n ≈ lift P₁₃ n
    ea-L  : (₄₊ n) ⊢ lift (B46.πa • (Ex ↑ • Ex)) n ≈ lift (Ex • (Ex ↑ • Ex ↑ ↑)) n
    ea-R  : (₄₊ n) ⊢ lift ((Ex • Ex ↑) • B46.πa′) n ≈ lift ((Ex ↑ ↑ • Ex ↑) • Ex) n
    eb-X  : (₄₊ n) ⊢ lift (B46.πb • X • B46.πb′) n ≈ lift (X ↑ ↑) n
    eb-X₂ : (₄₊ n) ⊢ lift (B46.πb • X ↑ ↑ • B46.πb′) n ≈ lift (X ↑ ↑ ↑) n
    eb-P  : (₄₊ n) ⊢ lift (B46.πb • PP ↑ • B46.πb′) n ≈ lift P₁₃ n
    eb-L  : (₄₊ n) ⊢ lift (B46.πb • Ex) n ≈ lift (Ex • (Ex ↑ • Ex ↑ ↑)) n
    eb-R  : (₄₊ n) ⊢ lift (Ex • B46.πb′) n ≈ lift ((Ex ↑ ↑ • Ex ↑) • Ex) n
    e-X₂P : (₄₊ n) ⊢ lift (X ↑ ↑ • P₁₃) n ≈ lift (P₁₃ • X ↑ ↑) n
    e-ζη  : (₄₊ n) ⊢ lift (B46.ζ • B46.η) n ≈ lift (B46.Vo • B46.Vc) n
    e-Vc  : (₄₊ n) ⊢ lift (B46.Vc • B46.η • B46.ζ) n ≈ lift B46.Vo′ n
