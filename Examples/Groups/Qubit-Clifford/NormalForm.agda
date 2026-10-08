------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal forms of Clifford circuits (Section 4 of Selinger)
--
-- The gates A, B, C, D and E of Definition 4.2 (Figure 1) are letter
-- lists.  The families of Definition 4.3 are inductive types:
--
--   Lad n     a ladder of B gates on n wires, climbing from wire 0 to
--             the top and closed by a C gate;
--   Zc n      a Z-normal circuit: an A gate on some wire, then a ladder;
--   DL n      a ladder of D gates descending from the top to wire 0;
--   Xc n      an X-normal circuit: a D-ladder closed by an E gate on
--             wire 0;
--   NF n      a normal circuit: a Z-normal and an X-normal circuit on
--             all n wires, then a normal circuit on the top n − 1.
--
-- The paper numbers qubits from the top, so its normal form
-- L(n) M(n) N(n−1) ω^p, read left to right, is the word
-- N ↑ • M • L here, the scalar ω^p kept at width 0, where the recursion
-- ends.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.NormalForm where

open import Data.Fin.Base using (Fin ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Engine using (⟪_⟫)
open import Examples.Groups.Qubit-Clifford.Axioms
  using (𝕨 ; h₀ ; h₁ ; s₀ ; s₁ ; c₀)

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- The gates of Figure 1

data AT : Set where
  A₁ A₂ A₃ : AT

data BT : Set where
  B₁ B₂ B₃ B₄ : BT

data CT : Set where
  C₁ C₂ : CT

data DT : Set where
  D₁ D₂ D₃ D₄ : DT

data ET : Set where
  E₁ E₂ E₃ E₄ : ET

-- Their letters, in operator order, on the bottom wires; a two-wire
-- gate's upper wire is wire 1.
Al : AT → List (Gen (₁₊ n))
Al A₁ = []
Al A₂ = h₀ ∷ []
Al A₃ = h₀ ∷ s₀ ∷ h₀ ∷ []

Bl : BT → List (Gen (₂₊ n))
Bl B₁ = c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ []
Bl B₂ = c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ []
Bl B₃ = c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₁ ∷ h₁ ∷ []
Bl B₄ = c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ []

Cl : CT → List (Gen (₁₊ n))
Cl C₁ = []
Cl C₂ = h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ []

Dl : DT → List (Gen (₂₊ n))
Dl D₁ = h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ []
Dl D₂ = h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ []
Dl D₃ = h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ []
Dl D₄ = h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ []

El : ET → List (Gen (₁₊ n))
El E₁ = []
El E₂ = s₀ ∷ []
El E₃ = s₀ ∷ s₀ ∷ []
El E₄ = s₀ ∷ s₀ ∷ s₀ ∷ []

------------------------------------------------------------------------
-- Z-normal circuits, X-normal circuits and normal circuits

-- A ladder on ₁₊ m wires.
data Lad : ℕ → Set where
  top  : CT → Lad 1
  _∷ᴮ_ : BT → Lad (₁₊ m) → Lad (₂₊ m)

infixr 5 _∷ᴮ_

⟦_⟧ᴸ : Lad n → Circuit n
⟦ top c ⟧ᴸ    = ⟪ Cl c ⟫
⟦ b ∷ᴮ lad ⟧ᴸ = ⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫

-- A Z-normal circuit: an A gate on wire 0 and a ladder, or a Z-normal
-- circuit one wire up.
data Zc : ℕ → Set where
  up : Zc (₁₊ m) → Zc (₂₊ m)
  at : AT → Lad (₁₊ m) → Zc (₁₊ m)

⟦_⟧ᶻ : Zc n → Circuit n
⟦ up L ⟧ᶻ     = ⟦ L ⟧ᶻ ↑
⟦ at a lad ⟧ᶻ = ⟦ lad ⟧ᴸ • ⟪ Al a ⟫

-- A ladder of D gates on ₁₊ m wires, D on wires 0 and 1 last.
data DL : ℕ → Set where
  []ᴰ  : DL 1
  _∷ᴰ_ : DT → DL (₁₊ m) → DL (₂₊ m)

infixr 5 _∷ᴰ_

⟦_⟧ᴰ : DL n → Circuit n
⟦ []ᴰ ⟧ᴰ      = ε
⟦ d ∷ᴰ dl ⟧ᴰ  = ⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑

-- An X-normal circuit.
record Xc (n : ℕ) : Set where
  constructor _,ˣ_
  field
    e  : ET
    dl : DL n

⟦_⟧ˣ : Xc (₁₊ m) → Circuit (₁₊ m)
⟦ e ,ˣ dl ⟧ˣ = ⟪ El e ⟫ • ⟦ dl ⟧ᴰ

-- Normal circuits.  The scalar ω^p sits at width 0, shifted up to every
-- width.
data NF : ℕ → Set where
  nf₀  : Fin 8 → NF 0
  nfₛ  : Zc (₁₊ m) → Xc (₁₊ m) → NF m → NF (₁₊ m)

⟦_⟧ⁿ : NF n → Circuit n
⟦ nf₀ p ⟧ⁿ        = ω ^ toℕ p
⟦ nfₛ L M N ⟧ⁿ    = ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ • ⟦ L ⟧ᶻ
