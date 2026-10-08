------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal forms of real Clifford circuits (Section 4 of Makary, Ross and
-- Selinger)
--
-- The derived generators of kinds A, B, C, D and E (Definitions 4.1 to
-- 4.5) are letter lists.  The type of a wire, single (sg) or double
-- (db), says whether the Pauli operator a Z-circuit is tracking is Z or
-- XZ there (Definition 4.6); an A gate fixes the type of its wire and a
-- B gate turns the type of its lower input into the type of its upper
-- output, so the types make the families of Definitions 4.8 to 4.10
-- inductive types:
--
--   Lad t n   a ladder of B gates on n wires, its lower input of type t,
--             climbing from wire 0 to the top and closed by a C gate;
--   Zc n      a Z-circuit: an A gate on some wire, then a ladder;
--   Dl n      a ladder of D gates descending from the top to wire 0;
--   Xc n      an X-circuit: a D-ladder closed by an E gate on wire 0;
--   NF n      a normal form: a sign, then a Z-circuit and an X-circuit
--             on all n wires, then a normal form on the top n − 1.
--
-- Wire 0 is the bottom wire and words are in operator order, so the
-- normal form L_n M_n N_{n-1} (−1)^s of the paper, read left to right,
-- is the word  (−1)^s • N ↑ • M • L.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.NormalForm where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Data.Nat.Base using (ℕ)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Engine using (⟪_⟫)
open import Examples.Groups.Real-Clifford.Axioms
  using (𝕞 ; h₀ ; h₁ ; h₂ ; z₀ ; z₁ ; z₂ ; c₀ ; c₁)

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- Wire types and the derived generators

data Ty : Set where
  sg db : Ty

private
  variable
    t u v : Ty

-- A gates, by the type of the wire they start.
data AT : Ty → Set where
  A₁ A₂ : AT sg
  A₃    : AT db

-- B gates, by the types of their lower input and upper output.
data BT : Ty → Ty → Set where
  B₁ B₂ B₃ : BT sg sg
  B₄       : BT sg db
  B₅ B₆ B₇ : BT db db
  B₈       : BT db sg

data CT : Set where
  C₁ C₂ : CT

data DT : Set where
  D₁ D₂ D₃ D₄ : DT

data ET : Set where
  E₁ E₂ : ET

-- Their letters, in operator order, on the bottom wires.
Al : AT t → List (Gen (₁₊ n))
Al A₁ = []
Al A₂ = h₀ ∷ []
Al A₃ = []

Bl : BT t u → List (Gen (₂₊ n))
Bl B₁ = c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ []
Bl B₂ = c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ []
Bl B₃ = c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ []
Bl B₄ = c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ []
Bl B₅ = c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ []
Bl B₆ = c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ []
Bl B₇ = c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ []
Bl B₈ = c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ []

Cl : CT → List (Gen (₁₊ n))
Cl C₁ = []
Cl C₂ = h₀ ∷ z₀ ∷ h₀ ∷ []

Dl : DT → List (Gen (₂₊ n))
Dl D₁ = h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ []
Dl D₂ = h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ []
Dl D₃ = h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ []
Dl D₄ = c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ []

El : ET → List (Gen (₁₊ n))
El E₁ = []
El E₂ = z₀ ∷ []

-- Two derived dirty gates: X, and the CXZ gate with its XZ on wire 1.
Xl : List (Gen (₁₊ n))
Xl = h₀ ∷ z₀ ∷ h₀ ∷ []

XZCl : List (Gen (₂₊ n))
XZCl = c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ []

------------------------------------------------------------------------
-- Z-circuits, X-circuits and normal forms

-- A ladder on ₁₊ m wires whose lower input has type t.
data Lad : Ty → ℕ → Set where
  top  : CT → Lad sg 1
  _∷ᴮ_ : BT t u → Lad u (₁₊ m) → Lad t (₂₊ m)

infixr 5 _∷ᴮ_

⟦_⟧ᴸ : Lad t n → Circuit n
⟦ top c ⟧ᴸ    = ⟪ Cl c ⟫
⟦ b ∷ᴮ lad ⟧ᴸ = ⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫

-- A Z-circuit: an A gate on wire 0 and a ladder, or a Z-circuit one
-- wire up.
data Zc : ℕ → Set where
  up : Zc (₁₊ m) → Zc (₂₊ m)
  at : AT t → Lad t (₁₊ m) → Zc (₁₊ m)

⟦_⟧ᶻ : Zc n → Circuit n
⟦ up L ⟧ᶻ     = ⟦ L ⟧ᶻ ↑
⟦ at a lad ⟧ᶻ = ⟦ lad ⟧ᴸ • ⟪ Al a ⟫

-- A ladder of D gates on ₁₊ m wires, D[0] (on wires 0, 1) last.
data DL : ℕ → Set where
  []ᴰ  : DL 1
  _∷ᴰ_ : DT → DL (₁₊ m) → DL (₂₊ m)

infixr 5 _∷ᴰ_

⟦_⟧ᴰ : DL n → Circuit n
⟦ []ᴰ ⟧ᴰ      = ε
⟦ d ∷ᴰ dl ⟧ᴰ  = ⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑

-- An X-circuit.
record Xc (n : ℕ) : Set where
  constructor _,ˣ_
  field
    e  : ET
    dl : DL n

⟦_⟧ˣ : Xc (₁₊ m) → Circuit (₁₊ m)
⟦ e ,ˣ dl ⟧ˣ = ⟪ El e ⟫ • ⟦ dl ⟧ᴰ

-- The sign.
sgn : Bool → Circuit n
sgn false = ε
sgn true  = neg

-- Normal forms.
data NF : ℕ → Set where
  nf₀  : Bool → NF 0
  nfₛ  : Bool → Zc (₁₊ m) → Xc (₁₊ m) → NF m → NF (₁₊ m)

⟦_⟧ⁿ : NF n → Circuit n
⟦ nf₀ s ⟧ⁿ          = sgn s
⟦ nfₛ s L M N ⟧ⁿ    = sgn s • ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ • ⟦ L ⟧ᶻ
