------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal forms of qutrit Clifford circuits (Section 3 of the paper)
--
-- The normal boxes A, B, C, D, E and F of Figure 9 are letter lists,
-- one constructor per variant.  The families of Definitions 3.2 and
-- 3.3 are inductive types, as in Examples.Groups.Qubit-Clifford:
--
--   Lad n     a ladder of B boxes on n wires, climbing from wire 0 to
--             the top and closed by a C box;
--   Zc n      a Z-normal circuit (Figure 10a): an A box on some wire,
--             then a ladder;
--   DL n      a ladder of D boxes descending from the top to wire 0;
--   Xc n      an X-normal circuit (Figure 10b): a D-ladder, then an E
--             and an F box on wire 0;
--   NF n      a normal circuit (Figure 11): a Z-normal and an X-normal
--             circuit on all n wires, then a normal circuit on the top
--             n − 1.
--
-- The paper numbers qutrits from the top, so its normal form
-- L(n) M(n) N(n−1) (−ω)^t, read left to right, is the word
-- N ↑ • M • L here, the scalar (−ω)^t kept at width 0, where the
-- recursion ends.  A two-wire box sits on wires 0 and 1, wire 1 being
-- the paper's upper wire.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.NormalForm where

open import Data.Fin.Base using (Fin ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat.Base using (ℕ)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine using (⟪_⟫)
open import Examples.Groups.Qutrit-Clifford.Axioms
  using (𝕟 ; h₀ ; h₁ ; s₀ ; s₁ ; c₀)

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- The derived generators the boxes are built from, as letter lists
-- spelled as in Syntactics

SWAPˡ XCˡ : List (Gen (₂₊ n))
SWAPˡ = c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ []
XCˡ   = h₁ ∷ h₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ []

Xˡ Zˡ : List (Gen (₁₊ n))
Xˡ = h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ []
Zˡ = s₀ ∷ h₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ []

------------------------------------------------------------------------
-- The boxes of Figure 9

-- A_ab for (a , b) ≠ (0 , 0), B_ab, C_b, D_ab, E_b and F_b.
data AT : Set where
  A₀₁ A₀₂ A₁₀ A₁₁ A₁₂ A₂₀ A₂₁ A₂₂ : AT

data BT : Set where
  B₀₀ B₀₁ B₀₂ B₁₀ B₁₁ B₁₂ B₂₀ B₂₁ B₂₂ : BT

data CT : Set where
  C₀ C₁ C₂ : CT

data DT : Set where
  D₀₀ D₀₁ D₀₂ D₁₀ D₁₁ D₁₂ D₂₀ D₂₁ D₂₂ : DT

data ET : Set where
  E₀ E₁ E₂ : ET

data FT : Set where
  F₀ F₁ F₂ : FT

-- Their letters, in operator order.  A_1b is S^b then H, A_2b is H²,
-- S^2b, H; C_b = X^b, E_b = S^b, F_b = Z^2b, with C₂ and F₁ spelled as
-- in Figures 15 and 16.
Al : AT → List (Gen (₁₊ n))
Al A₀₁ = []
Al A₀₂ = h₀ ∷ h₀ ∷ []
Al A₁₀ = h₀ ∷ []
Al A₁₁ = h₀ ∷ s₀ ∷ []
Al A₁₂ = h₀ ∷ s₀ ∷ s₀ ∷ []
Al A₂₀ = h₀ ∷ h₀ ∷ h₀ ∷ []
Al A₂₁ = h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ []
Al A₂₂ = h₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ []

Cl : CT → List (Gen (₁₊ n))
Cl C₀ = []
Cl C₁ = Xˡ
Cl C₂ = h₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ []

El : ET → List (Gen (₁₊ n))
El E₀ = []
El E₁ = s₀ ∷ []
El E₂ = s₀ ∷ s₀ ∷ []

Fl : FT → List (Gen (₁₊ n))
Fl F₀ = []
Fl F₁ = s₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ []
Fl F₂ = Zˡ

-- B_00 is the swap, then CZ; B_01 the swap, CZ², then XC; B_02 is A_02
-- on the upper wire, CZ, then B_01; and B_ab for a ≠ 0 is A_ab on the
-- upper wire, CZ², then B_01.
B₀₁ˡ : List (Gen (₂₊ n))
B₀₁ˡ = XCˡ ++ c₀ ∷ c₀ ∷ SWAPˡ

Bl : BT → List (Gen (₂₊ n))
Bl B₀₀ = c₀ ∷ SWAPˡ
Bl B₀₁ = B₀₁ˡ
Bl B₀₂ = B₀₁ˡ ++ c₀ ∷ map _↥ (Al A₀₂)
Bl B₁₀ = B₀₁ˡ ++ c₀ ∷ c₀ ∷ map _↥ (Al A₁₀)
Bl B₁₁ = B₀₁ˡ ++ c₀ ∷ c₀ ∷ map _↥ (Al A₁₁)
Bl B₁₂ = B₀₁ˡ ++ c₀ ∷ c₀ ∷ map _↥ (Al A₁₂)
Bl B₂₀ = B₀₁ˡ ++ c₀ ∷ c₀ ∷ map _↥ (Al A₂₀)
Bl B₂₁ = B₀₁ˡ ++ c₀ ∷ c₀ ∷ map _↥ (Al A₂₁)
Bl B₂₂ = B₀₁ˡ ++ c₀ ∷ c₀ ∷ map _↥ (Al A₂₂)

-- D_0b is the swap, then CZ^2b; D_ab for a ≠ 0 is A_ab on the lower
-- wire, then D_01.
Dl : DT → List (Gen (₂₊ n))
Dl D₀₀ = SWAPˡ
Dl D₀₁ = c₀ ∷ c₀ ∷ SWAPˡ
Dl D₀₂ = c₀ ∷ SWAPˡ
Dl D₁₀ = Dl D₀₁ ++ Al A₁₀
Dl D₁₁ = Dl D₀₁ ++ Al A₁₁
Dl D₁₂ = Dl D₀₁ ++ Al A₁₂
Dl D₂₀ = Dl D₀₁ ++ Al A₂₀
Dl D₂₁ = Dl D₀₁ ++ Al A₂₁
Dl D₂₂ = Dl D₀₁ ++ Al A₂₂

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

-- A Z-normal circuit: an A box on wire 0 and a ladder, or a Z-normal
-- circuit one wire up.
data Zc : ℕ → Set where
  up : Zc (₁₊ m) → Zc (₂₊ m)
  at : AT → Lad (₁₊ m) → Zc (₁₊ m)

⟦_⟧ᶻ : Zc n → Circuit n
⟦ up L ⟧ᶻ     = ⟦ L ⟧ᶻ ↑
⟦ at a lad ⟧ᶻ = ⟦ lad ⟧ᴸ • ⟪ Al a ⟫

-- A ladder of D boxes on ₁₊ m wires, the D box on wires 0 and 1 last.
data DL : ℕ → Set where
  []ᴰ  : DL 1
  _∷ᴰ_ : DT → DL (₁₊ m) → DL (₂₊ m)

infixr 5 _∷ᴰ_

⟦_⟧ᴰ : DL n → Circuit n
⟦ []ᴰ ⟧ᴰ      = ε
⟦ d ∷ᴰ dl ⟧ᴰ  = ⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑

-- An X-normal circuit: the D-ladder, then E_h and F_v on wire 0.
record Xc (n : ℕ) : Set where
  constructor xc
  field
    e  : ET
    f  : FT
    dl : DL n

⟦_⟧ˣ : Xc (₁₊ m) → Circuit (₁₊ m)
⟦ xc e f dl ⟧ˣ = ⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟦ dl ⟧ᴰ

-- Normal circuits.  The scalar (−ω)^t sits at width 0, shifted up to
-- every width.
data NF : ℕ → Set where
  nf₀  : Fin 6 → NF 0
  nfₛ  : Zc (₁₊ m) → Xc (₁₊ m) → NF m → NF (₁₊ m)

⟦_⟧ⁿ : NF n → Circuit n
⟦ nf₀ t ⟧ⁿ        = ν ^ toℕ t
⟦ nfₛ L M N ⟧ⁿ    = ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ • ⟦ L ⟧ᶻ
