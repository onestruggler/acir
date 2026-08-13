------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's basic gates A, B, C, D, E (arXiv:1310.6813, Definition 4.2
-- and Figure 1), as circuits over the Figure-8 generator set.
--
-- Definition 4.2 introduces gates Aᵢ, Bⱼ, C_k, D_ℓ, E_h with i ∈ {1,2,3},
-- j, ℓ, h ∈ {1,2,3,4} and k ∈ {1,2}, "given in Figure 1".  The gate set
-- is deliberately redundant -- A₁, C₁ and E₁ are three names for the
-- identity -- and is chosen for how the gates act on Pauli operators
-- (the paper's Figure 2), which is what makes them the right building
-- blocks for the normal forms of Definition 4.3.
--
-- The A, C and E boxes act on one qubit; B and D act on two adjacent
-- qubits, which by Remark 4.1 is the only two-qubit case that has to be
-- considered.
--
-- Qubit numbering.  The paper's qubit j is wire j here, directly: a
-- two-qubit box sits on qubits 0 and 1, and its generators Hx 0, Sx 0
-- are the un-shifted wire (`w ↓`) while Hx 1, Sx 1 are one shift up
-- (`w ↑`), with the controlled-Z of Circuit.Base spanning both.
--
-- A trap in reading the source, worth recording because it caught the
-- first transcription.  The qcircuit macros of Definition 4.3 take a
-- Y-COORDINATE, not a qubit number, and the two run opposite ways: the
-- paper numbers qubits from the TOP (§4), while y increases upward, so
-- for an N-wire picture qubit = (N-1) - y.  In L(n) the A is drawn at
-- y=2 and the C at y=6, which is qubit 4 and qubit 0 -- the C is on
-- qubit 0 and the B boxes run away from it through (0,1), (1,2), ...
-- Read as qubit numbers those coordinates say the opposite of what they
-- appear to say.
--
-- For a box in isolation the choice would be immaterial -- relabelling
-- the two wires of a single box gives an isomorphic circuit, and CZ is
-- symmetric.  It stops being immaterial as soon as boxes are composed,
-- because then their orientation has to agree with the direction the
-- chain of Normal.Chain and the staircase of Normal.Mx run.  Both run
-- away from wire 0, matching the paper's qubit numbering exactly.
--
-- Word order is the circuit order: `w • v` runs w first, then v, which
-- is how the paper reads its diagrams ("from left to right, i.e., in the
-- opposite order of the notation for matrix multiplication", §4).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger2.Boxes where

open import Data.Nat using (ℕ)

open import Notations using (₁₊ ; ₂₊)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford.Qubit.Selinger2.Figure8
  using (Circuit ; H ; S ; CZ ; _↑ ; _↓)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The box indices
--
-- Named after the paper's subscripts rather than given as Fin, so that a
-- clause `[ b₃ ]ᴮ` reads as the B₃ of Figure 1.

data ABox : Set where
  a₁ a₂ a₃ : ABox

data BBox : Set where
  b₁ b₂ b₃ b₄ : BBox

data CBox : Set where
  c₁ c₂ : CBox

data DBox : Set where
  d₁ d₂ d₃ d₄ : DBox

data EBox : Set where
  e₁ e₂ e₃ e₄ : EBox

------------------------------------------------------------------------
-- The one-qubit boxes
--
-- A₁ = C₁ = E₁ = the identity, as the paper notes.

[_]ᴬ : ABox → Circuit (₁₊ n)
[ a₁ ]ᴬ = ε
[ a₂ ]ᴬ = H
[ a₃ ]ᴬ = H • S • H

-- C₂ is the Pauli X, which §4 defines as HSSH.
[_]ᶜ : CBox → Circuit (₁₊ n)
[ c₁ ]ᶜ = ε
[ c₂ ]ᶜ = H • S • S • H

-- The E boxes are the powers of S, i.e. the four phases on one qubit.
[_]ᴱ : EBox → Circuit (₁₊ n)
[ e₁ ]ᴱ = ε
[ e₂ ]ᴱ = S
[ e₃ ]ᴱ = S • S
[ e₄ ]ᴱ = S • S • S

------------------------------------------------------------------------
-- The two-qubit boxes
--
-- B₁ and B₄ differ only in their opening gates, as do D₁ and D₄; the
-- four D boxes share the trailing H on qubit 1.

-- Paper qubit 0 is the un-shifted wire, so Hx 0 reads as H ↓ and Hx 1
-- as H ↑.
[_]ᴮ : BBox → Circuit (₂₊ n)
[ b₁ ]ᴮ = H ↑ • CZ • H ↑ • H ↓ • CZ • H ↓ • H ↑ • CZ
[ b₂ ]ᴮ = CZ • H ↓ • H ↑ • CZ
[ b₃ ]ᴮ = H ↓ • S ↓ • CZ • H ↓ • H ↑ • CZ
[ b₄ ]ᴮ = H ↓ • CZ • H ↓ • H ↑ • CZ

[_]ᴰ : DBox → Circuit (₂₊ n)
[ d₁ ]ᴰ = CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↑
[ d₂ ]ᴰ = H ↓ • CZ • H ↓ • H ↑ • CZ • H ↑
[ d₃ ]ᴰ = H ↓ • H ↑ • S ↑ • CZ • H ↓ • H ↑ • CZ • H ↑
[ d₄ ]ᴰ = H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↑
