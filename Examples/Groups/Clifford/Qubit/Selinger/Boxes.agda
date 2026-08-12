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
-- Qubit numbering.  The paper numbers qubits from the top, so a
-- two-qubit box sits on qubits 0 and 1 and its generators are written
-- Hx 0, Hx 1, ZZx 0 1.  Here qubit 0 is the un-shifted wire, written
-- `w ↓`, and qubit 1 is one shift up, written `w ↑`; the controlled-Z of
-- Circuit.Base spans both.  The words below therefore say exactly what
-- Figure 1 says, gate for gate and qubit for qubit -- only the drawing
-- convention (which wire is on top) differs, and CZ is symmetric so
-- nothing turns on it.
--
-- Word order is the circuit order: `w • v` runs w first, then v, which
-- is how the paper reads its diagrams ("from left to right, i.e., in the
-- opposite order of the notation for matrix multiplication", §4).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.Boxes
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Notations using (₁₊ ; ₂₊)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime
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
