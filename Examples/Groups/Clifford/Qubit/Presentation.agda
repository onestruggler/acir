------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit (more generally n-qupit) Clifford group, presented as a
-- group extension (Selinger, arXiv:1310.6813).
--
--     1 ─→ Pauli n ─→ Clifford n ─→ Sp(2n, p) ─→ 1
--
-- The Pauli group is normal and the quotient is the symplectic group.
-- Using Presentation.Construct.Properties.Extension (Proposition 2.55),
-- a presentation of the extension is
--
--     extension-presentation S R̄ conj corr
--
-- where
--   * S    = the Pauli presentation      (Examples.Groups.Pauli.Presentation),
--   * R̄    = the symplectic relations     (Symplectic._QRel,_===_),
--   * conj = the symplectic action of a quotient generator on a Pauli
--            generator (the word-valued form of Symplectic.Action.act1),
--   * corr = the cocycle: the Pauli correction word carried by each
--            symplectic relator when it is lifted to Clifford (e.g. at
--            p = 2, S² = Z).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Presentation
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Word.Base using (Word ; WRel)

open import Presentation.Construct.Base using (_⊕^_ ; _⊎^_)
open import Presentation.Construct.Properties.Extension using (extension-presentation)

-- S : the Pauli presentation, over the generators (⊤ ⊎ ⊤) ⊎^ n
-- (an X- and a Z-generator per qupit).
open import Examples.Groups.Pauli.Presentation p-2 p-prime using (Γ-H)

-- R̄ : the symplectic relations, over the Clifford generators Gen n.
open import Examples.Groups.Symplectic.Symplectic-Derived p-2 p-prime
open Symplectic-Derived-Gen using (Gen ; _QRel,_===_)

------------------------------------------------------------------------
-- Generator sets

-- The Pauli generators of n qupits: X_i and Z_i for each i.
PauliGen : ℕ → Set
PauliGen n = (⊤ ⊎ ⊤) ⊎^ n

------------------------------------------------------------------------
-- The two families of Clifford-specific data
--
-- conj g y :   the word over Pauli generators equal, inside Clifford, to
--              the conjugate g · y · g⁻¹ of the Pauli generator y by the
--              quotient generator g.  Determined by Symplectic.Action.act1.
--
-- corr r :     the Pauli correction word by which the quotient relator r
--              fails to hold on the chosen Clifford lifts (the cocycle).

conj : ∀ {n} → Gen n → PauliGen n → Word (PauliGen n)
conj = {!!}

corr : ∀ {n} {u v} → (n QRel,_===_) u v → Word (PauliGen n)
corr = {!!}

------------------------------------------------------------------------
-- The Clifford presentation, as an extension of Pauli by the symplectic
-- group.

Clifford-pres : (n : ℕ) → WRel (PauliGen n ⊎ Gen n)
Clifford-pres n = extension-presentation (Γ-H ⊕^ n) (n QRel,_===_) conj corr
