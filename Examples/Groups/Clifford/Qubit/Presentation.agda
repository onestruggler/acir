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

open import Data.Nat using (ℕ ; 2+ ; zero)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Presentation
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.Fin using (toℕ)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^'_ ; wmap)
open import Notations using (₁₊ ; ₂₊)

open import Presentation.Construct.Base using (_⊕^_ ; _⊎^_)
open import Presentation.Construct.Properties.Extension using (extension-presentation)

-- S : the Pauli presentation, over the generators (⊤ ⊎ ⊤) ⊎^ n
-- (an X- and a Z-generator per qupit).
open import Examples.Groups.Pauli.Presentation p-2 p-prime using (Γ-H)

-- The Pauli group as vectors, and the symplectic action act1.
open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pX ; pZ ; pI ; pIₙ)
open import Examples.Groups.Symplectic.Action p-2 p-prime using (act1)

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

-- A Pauli generator names a single-qupit X or Z at one position; read it
-- back as a basis vector of the Pauli group.
genToVec : ∀ {n} → PauliGen n → Pauli n
genToVec {₁₊ zero}  (inj₁ tt)        = pX ∷ []
genToVec {₁₊ zero}  (inj₂ tt)        = pZ ∷ []
genToVec {₂₊ n} (inj₁ (inj₁ tt)) = pX ∷ pIₙ
genToVec {₂₊ n} (inj₁ (inj₂ tt)) = pZ ∷ pIₙ
genToVec {₂₊ n} (inj₂ y)         = pI ∷ genToVec {₁₊ n} y

-- Delog a Pauli vector to a word: position i with exponents (a , b) becomes
-- X_i^a • Z_i^b, positions laid out left to right.
vecToWord : ∀ {n} → Pauli n → Word (PauliGen n)
vecToWord {zero}     []              = ε
vecToWord {₁₊ zero}  ((a , b) ∷ []) =
  [ inj₁ tt ]ʷ ^' toℕ a • [ inj₂ tt ]ʷ ^' toℕ b
vecToWord {₂₊ n} ((a , b) ∷ ps) =
  ([ inj₁ (inj₁ tt) ]ʷ ^' toℕ a • [ inj₁ (inj₂ tt) ]ʷ ^' toℕ b)
  • wmap inj₂ (vecToWord {₁₊ n} ps)

-- conj g y : the symplectic action of the quotient generator g on the Pauli
-- generator y, read back into a word.
conj : ∀ {n} → Gen n → PauliGen n → Word (PauliGen n)
conj g y = vecToWord (act1 g (genToVec y))

-- corr r : the Pauli correction word carried by the symplectic relator r
-- when the two sides are lifted to Clifford, i.e. [ lhs ]ᵣ ≈ [ corr r ]ₗ •
-- [ rhs ]ᵣ.  For odd p the extension splits (Selinger; the metaplectic
-- section is a genuine homomorphism modulo Pauli), so every correction is
-- the empty word — the trivial `no-twist` cocycle of Extension.agda, giving
-- the semidirect product Pauli ⋊ Sp.  At p = 2 the extension is *non-split*:
-- e.g. order-S then carries S² = Z on the top qupit, and the selinger-c1x
-- relators carry their own Pauli corrections.
corr : ∀ {n} {u v} → (n QRel,_===_) u v → Word (PauliGen n)
corr _ = ε

------------------------------------------------------------------------
-- The Clifford presentation, as an extension of Pauli by the symplectic
-- group.

Clifford-pres : (n : ℕ) → WRel (PauliGen n ⊎ Gen n)
Clifford-pres n = extension-presentation (Γ-H ⊕^ n) (n QRel,_===_) conj corr
