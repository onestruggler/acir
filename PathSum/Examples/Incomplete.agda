------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 4: normal forms are not unique, and the calculus is
-- incomplete for Clifford+T
--
-- Section 4 of Amy's QPL 2018 paper says that "the normal forms are
-- not necessarily unique and hence our reduction system is
-- incomplete", and gives a witness: a two-qubit Clifford+T identity
-- from Selinger and Bian [29], drawn as a box of CNOT, X, T, H, T† and
-- H gates squared, "gives the irreducible path-sum"
--
--   |x1 x2⟩ ↦ 1/√2^8 Σ_{y ∈ Z₂^8} e^{2πi P(x,y)/8} |x1 y8⟩ ,
--
--   P = 2 + 6x1x2 + x2 + y1 + 4y1(x1 + x2 + y2) + 6y2 + 4y2y3 + 2y2x1
--       + 3y3 + 4y3(x1 + y4) + 4y4y5 + 6y4x1 + y5 + 4y5(x1 + y6) + 6y6
--       + 4y6y7 + 2y6x1 + 3y7 + 4y7(x1 + y8) + 7y8 .
--
-- Everything here is at the examples' precision M₀ = 0 (eighths), and
-- all of the paper's claims about the witness hold as printed.
--
-- * The printed path-sum is ξᴾ, with the paper's y1 … y8 as the path
--   variables 0 … 7 (so its outputs are x1 and the variable 7).
--
-- * ξᴾ is irreducible under all of figure 2 -- [Elim], [ω], [HH] and
--   [Case], at every path variable and pair of them (ξᴾ-irreducible,
--   PathSum.Full.Match's Irreducibleᶠ).  The proof is the certificate
--   of PathSum.Full.Obstruction, four coefficients at each of the 64
--   double renumberings, computed in seconds.  PathSum.Full.Match's
--   exact decider, irreducibleᶠ?, had not finished on ξᴾ after 14
--   minutes of checking under a 6 GB heap, when the run was cut off
--   (it computes a canonical quotient for every rule at every
--   renumbering, each a fold over every monomial).
--
-- * The circuit is reconstructed from the figure as SB, two copies of
--   the box SB-half, over {H, X, CNOT, T, T†} (PathSum.CRK.WithX: the
--   figure has X gates, which definition 2.9 does not; X is read as
--   |x⟩ ↦ |1 ⊕ x⟩).  Its path-sum, by definition 2.9 with its path
--   variables renumbered from newest-first into the order the
--   Hadamards introduce them, is congruent to ξᴾ, coefficient by
--   coefficient (SB-printed), hence equivalent to it (SB≋ξᴾ).  So the
--   printed polynomial is the circuit's: no erratum.
--
-- * The circuit is the identity (SB-id), hence so is ξᴾ (ξᴾ≋id).  No
--   rule proves it; it is checked by computing the circuit's 4×4
--   matrix gate by gate (PathSum.CRK.WithX.circuit-id!) -- the
--   "explicit expansion of the remaining variables" the paper suggests
--   for a complete procedure, and exponential in the number of qubits
--   and of Hadamards.  The box alone is not the identity
--   (SB-half-not-id): the square in the figure matters.
--
-- * The circuit's own path-sum ⟦ SB ⟧ is irreducible too
--   (SB-irreducible), so no chain of rules of figure 2 from it -- in
--   any order, at any variables -- reaches a path-sum without path
--   variables (SB-stuck).  That is the incompleteness
--   (incompleteness): SB is the identity, but the verdict of corollary
--   4.4, read off a reduct without path variables, is never available
--   for its path-sum.  For Clifford circuits it always is, from the
--   restriction ⟦ C ⟧ᴿ, and an irreducible reduct that keeps path
--   variables refutes the identity
--   (PathSum.Full.Clifford.corollary-4-4-normalᶠ); for Clifford+T an
--   irreducible path-sum with path variables can be the identity.
--
-- * Normal forms are not unique (normal-forms-not-unique): ξᴾ and the
--   identity idPS are equivalent and both irreducible, but have eight
--   path variables and none.  UniqueNormalForms is the weakest
--   uniqueness of normal forms up to equivalence -- that equivalent
--   irreducible path-sums have the same number of path variables -- so
--   every stronger one (syntactic equality, congruence up to
--   renumbering) fails with it.  (Confluence -- each path-sum reducing
--   to a single normal form -- is a different notion, not refuted here.)
--
-- Not formalised: footnote 2's complexity half (uniqueness would imply
-- P = co-NP; its logical half, that uniqueness would make expansion
-- unnecessary, is PathSum.Expand's unique⇒no-expansion), and
-- the restriction of section 4.1 for this gate set, so for this
-- example (the statements above are about ⟦ SB ⟧ itself, not about a
-- restriction of it).
--
-- Every statement about the closed circuit is made with one instance
-- of the denotation, D, and one of the gate set, CX, and proved
-- through a lemma stated for an arbitrary circuit (identity!,
-- not-identity!, renumbered!, through): a statement ⟦ SB ⟧ ≋ ζ written
-- with another instance's _≋_, or with a normalisation that differs
-- from the one written here (the numeral 8 against norm SB), is
-- matched against these only by unfolding both into amplitudes (a
-- first draft of this module that did so ran out of 900 s, where the
-- computations themselves take under a minute each).  A client
-- restating them must use D._≋_ and CX, as PathSum.ContractINCOMPLETE
-- does.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Incomplete where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst)
open import Relation.Nullary.Decidable using (True; False; toWitness)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base
open import PathSum.Polynomial hiding (subst)
open import PathSum.Full 3 using (_⟶ᶠ*_)
open import PathSum.Full.Match 3 using (Irreducibleᶠ)
open import PathSum.Full.Obstruction 3 using
  (irreducible!; no-paths-irreducible; irreducible-stuck)
open import PathSum.Examples.Base using
  (_⋆_; x₁; x₂; y₁; y₂; y₃; y₄; module Cong)

import PathSum.CRK.WithX
import PathSum.Denotation

-- The instances every statement below is made with.

module D  = PathSum.Denotation 0
module CX = PathSum.CRK.WithX 0

open D using (_≋_; ≋-sym; ≋-trans)

private
  variable
    n k′ m′ : ℕ


------------------------------------------------------------------------
-- The printed path-sum

private
  -- The paper's y5 … y8 (Examples.Base names y1 … y4).

  y₅ : ∀ {n m} → Mon n (suc (suc (suc (suc (suc m)))))
  y₅ = ⟪ y[ suc (suc (suc (suc zero))) ] ⟫

  y₆ : ∀ {n m} → Mon n (suc (suc (suc (suc (suc (suc m))))))
  y₆ = ⟪ y[ suc (suc (suc (suc (suc zero)))) ] ⟫

  y₇ : ∀ {n m} → Mon n (suc (suc (suc (suc (suc (suc (suc m)))))))
  y₇ = ⟪ y[ suc (suc (suc (suc (suc (suc zero))))) ] ⟫

  y₈ : ∀ {n m} →
       Mon n (suc (suc (suc (suc (suc (suc (suc (suc m))))))))
  y₈ = ⟪ y[ suc (suc (suc (suc (suc (suc (suc zero)))))) ] ⟫

-- P, term by term as printed, the products 4y_i(…) multiplied out.

Pᵖ : Poly 2 8
Pᵖ =
  (+ 2) ⋆ 1ᵐ +ᴾ (+ 6) ⋆ (x₁ ∪ᵐ x₂) +ᴾ (+ 1) ⋆ x₂ +ᴾ
  (+ 1) ⋆ y₁ +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₁) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ x₂) +ᴾ
  (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ
  (+ 6) ⋆ y₂ +ᴾ (+ 4) ⋆ (y₂ ∪ᵐ y₃) +ᴾ (+ 2) ⋆ (y₂ ∪ᵐ x₁) +ᴾ
  (+ 3) ⋆ y₃ +ᴾ (+ 4) ⋆ (y₃ ∪ᵐ x₁) +ᴾ (+ 4) ⋆ (y₃ ∪ᵐ y₄) +ᴾ
  (+ 4) ⋆ (y₄ ∪ᵐ y₅) +ᴾ (+ 6) ⋆ (y₄ ∪ᵐ x₁) +ᴾ
  (+ 1) ⋆ y₅ +ᴾ (+ 4) ⋆ (y₅ ∪ᵐ x₁) +ᴾ (+ 4) ⋆ (y₅ ∪ᵐ y₆) +ᴾ
  (+ 6) ⋆ y₆ +ᴾ (+ 4) ⋆ (y₆ ∪ᵐ y₇) +ᴾ (+ 2) ⋆ (y₆ ∪ᵐ x₁) +ᴾ
  (+ 3) ⋆ y₇ +ᴾ (+ 4) ⋆ (y₇ ∪ᵐ x₁) +ᴾ (+ 4) ⋆ (y₇ ∪ᵐ y₈) +ᴾ
  (+ 7) ⋆ y₈

-- Normalisation 8, eight path variables, outputs x1 and y8.

ξᴾ : PathSum 2 8 8
ξᴾ = ⟨ Pᵖ , outs ⟩
  where
  outs : Fin 2 → Poly 2 8
  outs zero       = μ x[ zero ]
  outs (suc zero) = μ y[ suc (suc (suc (suc (suc (suc (suc zero)))))) ]

-- No rule of figure 2 applies to it, at any variable or pair: the
-- obstruction is read at the input x1.

ξᴾ-irreducible : Irreducibleᶠ ξᴾ
ξᴾ-irreducible = irreducible! zero ξᴾ


------------------------------------------------------------------------
-- The circuit

-- The gates of the figure: a CNOT from the first wire to the second,
-- X on the first, and H, T = R 3 and T† = R† 3 on the second.

CNOT₁₂ X₁ H₂ T₂ T†₂ : CX.Gate 2
CNOT₁₂ = CX.CNOT zero (suc zero) (λ ())
X₁     = CX.X zero
H₂     = CX.H (suc zero)
T₂     = CX.R 3 (suc zero)
T†₂    = CX.R† 3 (suc zero)

-- One box, first gate first: the CNOT; X beside T (they commute);
-- H T H T†; again the CNOT, and X beside T; then H T† H T†.

SB-half : CX.Circuit 2
SB-half =
  CNOT₁₂ ∷ X₁ ∷ T₂ ∷ H₂ ∷ T₂ ∷ H₂ ∷ T†₂ ∷
  CNOT₁₂ ∷ X₁ ∷ T₂ ∷ H₂ ∷ T†₂ ∷ H₂ ∷ T†₂ ∷ []

-- The figure: the box squared.

SB : CX.Circuit 2
SB = SB-half ++ SB-half

-- The renumbering from the circuit's order of path variables (the
-- newest first) to the paper's (the order of the Hadamards): bring
-- variables 1, 2, …, 7 to the front in turn.

SB-renumbering : List (Fin 8)
SB-renumbering =
  suc zero ∷
  suc (suc zero) ∷
  suc (suc (suc zero)) ∷
  suc (suc (suc (suc zero))) ∷
  suc (suc (suc (suc (suc zero)))) ∷
  suc (suc (suc (suc (suc (suc zero))))) ∷
  suc (suc (suc (suc (suc (suc (suc zero)))))) ∷ []


------------------------------------------------------------------------
-- Statements about a circuit, for an arbitrary circuit

-- Each restates a lemma at the instances above, so that at the closed
-- circuit its conclusion is literally the declared type (see the
-- header).

-- The circuit is the identity, or is not, by computing its matrix.

identity! : (C : CX.Circuit n) → {True (CX.matrix-id? C)} →
            CX.⟦ C ⟧ ≋ idPS
identity! C {t} = CX.circuit-id! C {t}

not-identity! : (C : CX.Circuit n) → {False (CX.matrix-id? C)} →
                ¬ (CX.⟦ C ⟧ ≋ idPS)
not-identity! C {f} = CX.circuit-not-id! C {f}

-- The circuit's path-sum against a literal it is congruent to once its
-- path variables are renumbered.

renumbered! :
  (C : CX.Circuit n) (ζ : PathSum n k′ m′)
  (js : List (Fin (CX.paths C))) →
  (k≡k′ : CX.norm C ≡ k′) (m′≡p : m′ ≡ CX.paths C) →
  {True (Cong.congruent? (Cong.fronts js CX.⟦ C ⟧)
                         (subst (PathSum n k′) m′≡p ζ))} →
  CX.⟦ C ⟧ ≋ ζ
renumbered! C ζ js k≡k′ m′≡p {t} =
  Cong.renumbered-≋ CX.⟦ C ⟧ ζ js k≡k′ m′≡p {t}

-- A path-sum equivalent to an identity circuit is the identity.

through : (C : CX.Circuit n) (ζ : PathSum n k′ m′) →
          CX.⟦ C ⟧ ≋ ζ → CX.⟦ C ⟧ ≋ idPS → ζ ≋ idPS
through C ζ C≋ζ C≋id =
  ≋-trans {ξ = ζ} {ζ = CX.⟦ C ⟧} {χ = idPS}
    (≋-sym {ξ = CX.⟦ C ⟧} {ζ = ζ} C≋ζ) C≋id


------------------------------------------------------------------------
-- The circuit gives the printed path-sum

-- Renumbered, the circuit's path-sum is the printed one, coefficient
-- by coefficient (phase modulo 8, outputs modulo 2).

SB-printed : Cong.Congruent (Cong.fronts SB-renumbering CX.⟦ SB ⟧) ξᴾ
SB-printed = toWitness
  {a? = Cong.congruent? (Cong.fronts SB-renumbering CX.⟦ SB ⟧) ξᴾ} tt

-- Hence they are equivalent.

SB≋ξᴾ : CX.⟦ SB ⟧ ≋ ξᴾ
SB≋ξᴾ = renumbered! SB ξᴾ SB-renumbering refl refl


------------------------------------------------------------------------
-- The circuit is the identity

SB-id : CX.⟦ SB ⟧ ≋ idPS
SB-id = identity! SB

ξᴾ≋id : ξᴾ ≋ idPS
ξᴾ≋id = through SB ξᴾ SB≋ξᴾ SB-id

-- The box alone is not.

SB-half-not-id : ¬ (CX.⟦ SB-half ⟧ ≋ idPS)
SB-half-not-id = not-identity! SB-half


------------------------------------------------------------------------
-- Incompleteness

-- The circuit's path-sum is irreducible, so no chain of rules from it
-- ends without path variables.

SB-irreducible : Irreducibleᶠ CX.⟦ SB ⟧
SB-irreducible = irreducible! zero CX.⟦ SB ⟧

SB-stuck : ∀ {k′} {ζ : PathSum 2 k′ 0} → ¬ (CX.⟦ SB ⟧ ⟶ᶠ* ζ)
SB-stuck = irreducible-stuck CX.⟦ SB ⟧ SB-irreducible

-- A Clifford+T circuit that is the identity, whose path-sum no rule of
-- figure 2 reduces at all.

incompleteness :
  CX.⟦ SB ⟧ ≋ idPS × Irreducibleᶠ CX.⟦ SB ⟧ ×
  (∀ {k′} {ζ : PathSum 2 k′ 0} → ¬ (CX.⟦ SB ⟧ ⟶ᶠ* ζ))
incompleteness = SB-id , SB-irreducible , SB-stuck


------------------------------------------------------------------------
-- Normal forms are not unique

-- The weakest uniqueness of normal forms up to equivalence:
-- equivalent irreducible path-sums have as many path variables.

UniqueNormalForms : Set
UniqueNormalForms =
  ∀ {n k m k′ m′} (ξ : PathSum n k m) (ζ : PathSum n k′ m′) →
  Irreducibleᶠ ξ → Irreducibleᶠ ζ → ξ ≋ ζ → m ≡ m′

-- It fails at ξᴾ and the identity.

normal-forms-not-unique : ¬ UniqueNormalForms
normal-forms-not-unique unique =
  8≢0 (unique ξᴾ idPS ξᴾ-irreducible (no-paths-irreducible idPS) ξᴾ≋id)
  where
  8≢0 : ¬ (8 ≡ 0)
  8≢0 ()
