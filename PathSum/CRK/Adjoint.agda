------------------------------------------------------------------------
-- Presentations of groups
--
-- The inverse of a circuit over {H, CNOT, R_k, R_k†} (Amy, QPL 2018,
-- sections 2.2 and 3)
--
-- Section 2.2 interprets a circuit "given a path-sum representation of
-- each gate in a basis B and their inverses", and section 3 checks a
-- circuit C against a specification ξ through the miter ⟦ C† ⟧ ∘ ξ.
-- This module is the syntax of that inverse for the paper's own gate
-- set (PathSum.CRK.Circuit): C† runs the gates of C last to first,
-- each replaced by its inverse.  H and CNOT are their own inverses,
-- and R_k and R_k† are each other's -- definition 2.9 lists R_k†
-- beside R_k for exactly this.  So, unlike PathSum.Adjoint for
-- {H , S , CZ}, where S† has to be spelled S S S, the inverse of a
-- gate is again a single gate, inv is an involution, and C † † is C on
-- the nose (†-involutive).  As a list, C† is reverse C with every gate
-- inverted (†-reverse).  Inverting keeps the number of Hadamards
-- (norm-†) and the largest k of an R_k or R_k† (level-†), so the
-- miter of two Clifford circuits (level at most 2) is again Clifford.
--
-- This is the first module of a package extending sections 3 and 4
-- to circuits over {H, CNOT, R_k, R_k†}, as PathSum.Adjoint,
-- PathSum.Miter and PathSum.Equivalence do for {H , S , CZ}:
--
--  1. PathSum.CRK.Adjoint (this module): inv, _†, and how norm and
--     level behave under ++ and †.
--  2. PathSum.Adjoint.Gates: the facts about the three kinds of gate
--     matrix of PathSum.Unitarity.Gates -- a Hadamard, a diagonal
--     phase, a CNOT -- that both gate sets share: H H = 2, CNOT CNOT = 1
--     and a phase undone by its negation, as unnormalised matrices; and
--     how each commutes with conjugation in Z[ζ] (PathSum.Ring's conj).
--  3. PathSum.CRK.Miter: C† undoes C on both sides at the level of
--     matrices, up to 2^(norm C), gate by gate and with no appeal to
--     unitarity (†-cancelʳ, †-cancelˡ); the miter of a circuit against
--     a specification, on columns (spec-miter); and the miter of two
--     circuits, ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ⟦ C₁ ++ C₂ † ⟧ ≋ idPS (miter).  The
--     proofs are PathSum.Miter's, over PathSum.CRK.Semantics.
--  4. PathSum.CRK.Equivalence: equivalence of two Clifford circuits
--     (level at most 2) by the paper's route, corollary 4.4 by Gaussian
--     elimination (PathSum.Gauss.Corollary) at the miter C₁ ++ C₂ †:
--     characterised (equivalence-gauss and its companions) and decided
--     (equivalence-decidable-gauss).
--  5. PathSum.Adjoint.Conjugate and PathSum.CRK.Conjugate: the adjoint
--     proper, for both gate sets.  The amplitude of ⟦ C† ⟧ from x to z
--     is the conjugate of that of ⟦ C ⟧ from z to x (circuit-adjoint):
--     the path-sum of C† is the conjugate transpose.  The transpose is
--     PathSum.Unitarity's and PathSum.CRK.Unitarity's circuit-transpose
--     (the matrix of C transposed is that of reverse C); what is added
--     is that inverting every gate conjugates the matrix entry by entry
--     (conj-apply), since each gate matrix has integer entries apart
--     from its phases, and the inverse gate carries the opposite phase.
--
-- Only the syntax is here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.CRK.Adjoint (M : ℕ) where

open import Data.List.Base using ([]; _∷_; _++_; reverse; map)
open import Data.List.Properties using
  (map-++; unfold-reverse; ++-assoc; ++-identityʳ)
open import Data.Nat.Base using (suc; _+_; _⊔_; _≤_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; norm; level)

import Data.Nat.Properties as ℕ

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The inverse of a gate, and of a circuit

-- H and CNOT are self-inverse; R_k and R_k† are each other's inverse.

inv : Gate n → Gate n
inv (H w)        = H w
inv (CNOT c t p) = CNOT c t p
inv (R k w)      = R† k w
inv (R† k w)     = R k w

inv-involutive : (g : Gate n) → inv (inv g) ≡ g
inv-involutive (H _)        = refl
inv-involutive (CNOT _ _ _) = refl
inv-involutive (R _ _)      = refl
inv-involutive (R† _ _)     = refl

-- The gates of C† are those of C, inverted, in the opposite order.
-- The fixity makes C₁ ++ C₂ † the circuit C₁ followed by C₂†, and
-- lets C † † parse.

infixl 8 _†

_† : Circuit n → Circuit n
[]      † = []
(g ∷ C) † = C † ++ inv g ∷ []


------------------------------------------------------------------------
-- As a list

-- C† is reverse C with each gate inverted.

†-reverse : (C : Circuit n) → C † ≡ map inv (reverse C)
†-reverse []      = refl
†-reverse (g ∷ C) =
  trans (cong (λ D → D ++ inv g ∷ []) (†-reverse C))
    (trans (sym (map-++ inv (reverse C) (g ∷ [])))
           (cong (map inv) (sym (unfold-reverse g C))))

-- The inverse of a concatenation is the concatenation of the inverses,
-- in the opposite order.

†-++ : (C D : Circuit n) → (C ++ D) † ≡ D † ++ C †
†-++ []      D = sym (++-identityʳ (D †))
†-++ (g ∷ C) D =
  trans (cong (λ E → E ++ inv g ∷ []) (†-++ C D))
        (++-assoc (D †) (C †) (inv g ∷ []))

-- Inverting twice gives the circuit back, gate for gate.

†-involutive : (C : Circuit n) → C † † ≡ C
†-involutive []      = refl
†-involutive (g ∷ C) =
  trans (†-++ (C †) (inv g ∷ []))
        (cong₂ _∷_ (inv-involutive g) (†-involutive C))


------------------------------------------------------------------------
-- Normalisation

-- The normalisation counts Hadamards, so it adds up along a
-- concatenation, and inverting a gate or a circuit leaves it alone.

norm-++ : (C D : Circuit n) → norm (C ++ D) ≡ norm C + norm D
norm-++ []                D = refl
norm-++ (H _ ∷ C)         D = cong suc (norm-++ C D)
norm-++ (CNOT _ _ _ ∷ C)  D = norm-++ C D
norm-++ (R _ _ ∷ C)       D = norm-++ C D
norm-++ (R† _ _ ∷ C)      D = norm-++ C D

norm-inv : (g : Gate n) → norm (inv g ∷ []) ≡ norm (g ∷ [])
norm-inv (H _)        = refl
norm-inv (CNOT _ _ _) = refl
norm-inv (R _ _)      = refl
norm-inv (R† _ _)     = refl

norm-† : (C : Circuit n) → norm (C †) ≡ norm C
norm-† []      = refl
norm-† (g ∷ C) =
  trans (norm-++ (C †) (inv g ∷ []))
    (trans (cong₂ _+_ (norm-† C) (norm-inv g))
      (trans (ℕ.+-comm (norm C) (norm (g ∷ [])))
             (sym (norm-++ (g ∷ []) C))))


------------------------------------------------------------------------
-- Level

-- The level is the largest k of an R_k or R_k†, so it is a maximum
-- along a concatenation, and inverting a gate or a circuit leaves it
-- alone.

level-++ : (C D : Circuit n) → level (C ++ D) ≡ level C ⊔ level D
level-++ []                D = refl
level-++ (H _ ∷ C)         D = level-++ C D
level-++ (CNOT _ _ _ ∷ C)  D = level-++ C D
level-++ (R k _ ∷ C)       D =
  trans (cong (k ⊔_) (level-++ C D))
        (sym (ℕ.⊔-assoc k (level C) (level D)))
level-++ (R† k _ ∷ C)      D =
  trans (cong (k ⊔_) (level-++ C D))
        (sym (ℕ.⊔-assoc k (level C) (level D)))

level-inv : (g : Gate n) → level (inv g ∷ []) ≡ level (g ∷ [])
level-inv (H _)        = refl
level-inv (CNOT _ _ _) = refl
level-inv (R _ _)      = refl
level-inv (R† _ _)     = refl

level-† : (C : Circuit n) → level (C †) ≡ level C
level-† []      = refl
level-† (g ∷ C) =
  trans (level-++ (C †) (inv g ∷ []))
    (trans (cong₂ _⊔_ (level-† C) (level-inv g))
      (trans (ℕ.⊔-comm (level C) (level (g ∷ [])))
             (sym (level-++ (g ∷ []) C))))

-- The miter of two circuits of level at most d has level at most d:
-- in particular the miter of two Clifford circuits is Clifford.

level-miter : ∀ {d} (C₁ C₂ : Circuit n) → level C₁ ≤ d → level C₂ ≤ d →
              level (C₁ ++ C₂ †) ≤ d
level-miter {d = d} C₁ C₂ lv₁ lv₂ =
  subst (λ l → l ≤ d) (sym (trans (level-++ C₁ (C₂ †))
                           (cong (level C₁ ⊔_) (level-† C₂))))
        (ℕ.⊔-lub lv₁ lv₂)
