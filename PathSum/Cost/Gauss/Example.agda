------------------------------------------------------------------------
-- Presentations of groups
--
-- Gaussian elimination and corollary 4.4 in the cost model, run on
-- closed circuits (Amy, QPL 2018, section 4.1 and corollary 4.4)
--
-- Sanity checks of PathSum.Cost.Gauss and PathSum.Cost.Gauss.Corollary
-- at the precision M = 3, each computed by refl, on circuits over
-- {H, CNOT, R_k, R_k†}.
--
-- The elimination (interpret with PathSum.Cost.Interpreter.interpKᶜ,
-- then gaussᶜ 2):
--
--  * The swap of two wires by three CNOTs has no path variables and
--    the outputs x₁, x₀.  Elimination finds no pivot, and the finish
--    refutes wire 0 at the unit vector at 0 -- the input 10, which the
--    swap sends to 01 (swap-refuted).
--  * H twice has two path variables, the phase ½ y₀y₁ + ½ x₀y₁, and the
--    output y₀.  Elimination pivots on y₀, substitutes x₀ for it -- the
--    phase becomes x₀y₁, which vanishes modulo 1 and is dropped by the
--    re-canonicalisation -- and reifies the restriction with one path
--    variable left, internal, and no terms (hh-reified); the rule
--    [Elim] would remove the last variable.
--
-- The decision (PathSum.Cost.Gauss.Corollary.decideᴳᶜ, at M₀ = 0), with
-- the normalisation and the number of path variables of the normal
-- form it reads (normalOf), to show which way each answer is reached:
--
--  * H H is the identity: [Elim] removes the last path variable and
--    two factors of 1/√2, leaving no normalisation, no path variable and
--    the final test passes (hh-normal, hh-id);
--  * the swap is refuted by the elimination (swap-not-id);
--  * CNOT CNOT has no path variables and passes the final test
--    (cnot-cnot-normal, cnot-cnot-id); S alone fails it on its phase
--    ¼ x₀ (s-normal, s-not-id);
--  * H S H: the restriction has the phase ¼ y₀, [ω] removes y₀ and one
--    factor of 1/√2, and the final test fails on the normalisation left
--    (hsh-normal, hsh-not-id);
--  * H Z H (= X): the restriction has the phase ½ y₀ and no rule
--    applies, so a path variable is left and the answer is no -- by
--    lemma 4.2, the sum over y₀ vanishes (hzh-normal, hzh-not-id).
--
-- Equivalence by the miter (equivᴳᶜ): S S and Z (ss≡z); the swap by
-- CNOTs one way and the other (swap≡swap′); H⊗H CNOT(0,1) H⊗H and
-- CNOT(1,0) (flip≡cnot); and H against S (h≢s).
--
-- These are values of the programs, read in the cost model of
-- PathSum.Cost: a cost model, not a machine model; nothing is claimed
-- about Turing machines or complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Cost.Gauss.Example where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using ([]; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import PathSum.Cost using (value)
open import PathSum.Cost.Gauss 3 using (Outcome; refutes; reifies; gaussᶜ)
open import PathSum.Cost.Gauss.Corollary 0 using (decideᴳᶜ; equivᴳᶜ)
open import PathSum.Cost.Interpreter 3 using (interpKᶜ)
open import PathSum.Cost.Normalise 3 using (nk; nm; normaliseᶜ)
open import PathSum.CRK.Circuit 3 using (Circuit; H; CNOT; R; norm)
open import PathSum.Gauss.Forms using (point)
open import PathSum.Size.Sparse 3 using (terms)


------------------------------------------------------------------------
-- The elimination

-- The number of path variables and of terms a reification leaves.

leftover : ∀ {n} → Outcome n → Maybe (ℕ × ℕ)
leftover (refutes x)     = nothing
leftover (reifies {m} Q) = just (m , length (terms Q))

-- Interpret, then eliminate at order 2.

restrictᶜ : ∀ {n} → Circuit n → Outcome n
restrictᶜ C = value (gaussᶜ 2 (proj₂ (value (interpKᶜ C))))

-- The swap is refuted at the input 10.

swap : Circuit 2
swap = CNOT zero (suc zero) (λ ()) ∷ CNOT (suc zero) zero (λ ()) ∷
       CNOT zero (suc zero) (λ ()) ∷ []

swap-refuted : restrictᶜ swap ≡ refutes (point zero)
swap-refuted = refl

-- H twice: one internal path variable left, and the zero phase.

hh : Circuit 1
hh = H zero ∷ H zero ∷ []

hh-reified : leftover (restrictᶜ hh) ≡ just (1 , 0)
hh-reified = refl


------------------------------------------------------------------------
-- The decision

-- The normalisation and the number of path variables of the normal
-- form the decision reads, when the elimination reifies.

normalAt : ∀ {n} → ℕ → Outcome n → Maybe (ℕ × ℕ)
normalAt k (refutes x) = nothing
normalAt k (reifies Q) =
  just (nk (value (normaliseᶜ 2 k Q)) , nm (value (normaliseᶜ 2 k Q)))

normalOf : ∀ {n} → Circuit n → Maybe (ℕ × ℕ)
normalOf C = normalAt (norm C) (restrictᶜ C)

-- H H: [Elim] leaves nothing, and the final test passes.

hh-normal : normalOf hh ≡ just (0 , 0)
hh-normal = refl

hh-id : value (decideᴳᶜ hh) ≡ true
hh-id = refl

-- The swap: refuted by the elimination.

swap-not-id : value (decideᴳᶜ swap) ≡ false
swap-not-id = refl

-- CNOT CNOT: no path variables, and the final test passes.

cnot-cnot : Circuit 2
cnot-cnot = CNOT zero (suc zero) (λ ()) ∷ CNOT zero (suc zero) (λ ()) ∷ []

cnot-cnot-normal : normalOf cnot-cnot ≡ just (0 , 0)
cnot-cnot-normal = refl

cnot-cnot-id : value (decideᴳᶜ cnot-cnot) ≡ true
cnot-cnot-id = refl

-- S: no path variables, and the final test fails on the phase.

s : Circuit 1
s = R 2 zero ∷ []

s-normal : normalOf s ≡ just (0 , 0)
s-normal = refl

s-not-id : value (decideᴳᶜ s) ≡ false
s-not-id = refl

-- H S H: [ω] leaves one factor of 1/√2, and the final test fails.

hsh : Circuit 1
hsh = H zero ∷ R 2 zero ∷ H zero ∷ []

hsh-normal : normalOf hsh ≡ just (1 , 0)
hsh-normal = refl

hsh-not-id : value (decideᴳᶜ hsh) ≡ false
hsh-not-id = refl

-- H Z H: irreducible with a path variable left.

hzh : Circuit 1
hzh = H zero ∷ R 1 zero ∷ H zero ∷ []

hzh-normal : normalOf hzh ≡ just (2 , 1)
hzh-normal = refl

hzh-not-id : value (decideᴳᶜ hzh) ≡ false
hzh-not-id = refl


------------------------------------------------------------------------
-- Equivalence by the miter

-- S S = Z.

ss : Circuit 1
ss = R 2 zero ∷ R 2 zero ∷ []

z : Circuit 1
z = R 1 zero ∷ []

ss≡z : value (equivᴳᶜ ss z) ≡ true
ss≡z = refl

-- The swap, by CNOTs one way and the other.

swap′ : Circuit 2
swap′ = CNOT (suc zero) zero (λ ()) ∷ CNOT zero (suc zero) (λ ()) ∷
        CNOT (suc zero) zero (λ ()) ∷ []

swap≡swap′ : value (equivᴳᶜ swap swap′) ≡ true
swap≡swap′ = refl

-- Hadamards on both wires turn a CNOT around.

flip : Circuit 2
flip = H zero ∷ H (suc zero) ∷ CNOT zero (suc zero) (λ ()) ∷
       H zero ∷ H (suc zero) ∷ []

cnot : Circuit 2
cnot = CNOT (suc zero) zero (λ ()) ∷ []

flip≡cnot : value (equivᴳᶜ flip cnot) ≡ true
flip≡cnot = refl

-- H is not S.

h≢s : value (equivᴳᶜ (H zero ∷ []) s) ≡ false
h≢s = refl
