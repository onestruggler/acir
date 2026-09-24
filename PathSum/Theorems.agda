------------------------------------------------------------------------
-- Presentations of groups
--
-- The results of the path-sum calculus, at the denotation in Z[ζ]
--
-- PathSum.Clifford proves section 4.3 over the semantic interface of
-- PathSum.Semantics, and PathSum.Denotation builds a value of that
-- interface out of the cyclotomic integers.  Instantiating the one at
-- the other is what makes the section unconditional; this module
-- states the results in that form.  Lemma 4.1 (PathSum.Isometry) and
-- proposition 2.10 over {H, S, CZ} (PathSum.CircuitSemantics) then
-- carry corollary 4.4 from the restricted path-sum it reduces back to
-- the circuit itself, and PathSum.Syntactic shows the end of the
-- reduction is a syntactic test: a Clifford circuit is the identity
-- exactly when its restriction reduces to a path-sum with the
-- identity's polynomials (corollary-4-4-syntactic).
--
-- Not formalised: the polynomial time bounds (proposition 3.2,
-- corollary 4.4); the rule [Case], and [HH], [ω] and lemma 4.2 for
-- quotients that are not Z₂-linear; circuits with CNOT or R_k (the
-- circuit results are over {H, S, CZ}, which generates the Clifford
-- group), with the Gaussian elimination their outputs would need;
-- composition of path-sums (definition 2.6, proposition 2.7) and
-- propositions 2.14-2.15; constant inputs; equivalence of two
-- circuits, as opposed to one being the identity; unitarity of ⟦ C ⟧
-- beyond unit trace-form column norms; and that definition 2.4 implies
-- WellFormed, argued in prose in PathSum.Isometry.
--
-- Each section's banner names the module the proof lives in, or none
-- when it is proved here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _<_)

module PathSum.Theorems (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (_+_; _^_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Subset using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (≤-reflexive)
open import Data.Product.Base using (_×_; _,_; ∃; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans)
open import Relation.Nullary.Decidable using (Dec; no; map′)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.AssignSum using (Σᶻ)
open import PathSum.Circuit M using
  (Gate; H; S; CZ; Circuit; norm; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.Cyclotomic M₀ using (_≐_; scale; scale-map)
open import PathSum.Norm M₀ using (‖_‖²)
open import PathSum.Order M
open import PathSum.Polynomial
open import PathSum.Reduction M hiding (⟶*-length)

import PathSum.Circuit
module Circ = PathSum.Circuit M

import PathSum.Reduction
module Red = PathSum.Reduction M

import PathSum.Denotation
module Den = PathSum.Denotation M₀

open Den using (Assign; hits; amp; _≋_; semantics)

import PathSum.Clifford
module Cliff = PathSum.Clifford M₀ semantics

import PathSum.Identity
module Idn = PathSum.Identity M₀

import PathSum.Isometry
module Isom = PathSum.Isometry M₀

open Isom using (WellFormed; Restriction-id)

import PathSum.CircuitAmp
module CAmp = PathSum.CircuitAmp M₀

import PathSum.CircuitSemantics
module CSem = PathSum.CircuitSemantics M₀

open CSem using (Column; δ; applyᴬ)

import PathSum.Decide
module Dcd = PathSum.Decide M₀

import PathSum.Syntactic
module Syn = PathSum.Syntactic M₀

private
  variable
    n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Definition 2.3 is an equivalence (PathSum.Denotation)

≋-refl : {ξ : PathSum n k m} → ξ ≋ ξ
≋-refl {ξ = a} = Den.≋-refl {ξ = a}

≋-sym : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ≋ ζ → ζ ≋ ξ
≋-sym {ξ = a} {ζ = b} = Den.≋-sym {ξ = a} {ζ = b}

≋-trans : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
          {χ : PathSum n k″ m″} → ξ ≋ ζ → ζ ≋ χ → ξ ≋ χ
≋-trans {ξ = a} {ζ = b} {χ = d} =
  Den.≋-trans {ξ = a} {ζ = b} {χ = d}


------------------------------------------------------------------------
-- Definition 2.9 and proposition 2.10, over {H, S, CZ}
-- (PathSum.Circuit, PathSum.CircuitSemantics)

-- ⟦ C ⟧ is the path-sum of the circuit, every Hadamard allocating a
-- path variable.  Its entry from x to z is the z-th amplitude of the
-- column the gates of C produce from the basis column δ x, each
-- acting by its own matrix: the path-sum computes the circuit's
-- operator, both unnormalised by the same √2^(norm C).

prop-2-10 : (C : Circuit n) (x z : Assign n) →
            amp ⟦ C ⟧ x z ≐ applyᴬ C (δ x) z
prop-2-10 = CSem.prop-2-10

-- Once divided by √2^(norm C), every column of that operator has norm
-- 1 in the trace form of PathSum.Norm -- the bound lemma 4.1 asks for
-- (WellFormed).  That ⟦ C ⟧ is unitary (true: it is a product of
-- unitary gate matrices) is not stated.

circuit-unit-columns : (C : Circuit n) (x : Assign n) →
                       Σᶻ (λ z → ‖ amp ⟦ C ⟧ x z ‖²) ≡ + (2 ^ norm C)
circuit-unit-columns = CSem.⟦⟧-unit-columns

-- So "⟦ C ⟧ is the identity" means what it should: the circuit's
-- matrix, computed gate by gate, is the identity matrix.

circuit-≋-id : (C : Circuit n) →
               (⟦ C ⟧ ≋ idPS ⇔
                (∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z)))
circuit-≋-id C = mk⇔
  (λ eq x z i → trans (sym (prop-2-10 C x z i))
    (trans (eq x z i) (scale-map (norm C) (CAmp.ampˢ-init x z) i)))
  (λ eq x z i → trans (prop-2-10 C x z i)
    (trans (eq x z i) (sym (scale-map (norm C) (CAmp.ampˢ-init x z) i))))


------------------------------------------------------------------------
-- Proposition 3.1 for [Elim], [ω] and [HH] (PathSum.Denotation)

-- The rules as PathSum.Reduction has them: each eliminates the first
-- path variable, and the quotients of [ω] and [HH] are Z₂-linear
-- forms -- all that lemma 4.3 needs.  [Case] is not formalised.

⟶-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ ζ → ξ ≋ ζ
⟶-sound {ξ = a} {ζ = b} = Den.⟶-sound {ξ = a} {ζ = b}


------------------------------------------------------------------------
-- Proposition 3.2: strong normalization (PathSum.Reduction)

-- Every rule removes exactly one path variable, so the length of a
-- chain is the number of path variables it removes -- in particular
-- no chain is longer than the path-sum has, and none is infinite.

⟶*-length : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
            (steps : ξ ⟶* ζ) → len steps + m′ ≡ m
⟶*-length = Red.⟶*-length


------------------------------------------------------------------------
-- Lemma 4.1: isometry restrictions (PathSum.Isometry)

-- Restriction-id ξ is ξ|f(x,y)=x ≡ |x⟩ ↦ |x⟩: at every x, the paths
-- carrying x back to x sum to the normalised 1.  WellFormed ξ bounds
-- the trace-form norm of every column of U_ξ by 1.  The module header
-- argues, in prose, that definition 2.4 implies it for path-sums whose
-- inputs are all variables (the only ones PathSum.Base can express),
-- so, granted that argument, for those the lemma assumes no more than
-- the paper does.

lemma-4-1 : (ξ : PathSum n k m) → WellFormed ξ →
            (ξ ≋ idPS ⇔ Restriction-id ξ)
lemma-4-1 = Isom.lemma-4-1


------------------------------------------------------------------------
-- Lemma 4.2: destructive interference (PathSum.Denotation)

-- For a quotient ½Q with Q a non-zero Z₂-linear form in the inputs,
-- liftXor c S; the paper allows any Boolean-valued Q, but the linear
-- case is all lemma 4.3 needs.

interference :
  (ξ : PathSum n k (suc m)) (c : Bool) (S : Mon n m) →
  head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
  (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
  proj₂ S ≡ ⊥ → ¬ (c ≡ false × S ≡ 1ᵐ) →
  ¬ (ξ ≋ idPS)
interference = Den.interference-lemma


------------------------------------------------------------------------
-- Lemma 4.3: Clifford progress and preservation (PathSum.Clifford)

-- The case the paper leaves implicit -- [ω] consumes one unit of
-- normalisation and [Elim] two, and nothing in the hypotheses
-- supplies them -- is discharged rather than reported: such a
-- path-sum is not the identity, so the hypothesis rules it out.

lemma-4-3 : (ξ : PathSum n k (suc m)) → Internal ξ → Ord≤ 2 (phase ξ) →
            ξ ≋ idPS →
            ∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ m) →
              (ξ ⟶ ξ′) × Ord≤ 2 (phase ξ′)
lemma-4-3 = Cliff.lemma-4-3


------------------------------------------------------------------------
-- Corollary 4.4: a path-sum without path variables, or a refutation
-- (PathSum.Clifford)

corollary-4-4 : (ξ : PathSum n k m) → Internal ξ → Ord≤ 2 (phase ξ) →
                Cliff.Reduces ξ
corollary-4-4 = Cliff.corollary-4-4


------------------------------------------------------------------------
-- The hypotheses of corollary 4.4, at a Clifford circuit
-- (PathSum.Circuit)

-- Neither hypothesis holds of an arbitrary path-sum, and neither is
-- meant to: corollary 4.4 applies lemma 4.3 to the isometry
-- restriction of section 4.1, ⟦ C ⟧ᴿ below, whose output signature is
-- the identity.  Both are theorems of that path-sum -- every path
-- variable is internal because no output mentions one, and the phase
-- is of order two because a Clifford gate contributes ¼ u or ½ u v.

circuit-Internal : (C : Circuit n) → Internal ⟦ C ⟧ᴿ
circuit-Internal = Circ.⟦⟧ᴿ-Internal

circuit-Ord≤ : (C : Circuit n) → Ord≤ 2 (phase ⟦ C ⟧ᴿ)
circuit-Ord≤ = Circ.⟦⟧ᴿ-Ord≤

-- So the corollary applies to every Clifford circuit unconditionally.

corollary-4-4-circuit : (C : Circuit n) → Cliff.Reduces ⟦ C ⟧ᴿ
corollary-4-4-circuit C =
  Cliff.corollary-4-4 ⟦ C ⟧ᴿ (circuit-Internal C) (circuit-Ord≤ C)


------------------------------------------------------------------------
-- Lemma 4.1 at a circuit (PathSum.CircuitSemantics, PathSum.Isometry)

-- ⟦ C ⟧ satisfies WellFormed, and ⟦ C ⟧ᴿ is its isometry restriction,
-- reified: the two have the same diagonal, and no path of ⟦ C ⟧ᴿ
-- leaves its input.  So whether the circuit is the identity is exactly
-- whether ⟦ C ⟧ᴿ is -- the question the reduction answers.

circuit-WellFormed : (C : Circuit n) → WellFormed ⟦ C ⟧
circuit-WellFormed C x = ≤-reflexive (circuit-unit-columns C x)

lemma-4-1-circuit : (C : Circuit n) → (⟦ C ⟧ ≋ idPS ⇔ ⟦ C ⟧ᴿ ≋ idPS)
lemma-4-1-circuit C = mk⇔ to from
  where
  whole : ⟦ C ⟧ ≋ idPS ⇔ Restriction-id ⟦ C ⟧
  whole = Isom.lemma-4-1 ⟦ C ⟧ (circuit-WellFormed C)

  restricted : ⟦ C ⟧ᴿ ≋ idPS ⇔ Restriction-id ⟦ C ⟧ᴿ
  restricted = Isom.diagonal-≋ ⟦ C ⟧ᴿ (CSem.⟦⟧ᴿ-diagonal C)

  to : ⟦ C ⟧ ≋ idPS → ⟦ C ⟧ᴿ ≋ idPS
  to eq = Equivalence.from restricted (λ x i →
    trans (CSem.⟦⟧ᴿ-restricts C x i) (Equivalence.to whole eq x i))

  from : ⟦ C ⟧ᴿ ≋ idPS → ⟦ C ⟧ ≋ idPS
  from eq = Equivalence.from whole (λ x i →
    trans (sym (CSem.⟦⟧ᴿ-restricts C x i))
          (Equivalence.to restricted eq x i))


------------------------------------------------------------------------
-- Proposition 3.1 along a chain (PathSum.Clifford)

⟶*-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶* ζ → ξ ≋ ζ
⟶*-sound = Cliff.⟶*-sound


------------------------------------------------------------------------
-- Whether a reduced path-sum is the identity (PathSum.Identity)

-- What the corollary stops short of: `done` says the path variables
-- are exhausted, not that what is left is the identity.  id-if is the
-- criterion stated coefficient by coefficient, and each refutation a
-- disproof at one input.  id-if is also necessary (id⇔syntactic
-- below); the input-by-input form id-if′, with the refutations, covers
-- every case (decide-≋-id).

id-if : (ξ : PathSum n 0 0) →
        (∀ w → out ξ w ≈[ + 2 ] μ x[ w ]) →
        phase ξ ≈[ pow M ] 0ᴾ →
        ξ ≋ idPS
id-if = Idn.id-if

not-id-out : (ξ : PathSum n k 0) (x : Assign n) →
             (∀ y → hits ξ x y x ≡ false) → ¬ (ξ ≋ idPS)
not-id-out = Idn.not-id-out

not-id-norm : (ξ : PathSum n (suc k) 0) (x : Assign n) (y : Assign 0) →
              hits ξ x y x ≡ true → ¬ (ξ ≋ idPS)
not-id-norm = Idn.not-id-norm

not-id-phase : (ξ : PathSum n 0 0) (x : Assign n) (y : Assign 0) →
               hits ξ x y x ≡ true →
               ¬ (pow M ∣ eval (phase ξ) x y) → ¬ (ξ ≋ idPS)
not-id-phase = Idn.not-id-phase


------------------------------------------------------------------------
-- The verdict, transported back to the circuit

-- A reduct is equivalent to ⟦ C ⟧ᴿ (proposition 3.1 along the chain),
-- and lemma 4.1 at the circuit carries that to ⟦ C ⟧: a reduction that
-- lands on the identity proves the circuit is the identity, a reduct
-- that is not the identity proves it is not, and whichever way
-- corollary 4.4 ends, the question about the circuit is the question
-- about its outcome.

reduct≋ : (C : Circuit n) {ξ′ : PathSum n k′ 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
          (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS)
reduct≋ C {ξ′ = ξ′} steps = mk⇔
  (λ eq → ≋-trans {ξ = ξ′} {ζ = ⟦ C ⟧ᴿ} {χ = idPS}
            (≋-sym {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} (⟶*-sound steps))
            (Equivalence.to (lemma-4-1-circuit C) eq))
  (λ eq → Equivalence.from (lemma-4-1-circuit C)
            (≋-trans {ξ = ⟦ C ⟧ᴿ} {ζ = ξ′} {χ = idPS}
                     (⟶*-sound steps) eq))

circuit-id : (C : Circuit n) {ξ′ : PathSum n 0 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
             (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) →
             phase ξ′ ≈[ pow M ] 0ᴾ →
             ⟦ C ⟧ ≋ idPS
circuit-id C {ξ′} steps eqf eqP =
  Equivalence.from (reduct≋ C steps) (id-if ξ′ eqf eqP)

circuit-not-id : (C : Circuit n) {ξ′ : PathSum n k′ 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
                 ¬ (ξ′ ≋ idPS) → ¬ (⟦ C ⟧ ≋ idPS)
circuit-not-id C steps ¬id C≋id =
  ¬id (Equivalence.to (reduct≋ C steps) C≋id)

-- Corollary 4.4 about the circuit itself: either ⟦ C ⟧ᴿ reduces to a
-- path-sum with no path variables left, whose being the identity is
-- exactly the circuit's, or the reduction has already refuted the
-- circuit.

corollary-4-4-⟦⟧ : (C : Circuit n) →
  (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
     (⟦ C ⟧ᴿ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
  ⊎ ¬ (⟦ C ⟧ ≋ idPS)
corollary-4-4-⟦⟧ C with corollary-4-4-circuit C
... | Cliff.done {ξ′ = ξ′} steps = inj₁ (_ , ξ′ , steps , reduct≋ C steps)
... | Cliff.no-id ¬id =
  inj₂ (λ eq → ¬id (Equivalence.to (lemma-4-1-circuit C) eq))


------------------------------------------------------------------------
-- The identity, syntactically (PathSum.Syntactic)

-- A path-sum without path variables is the identity exactly when it
-- has the identity's polynomials: no normalisation, outputs that are
-- the inputs modulo 2 and a phase that vanishes modulo 2^M,
-- coefficient by coefficient.  The converse of id-if goes through
-- Möbius inversion (PathSum.Mobius).

id⇔syntactic : (ξ : PathSum n k 0) →
               (ξ ≋ idPS ⇔
                (k ≡ 0 ×
                 (∀ w → out ξ w ≈[ + 2 ] μ x[ w ]) ×
                 phase ξ ≈[ pow M ] 0ᴾ))
id⇔syntactic = Syn.id⇔syntactic

-- Corollary 4.4 as the paper states it (its proof: "either ⟦C⟧|f(x,y)=x
-- reduces to |x⟩ ↦ |x⟩ ... or ξ′ ≢ |x⟩ ↦ |x⟩"): a Clifford circuit is
-- the identity exactly when its restriction reduces to a path-sum that
-- is syntactically the identity.  The time bound is not formalised.

corollary-4-4-syntactic : (C : Circuit n) →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (⟦ C ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntactic {n} C = mk⇔ to from
  where
  Syntactically : ∀ {k′} → PathSum n k′ 0 → Set
  Syntactically {k′} ξ′ =
    k′ ≡ 0 × (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ

  reduced : ∀ {k′} (ξ′ : PathSum n k′ 0) → ⟦ C ⟧ᴿ ⟶* ξ′ →
            Syntactically ξ′ →
            ∃ λ (ξ″ : PathSum n 0 0) →
              (⟦ C ⟧ᴿ ⟶* ξ″) ×
              (∀ w → out ξ″ w ≈[ + 2 ] μ x[ w ]) × phase ξ″ ≈[ pow M ] 0ᴾ
  reduced ξ′ steps (refl , outs , ph) = ξ′ , steps , outs , ph

  pick : ⟦ C ⟧ ≋ idPS →
         (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
            (⟦ C ⟧ᴿ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
         ⊎ ¬ (⟦ C ⟧ ≋ idPS) →
         ∃ λ (ξ″ : PathSum n 0 0) →
           (⟦ C ⟧ᴿ ⟶* ξ″) ×
           (∀ w → out ξ″ w ≈[ + 2 ] μ x[ w ]) × phase ξ″ ≈[ pow M ] 0ᴾ
  pick eq (inj₁ (_ , ξ′ , steps , C⇔ξ′)) = reduced ξ′ steps
    (Equivalence.to (id⇔syntactic ξ′) (Equivalence.to C⇔ξ′ eq))
  pick eq (inj₂ ¬id) = contradiction eq ¬id

  to = λ eq → pick eq (corollary-4-4-⟦⟧ C)

  from : (∃ λ (ξ′ : PathSum n 0 0) →
            (⟦ C ⟧ᴿ ⟶* ξ′) ×
            (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ) →
         ⟦ C ⟧ ≋ idPS
  from (ξ′ , steps , outs , ph) = circuit-id C steps outs ph


------------------------------------------------------------------------
-- A decision procedure that follows corollary 4.4 (PathSum.Decide)

-- The same test input by input: a path-sum with no path variables is
-- the identity exactly when it spends no normalisation and, at every
-- input, its path returns the input with a phase that vanishes modulo
-- 2^M.  Every way that fails is one of the refutations above.

id⇔′ : (ξ : PathSum n 0 0) →
       (ξ ≋ idPS ⇔
        ((∀ x y → hits ξ x y x ≡ true) ×
         (∀ x y → pow M ∣ eval (phase ξ) x y)))
id⇔′ = Dcd.id⇔′

decide-≋-id : (ξ : PathSum n k 0) → Dec (ξ ≋ idPS)
decide-≋-id = Dcd.decide-≋-id

-- Reduce ⟦ C ⟧ᴿ, then test what is left.  Decidability as such is
-- elementary -- the matrix has finitely many entries in Z[ζ], each
-- decidably equal to the identity's -- and the type below does not
-- record the route; what the route adds is the reduction, whose content
-- is corollary-4-4-⟦⟧ and corollary-4-4-syntactic above.  (Polynomials
-- are functions on all 2^(n+m) monomials and the test visits every
-- input, so nothing here is polynomial-time.)

circuit-decidable : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
circuit-decidable C with corollary-4-4-⟦⟧ C
... | inj₁ (_ , ξ′ , _ , C⇔ξ′) =
  map′ (Equivalence.from C⇔ξ′) (Equivalence.to C⇔ξ′) (decide-≋-id ξ′)
... | inj₂ ¬id = no ¬id

matrix-decidable : (C : Circuit n) →
  Dec (∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z))
matrix-decidable C =
  map′ (Equivalence.to (circuit-≋-id C)) (Equivalence.from (circuit-≋-id C))
       (circuit-decidable C)
