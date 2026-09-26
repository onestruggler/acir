------------------------------------------------------------------------
-- Presentations of groups
--
-- Translation validation of circuits over {H, CNOT, R_k, R_k†}
-- (Amy, QPL 2018, section 5.1)
--
-- Section 5.1 verifies an optimised circuit C₂ against its input C₁ --
-- Clifford+T circuits of any size, not Clifford ones -- by the
-- procedure of sections 3 and 4: form the miter, restrict it to the
-- paths with f(x,y) = x (section 4.1), reduce with the rules of figure
-- 2, and read the verdict off what is left; "to prove non-equivalence"
-- it uses lemma 4.2 on what is left (section 4.2).  Here that
-- procedure is formalised as the theorems it rests on, for circuits of
-- any level over the paper's own gate set (PathSum.CRK.Circuit; e.g.
-- Clifford+T at level 3):
--
--  * The miter of C₁ and C₂ is the circuit C₁ ++ C₂ † (PathSum.CRK.Miter;
--    PathSum.CRK.Miter.Compose relates it to the composite
--    ⟦ C₂ † ⟧ ∘ ⟦ C₁ ⟧ of section 3), and its isometry restriction is
--    reified by Gaussian elimination (PathSum.Gauss.Corollary's ⟦_⟧ᴿ).
--    Whatever the restriction ξ reduces to by any chain of all of
--    figure 2, at any variables (PathSum.Full's _⟶ᶠ*_), the circuits
--    are equivalent exactly when that reduct is the identity
--    (validation-reduct): lemma 4.1 at the miter, which is an
--    isometry, and proposition 3.1 along the chain.
--
--  * Soundness (validation-sound): if the chain ends without path
--    variables at the identity's polynomials -- no normalisation, the
--    inputs as outputs modulo 2, phase 0 modulo 1 -- then
--    ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧.  Conversely, a chain that ends without path
--    variables anywhere else refutes (validation-any: an end without
--    path variables decides the question syntactically, by
--    PathSum.Syntactic).
--
--  * The two refutations the paper uses.  The elimination finds no
--    solution of f(x,y) = x for some input (validation-refuted-gauss).
--    Or a reduct matches lemma 4.2 as corrected in
--    PathSum.Interference (validation-refuted-interference): its phase
--    is ½y₀Q + R with y₀ internal and Q free of path variables and not
--    ≡ 0, both modulo 2 -- so Q is odd at some input, at every path,
--    and the branches of y₀ cancel on the diagonal there.  (The paper
--    asks only that Q be non-zero, which is not enough; see
--    PathSum.Interference's counterexamples.)  The paper applies the
--    lemma at y₀; it holds at any path variable y_j
--    (validation-refuted-interference-at, with lemma 4.2 renumbered:
--    interference-at-var).
--
--  * Every miter reaches a normal form: the elimination refutes, or the
--    restriction reduces to a path-sum to which no rule of figure 2
--    applies and whose being the identity is the circuits' equivalence
--    (validation-normal-form, by PathSum.Full.Match).
--
-- The procedure is sound but not complete, as the paper says (section
-- 4: "the normal forms are not necessarily unique and hence our
-- reduction system is incomplete"; its example is a two-qubit
-- Clifford+T identity whose path-sum reduces to an irreducible one
-- with eight path variables left).  An irreducible normal form with
-- path variables left that matches no case of lemma 4.2 gives no
-- verdict, and nothing here claims otherwise.  That incompleteness is
-- not formalised as a statement: exhibiting it needs the
-- irreducibility of a particular normal form, a closed computation
-- over all 2^(2+8) monomials that was not attempted (and the circuit
-- is printed only as a figure).  For Clifford circuits (level at most 2)
-- the procedure is complete, along every chain: every step keeps the
-- restriction Clifford (PathSum.Full.Clifford), so by lemma 4.3 an
-- irreducible end with a path variable left refutes
-- (validation-clifford-refutes; the refutation is lemma 4.3's, which
-- besides lemma 4.2 may find the normalisation too small for the rule
-- the phase calls for),
-- and the circuits are equivalent exactly when the normal form has no
-- path variables and is syntactically the identity
-- (validation-clifford); hence a decision procedure along this route
-- (validation-decidable-clifford; decidability as such is elementary,
-- and the type does not record the route).
--
-- Not formalised: the polynomial time bounds, and the benchmarks of
-- table 1.  The paper's procedure is a program returning a verdict;
-- here the verdicts are theorems about any chain of reductions, and
-- the only procedures are the normal form and the Clifford decision.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CRK.Validation (M₀ : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (_++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; _≤_)
open import Data.Product.Base using (_×_; _,_; ∃; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Properties.Equivalence using ()
  renaming (trans to ⇔-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; no; map′)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere.Sound M₀ using (front-≋)
open import PathSum.Base using (PathSum; phase; out; idPS; y₀; head-part)
open import PathSum.CRK.Adjoint M using (_†; level-miter)
open import PathSum.CRK.Circuit M using (Circuit; norm; level; ⟦_⟧)
open import PathSum.CRK.Equivalence M₀ using (equivalence-refuted-gauss)
open import PathSum.CRK.Miter M₀ using (miter)
open import PathSum.Decide M₀ using (decide-≋-id)
open import PathSum.Denotation M₀ using (_≋_; ≋-trans)
open import PathSum.Full M using (_⟶ᶠ*_)
open import PathSum.Full.Clifford M₀ using
  (IsClifford; ⟶ᶠ*-Clifford; stuck-not-id)
open import PathSum.Full.Match M using (Irreducibleᶠ; normal-formᶠ)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Gauss.Corollary M₀ using
  (⟦_⟧ᴿ; reduct≋-gauss; ⟦⟧ᴿ-Internal; ⟦⟧ᴿ-Ord≤2)
open import PathSum.Identity M₀ using (id-if)
open import PathSum.Interference M₀ using (interferenceᴳ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Poly; μ; x[_]; y[_]; 0ᴾ; _·ᴾ_; _≈[_]_; NoVar)
open import PathSum.Reduction M using (½)
open import PathSum.Reorder using (front; _/ʸ_; NoVar-front)
open import PathSum.Syntactic M₀ using (id⇔syntactic)

private
  variable
    n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Lemma 4.2 at any path variable

-- Lemma 4.2 (corrected, PathSum.Interference) at y_j: renumbering y_j
-- to the front changes neither the denotation (front-≋) nor, by
-- definition, the quotient of the phase by y_j.

interference-at-var : (ξ : PathSum n k (suc m)) (j : Fin (suc m))
                      (Q : Poly n m) →
                      (phase ξ /ʸ j) ≈[ pow M ] (½ ·ᴾ Q) →
                      (∀ w → NoVar (+ 2) y[ j ] (out ξ w)) →
                      (∀ i → NoVar (+ 2) y[ i ] Q) →
                      ¬ (Q ≈[ + 2 ] 0ᴾ) →
                      ¬ (ξ ≋ idPS)
interference-at-var ξ j Q eqP eqf noy nonzero ξ≋id =
  interferenceᴳ (front j ξ) Q eqP
    (λ w → NoVar-front j (out ξ w) (eqf w)) noy nonzero
    (≋-trans {ξ = front j ξ} {ζ = ξ} {χ = idPS} (front-≋ j ξ) ξ≋id)


------------------------------------------------------------------------
-- The verdict of a reduct of the miter

-- Whatever the restriction of the miter reduces to, by any rules of
-- figure 2 at any variables, the circuits are equivalent exactly when
-- the reduct is the identity.  No bound on the level.

validation-reduct : (C₁ C₂ : Circuit n)
  {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ″ : PathSum n k″ m″} → ξ ⟶ᶠ* ξ″ →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ξ″ ≋ idPS)
validation-reduct C₁ C₂ {ξ} eq {ξ″} steps =
  ⇔-trans (miter C₁ C₂)
    (reduct≋-gauss (C₁ ++ C₂ †) eq {ξ′ = ξ″}
                   (⟶ᶠ*-sound {ξ = ξ} {ζ = ξ″} steps))


------------------------------------------------------------------------
-- Soundness

-- A chain to the identity's polynomials proves the circuits
-- equivalent ...

validation-sound : (C₁ C₂ : Circuit n)
  {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ′ : PathSum n 0 0} → ξ ⟶ᶠ* ξ′ →
  (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) → phase ξ′ ≈[ pow M ] 0ᴾ →
  ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧
validation-sound C₁ C₂ eq {ξ′} steps outs ph =
  Equivalence.from (validation-reduct C₁ C₂ eq {ξ″ = ξ′} steps)
                   (id-if ξ′ outs ph)

-- ... and any chain that ends without path variables decides the
-- question syntactically.

validation-any : (C₁ C₂ : Circuit n)
  {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ′ : PathSum n k′ 0} → ξ ⟶ᶠ* ξ′ →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
validation-any C₁ C₂ eq {ξ′} steps =
  ⇔-trans (validation-reduct C₁ C₂ eq {ξ″ = ξ′} steps) (id⇔syntactic ξ′)


------------------------------------------------------------------------
-- The two refutations

-- The elimination finds no solution of f(x,y) = x.

validation-refuted-gauss : (C₁ C₂ : Circuit n) →
                           ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ nothing →
                           ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
validation-refuted-gauss = equivalence-refuted-gauss

-- A reduct matches lemma 4.2 at y₀: its phase is ½y₀Q + R with y₀
-- internal and Q free of path variables and not even.

validation-refuted-interference : (C₁ C₂ : Circuit n)
  {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ″ : PathSum n k″ (suc m″)} → ξ ⟶ᶠ* ξ″ →
  (Q : Poly n m″) →
  head-part (phase ξ″) ≈[ pow M ] (½ ·ᴾ Q) →
  (∀ w → NoVar (+ 2) y₀ (out ξ″ w)) →
  (∀ j → NoVar (+ 2) y[ j ] Q) →
  ¬ (Q ≈[ + 2 ] 0ᴾ) →
  ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
validation-refuted-interference C₁ C₂ eq {ξ″} steps Q eqP eqf noy nonzero
  e = interferenceᴳ ξ″ Q eqP eqf noy nonzero
        (Equivalence.to (validation-reduct C₁ C₂ eq {ξ″ = ξ″} steps) e)

-- The same at any path variable y_j of the reduct.

validation-refuted-interference-at : (C₁ C₂ : Circuit n)
  {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ″ : PathSum n k″ (suc m″)} → ξ ⟶ᶠ* ξ″ →
  (j : Fin (suc m″)) (Q : Poly n m″) →
  (phase ξ″ /ʸ j) ≈[ pow M ] (½ ·ᴾ Q) →
  (∀ w → NoVar (+ 2) y[ j ] (out ξ″ w)) →
  (∀ i → NoVar (+ 2) y[ i ] Q) →
  ¬ (Q ≈[ + 2 ] 0ᴾ) →
  ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
validation-refuted-interference-at C₁ C₂ eq {ξ″} steps j Q eqP eqf noy
  nonzero e = interference-at-var ξ″ j Q eqP eqf noy nonzero
                (Equivalence.to (validation-reduct C₁ C₂ eq {ξ″ = ξ″} steps) e)


------------------------------------------------------------------------
-- Normal forms

-- The elimination refutes, or the miter's restriction reduces to an
-- irreducible path-sum whose being the identity is the circuits'
-- equivalence.  Whether that end gives a verdict is another matter:
-- beyond Clifford circuits it may not.

private
  NormalVerdict : Circuit n → Circuit n → Set
  NormalVerdict {n} C₁ C₂ =
    (∃ λ m′ → ∃ λ (ξ : PathSum n (norm (C₁ ++ C₂ †)) m′) →
       ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) ×
       ∃ λ k″ → ∃ λ m″ → ∃ λ (ξ′ : PathSum n k″ m″) →
         (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′ × (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ξ′ ≋ idPS))
    ⊎ ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)

validation-normal-form : (C₁ C₂ : Circuit n) →
  (∃ λ m′ → ∃ λ (ξ : PathSum n (norm (C₁ ++ C₂ †)) m′) →
     ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) ×
     ∃ λ k″ → ∃ λ m″ → ∃ λ (ξ′ : PathSum n k″ m″) →
       (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′ × (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ξ′ ≋ idPS))
  ⊎ ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
validation-normal-form {n} C₁ C₂ = by ⟦ C₁ ++ C₂ † ⟧ᴿ refl
  where
  by : (r : Maybe (Σ ℕ (PathSum n (norm (C₁ ++ C₂ †))))) →
       ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ r → NormalVerdict C₁ C₂
  by nothing         eq = inj₂ (validation-refuted-gauss C₁ C₂ eq)
  by (just (m′ , ξ)) eq = pack (normal-formᶠ ξ)
    where
    pack : (∃ λ k″ → ∃ λ m″ → ∃ λ (ξ′ : PathSum n k″ m″) →
              (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′) →
           NormalVerdict C₁ C₂
    pack (k″ , m″ , ξ′ , steps , irr) = inj₁
      (m′ , ξ , eq , k″ , m″ , ξ′ , steps , irr ,
       validation-reduct C₁ C₂ eq {ξ″ = ξ′} steps)


------------------------------------------------------------------------
-- Completeness for Clifford circuits

-- The miter of two Clifford circuits is Clifford, so its restriction
-- has internal path variables and a phase of order at most 2, and
-- every step of figure 2 keeps it so (PathSum.Full.Clifford).

private
  restriction-Clifford : (C₁ C₂ : Circuit n) →
    level C₁ ≤ 2 → level C₂ ≤ 2 →
    {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
    ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) → IsClifford ξ
  restriction-Clifford C₁ C₂ lv₁ lv₂ eq =
    ⟦⟧ᴿ-Internal (C₁ ++ C₂ †) eq ,
    ⟦⟧ᴿ-Ord≤2 (C₁ ++ C₂ †) eq (level-miter C₁ C₂ lv₁ lv₂)

-- An irreducible end with a path variable left refutes: lemma 4.3
-- would otherwise make progress.

validation-clifford-refutes : (C₁ C₂ : Circuit n) →
  level C₁ ≤ 2 → level C₂ ≤ 2 →
  {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ′ : PathSum n k′ (suc m″)} → ξ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ →
  ¬ (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
validation-clifford-refutes C₁ C₂ lv₁ lv₂ eq {ξ′} steps irr e =
  stuck-not-id ξ′
    (⟶ᶠ*-Clifford steps (restriction-Clifford C₁ C₂ lv₁ lv₂ eq)) irr
    (Equivalence.to (validation-reduct C₁ C₂ eq {ξ″ = ξ′} steps) e)

-- Reduce in any way until no rule applies: two Clifford circuits are
-- equivalent exactly when no path variable is left and what is left is
-- syntactically the identity.

validation-clifford : (C₁ C₂ : Circuit n) →
  level C₁ ≤ 2 → level C₂ ≤ 2 →
  {ξ : PathSum n (norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ′ : PathSum n k′ m″} → ξ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ →
  (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
   (m″ ≡ 0 × k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
validation-clifford {m″ = zero} C₁ C₂ lv₁ lv₂ eq {ξ′} steps irr = mk⇔
  (λ e → refl , Equivalence.to (validation-any C₁ C₂ eq {ξ′ = ξ′} steps) e)
  (λ (_ , s) → Equivalence.from (validation-any C₁ C₂ eq {ξ′ = ξ′} steps) s)
validation-clifford {m″ = suc _} C₁ C₂ lv₁ lv₂ eq {ξ′} steps irr = mk⇔
  (λ e → ⊥-elim (validation-clifford-refutes C₁ C₂ lv₁ lv₂ eq {ξ′ = ξ′}
                   steps irr e))
  (λ { (() , _) })

-- Hence a decision procedure for Clifford circuits along this route:
-- eliminate, normalise with all of figure 2, then refute or test what
-- is left.

validation-decidable-clifford : (C₁ C₂ : Circuit n) →
  level C₁ ≤ 2 → level C₂ ≤ 2 → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
validation-decidable-clifford {n} C₁ C₂ lv₁ lv₂ = by ⟦ C₁ ++ C₂ † ⟧ᴿ refl
  where
  by : (r : Maybe (Σ ℕ (PathSum n (norm (C₁ ++ C₂ †))))) →
       ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ r → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
  by nothing         eq = no (validation-refuted-gauss C₁ C₂ eq)
  by (just (m′ , ξ)) eq = settle (normal-formᶠ ξ)
    where
    at-end : ∀ {k″ m″} (ξ′ : PathSum n k″ m″) → ξ ⟶ᶠ* ξ′ →
             Irreducibleᶠ ξ′ → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
    at-end {m″ = zero}  ξ′ steps irr =
      map′ (Equivalence.from iff) (Equivalence.to iff) (decide-≋-id ξ′)
      where
      iff = validation-reduct C₁ C₂ eq {ξ″ = ξ′} steps
    at-end {m″ = suc _} ξ′ steps irr =
      no (validation-clifford-refutes C₁ C₂ lv₁ lv₂ eq {ξ′ = ξ′} steps irr)

    settle : (∃ λ k″ → ∃ λ m″ → ∃ λ (ξ′ : PathSum n k″ m″) →
                (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′) →
             Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
    settle (_ , _ , ξ′ , steps , irr) = at-end ξ′ steps irr
