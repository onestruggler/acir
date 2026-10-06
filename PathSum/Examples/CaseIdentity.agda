------------------------------------------------------------------------
-- Presentations of groups
--
-- The identity behind [Case]: (CNOT (X ⊗ T) controlled-H (X ⊗ T†))² = I
--
-- Section 3.2 of Amy's QPL 2018 paper says that "the final rule [Case]
-- is a specific case distinction needed to prove the 2-qubit
-- Clifford+T identity (CNOT (X ⊗ T) controlled-H (X ⊗ T†))²" of
-- Selinger and Bian [29].  This module formalises the identity, its
-- path-sum and its isometry restriction, a reduction of each to the
-- identity by the rules of figure 2 that uses [Case], and the claim
-- that [Case] is needed.  Everything is at the examples' precision
-- M₀ = 0 (eighths), over PathSum.CRK.WithX ({H, X, CNOT, R_k, R_k†},
-- X read as |x⟩ ↦ |1 ⊕ x⟩; S = R 2, T = R 3), the first wire being
-- the one X acts on.
--
-- * Controlled-H.  The paper does not say how controlled-H is built
--   from Clifford+T gates.  CH is the standard decomposition with one
--   CNOT: S†, H, T† on the target, the CNOT, then T, H, S on the target
--   (controlled-H is (1 ⊗ A) CNOT (1 ⊗ A†) for A = S H T, which
--   conjugates X to H).  Its matrix, computed gate by gate, is twice
--   that of controlled-H (CH-matrix, CH-amp): twice the identity on the
--   entries whose control reads 0, and √2 times the circuit's
--   unnormalised Hadamard on the target where it reads 1.  The factor
--   2 is the normalisation 1/√2² of the circuit's two Hadamards.
--
-- * The identity, in both readings.  As an operator product (the way
--   [29] writes relations) the rightmost factor acts first: W is
--   X ⊗ T†, CH, X ⊗ T, CNOT, in circuit order.  Read left to right as
--   a circuit, Wᶜ is CNOT, X ⊗ T, CH, X ⊗ T†.  Both squares are the
--   identity (W²-id, Wᶜ²-id), checked by computing the 4×4 matrix of
--   each (PathSum.CRK.WithX.circuit-id!), and neither W nor Wᶜ is
--   (W-not-id, Wᶜ-not-id).  (The X gates make both block diagonal:
--   W = |0⟩⟨0| ⊗ THT† + |1⟩⟨1| ⊗ X, and both blocks square to I.)
--   Everything below is done for both readings, and the paper's claim
--   holds in each.
--
-- * The path-sum.  ⟦ W² ⟧ has four path variables, one per Hadamard,
--   and normalisation 4.  With its path variables renumbered into the
--   order the Hadamards introduce them it is congruent to W²ᵖ, the
--   path-sum of a literal interpretation state stW² -- a phase and the
--   forms x₁ and x₁ ⊕ y₄ on the wires (x₁ and y₄ for Wᶜ²) --
--   (W²-renumbered), and so is equivalent to it (W²-literal).
--
-- * The isometry restriction.  Gaussian elimination (PathSum.Gauss,
--   which works on the affine forms X produces) solves the second
--   output for y₄, y₄ ← x₁ ⊕ x₂ (y₄ ← x₂ for Wᶜ²), leaving W²ᴿ: three
--   path variables, normalisation 4, the identity's outputs.  It is run
--   on stW² rather than on the circuit's own state, whose coefficients
--   unwind the whole circuit each time one is read.  W²ᴿ is the
--   restriction of ⟦ W² ⟧: it has its diagonal (W²ᴿ-diag), only
--   internal path variables (W²ᴿ-Internal), and is the identity
--   exactly when ⟦ W² ⟧ is (W²-restriction) -- lemma 4.1, every
--   circuit over the gate set having unit columns
--   (PathSum.CRK.WithX.WellFormed, through PathSum.CRK.WithX.Columns).
--   It is congruent to the literal W²ᴿᵖ (W²ᴿ-congruent, W²ᴿ-literal).
--
-- * [Case] is needed.  No rule of figure 2 other than [Case] -- [Elim],
--   [ω], [HH], with any Boolean-valued quotient, at any internal path
--   variable -- applies to ⟦ W² ⟧ or to W²ᴿ (W²-stuck⁻, W²ᴿ-stuck⁻;
--   PathSum.Full.WithoutCase): each of those three rules at a variable
--   y needs the coefficient of y to be a multiple of ¼ and that of x₁y
--   a multiple of ½, and every path variable y has an odd coefficient
--   or the coefficient ¼ or ¾ at x₁y.  So no chain of them reaches a
--   path-sum without path variables (W²-needs-case, W²ᴿ-needs-case),
--   and every chain of figure 2 that does begins with a [Case] step
--   (W²-case-first, W²ᴿ-case-first).
--
-- * [Case] suffices.  On W²ᴿᵖ, [Case] at (y₂ , y₁) with X = x₁ -- the
--   paper's own form, ¼y₂x₁ + ½y₂(y₁ + Q) + R = ¼y₁(1 - x₁) +
--   ½y₁(y₂ + Q′) + R′ -- and then [Elim] reach a path-sum congruent to
--   the identity (W²ᴿᵖ-chain, W²ᴿᵖ-end); on W²ᵖ, [Case] at the same
--   pair, [HH] substituting x₁ ⊕ x₂ for y₄ (x₂ for Wᶜ²) and [Elim] do
--   (W²ᵖ-chain, W²ᵖ-end).  Each step is a step of PathSum.Full's
--   _⟶ᶠ_ (caseAtᶠ, hhAtᶠ, elimAtᶠ) with its premises checked by
--   computation, and the first is a [Case] (W²ᵖ-uses-case,
--   W²ᴿᵖ-uses-case).  The chains run on the literals W²ᵖ and W²ᴿᵖ, not
--   on ⟦ W² ⟧ and W²ᴿ themselves: W²ᵖ is ⟦ W² ⟧ with its path
--   variables renumbered, congruent coefficient by coefficient
--   (W²-renumbered), and W²ᴿᵖ is congruent to W²ᴿ (W²ᴿ-congruent); the
--   chains are tied back to them by ≋.  So, by proposition 3.1 along
--   the chains, ⟦ W² ⟧ is the identity by the rules run on a renumbered
--   congruent literal of its path-sum (W²-by-rules), and by the
--   paper's route of section 4 (W²-by-restriction: the rules on a
--   congruent literal of its restriction, then lemma 4.1),
--   independently of its matrix.
--   case-identity (case-identityᶜ for the circuit reading) collects
--   the claim in one statement.
--
-- So the paper's claim holds as stated, for this decomposition of
-- controlled-H and for either reading of the product: without [Case]
-- no rule applies at all, with it the rules prove the identity.
-- "Needed" is relative to the circuit: another decomposition of
-- controlled-H gives another path-sum, and only this one is
-- formalised.  (A numerical check outside Agda found the same for the
-- other nine decompositions with one CNOT and at most four gates on
-- each side of it: no chain without [Case] gets rid of the path
-- variables, and every maximal chain with it ends at the identity.)
--
-- The chains run on literals, which are the path-sums renumbered: the
-- coefficients of a reduct are sums over coefficients of the path-sum
-- it comes from, and three rules nested on top of a circuit's phase,
-- or on top of an elimination, multiply those sums.  The certificates
-- of Stuck⁻ are computed on ⟦ W² ⟧ itself and on the literals, and
-- carried to W²ᴿ along its congruence with W²ᴿᵖ.
--
-- Closed facts are stated through lemmas about an arbitrary circuit or
-- path-sum, at one instance D of the denotation and one CX of the gate
-- set, and each closed statement is spelled exactly as the lemma's
-- conclusion (see PathSum.Examples.Incomplete's header): two spellings
-- of the same ≋ are compared by unfolding it into amplitudes.  A
-- client restating them must use D._≋_ and CX.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.CaseIdentity where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using () renaming (⊥ to ⊥ᵉ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using ([_,_]′)
open import Data.Unit.Base using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; True; False; toWitness; _×?_)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base
open import PathSum.Polynomial hiding (subst)
open import PathSum.Polynomial.Boolean using (BoolValued)
open import PathSum.Polynomial.Substitution using (Absent)
open import PathSum.Polynomial.Decidable using
  (_≈?[_]_; NoVar?; Absent?; BoolValued?)
open import PathSum.Order 3 using (pow)
open import PathSum.Reduction 3 using (elim-reduct; ¼; ½)
open import PathSum.Reduction.General 3 using (hhᴳ-reduct; case-reduct)
open import PathSum.Reorder using (front; _/ʸ_)
open import PathSum.Reorder.Pair using (front₂; q₀₁ʸ; q₁₀ʸ; q₁₁ʸ)
open import PathSum.Full 3 using
  (_⟶ᶠ_; _⟶ᶠ*_; εᶠ; _◅ᶠ_; elimAtᶠ; hhAtᶠ; caseAtᶠ)
open import PathSum.Full.WithoutCase 3 using
  (NoCaseᶠ; Stuck⁻; NeedsCase; CaseFirst; certificate?;
   certificate⇒stuck⁻; certificate-≈; stuck⁻!; stuck⁻-chains;
   case-first)
open import PathSum.CircuitSemantics 0 using (Column; δ; δ-resp)
open import PathSum.Cyclotomic 0 using
  (Amp; _≐_; zpow; 0ᴬ; scale; scale-map; scale-injective; Respects)
open import PathSum.Decide 0 using (search)
open import PathSum.Assign using (same-≗)
open import PathSum.CRK.Amp 0 using (toPS)
open import PathSum.CRK.Circuit 3 using (State; state)
open import PathSum.Compose.WellFormed 0 using (WellFormed-≋)
open import PathSum.Examples.Base using
  (_⋆_; mono; yᵐ; x₁; x₂; y₁; y₂; y₃; y₄; module Cong)

import PathSum.CRK.WithX
import PathSum.CRK.WithX.Columns
import PathSum.Denotation
import PathSum.Full.Sound
import PathSum.Gauss

-- The instances every statement below is made with.

module D  = PathSum.Denotation 0
module CX = PathSum.CRK.WithX 0

private
  module CC = PathSum.CRK.WithX.Columns 0
  module G  = PathSum.Gauss 0
  module FS = PathSum.Full.Sound 0

open D using (Assign; amp; _≋_; ≋-sym; ≋-trans)

private
  variable
    n k m k′ m′ m₀ : ℕ


------------------------------------------------------------------------
-- Statements about a circuit or a path-sum, for an arbitrary one

-- Each is a lemma restated at the instances above, so that at a closed
-- circuit its conclusion is literally the declared type.

-- A circuit is the identity, or is not, by computing its matrix.

identity! : (C : CX.Circuit n) → {True (CX.matrix-id? C)} →
            CX.⟦ C ⟧ ≋ idPS
identity! C {t} = CX.circuit-id! C {t}

not-identity! : (C : CX.Circuit n) → {False (CX.matrix-id? C)} →
                ¬ (CX.⟦ C ⟧ ≋ idPS)
not-identity! C {f} = CX.circuit-not-id! C {f}

-- A circuit's path-sum against one it is congruent to once its path
-- variables are renumbered.

renumbered! :
  (C : CX.Circuit n) (ζ : PathSum n k′ m′)
  (js : List (Fin (CX.paths C))) →
  (k≡k′ : CX.norm C ≡ k′) (m′≡p : m′ ≡ CX.paths C) →
  {True (Cong.congruent? (Cong.fronts js CX.⟦ C ⟧)
                         (subst (PathSum n k′) m′≡p ζ))} →
  CX.⟦ C ⟧ ≋ ζ
renumbered! C ζ js k≡k′ m′≡p {t} =
  Cong.renumbered-≋ CX.⟦ C ⟧ ζ js k≡k′ m′≡p {t}

-- The same from the congruence itself.

renumbered-from :
  (C : CX.Circuit n) (ζ : PathSum n k′ m′)
  (js : List (Fin (CX.paths C))) →
  CX.norm C ≡ k′ → (m′≡p : m′ ≡ CX.paths C) →
  Cong.Congruent (Cong.fronts js CX.⟦ C ⟧) (subst (PathSum n k′) m′≡p ζ) →
  CX.⟦ C ⟧ ≋ ζ
renumbered-from C ζ js refl refl c =
  ≋-trans {ξ = CX.⟦ C ⟧} {ζ = Cong.fronts js CX.⟦ C ⟧} {χ = ζ}
    (Cong.fronts-≋ js CX.⟦ C ⟧)
    (Cong.congruent-≋ (Cong.fronts js CX.⟦ C ⟧) ζ refl c)

-- A path-sum congruent to a literal is equivalent to it.

literal-≋ : (ξ : PathSum n k m) (ζ : PathSum n k m) →
            Cong.Congruent ζ ξ → ξ ≋ ζ
literal-≋ ξ ζ c = ≋-sym {ξ = ζ} {ζ = ξ} (Cong.congruent-≋ ζ ξ refl c)

-- Proposition 3.1 along a chain of figure 2 that ends at a path-sum
-- congruent to the identity.

reduces-to-id : (ξ : PathSum n k m) {ξ′ : PathSum n 0 0} → ξ ⟶ᶠ* ξ′ →
                {True (Cong.id-syntactic? ξ′)} → ξ ≋ idPS
reduces-to-id ξ {ξ′} steps {t} =
  ≋-trans {ξ = ξ} {ζ = ξ′} {χ = idPS} (FS.⟶ᶠ*-sound steps)
    (Cong.id-syntactic-≋ ξ′ (toWitness {a? = Cong.id-syntactic? ξ′} t))

-- A circuit equivalent to a path-sum that is the identity is.

through : (C : CX.Circuit n) (ζ : PathSum n k′ m′) →
          CX.⟦ C ⟧ ≋ ζ → ζ ≋ idPS → CX.⟦ C ⟧ ≋ idPS
through C ζ C≋ζ ζ≋id =
  ≋-trans {ξ = CX.⟦ C ⟧} {ζ = ζ} {χ = idPS} C≋ζ ζ≋id

-- No rule but [Case] applies to ξ, certified on a literal ζ whose
-- phase is congruent to ξ's.

stuck⁻-by : (i : Fin n) (ζ : PathSum n k (suc m))
            (ξ : PathSum n k′ (suc m)) → Cong.Congruent ζ ξ →
            {True (certificate? i ζ)} → Stuck⁻ ξ
stuck⁻-by i ζ ξ c {t} = certificate⇒stuck⁻ i ξ
  (certificate-≈ i ζ ξ (proj₂ c) (toWitness {a? = certificate? i ζ} t))


------------------------------------------------------------------------
-- The isometry restriction, for an arbitrary circuit

-- Elimination, when it reifies the restriction.

Reduced : {st : State n m} → G.Gauss st → Set
Reduced (G.refuted _ _) = ⊥ᵉ
Reduced (G.reduced _)   = ⊤

reified : {st : State n m} (g : G.Gauss st) → {Reduced g} → G.Reified st
reified (G.refuted _ _) {()}
reified (G.reduced r)       = r

-- ξᴿ is the path-sum elimination left, at the normalisation k, its
-- number of path variables written m (elimination computes it).

IsRestriction : {st : State n m₀} → G.Reified st → PathSum n k m → Set
IsRestriction {n = n} {k = k} r ξᴿ =
  Σ (G.Reified.m′ r ≡ _)
    (λ e → subst (PathSum n k) e (G.ξᴿ r {k = k}) ≡ ξᴿ)

-- Elimination may run on any interpretation state st whose path-sum is
-- equivalent to the circuit's at the same normalisation: the circuit's
-- own, or a literal one that is cheap to read.  The path-sum it leaves
-- is then the circuit's restriction: the identity exactly when the
-- circuit is (lemma 4.1: every circuit over the gate set is well
-- formed, and well-formedness passes along ≋), with the circuit's
-- diagonal and only internal path variables.  The path-sum st stands
-- for is passed with its definition (ξ ≡ toPS st), and the
-- normalisation explicitly, so that a closed instance is stated with
-- the names it was given rather than with an unfolding of them.

restriction-≋ :
  (C : CX.Circuit n) (st : State n m) (k : ℕ) → CX.norm C ≡ k →
  (ξ : PathSum n k m) → ξ ≡ toPS {k = k} st → CX.⟦ C ⟧ ≋ ξ →
  (r : G.Reified st)
  (ξᴿ : PathSum n k m′) → IsRestriction r ξᴿ →
  (CX.⟦ C ⟧ ≋ idPS ⇔ ξᴿ ≋ idPS)
restriction-≋ C st _ refl _ refl C≋ r ξᴿ (refl , refl) = mk⇔
  (λ C≋id → Equivalence.to iff
     (≋-trans {ξ = S} {ζ = CX.⟦ C ⟧} {χ = idPS}
       (≋-sym {ξ = CX.⟦ C ⟧} {ζ = S} C≋) C≋id))
  (λ R≋id → ≋-trans {ξ = CX.⟦ C ⟧} {ζ = S} {χ = idPS} C≋
     (Equivalence.from iff R≋id))
  where
  S : PathSum _ (CX.norm C) _
  S = toPS {k = CX.norm C} st

  iff : S ≋ idPS ⇔ ξᴿ ≋ idPS
  iff = G.reified-≋ r {k = CX.norm C}
    (WellFormed-≋ CX.⟦ C ⟧ S C≋ (CC.circuit-WellFormed C))

restriction-diag :
  (C : CX.Circuit n) (st : State n m) (k : ℕ) → CX.norm C ≡ k →
  (ξ : PathSum n k m) → ξ ≡ toPS {k = k} st → CX.⟦ C ⟧ ≋ ξ →
  (r : G.Reified st)
  (ξᴿ : PathSum n k m′) → IsRestriction r ξᴿ →
  ∀ x → amp CX.⟦ C ⟧ x x ≐ amp ξᴿ x x
restriction-diag C st _ refl _ refl C≋ r ξᴿ (refl , refl) x i =
  trans (scale-injective (CX.norm C) (amp CX.⟦ C ⟧ x x)
                         (amp (toPS {k = CX.norm C} st) x x) (C≋ x x) i)
        (G.reified-diag r {k = CX.norm C} x i)

restriction-Internal :
  (st : State n m) (r : G.Reified st) (ξᴿ : PathSum n k m′) →
  IsRestriction r ξᴿ → Internal ξᴿ
restriction-Internal {k = k} st r ξᴿ (refl , refl) =
  G.reified-Internal r {k = k}

-- A circuit is the identity when its restriction is equivalent to a
-- path-sum that is.

by-restriction : (C : CX.Circuit n) (ξᴿ : PathSum n k m)
                 (ζ : PathSum n k′ m′) →
                 (CX.⟦ C ⟧ ≋ idPS ⇔ ξᴿ ≋ idPS) →
                 ξᴿ ≋ ζ → ζ ≋ idPS → CX.⟦ C ⟧ ≋ idPS
by-restriction C ξᴿ ζ iff R≋ζ ζ≋id = Equivalence.from iff
  (≋-trans {ξ = ξᴿ} {ζ = ζ} {χ = idPS} R≋ζ ζ≋id)


------------------------------------------------------------------------
-- Steps of figure 2, premises checked by computation

-- [Case] at (y_i , y_j), [HH] at y_j substituting for y_i, and [Elim]
-- at y_j, as PathSum.Full states them.

CasePremises : (ξ : PathSum n (suc (suc k)) (suc (suc m)))
               (i j : Fin (suc (suc m))) → i ≢ j →
               (X Q Q′ : Poly n m) → Set
CasePremises ξ i j i≢j X Q Q′ =
  BoolValued X × BoolValued Q × BoolValued Q′ ×
  q₁₁ʸ i j i≢j (phase ξ) ≈[ pow 3 ] κ ½ ×
  q₁₀ʸ i j i≢j (phase ξ) ≈[ pow 3 ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) ×
  q₀₁ʸ i j i≢j (phase ξ) ≈[ pow 3 ]
    ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) ×
  (∀ w → NoVar (+ 2) y[ i ] (out ξ w)) ×
  (∀ w → NoVar (+ 2) y[ j ] (out ξ w))

caseAt? : (ξ : PathSum n (suc (suc k)) (suc (suc m)))
          (i j : Fin (suc (suc m))) (i≢j : i ≢ j) (X Q Q′ : Poly n m) →
          Dec (CasePremises ξ i j i≢j X Q Q′)
caseAt? ξ i j i≢j X Q Q′ =
  BoolValued? X ×? BoolValued? Q ×? BoolValued? Q′ ×?
  (q₁₁ʸ i j i≢j (phase ξ) ≈?[ pow 3 ] κ ½) ×?
  (q₁₀ʸ i j i≢j (phase ξ) ≈?[ pow 3 ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q))) ×?
  (q₀₁ʸ i j i≢j (phase ξ) ≈?[ pow 3 ]
     ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′))) ×?
  all? (λ w → NoVar? (+ 2) y[ i ] (out ξ w)) ×?
  all? (λ w → NoVar? (+ 2) y[ j ] (out ξ w))

caseAt! : (ξ : PathSum n (suc (suc k)) (suc (suc m)))
          (i j : Fin (suc (suc m))) (i≢j : i ≢ j) (X Q Q′ : Poly n m) →
          {True (caseAt? ξ i j i≢j X Q Q′)} →
          ξ ⟶ᶠ case-reduct (front₂ i j i≢j ξ) X Q Q′
caseAt! ξ i j i≢j X Q Q′ {t} =
  let (bX , bQ , bQ′ , e₁₁ , e₁₀ , e₀₁ , oᵢ , oⱼ) =
        toWitness {a? = caseAt? ξ i j i≢j X Q Q′} t
  in caseAtᶠ ξ i j i≢j X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ oᵢ oⱼ

HHPremises : (ξ : PathSum n k (suc m)) (j : Fin (suc m)) (i : Fin m)
             (Q : Poly n m) → Set
HHPremises ξ j i Q =
  BoolValued Q × Absent y[ i ] Q ×
  (phase ξ /ʸ j) ≈[ pow 3 ] (½ ·ᴾ (μ y[ i ] +ᴾ Q)) ×
  (∀ w → NoVar (+ 2) y[ j ] (out ξ w))

hhAt? : (ξ : PathSum n k (suc m)) (j : Fin (suc m)) (i : Fin m)
        (Q : Poly n m) → Dec (HHPremises ξ j i Q)
hhAt? ξ j i Q =
  BoolValued? Q ×? Absent? y[ i ] Q ×?
  ((phase ξ /ʸ j) ≈?[ pow 3 ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))) ×?
  all? (λ w → NoVar? (+ 2) y[ j ] (out ξ w))

hhAt! : (ξ : PathSum n k (suc m)) (j : Fin (suc m)) (i : Fin m)
        (Q : Poly n m) → {True (hhAt? ξ j i Q)} →
        ξ ⟶ᶠ hhᴳ-reduct (front j ξ) i Q
hhAt! ξ j i Q {t} =
  let (bQ , absQ , eq , o) = toWitness {a? = hhAt? ξ j i Q} t
  in hhAtᶠ ξ j i Q bQ absQ eq o

ElimPremises : (ξ : PathSum n (suc (suc k)) (suc m)) (j : Fin (suc m)) →
               Set
ElimPremises ξ j =
  (phase ξ /ʸ j) ≈[ pow 3 ] 0ᴾ × (∀ w → NoVar (+ 2) y[ j ] (out ξ w))

elimAt? : (ξ : PathSum n (suc (suc k)) (suc m)) (j : Fin (suc m)) →
          Dec (ElimPremises ξ j)
elimAt? ξ j =
  ((phase ξ /ʸ j) ≈?[ pow 3 ] 0ᴾ) ×?
  all? (λ w → NoVar? (+ 2) y[ j ] (out ξ w))

elimAt! : (ξ : PathSum n (suc (suc k)) (suc m)) (j : Fin (suc m)) →
          {True (elimAt? ξ j)} → ξ ⟶ᶠ elim-reduct (front j ξ)
elimAt! ξ j {t} =
  let (eq , o) = toWitness {a? = elimAt? ξ j} t
  in elimAtᶠ ξ j eq o

-- The pair (y₂ , y₁) every [Case] below acts at.

1≢0 : _≢_ {A = Fin (suc (suc m))} (suc zero) zero
1≢0 ()

-- Quotients: 1 - u, and the liftings of u ⊕ v and 1 ⊕ u ⊕ v.

not₁ : Mon 2 m → Poly 2 m
not₁ a = κ (+ 1) -ᴾ mono a

xor₂ : Mon 2 m → Mon 2 m → Poly 2 m
xor₂ a b = mono a +ᴾ mono b -ᴾ (+ 2) ⋆ (a ∪ᵐ b)

not-xor₂ : Mon 2 m → Mon 2 m → Poly 2 m
not-xor₂ a b = κ (+ 1) -ᴾ mono a -ᴾ mono b +ᴾ (+ 2) ⋆ (a ∪ᵐ b)


------------------------------------------------------------------------
-- Comparing a circuit's matrix with an operator on columns

private
  every? : {P : Assign n → Set} → (∀ x → Dec (P x)) →
           (∀ {x x′} → (∀ i → x i ≡ x′ i) → P x → P x′) →
           Dec (∀ x → P x)
  every? {P = P} P? resp =
    [ yes , (λ (x , ¬p) → no (λ h → ¬p (h x))) ]′ (search P P? resp)

  coords? : (a b : Amp) → Dec (a ≐ b)
  coords? a b = all? (λ i → a i ≟ℤ b i)

  δ-≗ : {x x′ : Assign n} → (∀ i → x i ≡ x′ i) → ∀ z → δ x z ≐ δ x′ z
  δ-≗ {x = x} {x′} xx z i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
    (same-≗ {x = x} {x′ = x′} {z = z} {z′ = z} xx (λ _ → refl))

-- The circuit C acts on basis columns as F does.

SameMatrix : CX.Circuit n → (Column n → Column n) → Set
SameMatrix C F = ∀ x z → CX.applyᴬ C (δ x) z ≐ F (δ x) z

-- Decidable when F, like a circuit, reads assignments only through
-- their values and acts on columns entry by entry.

same-matrix? :
  (C : CX.Circuit n) (F : Column n → Column n) →
  (∀ {ψ} → Respects ψ → Respects (F ψ)) →
  (∀ {φ φ′} → (∀ z → φ z ≐ φ′ z) → ∀ z → F φ z ≐ F φ′ z) →
  Dec (SameMatrix C F)
same-matrix? {n} C F F-resp F-cong =
  every? (λ x → every? (entry? x) (resp-z x)) resp-x
  where
  Entry : Assign n → Assign n → Set
  Entry x z = CX.applyᴬ C (δ x) z ≐ F (δ x) z

  entry? : ∀ x z → Dec (Entry x z)
  entry? x z = coords? (CX.applyᴬ C (δ x) z) (F (δ x) z)

  resp-z : ∀ x {z z′} → (∀ w → z w ≡ z′ w) → Entry x z → Entry x z′
  resp-z x {z} {z′} zz e i =
    trans (sym (CX.applyᴬ-resp C (δ-resp x) z z′ zz i))
      (trans (e i) (F-resp (δ-resp x) z z′ zz i))

  resp-x : ∀ {x x′} → (∀ i → x i ≡ x′ i) →
           (∀ z → Entry x z) → ∀ z → Entry x′ z
  resp-x {x} {x′} xx h z i =
    trans (sym (CX.applyᴬ-cong C {δ x} {δ x′} (δ-≗ xx) z i))
      (trans (h z i) (F-cong (δ-≗ xx) z i))


------------------------------------------------------------------------
-- Controlled-H

-- The gates: a CNOT from the first wire to the second, X on the
-- first, and H, S = R 2, T = R 3 and their inverses on the second.

CNOT₁₂ X₁ H₂ S₂ S†₂ T₂ T†₂ : CX.Gate 2
CNOT₁₂ = CX.CNOT zero (suc zero) (λ ())
X₁     = CX.X zero
H₂     = CX.H (suc zero)
S₂     = CX.R 2 (suc zero)
S†₂    = CX.R† 2 (suc zero)
T₂     = CX.R 3 (suc zero)
T†₂    = CX.R† 3 (suc zero)

-- (1 ⊗ S H T) CNOT (1 ⊗ T† H S†), first gate first.

CH : CX.Circuit 2
CH = S†₂ ∷ H₂ ∷ T†₂ ∷ CNOT₁₂ ∷ T₂ ∷ H₂ ∷ S₂ ∷ []

-- Twice controlled-H, unnormalised as the circuit's matrix is: on the
-- entries whose control reads 1, √2 times the unnormalised Hadamard
-- of the target (√2 · √2 H = 2H); on the others, twice the entry.

CHᴬ : Column 2 → Column 2
CHᴬ ψ z = if z zero then scale 1 (CX.gateᴬ H₂ ψ z) else scale 2 (ψ z)

private
  if-≐ : {b b′ : Bool} {a a′ c c′ : Amp} → b ≡ b′ → a ≐ a′ → c ≐ c′ →
         (if b then a else c) ≐ (if b′ then a′ else c′)
  if-≐ {b = true}  refl aa _  = aa
  if-≐ {b = false} refl _  cc = cc

  CHᴬ-resp : ∀ {ψ} → Respects ψ → Respects (CHᴬ ψ)
  CHᴬ-resp {ψ} resp z z′ zz =
    if-≐ {b = z zero} {b′ = z′ zero} (zz zero)
         (scale-map 1 (CX.gateᴬ-resp H₂ resp z z′ zz))
         (scale-map 2 (resp z z′ zz))

  CHᴬ-cong : ∀ {φ φ′} → (∀ z → φ z ≐ φ′ z) → ∀ z → CHᴬ φ z ≐ CHᴬ φ′ z
  CHᴬ-cong h z =
    if-≐ {b = z zero} {b′ = z zero} refl
         (scale-map 1 (CX.gateᴬ-cong H₂ h z)) (scale-map 2 (h z))

-- The circuit's matrix, computed gate by gate.

CH-matrix : SameMatrix CH CHᴬ
CH-matrix = toWitness {a? = same-matrix? CH CHᴬ CHᴬ-resp CHᴬ-cong} tt

-- Hence its path-sum (proposition 2.10 with X).

CH-amp : ∀ x z → amp CX.⟦ CH ⟧ x z ≐ CHᴬ (δ x) z
CH-amp x z i = trans (CX.prop-2-10 CH x z i) (CH-matrix x z i)


------------------------------------------------------------------------
-- The identity

-- As an operator product, CNOT (X ⊗ T) CH (X ⊗ T†) applies X ⊗ T†
-- first.

W : CX.Circuit 2
W = X₁ ∷ T†₂ ∷ CH ++ X₁ ∷ T₂ ∷ CNOT₁₂ ∷ []

W² : CX.Circuit 2
W² = W ++ W

-- Read left to right as a circuit.

Wᶜ : CX.Circuit 2
Wᶜ = CNOT₁₂ ∷ X₁ ∷ T₂ ∷ CH ++ X₁ ∷ T†₂ ∷ []

Wᶜ² : CX.Circuit 2
Wᶜ² = Wᶜ ++ Wᶜ

-- Both squares are the identity, neither factor is.

W²-id : CX.⟦ W² ⟧ ≋ idPS
W²-id = identity! W²

Wᶜ²-id : CX.⟦ Wᶜ² ⟧ ≋ idPS
Wᶜ²-id = identity! Wᶜ²

W-not-id : ¬ (CX.⟦ W ⟧ ≋ idPS)
W-not-id = not-identity! W

Wᶜ-not-id : ¬ (CX.⟦ Wᶜ ⟧ ≋ idPS)
Wᶜ-not-id = not-identity! Wᶜ


------------------------------------------------------------------------
-- The path-sums

-- y₁ … y₄ in the order the Hadamards introduce them (⟦_⟧ lists them
-- newest first: bring variables 1, 2, 3 to the front in turn).

hadamard-order : List (Fin 4)
hadamard-order = suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero)) ∷ []

-- The operator reading: the state W² runs to, as a literal -- the
-- phase, and the forms x₁ and x₁ ⊕ y₄ on the wires.

stW² : State 2 4
stW² = state P σ
  where
  P : Poly 2 4
  P = (+ 2) ⋆ 1ᵐ +ᴾ (+ 3) ⋆ x₁ +ᴾ (+ 5) ⋆ x₂ +ᴾ
      (+ 6) ⋆ y₁ +ᴾ (+ 4) ⋆ y₂ +ᴾ (+ 6) ⋆ y₃ +ᴾ (+ 7) ⋆ y₄ +ᴾ
      (+ 2) ⋆ (x₁ ∪ᵐ y₁) +ᴾ (+ 2) ⋆ (x₁ ∪ᵐ y₂) +ᴾ (+ 6) ⋆ (x₁ ∪ᵐ y₃) +ᴾ
      (+ 4) ⋆ (x₁ ∪ᵐ y₄) +ᴾ (+ 4) ⋆ (x₂ ∪ᵐ y₁) +ᴾ
      (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (y₂ ∪ᵐ y₃) +ᴾ (+ 4) ⋆ (y₃ ∪ᵐ y₄)

  σ : Fin 2 → Bool × Mon 2 4
  σ zero       = false , x₁
  σ (suc zero) = false , x₁ ∪ᵐ y₄

W²ᵖ : PathSum 2 4 4
W²ᵖ = toPS {k = 4} stW²

-- ⟦ W² ⟧ renumbered is W²ᵖ, coefficient by coefficient (phase modulo
-- 8, outputs modulo 2), hence equivalent to it.

W²-renumbered :
  Cong.Congruent (Cong.fronts hadamard-order CX.⟦ W² ⟧) W²ᵖ
W²-renumbered = toWitness
  {a? = Cong.congruent? (Cong.fronts hadamard-order CX.⟦ W² ⟧) W²ᵖ} tt

W²-literal : CX.⟦ W² ⟧ ≋ W²ᵖ
W²-literal =
  renumbered-from W² W²ᵖ hadamard-order refl refl W²-renumbered

-- The circuit reading: the forms x₁ and y₄.

stWᶜ² : State 2 4
stWᶜ² = state P σ
  where
  P : Poly 2 4
  P = (+ 2) ⋆ 1ᵐ +ᴾ (+ 4) ⋆ x₁ +ᴾ (+ 7) ⋆ x₂ +ᴾ (+ 2) ⋆ (x₁ ∪ᵐ x₂) +ᴾ
      (+ 6) ⋆ y₁ +ᴾ (+ 4) ⋆ y₂ +ᴾ (+ 6) ⋆ y₃ +ᴾ (+ 5) ⋆ y₄ +ᴾ
      (+ 6) ⋆ (x₁ ∪ᵐ y₁) +ᴾ (+ 6) ⋆ (x₁ ∪ᵐ y₂) +ᴾ (+ 6) ⋆ (x₁ ∪ᵐ y₃) +ᴾ
      (+ 4) ⋆ (x₁ ∪ᵐ y₄) +ᴾ (+ 4) ⋆ (x₂ ∪ᵐ y₁) +ᴾ
      (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (y₂ ∪ᵐ y₃) +ᴾ (+ 4) ⋆ (y₃ ∪ᵐ y₄)

  σ : Fin 2 → Bool × Mon 2 4
  σ zero       = false , x₁
  σ (suc zero) = false , y₄

Wᶜ²ᵖ : PathSum 2 4 4
Wᶜ²ᵖ = toPS {k = 4} stWᶜ²

Wᶜ²-renumbered :
  Cong.Congruent (Cong.fronts hadamard-order CX.⟦ Wᶜ² ⟧) Wᶜ²ᵖ
Wᶜ²-renumbered = toWitness
  {a? = Cong.congruent? (Cong.fronts hadamard-order CX.⟦ Wᶜ² ⟧) Wᶜ²ᵖ} tt

Wᶜ²-literal : CX.⟦ Wᶜ² ⟧ ≋ Wᶜ²ᵖ
Wᶜ²-literal =
  renumbered-from Wᶜ² Wᶜ²ᵖ hadamard-order refl refl Wᶜ²-renumbered


------------------------------------------------------------------------
-- The isometry restrictions

-- Gaussian elimination on the literal states solves the second output
-- for y₄: y₄ ← x₁ ⊕ x₂ for W², y₄ ← x₂ for Wᶜ².  The path variables
-- left are y₁, y₂, y₃, in order.

rW² : G.Reified stW²
rW² = reified (G.gauss stW²)

W²ᴿ : PathSum 2 4 3
W²ᴿ = G.ξᴿ rW² {k = 4}

rWᶜ² : G.Reified stWᶜ²
rWᶜ² = reified (G.gauss stWᶜ²)

Wᶜ²ᴿ : PathSum 2 4 3
Wᶜ²ᴿ = G.ξᴿ rWᶜ² {k = 4}

-- Each is the circuit's restriction: the identity exactly when the
-- circuit is, with the circuit's diagonal and only internal path
-- variables.

W²-restriction : CX.⟦ W² ⟧ ≋ idPS ⇔ W²ᴿ ≋ idPS
W²-restriction =
  restriction-≋ W² stW² 4 refl W²ᵖ refl W²-literal rW² W²ᴿ (refl , refl)

W²ᴿ-diag : ∀ x → amp CX.⟦ W² ⟧ x x ≐ amp W²ᴿ x x
W²ᴿ-diag =
  restriction-diag W² stW² 4 refl W²ᵖ refl W²-literal rW² W²ᴿ
    (refl , refl)

W²ᴿ-Internal : Internal W²ᴿ
W²ᴿ-Internal = restriction-Internal stW² rW² W²ᴿ (refl , refl)

Wᶜ²-restriction : CX.⟦ Wᶜ² ⟧ ≋ idPS ⇔ Wᶜ²ᴿ ≋ idPS
Wᶜ²-restriction =
  restriction-≋ Wᶜ² stWᶜ² 4 refl Wᶜ²ᵖ refl Wᶜ²-literal rWᶜ² Wᶜ²ᴿ
    (refl , refl)

Wᶜ²ᴿ-diag : ∀ x → amp CX.⟦ Wᶜ² ⟧ x x ≐ amp Wᶜ²ᴿ x x
Wᶜ²ᴿ-diag =
  restriction-diag Wᶜ² stWᶜ² 4 refl Wᶜ²ᵖ refl Wᶜ²-literal rWᶜ² Wᶜ²ᴿ
    (refl , refl)

Wᶜ²ᴿ-Internal : Internal Wᶜ²ᴿ
Wᶜ²ᴿ-Internal =
  restriction-Internal stWᶜ² rWᶜ² Wᶜ²ᴿ (refl , refl)

-- Each is congruent to a literal with the identity's outputs.

W²ᴿᵖ : PathSum 2 4 3
W²ᴿᵖ = ⟨ P , (λ w → μ x[ w ]) ⟩
  where
  P : Poly 2 3
  P = (+ 2) ⋆ 1ᵐ +ᴾ (+ 6) ⋆ x₁ +ᴾ (+ 4) ⋆ x₂ +ᴾ (+ 6) ⋆ (x₁ ∪ᵐ x₂) +ᴾ
      (+ 6) ⋆ y₁ +ᴾ (+ 4) ⋆ y₂ +ᴾ (+ 6) ⋆ y₃ +ᴾ
      (+ 2) ⋆ (x₁ ∪ᵐ y₁) +ᴾ (+ 2) ⋆ (x₁ ∪ᵐ y₂) +ᴾ (+ 2) ⋆ (x₁ ∪ᵐ y₃) +ᴾ
      (+ 4) ⋆ (x₂ ∪ᵐ y₁) +ᴾ (+ 4) ⋆ (x₂ ∪ᵐ y₃) +ᴾ
      (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (y₂ ∪ᵐ y₃)

W²ᴿ-congruent : Cong.Congruent W²ᴿᵖ W²ᴿ
W²ᴿ-congruent = toWitness {a? = Cong.congruent? W²ᴿᵖ W²ᴿ} tt

W²ᴿ-literal : W²ᴿ ≋ W²ᴿᵖ
W²ᴿ-literal = literal-≋ W²ᴿ W²ᴿᵖ W²ᴿ-congruent

Wᶜ²ᴿᵖ : PathSum 2 4 3
Wᶜ²ᴿᵖ = ⟨ P , (λ w → μ x[ w ]) ⟩
  where
  P : Poly 2 3
  P = (+ 2) ⋆ 1ᵐ +ᴾ (+ 4) ⋆ x₁ +ᴾ (+ 4) ⋆ x₂ +ᴾ (+ 6) ⋆ (x₁ ∪ᵐ x₂) +ᴾ
      (+ 6) ⋆ y₁ +ᴾ (+ 4) ⋆ y₂ +ᴾ (+ 6) ⋆ y₃ +ᴾ
      (+ 6) ⋆ (x₁ ∪ᵐ y₁) +ᴾ (+ 6) ⋆ (x₁ ∪ᵐ y₂) +ᴾ (+ 6) ⋆ (x₁ ∪ᵐ y₃) +ᴾ
      (+ 4) ⋆ (x₂ ∪ᵐ y₁) +ᴾ (+ 4) ⋆ (x₂ ∪ᵐ y₃) +ᴾ
      (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ (+ 4) ⋆ (y₂ ∪ᵐ y₃)

Wᶜ²ᴿ-congruent : Cong.Congruent Wᶜ²ᴿᵖ Wᶜ²ᴿ
Wᶜ²ᴿ-congruent = toWitness {a? = Cong.congruent? Wᶜ²ᴿᵖ Wᶜ²ᴿ} tt

Wᶜ²ᴿ-literal : Wᶜ²ᴿ ≋ Wᶜ²ᴿᵖ
Wᶜ²ᴿ-literal = literal-≋ Wᶜ²ᴿ Wᶜ²ᴿᵖ Wᶜ²ᴿ-congruent


------------------------------------------------------------------------
-- Without [Case], no rule applies

-- At the input x₁: every path variable y has an odd coefficient, or a
-- coefficient at x₁y that is not a multiple of ½ (¼ or ¾).  Checked on
-- the circuits' own path-sums and on the literals, and carried to the
-- restrictions along their congruence with the literals.

W²-stuck⁻ : Stuck⁻ CX.⟦ W² ⟧
W²-stuck⁻ = stuck⁻! zero CX.⟦ W² ⟧

W²ᵖ-stuck⁻ : Stuck⁻ W²ᵖ
W²ᵖ-stuck⁻ = stuck⁻! zero W²ᵖ

W²ᴿᵖ-stuck⁻ : Stuck⁻ W²ᴿᵖ
W²ᴿᵖ-stuck⁻ = stuck⁻! zero W²ᴿᵖ

W²ᴿ-stuck⁻ : Stuck⁻ W²ᴿ
W²ᴿ-stuck⁻ = stuck⁻-by zero W²ᴿᵖ W²ᴿ W²ᴿ-congruent

Wᶜ²-stuck⁻ : Stuck⁻ CX.⟦ Wᶜ² ⟧
Wᶜ²-stuck⁻ = stuck⁻! zero CX.⟦ Wᶜ² ⟧

Wᶜ²ᵖ-stuck⁻ : Stuck⁻ Wᶜ²ᵖ
Wᶜ²ᵖ-stuck⁻ = stuck⁻! zero Wᶜ²ᵖ

Wᶜ²ᴿᵖ-stuck⁻ : Stuck⁻ Wᶜ²ᴿᵖ
Wᶜ²ᴿᵖ-stuck⁻ = stuck⁻! zero Wᶜ²ᴿᵖ

Wᶜ²ᴿ-stuck⁻ : Stuck⁻ Wᶜ²ᴿ
Wᶜ²ᴿ-stuck⁻ = stuck⁻-by zero Wᶜ²ᴿᵖ Wᶜ²ᴿ Wᶜ²ᴿ-congruent

-- So [Elim], [ω] and [HH] never get rid of the path variables, and
-- every chain of figure 2 that does begins with a [Case].

W²-needs-case : NeedsCase CX.⟦ W² ⟧
W²-needs-case = stuck⁻-chains CX.⟦ W² ⟧ W²-stuck⁻

W²ᴿ-needs-case : NeedsCase W²ᴿ
W²ᴿ-needs-case = stuck⁻-chains W²ᴿ W²ᴿ-stuck⁻

W²-case-first : CaseFirst CX.⟦ W² ⟧
W²-case-first = case-first CX.⟦ W² ⟧ W²-stuck⁻

W²ᴿ-case-first : CaseFirst W²ᴿ
W²ᴿ-case-first = case-first W²ᴿ W²ᴿ-stuck⁻

Wᶜ²-needs-case : NeedsCase CX.⟦ Wᶜ² ⟧
Wᶜ²-needs-case = stuck⁻-chains CX.⟦ Wᶜ² ⟧ Wᶜ²-stuck⁻

Wᶜ²ᴿ-needs-case : NeedsCase Wᶜ²ᴿ
Wᶜ²ᴿ-needs-case = stuck⁻-chains Wᶜ²ᴿ Wᶜ²ᴿ-stuck⁻

Wᶜ²-case-first : CaseFirst CX.⟦ Wᶜ² ⟧
Wᶜ²-case-first = case-first CX.⟦ Wᶜ² ⟧ Wᶜ²-stuck⁻

Wᶜ²ᴿ-case-first : CaseFirst Wᶜ²ᴿ
Wᶜ²ᴿ-case-first = case-first Wᶜ²ᴿ Wᶜ²ᴿ-stuck⁻


------------------------------------------------------------------------
-- With [Case], the restrictions reduce to the identity

-- [Case] at (y₂ , y₁) with X = x₁: the y₂-quarter of the phase is
-- ¼x₁ + ½Q and the y₁-quarter ¼(1 - x₁) + ½Q′, with Q and Q′ Boolean
-- polynomials in x₁, x₂ and y₃ (the only path variable left, now
-- yᵐ zero).  Then [Elim] removes y₃.

-- W²: Q = 1 - y₃, Q′ = 1 ⊕ x₁ ⊕ x₂.

W²ᴿᵖ₁ : PathSum 2 2 1
W²ᴿᵖ₁ = case-reduct (front₂ (suc zero) zero 1≢0 W²ᴿᵖ)
          (mono x₁) (not₁ (yᵐ zero)) (not-xor₂ x₁ x₂)

W²ᴿᵖ₂ : PathSum 2 0 0
W²ᴿᵖ₂ = elim-reduct (front zero W²ᴿᵖ₁)

W²ᴿᵖ-case : W²ᴿᵖ ⟶ᶠ W²ᴿᵖ₁
W²ᴿᵖ-case = caseAt! W²ᴿᵖ (suc zero) zero 1≢0
              (mono x₁) (not₁ (yᵐ zero)) (not-xor₂ x₁ x₂)

W²ᴿᵖ-chain : W²ᴿᵖ ⟶ᶠ* W²ᴿᵖ₂
W²ᴿᵖ-chain = W²ᴿᵖ-case ◅ᶠ elimAt! W²ᴿᵖ₁ zero ◅ᶠ εᶠ

W²ᴿᵖ-uses-case : ¬ NoCaseᶠ W²ᴿᵖ-case
W²ᴿᵖ-uses-case ()

W²ᴿᵖ-end : Cong.Id-syntactic W²ᴿᵖ₂
W²ᴿᵖ-end = toWitness {a? = Cong.id-syntactic? W²ᴿᵖ₂} tt

W²ᴿᵖ-id : W²ᴿᵖ ≋ idPS
W²ᴿᵖ-id = reduces-to-id W²ᴿᵖ W²ᴿᵖ-chain

-- Wᶜ²: Q = 1 ⊕ x₁ ⊕ y₃, Q′ = 1 - x₂.

Wᶜ²ᴿᵖ₁ : PathSum 2 2 1
Wᶜ²ᴿᵖ₁ = case-reduct (front₂ (suc zero) zero 1≢0 Wᶜ²ᴿᵖ)
           (mono x₁) (not-xor₂ x₁ (yᵐ zero)) (not₁ x₂)

Wᶜ²ᴿᵖ₂ : PathSum 2 0 0
Wᶜ²ᴿᵖ₂ = elim-reduct (front zero Wᶜ²ᴿᵖ₁)

Wᶜ²ᴿᵖ-case : Wᶜ²ᴿᵖ ⟶ᶠ Wᶜ²ᴿᵖ₁
Wᶜ²ᴿᵖ-case = caseAt! Wᶜ²ᴿᵖ (suc zero) zero 1≢0
               (mono x₁) (not-xor₂ x₁ (yᵐ zero)) (not₁ x₂)

Wᶜ²ᴿᵖ-chain : Wᶜ²ᴿᵖ ⟶ᶠ* Wᶜ²ᴿᵖ₂
Wᶜ²ᴿᵖ-chain = Wᶜ²ᴿᵖ-case ◅ᶠ elimAt! Wᶜ²ᴿᵖ₁ zero ◅ᶠ εᶠ

Wᶜ²ᴿᵖ-uses-case : ¬ NoCaseᶠ Wᶜ²ᴿᵖ-case
Wᶜ²ᴿᵖ-uses-case ()

Wᶜ²ᴿᵖ-end : Cong.Id-syntactic Wᶜ²ᴿᵖ₂
Wᶜ²ᴿᵖ-end = toWitness {a? = Cong.id-syntactic? Wᶜ²ᴿᵖ₂} tt

Wᶜ²ᴿᵖ-id : Wᶜ²ᴿᵖ ≋ idPS
Wᶜ²ᴿᵖ-id = reduces-to-id Wᶜ²ᴿᵖ Wᶜ²ᴿᵖ-chain

-- Hence the circuits are the identity by the paper's route of section
-- 4: the rules on the restriction, then lemma 4.1.

W²-by-restriction : CX.⟦ W² ⟧ ≋ idPS
W²-by-restriction =
  by-restriction W² W²ᴿ W²ᴿᵖ W²-restriction W²ᴿ-literal W²ᴿᵖ-id

Wᶜ²-by-restriction : CX.⟦ Wᶜ² ⟧ ≋ idPS
Wᶜ²-by-restriction =
  by-restriction Wᶜ² Wᶜ²ᴿ Wᶜ²ᴿᵖ Wᶜ²-restriction Wᶜ²ᴿ-literal Wᶜ²ᴿᵖ-id


------------------------------------------------------------------------
-- With [Case], the path-sums reduce to the identity

-- [Case] at (y₂ , y₁) with X = x₁, Q and Q′ in x₁, x₂ and the path
-- variables y₃, y₄ left (now yᵐ zero and yᵐ (suc zero)); then [HH] at
-- y₃ substituting for y₄, and [Elim] removes y₄.

-- W²: Q = 1 - y₃, Q′ = 1 ⊕ x₁ ⊕ x₂; then y₄ ← x₁ ⊕ x₂.

W²ᵖ₁ : PathSum 2 2 2
W²ᵖ₁ = case-reduct (front₂ (suc zero) zero 1≢0 W²ᵖ)
         (mono x₁) (not₁ (yᵐ zero)) (not-xor₂ x₁ x₂)

W²ᵖ₂ : PathSum 2 2 1
W²ᵖ₂ = hhᴳ-reduct (front zero W²ᵖ₁) zero (xor₂ x₁ x₂)

W²ᵖ₃ : PathSum 2 0 0
W²ᵖ₃ = elim-reduct (front zero W²ᵖ₂)

W²ᵖ-case : W²ᵖ ⟶ᶠ W²ᵖ₁
W²ᵖ-case = caseAt! W²ᵖ (suc zero) zero 1≢0
             (mono x₁) (not₁ (yᵐ zero)) (not-xor₂ x₁ x₂)

W²ᵖ-chain : W²ᵖ ⟶ᶠ* W²ᵖ₃
W²ᵖ-chain =
  W²ᵖ-case ◅ᶠ hhAt! W²ᵖ₁ zero zero (xor₂ x₁ x₂) ◅ᶠ
  elimAt! W²ᵖ₂ zero ◅ᶠ εᶠ

W²ᵖ-uses-case : ¬ NoCaseᶠ W²ᵖ-case
W²ᵖ-uses-case ()

W²ᵖ-end : Cong.Id-syntactic W²ᵖ₃
W²ᵖ-end = toWitness {a? = Cong.id-syntactic? W²ᵖ₃} tt

W²ᵖ-id : W²ᵖ ≋ idPS
W²ᵖ-id = reduces-to-id W²ᵖ W²ᵖ-chain

-- Wᶜ²: Q = 1 ⊕ x₁ ⊕ y₃, Q′ = 1 - x₂; then y₄ ← x₂.

Wᶜ²ᵖ₁ : PathSum 2 2 2
Wᶜ²ᵖ₁ = case-reduct (front₂ (suc zero) zero 1≢0 Wᶜ²ᵖ)
          (mono x₁) (not-xor₂ x₁ (yᵐ zero)) (not₁ x₂)

Wᶜ²ᵖ₂ : PathSum 2 2 1
Wᶜ²ᵖ₂ = hhᴳ-reduct (front zero Wᶜ²ᵖ₁) zero (mono x₂)

Wᶜ²ᵖ₃ : PathSum 2 0 0
Wᶜ²ᵖ₃ = elim-reduct (front zero Wᶜ²ᵖ₂)

Wᶜ²ᵖ-case : Wᶜ²ᵖ ⟶ᶠ Wᶜ²ᵖ₁
Wᶜ²ᵖ-case = caseAt! Wᶜ²ᵖ (suc zero) zero 1≢0
              (mono x₁) (not-xor₂ x₁ (yᵐ zero)) (not₁ x₂)

Wᶜ²ᵖ-chain : Wᶜ²ᵖ ⟶ᶠ* Wᶜ²ᵖ₃
Wᶜ²ᵖ-chain =
  Wᶜ²ᵖ-case ◅ᶠ hhAt! Wᶜ²ᵖ₁ zero zero (mono x₂) ◅ᶠ
  elimAt! Wᶜ²ᵖ₂ zero ◅ᶠ εᶠ

Wᶜ²ᵖ-uses-case : ¬ NoCaseᶠ Wᶜ²ᵖ-case
Wᶜ²ᵖ-uses-case ()

Wᶜ²ᵖ-end : Cong.Id-syntactic Wᶜ²ᵖ₃
Wᶜ²ᵖ-end = toWitness {a? = Cong.id-syntactic? Wᶜ²ᵖ₃} tt

Wᶜ²ᵖ-id : Wᶜ²ᵖ ≋ idPS
Wᶜ²ᵖ-id = reduces-to-id Wᶜ²ᵖ Wᶜ²ᵖ-chain

-- Hence the circuits are the identity by the rules, from their own
-- path-sums.

W²-by-rules : CX.⟦ W² ⟧ ≋ idPS
W²-by-rules = through W² W²ᵖ W²-literal W²ᵖ-id

Wᶜ²-by-rules : CX.⟦ Wᶜ² ⟧ ≋ idPS
Wᶜ²-by-rules = through Wᶜ² Wᶜ²ᵖ Wᶜ²-literal Wᶜ²ᵖ-id


------------------------------------------------------------------------
-- Section 3.2's claim, in one statement for each reading

-- The identity holds; no rule of figure 2 but [Case] applies to its
-- path-sum or to its restriction, so without [Case] neither loses its
-- path variables; with [Case] both reduce to the identity.

case-identity :
  CX.⟦ W² ⟧ ≋ idPS ×
  Stuck⁻ CX.⟦ W² ⟧ × Stuck⁻ W²ᴿ ×
  NeedsCase CX.⟦ W² ⟧ × NeedsCase W²ᴿ ×
  (W²ᵖ ⟶ᶠ* W²ᵖ₃) × Cong.Id-syntactic W²ᵖ₃ ×
  (W²ᴿᵖ ⟶ᶠ* W²ᴿᵖ₂) × Cong.Id-syntactic W²ᴿᵖ₂
case-identity =
  W²-id , W²-stuck⁻ , W²ᴿ-stuck⁻ , W²-needs-case , W²ᴿ-needs-case ,
  W²ᵖ-chain , W²ᵖ-end , W²ᴿᵖ-chain , W²ᴿᵖ-end

case-identityᶜ :
  CX.⟦ Wᶜ² ⟧ ≋ idPS ×
  Stuck⁻ CX.⟦ Wᶜ² ⟧ × Stuck⁻ Wᶜ²ᴿ ×
  NeedsCase CX.⟦ Wᶜ² ⟧ × NeedsCase Wᶜ²ᴿ ×
  (Wᶜ²ᵖ ⟶ᶠ* Wᶜ²ᵖ₃) × Cong.Id-syntactic Wᶜ²ᵖ₃ ×
  (Wᶜ²ᴿᵖ ⟶ᶠ* Wᶜ²ᴿᵖ₂) × Cong.Id-syntactic Wᶜ²ᴿᵖ₂
case-identityᶜ =
  Wᶜ²-id , Wᶜ²-stuck⁻ , Wᶜ²ᴿ-stuck⁻ , Wᶜ²-needs-case , Wᶜ²ᴿ-needs-case ,
  Wᶜ²ᵖ-chain , Wᶜ²ᵖ-end , Wᶜ²ᴿᵖ-chain , Wᶜ²ᴿᵖ-end
