------------------------------------------------------------------------
-- Presentations of groups
--
-- At order 2 the polynomial-time normal forms are normal forms of all
-- of figure 2
--
-- Proposition 3.2 (Amy, QPL 2018) says that every sequence of rewrites
-- "terminates with an irreducible path-sum" in time polynomial in n and
-- m.  PathSum.Cost.Normalise proves the time claim in a cost model,
-- for the linear rules of PathSum.Anywhere ([Elim], and [ω] and [HH]
-- with Z₂-linear quotients, at any variable): its normaliser's result
-- is irreducible under those rules (Normalised.stuck), and figure 2's
-- other steps -- [ω] and [HH] with Boolean-valued quotients that are not
-- linear, and [Case] -- are left out, since they can raise the order
-- the cost bounds rest on (PathSum.Cost.Excluded).  At order 2 nothing
-- is lost: there a path-sum to which no linear rule applies is
-- irreducible under all of figure 2 (PathSum.Full.Order2), so the
-- normaliser, run at d = 2 on a phase of order at most 2, computes a
-- normal form of the whole calculus _⟶ᶠ_ of PathSum.Full.
--
-- * stuckᶠ: every path-sum the result represents is irreducible under
--   _⟶ᶠ_ (Irreducibleᶠ), in particular the end of its chain
--   (reduct-irreducibleᶠ) and the path-sum it stands for
--   (psᴺ-irreducibleᶠ); the chain is one of _⟶ᶠ_ too (chainᶠ).
-- * Proposition-3-2ᶠ / proposition-3-2ᶠ: proposition 3.2 for all of
--   figure 2 at order 2.  Every chain of _⟶ᶠ_ terminates and its length
--   is between half of m − m′ and m − m′ (PathSum.Full), and the linear
--   normaliser reaches an Irreducibleᶠ path-sum along a chain of _⟶ᶠ_
--   at the cost PathSum.Cost.Normalise bounds, at most
--   (L + 284)(n + m + 3)^11 for an input of L terms.  The cost bound is
--   for that normaliser: a sequence of general [ω], [HH] or [Case]
--   steps is not costed.  At order 2 none is needed, since a linear
--   step applies whenever one of them does (PathSum.Full.Order2.⟶ᶠ⇒⟶ᵍ).
--   In particular this holds for the isometry restriction ⟦ C ⟧ᴿ of
--   every Clifford circuit (circuit-proposition-3-2ᶠ).
-- * PipelineNormalForm / pipeline-normal-form: the normal form
--   corollary 4.4's decision procedure computes and reads its verdict
--   from (PathSum.Cost.Corollary: count, interpret ⟦ C ⟧ᴿ sparsely,
--   normalise at order 2) is Irreducibleᶠ.  So the verdict is that of
--   PathSum.Full.Clifford.corollary-4-4-normalᶠ, corollary 4.4 for
--   every normal form of figure 2: the circuit is the identity iff no
--   path variable is left and what is left is syntactically |x⟩ ↦ |x⟩
--   (verdictᶠ).  corollary-4-4-polytimeᶠ packages this with
--   corollary-4-4-polytime.
--
-- The precision is M = 3 + M₀, as in PathSum.Full.Clifford and
-- PathSum.Cost.Corollary.  Costs are counted in the cost model of
-- PathSum.Cost: a cost model, not a machine model; nothing is claimed
-- about Turing machines or complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Irreducible (M₀ : ℕ) where

open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (List; _∷_; length)
open import Data.Nat.Base using (zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Function.Bundles using (_⇔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.Circuit M using
  (Gate; Circuit; norm; paths; ⟦_⟧; ⟦_⟧ᴿ; ⟦⟧ᴿ-Ord≤)
open import PathSum.Cost using (value; cost)
open import PathSum.Cost.Corollary M₀ using
  (pipelineᶜ; decideᶜ; verdictᶜ; Corollary-4-4; corollary-4-4-polytime)
open import PathSum.Cost.Normalise M using
  (Normal; nk; nm; nrep; psᴺ; normaliseᶜ; Normalised; reduct; chain;
   reduct-represents; reduct-ordered; stuck; normalise-sound;
   Proposition-3-2; proposition-3-2)
open import PathSum.Cost.Restriction M using
  (countHᶜ; value-countHᶜ; interpᴿᶜ; interpᴿ-denotes)
open import PathSum.Cost.Rules M using (phase-Ord≤; psʳ-represents)
open import PathSum.Anywhere M using (SN)
open import PathSum.Denotation M₀ using (_≋_)
open import PathSum.Full M using
  (_⟶ᶠ_; _⟶ᶠ*_; ⟶ᵍ*⇒⟶ᶠ*; ⟶ᶠ-SN; lenᶠ; ⟶ᶠ*-length; ⟶ᶠ*-length-lower)
open import PathSum.Full.Clifford M₀ using (corollary-4-4-normalᶠ)
open import PathSum.Full.Match M using (Irreducibleᶠ)
open import PathSum.Full.Order2 M₀ using (Irreducible⇒Irreducibleᶠ)
open import PathSum.Order M using (Ord≤; pow)
open import PathSum.Polynomial using (x[_]; 0ᴾ; μ; _≈[_]_)
open import PathSum.Size.Interpreter M using (Denotes; denotes)
open import PathSum.Size.Sparse M using (Rep; terms; Represents)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- The normaliser's result, at order 2

-- Every path-sum the result represents has a phase of order at most 2
-- and no linear step, hence no step of figure 2.

stuckᶠ : {ξ : PathSum n k m} {r : Normal n} → Normalised 2 ξ r →
         (ψ : PathSum n (nk r) (nm r)) → Represents ψ (nrep r) →
         Irreducibleᶠ ψ
stuckᶠ {r = r} N ψ rp = Irreducible⇒Irreducibleᶠ ψ
  (phase-Ord≤ ψ (nrep r) rp (reduct-ordered N)) (stuck N ψ rp)

-- In particular the end of the chain, and the path-sum the result
-- stands for.

reduct-irreducibleᶠ : {ξ : PathSum n k m} {r : Normal n}
                      (N : Normalised 2 ξ r) → Irreducibleᶠ (reduct N)
reduct-irreducibleᶠ N = stuckᶠ N (reduct N) (reduct-represents N)

psᴺ-irreducibleᶠ : {ξ : PathSum n k m} {r : Normal n}
                   (N : Normalised 2 ξ r) → Irreducibleᶠ (psᴺ r)
psᴺ-irreducibleᶠ {r = r} N =
  stuckᶠ N (psᴺ r) (psʳ-represents {k = nk r} (nrep r))

-- The chain is one of figure 2.

chainᶠ : {ξ : PathSum n k m} {r : Normal n} (N : Normalised 2 ξ r) →
         ξ ⟶ᶠ* reduct N
chainᶠ N = ⟶ᵍ*⇒⟶ᶠ* (chain N)


------------------------------------------------------------------------
-- Proposition 3.2 for all of figure 2, at order 2

-- The statement of PathSum.Cost.Normalise at d = 2 (every chain of the
-- linear rules terminates and has length m − m′; the normaliser's
-- result, its cost, and the cost of every sequence of sparse
-- rewrites), and for figure 2: every chain terminates and has length
-- between half of m − m′ and m − m′, and the normaliser's chain is one
-- of figure 2 ending at a normal form of figure 2.

record Proposition-3-2ᶠ {n k m : ℕ} (ξ : PathSum n k m)
                        (R : Rep n m) : Set where
  field
    linear      : Proposition-3-2 2 ξ R
    terminatesᶠ : SN _⟶ᶠ_ ξ
    lengthᶠ     : ∀ {k′ m′} {ζ : PathSum n k′ m′} (steps : ξ ⟶ᶠ* ζ) →
                  (lenᶠ steps + m′ ≤ m) ×
                  (m ≤ (lenᶠ steps + lenᶠ steps) + m′)
    reachesᶠ    : ξ ⟶ᶠ* reduct (Proposition-3-2.normalises linear)
    normalᶠ     : (ψ : PathSum n (nk (value (normaliseᶜ 2 k R)))
                                 (nm (value (normaliseᶜ 2 k R)))) →
                  Represents ψ (nrep (value (normaliseᶜ 2 k R))) →
                  Irreducibleᶠ ψ

proposition-3-2ᶠ : (ξ : PathSum n k m) (R : Rep n m) → Represents ξ R →
                   Ord≤ 2 (phase ξ) → Proposition-3-2ᶠ ξ R
proposition-3-2ᶠ ξ R rp ordP = record
  { linear      = P
  ; terminatesᶠ = ⟶ᶠ-SN ξ
  ; lengthᶠ     = λ steps → ⟶ᶠ*-length steps , ⟶ᶠ*-length-lower steps
  ; reachesᶠ    = chainᶠ (Proposition-3-2.normalises P)
  ; normalᶠ     = stuckᶠ (Proposition-3-2.normalises P)
  }
  where
  P = proposition-3-2 2 (s≤s (s≤s z≤n)) ξ R rp ordP

-- In particular for the isometry restriction of every Clifford circuit,
-- whatever represents it.

circuit-proposition-3-2ᶠ : (C : Circuit n) (R : Rep n (paths C)) →
                           Represents ⟦ C ⟧ᴿ R → Proposition-3-2ᶠ ⟦ C ⟧ᴿ R
circuit-proposition-3-2ᶠ C R rp = proposition-3-2ᶠ ⟦ C ⟧ᴿ R rp (⟦⟧ᴿ-Ord≤ C)


------------------------------------------------------------------------
-- The normal form of corollary 4.4's decision procedure

-- PathSum.Cost.Corollary's pipeline counts the Hadamards, interprets
-- ⟦ C ⟧ᴿ into a sparse representation, normalises it at order 2, and
-- reads the verdict off the result.  This is that result.

pipelineNormal : Circuit n → Normal n
pipelineNormal C =
  value (normaliseᶜ 2 (value (countHᶜ C)) (proj₂ (value (interpᴿᶜ C))))

-- The verdict is read off it, by definition; for a non-empty circuit
-- the decision is the pipeline's.

pipeline-reads : (C : Circuit n) →
                 value (pipelineᶜ C) ≡ value (verdictᶜ (pipelineNormal C))
pipeline-reads C = refl

decide-reads : (g : Gate n) (C : Circuit n) →
               value (decideᶜ (g ∷ C)) ≡
               value (verdictᶜ (pipelineNormal (g ∷ C)))
decide-reads g C = refl

-- It is a normal form of ⟦ C ⟧ᴿ under the linear rules, as
-- PathSum.Cost.Corollary.pipeline-correct uses it ...

pipeline-normalised : (C : Circuit n) →
                      Normalised 2 ⟦ C ⟧ᴿ (pipelineNormal C)
pipeline-normalised {n} C =
  at (value (countHᶜ C)) (value-countHᶜ C) (value (interpᴿᶜ C))
     (interpᴿ-denotes C)
  where
  at : (k : ℕ) → k ≡ norm C → (p : ∃ (Rep n)) → Denotes ⟦ C ⟧ᴿ p →
       Normalised 2 ⟦ C ⟧ᴿ (value (normaliseᶜ 2 k (proj₂ p)))
  at .(norm C) refl .(paths C , R) (denotes R rp) =
    normalise-sound 2 (s≤s (s≤s z≤n)) ⟦ C ⟧ᴿ R rp (⟦⟧ᴿ-Ord≤ C)

-- ... and of figure 2, from which the verdict of corollary 4.4 for
-- every normal form of figure 2 is read.

record PipelineNormalForm {n : ℕ} (C : Circuit n) : Set where
  field
    normalised : Normalised 2 ⟦ C ⟧ᴿ (pipelineNormal C)
    reachesᶠ   : ⟦ C ⟧ᴿ ⟶ᶠ* reduct normalised
    normalᶠ    : (ψ : PathSum n (nk (pipelineNormal C))
                                  (nm (pipelineNormal C))) →
                 Represents ψ (nrep (pipelineNormal C)) → Irreducibleᶠ ψ
    verdictᶠ   : ⟦ C ⟧ ≋ idPS ⇔
                 (nm (pipelineNormal C) ≡ 0 × nk (pipelineNormal C) ≡ 0 ×
                  (∀ w → out (reduct normalised) w ≈[ + 2 ] μ x[ w ]) ×
                  phase (reduct normalised) ≈[ pow M ] 0ᴾ)

pipeline-normal-form : (C : Circuit n) → PipelineNormalForm C
pipeline-normal-form C = record
  { normalised = N
  ; reachesᶠ   = chainᶠ N
  ; normalᶠ    = stuckᶠ N
  ; verdictᶠ   = corollary-4-4-normalᶠ C {ξ′ = reduct N} (chainᶠ N)
                   (reduct-irreducibleᶠ N)
  }
  where
  N = pipeline-normalised C

-- Corollary 4.4 in polynomial time, with the normal form it computes
-- one of figure 2.

corollary-4-4-polytimeᶠ : (C : Circuit n) →
                          Corollary-4-4 C × PipelineNormalForm C
corollary-4-4-polytimeᶠ C =
  corollary-4-4-polytime C , pipeline-normal-form C
