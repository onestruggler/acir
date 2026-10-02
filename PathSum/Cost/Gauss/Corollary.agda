------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary 4.4 in polynomial time by the paper's own route, for
-- Clifford circuits over {H, CNOT, R_k, R_k†}, and their equivalence
-- (Amy, QPL 2018)
--
-- Corollary 4.4 reads: "If C is a Clifford-group quantum circuit, then
-- ⟦C⟧ ≡ |x⟩ ↦ |x⟩ can be decided in time polynomial in the space-time
-- volume of C".  Its proof: ⟦C⟧ is well-formed, so by lemma 4.1 it
-- suffices to check the isometry restriction ⟦C⟧|f(x,y)=x; "as f(x,y)
-- is linear, we can compute via Gaussian elimination a solution y so
-- that f(x,y) = x for any x -- if no such solution exists, ⟦C⟧ ≢
-- |x⟩ ↦ |x⟩"; each substitution keeps the order at most 2, so by lemma
-- 4.3 and proposition 3.2 the restriction reduces to |x⟩ ↦ |x⟩ or is
-- not the identity.  PathSum.Cost.Corollary proves the time claim for
-- circuits over {H, S, CZ}, whose restriction can be read off during
-- interpretation.  This module proves it for the paper's own gate set,
-- {H, CNOT, R_k, R_k†} (PathSum.CRK.Circuit) at level ≤ 2 -- the
-- Clifford circuits: their only phase gates are R_0 = I, R_1 = Z and
-- R_2 = S and their inverses -- by the paper's own route, Gaussian
-- elimination, every step a program in the monad of PathSum.Cost.
--
-- The decision, for a circuit C (decideᴳᶜ):
--
--  1. count the Hadamards, the normalisation of ⟦ C ⟧ (countHᴷᶜ);
--  2. interpret C sparsely (PathSum.Cost.Interpreter.interpKᶜ, the
--     interpreter of corollary 2.15's time half): |C| (n + |C| + 1)^2
--     terms at most, and at most |C| path variables;
--  3. eliminate at order 2 (PathSum.Cost.Gauss.gaussᶜ 2): either an
--     input x for which f(x,y) = x has no solution y, or a sparse
--     representation of the reified restriction ⟦C⟧|f(x,y)=x, with at
--     most (n + m + 2)^2 terms;
--  4. if refuted, answer no (concludeᶜ): the diagonal entry at x
--     vanishes, so ⟦ C ⟧ ≢ |x⟩ ↦ |x⟩ (PathSum.Cost.Gauss.Correct.
--     circuit-refutes, the paper's "if no such solution exists");
--  5. otherwise normalise the restriction at order 2 (PathSum.Cost.
--     Normalise.normaliseᶜ 2), and read the verdict on the normal form
--     (PathSum.Cost.Corollary.verdictᶜ): a path variable left means no,
--     by lemma 4.3's progress (PathSum.Clifford.progress) on an
--     irreducible, internal path-sum of order 2; none left, the final
--     test of PathSum.Cost.Identity.
--
-- decideᴳ-correct: for level C ≤ 2 the value is true exactly when
-- ⟦ C ⟧ ≋ idPS.  The chain: interpK-tracks (the sparse run tracks the
-- dense one), the lockstep of the elimination with PathSum.Gauss's
-- (PathSum.Cost.Gauss.Correct), proposition 2.14 (corrected) for the
-- order, normalise-sound, proposition 3.1 along the normaliser's chain,
-- and lemma 4.1 at the circuit (circuit-identity: the restriction is
-- the identity exactly when ⟦ C ⟧ is, ⟦ C ⟧ having unit columns).  The
-- elimination refutes exactly when some input has no solution
-- (PathSum.Cost.Gauss.Correct.refutes⇔no-solution); when PathSum.Gauss.
-- Corollary's own restriction ⟦ C ⟧ᴿ exists, the program's is ≋ to it,
-- and the two never disagree about the identity (reifies-≋-⟦⟧ᴿ,
-- refutes-⟦⟧ᴿ, ⟦⟧ᴿ-nothing-reifies).
--
-- The cost is at most 398 (n + |C| + 3)^11 (cost-decideᴳᶜ): the
-- interpretation at most 23 B^4 (B = n + |C| + 3), the elimination at
-- most 6 B^6 + 74 B^9, the normalisation at most 6 B^5 + 279 B^11 -- it
-- dominates -- and the final test at most 7 B^6.  Every part is
-- bounded at a variable B ≥ n + |C| + 3 (the -at lemmas) and only then
-- instantiated.  In the volume n · |C| it is at most
-- 398 (2 n |C| + 3)^11 (cost-decideᴳ-volume): a gate names a wire, so
-- n ≥ 1 whenever |C| ≥ 1, and the empty circuit, whose path-sum is the
-- identity (PathSum.CRK.Miter.†-inverseʳ at []), is answered at once,
-- as in PathSum.Cost.Corollary.  corollary-4-4-polytime-gauss packages
-- the three.  The bounds are upper bounds, not tight.
--
-- Equivalence (equivᴳᶜ): the miter C₁ ++ C₂† of PathSum.CRK.Miter is
-- built in the monad (daggerᴷᶜ, miterᴷᶜ; here the inverse of a gate is
-- one gate, R_k† for R_k, so |C₂†| = |C₂|) and decided.  It is Clifford
-- when both circuits are (PathSum.CRK.Adjoint.level-miter).
-- equivᴳ-correct: for two circuits of level ≤ 2 the value is true
-- exactly when ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ (PathSum.CRK.Miter.miter), and the cost
-- is at most 400 (n + |C₁| + |C₂| + 3)^11 (cost-equivᴳᶜ):
-- equivalence-polytime-gauss, the abstract's "polynomial-time decision
-- procedure for checking the equivalence of Clifford group circuits"
-- for the paper's gate set and route.  Equivalence is definition 2.3's:
-- equality of the operators, global phase included.
--
-- What is assumed: level C ≤ 2 is a hypothesis, the promise of
-- corollary 4.4 ("if C is a Clifford-group circuit"); the program does
-- not check it (a linear scan would).  For larger levels the
-- elimination still refutes or reifies correctly (PathSum.Cost.Gauss.
-- Correct, at any d ≥ max(2, level C)), but the normalisation at order
-- 2 and its verdict are not a decision there.  The normaliser uses
-- PathSum.Anywhere's rules only ([Elim], [ω], [HH] with Z₂-linear
-- quotients), which is all lemma 4.3 needs.  The pivots of the
-- elimination follow the rule PathSum.Gauss.Forms.pivot? follows, but
-- are not proved to be gauss's own (see PathSum.Cost.Gauss.Correct).
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.  Conventions beyond PathSum.Cost's, as in
-- PathSum.Cost.Corollary: the Hadamard counter is read and updated in
-- one step each; reading which of the two outcomes the elimination
-- returned is one step; whether the circuit is empty is read in one
-- step when it is, and otherwise absorbed in the count, which reads
-- the first gate anyway; the circuit's level is not read at all.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Cost.Gauss.Corollary (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using
  (zero; _+_; _*_; _^_; _≤_; _⊔_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃; Σ; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Function.Properties.Equivalence using ()
  renaming (trans to ⇔-trans; sym to ⇔-sym)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base using (PathSum; idPS)
open import PathSum.Cost
open import PathSum.Cost.Bound using (^-mono; ^-pos; B*B)
open import PathSum.Cost.Canon M using
  (Canonical; canonical-length; canonᶜ; value-canonᶜ; cost-canonᶜ)
open import PathSum.Cost.Corollary M₀ using
  (verdictᶜ; verdict-correct; normalise-canonical)
open import PathSum.Cost.Gauss M using
  (Outcome; refutes; reifies; gaussᶜ; elimᶜ; cost-elimᶜ; elimBound-≤;
   gaussᶜ-shape)
open import PathSum.Cost.Gauss.Correct M₀ using
  (circuit-refutes; circuit-reifies; circuit-identity; reified;
   represents; internal; order; ≋-gauss)
open import PathSum.Cost.Identity M using (idTestᶜ; cost-idTest-poly)
open import PathSum.Cost.Interpreter M using
  (interpKᶜ; interpK-length; interpK-paths≤; cost-interpKᶜ)
open import PathSum.Cost.Normalise M using
  (Normal; normal; nrep; normaliseᶜ; normalise-sound; cost-normaliseᶜ;
   normBound)
open import PathSum.CRK.Adjoint M using (inv; _†; level-miter)
open import PathSum.CRK.Circuit M using
  (Gate; Circuit; norm; level; ⟦_⟧; prop-2-14; Ord≤-weaken)
open import PathSum.CRK.Miter M₀ using (miter; †-inverseʳ)
open import PathSum.Denotation M₀ using (_≋_)
open import PathSum.Gauss.Corollary M₀ using
  (lemma-4-1-gauss; not-id-gauss)
  renaming (⟦_⟧ᴿ to ⟦_⟧ᴳ)
open import PathSum.Size.Sparse M using
  (Rep; rep; terms; forms; volume-≤; ⟦_⟧ˢ)

import Data.List.Properties as List
import Data.Nat.Properties as ℕ
import PathSum.CRK.Circuit

private
  module K = PathSum.CRK.Circuit M

open +-*-Solver using (solve; _:+_; _:*_; _:^_; con; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The normalisation, counted

-- One step per gate, and one more to add a Hadamard.

countHᴷᶜ : Circuit n → Cost ℕ
countHᴷᶜ []                  = pure 0
countHᴷᶜ (K.H _ ∷ C)         = do
  tick
  c ← countHᴷᶜ C
  step (suc c)
countHᴷᶜ (K.CNOT _ _ _ ∷ C)  = tick >> countHᴷᶜ C
countHᴷᶜ (K.R _ _ ∷ C)       = tick >> countHᴷᶜ C
countHᴷᶜ (K.R† _ _ ∷ C)      = tick >> countHᴷᶜ C

value-countHᴷᶜ : (C : Circuit n) → value (countHᴷᶜ C) ≡ norm C
value-countHᴷᶜ []                 = refl
value-countHᴷᶜ (K.H _ ∷ C)        = cong suc (value-countHᴷᶜ C)
value-countHᴷᶜ (K.CNOT _ _ _ ∷ C) = value-countHᴷᶜ C
value-countHᴷᶜ (K.R _ _ ∷ C)      = value-countHᴷᶜ C
value-countHᴷᶜ (K.R† _ _ ∷ C)     = value-countHᴷᶜ C

private
  one-more : ∀ {a} L → a ≤ 2 * L → suc a ≤ 2 * suc L
  one-more L a≤ = ℕ.≤-trans (ℕ.n≤1+n _)
    (ℕ.≤-trans (s≤s (s≤s a≤)) (ℕ.≤-reflexive (sym (ℕ.*-suc 2 L))))

  two-more : ∀ {a} L → a ≤ 2 * L → suc (a + 1) ≤ 2 * suc L
  two-more {a} L a≤ = ℕ.≤-trans (ℕ.≤-reflexive (cong suc (ℕ.+-comm a 1)))
    (ℕ.≤-trans (s≤s (s≤s a≤)) (ℕ.≤-reflexive (sym (ℕ.*-suc 2 L))))

cost-countHᴷᶜ : (C : Circuit n) → cost (countHᴷᶜ C) ≤ 2 * length C
cost-countHᴷᶜ []                 = z≤n
cost-countHᴷᶜ (K.H _ ∷ C)        = two-more (length C) (cost-countHᴷᶜ C)
cost-countHᴷᶜ (K.CNOT _ _ _ ∷ C) = one-more (length C) (cost-countHᴷᶜ C)
cost-countHᴷᶜ (K.R _ _ ∷ C)      = one-more (length C) (cost-countHᴷᶜ C)
cost-countHᴷᶜ (K.R† _ _ ∷ C)     = one-more (length C) (cost-countHᴷᶜ C)


------------------------------------------------------------------------
-- After the elimination

-- Refuted: no.  Reified: normalise the restriction at order 2 and read
-- the verdict.  Reading which outcome it is costs one step.

concludeᶜ : ℕ → Outcome n → Cost Bool
concludeᶜ k (refutes x)  = step false
concludeᶜ k (reifies Q)  = do
  tick
  r ← normaliseᶜ 2 k Q
  verdictᶜ r


------------------------------------------------------------------------
-- The decision

-- Count, interpret, eliminate, conclude.

pipelineᴳᶜ : Circuit n → Cost Bool
pipelineᴳᶜ C = do
  k ← countHᴷᶜ C
  p ← interpKᶜ C
  o ← gaussᶜ 2 (proj₂ p)
  concludeᶜ k o

-- The empty circuit is the identity; any other goes through the
-- pipeline.

decideᴳᶜ : Circuit n → Cost Bool
decideᴳᶜ []      = step true
decideᴳᶜ (g ∷ C) = pipelineᴳᶜ (g ∷ C)

-- The empty circuit's path-sum is the identity: it is the miter of []
-- against itself.  (Through a substitution, so that no amplitude is
-- compared.)

private
  empty-miter : [] ++ [] † ≡ [] {A = Gate n}
  empty-miter = refl

empty-idᴷ : ⟦ [] ⟧ ≋ idPS {n}
empty-idᴷ {n} =
  subst (λ D → ⟦ D ⟧ ≋ idPS) (empty-miter {n}) (†-inverseʳ {n} [])

-- A Clifford circuit's phase has order at most 2 (proposition 2.14,
-- corrected).

private
  two⊔ : {C : Circuit n} → level C ≤ 2 → 2 ⊔ level C ≤ 2
  two⊔ lv = ℕ.⊔-lub ℕ.≤-refl lv

  one⊔ : {C : Circuit n} → level C ≤ 2 → 1 ⊔ level C ≤ 2
  one⊔ lv = ℕ.⊔-lub (s≤s z≤n) lv

-- The conclusion is correct on whatever the elimination returned.

conclude-correct : (C : Circuit n) → level C ≤ 2 → (o : Outcome n) →
                   value (gaussᶜ 2 (proj₂ (value (interpKᶜ C)))) ≡ o →
                   (value (concludeᶜ (norm C) o) ≡ true ⇔ ⟦ C ⟧ ≋ idPS)
conclude-correct C lv (refutes x) eq =
  mk⇔ (λ ()) (λ h → ⊥-elim (circuit-refutes C 2 (two⊔ {C = C} lv) eq h))
conclude-correct C lv (reifies Q) eq =
  ⇔-trans (verdict-correct (value (normaliseᶜ 2 (norm C) Q)) N (internal rs))
          (⇔-sym (circuit-identity C 2 le eq))
  where
  le : 2 ⊔ level C ≤ 2
  le = two⊔ {C = C} lv

  rs = circuit-reifies C 2 le eq

  N = normalise-sound 2 (s≤s (s≤s z≤n)) (reified rs) Q (represents rs)
        (order rs {2} (Ord≤-weaken le (prop-2-14 C)))

-- The pipeline answers true exactly for the identity circuits.

pipelineᴳ-correct : (C : Circuit n) → level C ≤ 2 →
                    (value (pipelineᴳᶜ C) ≡ true ⇔ ⟦ C ⟧ ≋ idPS)
pipelineᴳ-correct C lv = at (value (countHᴷᶜ C)) (value-countHᴷᶜ C)
  where
  at : (k : ℕ) → k ≡ norm C →
       (value (concludeᶜ k (value (gaussᶜ 2 (proj₂ (value (interpKᶜ C))))))
          ≡ true ⇔ ⟦ C ⟧ ≋ idPS)
  at _ refl = conclude-correct C lv _ refl

decideᴳ-correct : (C : Circuit n) → level C ≤ 2 →
                  (value (decideᴳᶜ C) ≡ true ⇔ ⟦ C ⟧ ≋ idPS)
decideᴳ-correct []      lv = mk⇔ (λ _ → empty-idᴷ) (λ _ → refl)
decideᴳ-correct (g ∷ C) lv = pipelineᴳ-correct (g ∷ C) lv

-- As a decision procedure: the Dec is the program's answer.

decideᴳ? : (C : Circuit n) → level C ≤ 2 → Dec (⟦ C ⟧ ≋ idPS)
decideᴳ? C lv = by (value (decideᴳᶜ C)) refl
  where
  by : ∀ b → value (decideᴳᶜ C) ≡ b → Dec (⟦ C ⟧ ≋ idPS)
  by true  e = yes (Equivalence.to (decideᴳ-correct C lv) e)
  by false e = no (λ h → false≢true
    (trans (sym e) (Equivalence.from (decideᴳ-correct C lv) h)))
    where
    false≢true : false ≡ true → ⊥
    false≢true ()


------------------------------------------------------------------------
-- Against PathSum.Gauss.Corollary's restriction

-- When PathSum.Gauss reifies the restriction ⟦ C ⟧ᴳ, the program's is
-- ≋ to it; and whichever of the two refutes, the other's restriction
-- is not the identity.  So the two never disagree about the identity.

reifies-≋-⟦⟧ᴿ : (C : Circuit n) (d : ℕ) (le : 2 ⊔ level C ≤ d)
                {m′ : ℕ} {Q : Rep n m′}
                (eq : value (gaussᶜ d (proj₂ (value (interpKᶜ C)))) ≡
                      reifies Q) →
                {m₀ : ℕ} {ξ₀ : PathSum n (norm C) m₀} →
                ⟦ C ⟧ᴳ ≡ just (m₀ , ξ₀) →
                reified (circuit-reifies C d le eq) ≋ ξ₀
reifies-≋-⟦⟧ᴿ C d le eq e = ≋-gauss (circuit-reifies C d le eq) e

refutes-⟦⟧ᴿ : (C : Circuit n) (d : ℕ) → 2 ⊔ level C ≤ d → ∀ {x} →
              value (gaussᶜ d (proj₂ (value (interpKᶜ C)))) ≡ refutes x →
              {m₀ : ℕ} {ξ₀ : PathSum n (norm C) m₀} →
              ⟦ C ⟧ᴳ ≡ just (m₀ , ξ₀) → ¬ (ξ₀ ≋ idPS)
refutes-⟦⟧ᴿ C d le eq e id₀ =
  circuit-refutes C d le eq (Equivalence.from (lemma-4-1-gauss C e) id₀)

⟦⟧ᴿ-nothing-reifies : (C : Circuit n) (d : ℕ) (le : 2 ⊔ level C ≤ d)
                      {m′ : ℕ} {Q : Rep n m′}
                      (eq : value (gaussᶜ d (proj₂ (value (interpKᶜ C)))) ≡
                            reifies Q) →
                      ⟦ C ⟧ᴳ ≡ nothing →
                      ¬ (reified (circuit-reifies C d le eq) ≋ idPS)
⟦⟧ᴿ-nothing-reifies C d le eq e id′ =
  not-id-gauss C e (Equivalence.from (circuit-identity C d le eq) id′)


------------------------------------------------------------------------
-- The explicit polynomials

-- Opaque: Agda never unfolds a power of a numeral-headed base, which it
-- would do into unary numbers.  Their defining equations are
-- decideᴳBound-def, volumeᴳBound-def and equivᴳBound-def.

opaque
  decideᴳBound : ℕ → ℕ → ℕ
  decideᴳBound n ℓ = 398 * (3 + (n + ℓ)) ^ 11

  decideᴳBound-def : ∀ n ℓ → decideᴳBound n ℓ ≡ 398 * (3 + (n + ℓ)) ^ 11
  decideᴳBound-def n ℓ = refl

  volumeᴳBound : ℕ → ℕ
  volumeᴳBound v = 398 * (3 + 2 * v) ^ 11

  volumeᴳBound-def : ∀ v → volumeᴳBound v ≡ 398 * (3 + 2 * v) ^ 11
  volumeᴳBound-def v = refl

  equivᴳBound : ℕ → ℕ → ℕ → ℕ
  equivᴳBound n a b = 400 * (3 + (n + (a + b))) ^ 11

  equivᴳBound-def : ∀ n a b →
                    equivᴳBound n a b ≡ 400 * (3 + (n + (a + b))) ^ 11
  equivᴳBound-def n a b = refl

-- Arithmetic at a variable B.

private
  1≤ : ∀ {x B} → 3 + x ≤ B → 1 ≤ B
  1≤ le = ℕ.≤-trans (s≤s z≤n) le

  -- Anything below B is below B^e for e ≥ 1.
  below : ∀ {a B} e → 1 ≤ B → a ≤ B → 1 ≤ e → a ≤ B ^ e
  below {a} {B} e 1≤B a≤ 1≤e = ℕ.≤-trans a≤
    (ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.^-identityʳ B))) (^-mono 1≤B 1≤e))

  -- L + 5 ≤ 6 B^k when L ≤ B^k.
  plus5 : ∀ {L B} k → 1 ≤ B → L ≤ B ^ k → L + 5 ≤ 6 * B ^ k
  plus5 {L} {B} k 1≤B L≤ = ℕ.≤-trans
    (ℕ.+-mono-≤ L≤ (ℕ.*-monoʳ-≤ 5 (^-pos {B = B} {k = k} 1≤B)))
    (ℕ.≤-reflexive (solve 1 (λ P → P :+ con 5 :* P := con 6 :* P) refl
                            (B ^ k)))

  -- (n + 1)² + n + 2 ≤ (n + 3)² ≤ B².
  square : ∀ n L B → L ≤ suc (n + 0) ^ 2 → 3 + n ≤ B →
           2 + (n + L) ≤ B * B
  square n L B L≤ le = ℕ.≤-trans
    (ℕ.+-monoʳ-≤ 2 (ℕ.+-monoʳ-≤ n (ℕ.≤-trans L≤ (ℕ.≤-reflexive
      (trans (sym (B*B (suc (n + 0))))
             (cong (λ y → suc y * suc y) (ℕ.+-identityʳ n)))))))
    (ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤m+n _ (3 * n + 6))
                          (ℕ.≤-reflexive (expand n)))
               (ℕ.*-mono-≤ le le))
    where
    expand : ∀ n → (2 + (n + suc n * suc n)) + (3 * n + 6) ≡
                   (3 + n) * (3 + n)
    expand = solve 1 (λ n → (con 2 :+ (n :+ (con 1 :+ n) :* (con 1 :+ n))) :+
                            (con 3 :* n :+ con 6) :=
                            (con 3 :+ n) :* (con 3 :+ n)) refl

  six : ∀ B → 6 * B ^ 3 * B * B ^ 2 ≡ 6 * B ^ 6
  six = solve 1 (λ B → con 6 :* B :^ 3 :* B :* B :^ 2 := con 6 :* B :^ 6)
                refl

  five : ∀ B → 6 * B ^ 2 * B * B ^ 2 ≡ 6 * B ^ 5
  five = solve 1 (λ B → con 6 :* B :^ 2 :* B :* B :^ 2 := con 6 :* B :^ 5)
                 refl


------------------------------------------------------------------------
-- The cost of the parts

-- The elimination, at a variable B ≥ n + m + 3: the canonicalisation
-- and the loop.

cost-gauss-at : (d : ℕ) (Q : Rep n m) (B : ℕ) → 3 + (n + m) ≤ B →
                cost (gaussᶜ d Q) ≤
                (length (terms Q) + 5) * B * B ^ d + 74 * B ^ (3 * d + 3)
cost-gauss-at {n} {m} d Q B le = ℕ.+-mono-≤ canon≤ loop≤
  where
  ts = value (canonᶜ d (terms Q))

  1≤B : 1 ≤ B
  1≤B = 1≤ le

  m≤B : m ≤ B
  m≤B = ℕ.≤-trans (ℕ.m≤n+m m n) (ℕ.≤-trans (ℕ.m≤n+m (n + m) 3) le)

  1N≤B : suc (n + m) ≤ B
  1N≤B = ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.≤-trans (ℕ.n≤1+n _) le)

  2N≤B : suc (suc (n + m)) ≤ B
  2N≤B = ℕ.≤-trans (ℕ.n≤1+n _) le

  canon≤ : cost (canonᶜ d (terms Q)) ≤ (length (terms Q) + 5) * B * B ^ d
  canon≤ = ℕ.≤-trans (cost-canonᶜ d (terms Q))
    (ℕ.*-mono-≤ (ℕ.*-monoʳ-≤ (length (terms Q) + 5) 2N≤B)
                (ℕ.^-monoˡ-≤ d 1N≤B))

  lents : length ts ≤ suc (suc (n + m)) ^ d
  lents = ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-canonᶜ d (terms Q))))
    (ℕ.≤-trans (canonical-length {n} {m} d ⟦ terms Q ⟧ˢ)
               (ℕ.^-monoˡ-≤ d (ℕ.n≤1+n _)))

  e≡ : suc (d + (2 + (d + d))) ≡ 3 * d + 3
  e≡ = solve 1 (λ d → con 1 :+ (d :+ (con 2 :+ (d :+ d))) :=
                      con 3 :* d :+ con 3) refl d

  spread : ∀ B Y → (68 * B + 6 * B) * Y ≡ 74 * (B * Y)
  spread = solve 2 (λ B Y → (con 68 :* B :+ con 6 :* B) :* Y :=
                            con 74 :* (B :* Y)) refl

  loop≤ : cost (elimᶜ d (rep ts (forms Q))) ≤ 74 * B ^ (3 * d + 3)
  loop≤ = ℕ.≤-trans (cost-elimᶜ d (rep ts (forms Q)) lents)
    (ℕ.≤-trans (elimBound-≤ n m d)
      (ℕ.≤-trans
        (ℕ.*-mono-≤ (ℕ.+-mono-≤ (ℕ.*-monoʳ-≤ 68 m≤B) (ℕ.*-monoʳ-≤ 6 1≤B))
                    (ℕ.^-monoˡ-≤ (d + (2 + (d + d))) le))
        (ℕ.≤-reflexive (trans (spread B (B ^ (d + (2 + (d + d)))))
                              (cong (74 *_) (cong (B ^_) e≡))))))

-- The normalisation of a list of at most B² terms: at most 285 B^11.

cost-normalise-at : (k : ℕ) (Q : Rep n m) (B : ℕ) → 3 + (n + m) ≤ B →
                    length (terms Q) ≤ B ^ 2 →
                    cost (normaliseᶜ 2 k Q) ≤ 285 * B ^ 11
cost-normalise-at {n} {m} k Q B le L≤ = ℕ.≤-trans (cost-normaliseᶜ 2 k Q)
  (ℕ.≤-trans (ℕ.+-mono-≤ can≤ nb≤)
    (ℕ.≤-reflexive (solve 1 (λ P → con 6 :* P :+ con 279 :* P :=
                                   con 285 :* P) refl (B ^ 11))))
  where
  1≤B : 1 ≤ B
  1≤B = 1≤ le

  1N≤B : suc (n + m) ≤ B
  1N≤B = ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.≤-trans (ℕ.n≤1+n _) le)

  2N≤B : suc (suc (n + m)) ≤ B
  2N≤B = ℕ.≤-trans (ℕ.n≤1+n _) le

  can≤ : (length (terms Q) + 5) * suc (suc (n + m)) * suc (n + m) ^ 2 ≤
         6 * B ^ 11
  can≤ = ℕ.≤-trans
    (ℕ.*-mono-≤ (ℕ.*-mono-≤ (plus5 2 1≤B L≤) 2N≤B) (ℕ.^-monoˡ-≤ 2 1N≤B))
    (ℕ.≤-trans (ℕ.≤-reflexive (five B))
               (ℕ.*-monoʳ-≤ 6 (^-mono 1≤B (ℕ.m≤m+n 5 6))))

  nb≤ : normBound n m 2 ≤ 279 * B ^ 11
  nb≤ = ℕ.*-monoʳ-≤ 279 (ℕ.^-monoˡ-≤ (3 * 2 + 5) le)

-- The verdict on a canonical normal form: at most 7 B^6, for any
-- B ≥ n + 3.

cost-verdict-small : (r : Normal n) → Canonical 2 (terms (nrep r)) →
                  (B : ℕ) → 3 + n ≤ B → cost (verdictᶜ r) ≤ 7 * B ^ 6
cost-verdict-small {n} (normal k zero Q) can B le = ℕ.≤-trans
  (s≤s (ℕ.≤-trans (cost-idTest-poly k Q)
    (ℕ.*-monoʳ-≤ 6 (ℕ.≤-trans
      (ℕ.^-monoˡ-≤ 3 (square n (length (terms Q)) B L≤ le))
      (ℕ.≤-reflexive (trans (cong (_^ 3) (B*B B)) (ℕ.^-*-assoc B 2 3)))))))
  (ℕ.≤-trans (ℕ.+-monoˡ-≤ (6 * B ^ 6) (^-pos {B = B} {k = 6} (1≤ le)))
             (ℕ.≤-reflexive (solve 1 (λ P → P :+ con 6 :* P := con 7 :* P)
                                    refl (B ^ 6))))
  where
  L≤ : length (terms Q) ≤ suc (n + 0) ^ 2
  L≤ = subst (λ ts → length ts ≤ suc (n + 0) ^ 2) (sym can)
             (canonical-length {n = n} {m = 0} 2 ⟦ terms Q ⟧ˢ)
cost-verdict-small (normal k (suc m) Q) can B le =
  ℕ.≤-trans (^-pos {B = B} {k = 6} (1≤ le)) (ℕ.m≤n*m (B ^ 6) 7)

-- After the elimination: at most 293 B^11, for a reified restriction
-- with m ≤ B − n − 3 path variables and at most B² terms.

cost-conclude-at : (k : ℕ) (Q : Rep n m) (B : ℕ) → 3 + (n + m) ≤ B →
                   length (terms Q) ≤ B ^ 2 →
                   cost (concludeᶜ k (reifies Q)) ≤ 293 * B ^ 11
cost-conclude-at {n} {m} k Q B le L≤ = ℕ.≤-trans
  (s≤s (ℕ.+-mono-≤ (cost-normalise-at k Q B le L≤) ver≤))
  (ℕ.≤-trans (ℕ.+-monoˡ-≤ (285 * B ^ 11 + 7 * B ^ 11)
                          (^-pos {B = B} {k = 11} (1≤ le)))
    (ℕ.≤-reflexive (solve 1 (λ P → P :+ (con 285 :* P :+ con 7 :* P) :=
                                   con 293 :* P) refl (B ^ 11))))
  where
  n3≤B : 3 + n ≤ B
  n3≤B = ℕ.≤-trans (ℕ.+-monoʳ-≤ 3 (ℕ.m≤m+n n m)) le

  ver≤ : cost (verdictᶜ (value (normaliseᶜ 2 k Q))) ≤ 7 * B ^ 11
  ver≤ = ℕ.≤-trans
    (cost-verdict-small (value (normaliseᶜ 2 k Q)) (normalise-canonical 2 k Q)
                     B n3≤B)
    (ℕ.*-monoʳ-≤ 7 (^-mono (1≤ le) (ℕ.m≤m+n 6 5)))


------------------------------------------------------------------------
-- The cost of the decision

-- The pipeline: 2 |C| to count, 23 B^4 to interpret, 6 B^6 + 74 B^9 to
-- eliminate, 293 B^11 to conclude; at most 398 B^11 for any
-- B ≥ n + |C| + 3.

cost-pipelineᴳ-at : (C : Circuit n) → level C ≤ 2 → (B : ℕ) →
                    3 + (n + length C) ≤ B →
                    cost (pipelineᴳᶜ C) ≤ 398 * B ^ 11
cost-pipelineᴳ-at {n} C lv B le = ℕ.≤-trans
  (ℕ.+-mono-≤ c₁ (ℕ.+-mono-≤ c₂ (ℕ.+-mono-≤ c₃ c₄)))
  (ℕ.≤-reflexive (solve 1 (λ P → con 2 :* P :+ (con 23 :* P :+
                                   (con 80 :* P :+ con 293 :* P)) :=
                                 con 398 :* P) refl (B ^ 11)))
  where
  kᴴ = value (countHᴷᶜ C)
  p  = value (interpKᶜ C)
  Q  = proj₂ p
  o  = value (gaussᶜ 2 Q)

  1≤B : 1 ≤ B
  1≤B = 1≤ le

  ℓ≤B : length C ≤ B
  ℓ≤B = ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤n+m (length C) n)
                             (ℕ.m≤n+m (n + length C) 3)) le

  X≤B : suc (n + length C) ≤ B
  X≤B = ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.≤-trans (ℕ.n≤1+n _) le)

  m≤ : 3 + (n + proj₁ p) ≤ B
  m≤ = ℕ.≤-trans (ℕ.+-monoʳ-≤ 3 (ℕ.+-monoʳ-≤ n (interpK-paths≤ C))) le

  c₁ : cost (countHᴷᶜ C) ≤ 2 * B ^ 11
  c₁ = ℕ.≤-trans (cost-countHᴷᶜ C)
    (ℕ.*-monoʳ-≤ 2 (below 11 1≤B ℓ≤B (s≤s z≤n)))

  e≤4 : suc (suc (1 ⊔ level C)) ≤ 4
  e≤4 = s≤s (s≤s (one⊔ {C = C} lv))

  c₂ : cost (interpKᶜ C) ≤ 23 * B ^ 11
  c₂ = ℕ.≤-trans (cost-interpKᶜ C) (ℕ.*-monoʳ-≤ 23
    (ℕ.≤-trans (ℕ.^-monoʳ-≤ (suc (n + length C)) e≤4)
      (ℕ.≤-trans (ℕ.^-monoˡ-≤ 4 X≤B) (^-mono 1≤B (ℕ.m≤m+n 4 7)))))

  -- The interpreter's terms: at most |C| (n + |C| + 1)^2 ≤ B³.
  L≤ : length (terms Q) ≤ B ^ 3
  L≤ = ℕ.≤-trans (interpK-length C)
    (ℕ.*-mono-≤ ℓ≤B (ℕ.≤-trans (ℕ.^-monoʳ-≤ (suc (n + length C))
                                             (one⊔ {C = C} lv))
                               (ℕ.^-monoˡ-≤ 2 X≤B)))

  c₃ : cost (gaussᶜ 2 Q) ≤ 80 * B ^ 11
  c₃ = ℕ.≤-trans (cost-gauss-at 2 Q B m≤)
    (ℕ.≤-trans (ℕ.+-mono-≤ g₁ g₂)
      (ℕ.≤-reflexive (solve 1 (λ P → con 6 :* P :+ con 74 :* P :=
                                     con 80 :* P) refl (B ^ 11))))
    where
    g₁ : (length (terms Q) + 5) * B * B ^ 2 ≤ 6 * B ^ 11
    g₁ = ℕ.≤-trans (ℕ.*-monoˡ-≤ (B ^ 2) (ℕ.*-monoˡ-≤ B (plus5 3 1≤B L≤)))
      (ℕ.≤-trans (ℕ.≤-reflexive (six B))
                 (ℕ.*-monoʳ-≤ 6 (^-mono 1≤B (ℕ.m≤m+n 6 5))))

    g₂ : 74 * B ^ (3 * 2 + 3) ≤ 74 * B ^ 11
    g₂ = ℕ.*-monoʳ-≤ 74 (^-mono 1≤B (ℕ.m≤m+n 9 2))

  c₄ : cost (concludeᶜ kᴴ o) ≤ 293 * B ^ 11
  c₄ = by o refl
    where
    by : (o′ : Outcome n) → o ≡ o′ → cost (concludeᶜ kᴴ o′) ≤ 293 * B ^ 11
    by (refutes x) _ =
      ℕ.≤-trans (^-pos {B = B} {k = 11} 1≤B) (ℕ.m≤n*m (B ^ 11) 293)
    by (reifies Q′) e = cost-conclude-at kᴴ Q′ B
      (ℕ.≤-trans (ℕ.+-monoʳ-≤ 3 (ℕ.+-monoʳ-≤ n (proj₁ sh))) m≤)
      (ℕ.≤-trans (proj₂ sh) (ℕ.^-monoˡ-≤ 2 (ℕ.≤-trans (ℕ.n≤1+n _) m≤)))
      where
      sh = gaussᶜ-shape 2 Q e

-- The decision.  (The case split on the circuit is made below the
-- variable B, so that no bound is ever read at a circuit of a given
-- shape.)

cost-decideᴳ-at : (C : Circuit n) → level C ≤ 2 → (B : ℕ) →
                  3 + (n + length C) ≤ B → cost (decideᴳᶜ C) ≤ 398 * B ^ 11
cost-decideᴳ-at []      lv B le =
  ℕ.≤-trans (^-pos {B = B} {k = 11} (1≤ le)) (ℕ.m≤n*m (B ^ 11) 398)
cost-decideᴳ-at (g ∷ C) lv B le = cost-pipelineᴳ-at (g ∷ C) lv B le

cost-decideᴳᶜ : (C : Circuit n) → level C ≤ 2 →
                cost (decideᴳᶜ C) ≤ decideᴳBound n (length C)
cost-decideᴳᶜ {n} C lv = subst (cost (decideᴳᶜ C) ≤_)
  (sym (decideᴳBound-def n (length C)))
  (cost-decideᴳ-at C lv (3 + (n + length C)) ℕ.≤-refl)

-- In the volume n · |C|: a gate names a wire, so n ≥ 1 when |C| ≥ 1,
-- and then n + |C| ≤ 2 n |C|.

private
  gate-wire : Gate n → 1 ≤ n
  gate-wire (K.H w)        = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)
  gate-wire (K.CNOT c t _) = ℕ.≤-trans (s≤s z≤n) (toℕ<n c)
  gate-wire (K.R k w)      = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)
  gate-wire (K.R† k w)     = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)

  volume-at : (C : Circuit n) → level C ≤ 2 → (v : ℕ) → v ≡ n * length C →
              cost (decideᴳᶜ C) ≤ 398 * (3 + 2 * v) ^ 11
  volume-at []      lv v eq =
    ℕ.≤-trans (^-pos {B = 3 + 2 * v} {k = 11} (s≤s z≤n))
              (ℕ.m≤n*m ((3 + 2 * v) ^ 11) 398)
  volume-at {n} (g ∷ C) lv v eq = cost-pipelineᴳ-at (g ∷ C) lv (3 + 2 * v)
    (ℕ.+-monoʳ-≤ 3 (ℕ.≤-trans
      (volume-≤ n (length (g ∷ C)) (gate-wire g) (s≤s z≤n))
      (ℕ.≤-reflexive (cong (2 *_) (sym eq)))))

cost-decideᴳ-volume : (C : Circuit n) → level C ≤ 2 →
                      cost (decideᴳᶜ C) ≤ volumeᴳBound (n * length C)
cost-decideᴳ-volume {n} C lv = subst (cost (decideᴳᶜ C) ≤_)
  (sym (volumeᴳBound-def (n * length C)))
  (volume-at C lv (n * length C) refl)


------------------------------------------------------------------------
-- Corollary 4.4 in polynomial time, by Gaussian elimination

-- For a Clifford circuit over {H, CNOT, R_k, R_k†}, whether ⟦ C ⟧ is
-- the identity is decided by decideᴳᶜ, at a cost polynomial in n + |C|
-- and in the volume n · |C|.

record Corollary-4-4ᴳ {n : ℕ} (C : Circuit n) : Set where
  field
    decides    : value (decideᴳᶜ C) ≡ true ⇔ ⟦ C ⟧ ≋ idPS
    polynomial : cost (decideᴳᶜ C) ≤ decideᴳBound n (length C)
    volume     : cost (decideᴳᶜ C) ≤ volumeᴳBound (n * length C)

corollary-4-4-polytime-gauss : (C : Circuit n) → level C ≤ 2 →
                               Corollary-4-4ᴳ C
corollary-4-4-polytime-gauss C lv = record
  { decides    = decideᴳ-correct C lv
  ; polynomial = cost-decideᴳᶜ C lv
  ; volume     = cost-decideᴳ-volume C lv
  }


------------------------------------------------------------------------
-- The miter, in the monad

-- C† gate by gate: the inverse of the rest, then the gate inverted.

daggerᴷᶜ : Circuit n → Cost (Circuit n)
daggerᴷᶜ []      = pure []
daggerᴷᶜ (g ∷ C) = do
  tick
  D ← daggerᴷᶜ C
  appendᶜ D (inv g ∷ [])

value-daggerᴷᶜ : (C : Circuit n) → value (daggerᴷᶜ C) ≡ C †
value-daggerᴷᶜ []      = refl
value-daggerᴷᶜ (g ∷ C) =
  trans (value-appendᶜ (value (daggerᴷᶜ C)) (inv g ∷ []))
        (cong (λ D → D ++ inv g ∷ []) (value-daggerᴷᶜ C))

-- Inverting keeps the number of gates.

length-†ᴷ : (C : Circuit n) → length (C †) ≡ length C
length-†ᴷ []      = refl
length-†ᴷ (g ∷ C) = trans (List.length-++ (C †))
  (trans (cong (_+ 1) (length-†ᴷ C)) (ℕ.+-comm (length C) 1))

cost-daggerᴷᶜ : (C : Circuit n) →
                cost (daggerᴷᶜ C) ≤ length C * suc (length C)
cost-daggerᴷᶜ []      = z≤n
cost-daggerᴷᶜ (g ∷ C) = s≤s (ℕ.≤-trans
  (ℕ.+-mono-≤ (cost-daggerᴷᶜ C) a≤)
  (ℕ.≤-trans (ℕ.+-mono-≤ (ℕ.*-monoʳ-≤ (length C) (ℕ.n≤1+n (suc (length C))))
                         (ℕ.n≤1+n (length C)))
             (ℕ.≤-reflexive (ℕ.+-comm (length C * suc (suc (length C)))
                                      (suc (length C))))))
  where
  a≤ : cost (appendᶜ (value (daggerᴷᶜ C)) (inv g ∷ [])) ≤ length C
  a≤ = ℕ.≤-trans (cost-appendᶜ (value (daggerᴷᶜ C)) (inv g ∷ []))
    (ℕ.≤-reflexive (trans (cong length (value-daggerᴷᶜ C)) (length-†ᴷ C)))

-- The miter C₁ ++ C₂†.

miterᴷᶜ : Circuit n → Circuit n → Cost (Circuit n)
miterᴷᶜ C₁ C₂ = do
  D ← daggerᴷᶜ C₂
  appendᶜ C₁ D

value-miterᴷᶜ : (C₁ C₂ : Circuit n) → value (miterᴷᶜ C₁ C₂) ≡ C₁ ++ C₂ †
value-miterᴷᶜ C₁ C₂ = trans (value-appendᶜ C₁ (value (daggerᴷᶜ C₂)))
                            (cong (C₁ ++_) (value-daggerᴷᶜ C₂))

cost-miterᴷᶜ : (C₁ C₂ : Circuit n) →
               cost (miterᴷᶜ C₁ C₂) ≤
               length C₂ * suc (length C₂) + length C₁
cost-miterᴷᶜ C₁ C₂ =
  ℕ.+-mono-≤ (cost-daggerᴷᶜ C₂) (cost-appendᶜ C₁ (value (daggerᴷᶜ C₂)))

length-miterᴷ : (C₁ C₂ : Circuit n) →
                length (value (miterᴷᶜ C₁ C₂)) ≡ length C₁ + length C₂
length-miterᴷ C₁ C₂ = trans (cong length (value-miterᴷᶜ C₁ C₂))
  (trans (List.length-++ C₁) (cong (length C₁ +_) (length-†ᴷ C₂)))

-- The miter of two Clifford circuits is Clifford.

level-miterᴷᶜ : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 → level C₂ ≤ 2 →
                level (value (miterᴷᶜ C₁ C₂)) ≤ 2
level-miterᴷᶜ C₁ C₂ lv₁ lv₂ = subst (λ E → level E ≤ 2)
  (sym (value-miterᴷᶜ C₁ C₂)) (level-miter C₁ C₂ lv₁ lv₂)


------------------------------------------------------------------------
-- Equivalence of two Clifford circuits

equivᴳᶜ : Circuit n → Circuit n → Cost Bool
equivᴳᶜ C₁ C₂ = miterᴷᶜ C₁ C₂ >>= decideᴳᶜ

equivᴳ-correct : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 → level C₂ ≤ 2 →
                 (value (equivᴳᶜ C₁ C₂) ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equivᴳ-correct {n} C₁ C₂ lv₁ lv₂ =
  ⇔-trans (decideᴳ-correct (value (miterᴷᶜ C₁ C₂))
                           (level-miterᴷᶜ C₁ C₂ lv₁ lv₂))
    (⇔-trans (mk⇔ (subst P eq) (subst P (sym eq))) (⇔-sym (miter C₁ C₂)))
  where
  P : Circuit n → Set
  P D = ⟦ D ⟧ ≋ idPS

  eq = value-miterᴷᶜ C₁ C₂

equivᴳ? : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 → level C₂ ≤ 2 →
          Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equivᴳ? C₁ C₂ lv₁ lv₂ = by (value (equivᴳᶜ C₁ C₂)) refl
  where
  by : ∀ b → value (equivᴳᶜ C₁ C₂) ≡ b → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
  by true  e = yes (Equivalence.to (equivᴳ-correct C₁ C₂ lv₁ lv₂) e)
  by false e = no (λ h → false≢true
    (trans (sym e) (Equivalence.from (equivᴳ-correct C₁ C₂ lv₁ lv₂) h)))
    where
    false≢true : false ≡ true → ⊥
    false≢true ()

-- At most 400 (n + |C₁| + |C₂| + 3)^11.

cost-equivᴳ-at : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 → level C₂ ≤ 2 →
                 (B : ℕ) → 3 + (n + (length C₁ + length C₂)) ≤ B →
                 cost (equivᴳᶜ C₁ C₂) ≤ 400 * B ^ 11
cost-equivᴳ-at {n} C₁ C₂ lv₁ lv₂ B le = ℕ.≤-trans
  (ℕ.+-mono-≤ (ℕ.≤-trans (cost-miterᴷᶜ C₁ C₂) (ℕ.+-mono-≤ bb≤ a≤))
    (cost-decideᴳ-at D (level-miterᴷᶜ C₁ C₂ lv₁ lv₂) B lenD≤))
  (ℕ.≤-reflexive (solve 1 (λ P → (P :+ P) :+ con 398 :* P := con 400 :* P)
                         refl (B ^ 11)))
  where
  D = value (miterᴷᶜ C₁ C₂)

  1≤B : 1 ≤ B
  1≤B = 1≤ le

  ab≤B : length C₁ + length C₂ ≤ B
  ab≤B = ℕ.≤-trans (ℕ.m≤n+m _ n) (ℕ.≤-trans (ℕ.m≤n+m _ 3) le)

  lenD≤ : 3 + (n + length D) ≤ B
  lenD≤ = subst (λ ℓ → 3 + (n + ℓ) ≤ B) (sym (length-miterᴷ C₁ C₂)) le

  b≤B : length C₂ ≤ B
  b≤B = ℕ.≤-trans (ℕ.m≤n+m (length C₂) (length C₁)) ab≤B

  sb≤B : suc (length C₂) ≤ B
  sb≤B = ℕ.≤-trans (s≤s (ℕ.≤-trans (ℕ.m≤n+m (length C₂) (length C₁))
                                   (ℕ.m≤n+m _ n)))
                   (ℕ.≤-trans (ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.n≤1+n _)) le)

  bb≤ : length C₂ * suc (length C₂) ≤ B ^ 11
  bb≤ = ℕ.≤-trans (ℕ.*-mono-≤ b≤B sb≤B)
    (ℕ.≤-trans (ℕ.≤-reflexive (B*B B)) (^-mono 1≤B (ℕ.m≤m+n 2 9)))

  a≤ : length C₁ ≤ B ^ 11
  a≤ = below 11 1≤B (ℕ.≤-trans (ℕ.m≤m+n (length C₁) (length C₂)) ab≤B)
             (s≤s z≤n)

cost-equivᴳᶜ : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 → level C₂ ≤ 2 →
               cost (equivᴳᶜ C₁ C₂) ≤ equivᴳBound n (length C₁) (length C₂)
cost-equivᴳᶜ {n} C₁ C₂ lv₁ lv₂ = subst (cost (equivᴳᶜ C₁ C₂) ≤_)
  (sym (equivᴳBound-def n (length C₁) (length C₂)))
  (cost-equivᴳ-at C₁ C₂ lv₁ lv₂ (3 + (n + (length C₁ + length C₂)))
                  ℕ.≤-refl)

-- Equivalence of Clifford circuits over {H, CNOT, R_k, R_k†} in
-- polynomial time, by Gaussian elimination at the miter.

record PolyEquivalenceᴳ {n : ℕ} (C₁ C₂ : Circuit n) : Set where
  field
    decides    : value (equivᴳᶜ C₁ C₂) ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧
    polynomial : cost (equivᴳᶜ C₁ C₂) ≤ equivᴳBound n (length C₁) (length C₂)

equivalence-polytime-gauss : (C₁ C₂ : Circuit n) → level C₁ ≤ 2 →
                             level C₂ ≤ 2 → PolyEquivalenceᴳ C₁ C₂
equivalence-polytime-gauss C₁ C₂ lv₁ lv₂ = record
  { decides    = equivᴳ-correct C₁ C₂ lv₁ lv₂
  ; polynomial = cost-equivᴳᶜ C₁ C₂ lv₁ lv₂
  }
