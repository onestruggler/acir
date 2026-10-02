------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary 4.4 in polynomial time, in the cost model, and the
-- equivalence of two Clifford circuits (Amy, QPL 2018)
--
-- Corollary 4.4 reads: "If C is a Clifford-group quantum circuit, then
-- ⟦C⟧ ≡ |x⟩ ↦ |x⟩ can be decided in time polynomial in the space-time
-- volume of C", and the abstract calls the result "a polynomial-time
-- decision procedure for checking the equivalence of Clifford group
-- circuits".  Here both are programs in the monad of PathSum.Cost,
-- with their value proved correct against ≋ and their cost bounded by
-- an explicit polynomial.
--
-- Scope: circuits over {H, S, CZ}, which generate the Clifford group.
-- The paper's own gate set {H, CNOT, R_k} at level ≤ 2 is
-- PathSum.Cost.Gauss.Corollary, by Gaussian elimination in the monad.
--
-- The decision, for a circuit C over {H, S, CZ} (decideᶜ):
--
--  1. count the Hadamards, the normalisation of ⟦ C ⟧ᴿ (countHᶜ);
--  2. interpret C into a sparse representation of its isometry
--     restriction ⟦ C ⟧ᴿ (PathSum.Cost.Restriction.interpᴿᶜ): |C|
--     terms, at most |C| path variables, every path variable internal
--     and the phase of order 2 (PathSum.Circuit);
--  3. normalise at order 2 (PathSum.Cost.Normalise.normaliseᶜ): the
--     result comes with a chain ⟦ C ⟧ᴿ ⟶ᵍ* ξ′ to a path-sum it
--     represents, and no rule of PathSum.Anywhere applies to ξ′ at any
--     variable (nor, by PathSum.Cost.Irreducible, any rule of figure
--     2);
--  4. read the verdict (verdictᶜ).  If a path variable is left, the
--     answer is no: ξ′ is irreducible, its path variables are internal
--     (every step keeps them so) and its phase has order 2, so lemma
--     4.3's progress (PathSum.Clifford.progress) cannot give a step,
--     and gives instead that ξ′ is not the identity -- by lemma 4.2,
--     or because the rule the phase calls for would need more
--     normalisation than ξ′ has.  If none is left, the final test of
--     PathSum.Cost.Identity decides whether ξ′ is the identity
--     (PathSum.Syntactic).
--
-- Proposition 3.1 along the chain (PathSum.Anywhere.Sound) and lemma
-- 4.1 at the circuit (PathSum.Corollary.lemma-4-1-circuit) carry the
-- answer back to ⟦ C ⟧: decide-correct says that the value is true
-- exactly when ⟦ C ⟧ ≋ idPS.  The cost is at most
-- 313 (n + |C| + 3)^12 (cost-decideᶜ), dominated by the normalisation;
-- the bound is an upper bound and is not tight.  In the volume n · |C|
-- it is at most 313 (2 n |C| + 3)^12 for every circuit
-- (cost-decide-volume): a gate names a wire, so n ≥ 1 whenever
-- |C| ≥ 1, and the empty circuit, whose path-sum is the identity, is
-- answered at once -- without that case the pipeline would still cost
-- a polynomial in n (about n³: interpreting, canonicalising and
-- testing the n wires) at volume 0, which no function of the volume
-- bounds.  corollary-4-4-polytime packages the three.
--
-- Equivalence (equivᶜ): the miter C₁ ++ C₂† is built in the monad
-- (daggerᶜ, miterᶜ; S† is S³ as in PathSum.Adjoint, so |C₂†| ≤ 3 |C₂|)
-- and decided.  equiv-correct says the value is true exactly when
-- ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ (PathSum.Miter.miter), and cost-equivᶜ bounds the
-- cost by 315 (n + 3 (|C₁| + |C₂|) + 3)^12.  Equivalence is
-- definition 2.3's: equality of the operators, global phase included.
--
-- decide? and equiv? turn the Boolean into a decision procedure in the
-- sense of Relation.Nullary: their Dec is computed by the program.
--
-- The bounds decideBound, volumeBound and equivBound are opaque, with
-- their defining equations exported (decideBound-def, ...), and every
-- cost lemma is proved at a variable B bounding n + |C| + 3 (the -at
-- lemmas) before being instantiated.  This is a matter of checking
-- time only: Agda, asked to compare two spellings of 313 (n + |C| + 3)^12,
-- unfolds the power into a unary number.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.  The normalisation counter, the number of path
-- variables and the Hadamard count are numbers read or changed in at
-- most one step each (the normaliser's case on the number of path
-- variables is charged nothing, absorbed by each round's charged work).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Cost.Corollary (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using
  (zero; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
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

open import PathSum.Adjoint M using (_†; inv)
open import PathSum.Anywhere M using (plain)
open import PathSum.Anywhere.Sound M₀ using (⟶ᵍ*-sound)
open import PathSum.Base using (PathSum; idPS; Internal)
open import PathSum.Circuit M using
  (Gate; H; S; CZ; Circuit; norm; paths; ⟦_⟧; ⟦_⟧ᴿ; ⟦⟧ᴿ-Internal; ⟦⟧ᴿ-Ord≤)
open import PathSum.Corollary M₀ using (lemma-4-1-circuit)
open import PathSum.Cost
open import PathSum.Cost.Bound using (^-mono; ^-pos; B*B)
open import PathSum.Cost.Canon M using
  (Canonical; canonical-length; canonᶜ-Canonical)
open import PathSum.Cost.Identity M using
  (idTestᶜ; idTest-correct; cost-idTest-poly)
open import PathSum.Cost.Normalise M using
  (Normal; normal; nk; nm; nrep; normᶜ; normNext; normaliseᶜ; Normalised;
   reduct; chain; reduct-represents; irreducible; reduct-Ord≤;
   normalise-sound; normalise-Internal; cost-normalise-poly)
open import PathSum.Cost.Restriction M using
  (countHᶜ; value-countHᶜ; cost-countHᶜ; interpᴿᶜ; interpᴿ-denotes;
   interpᴿ-length; interpᴿ-paths≤; cost-interpᴿᶜ)
open import PathSum.Cost.Search M using (searchᶜ; search-canonical)
open import PathSum.Denotation M₀ using (_≋_; ≋-refl; ≋-sym; ≋-trans; semantics)
open import PathSum.Miter M₀ using (miter)
open import PathSum.Size.Interpreter M using (Denotes; denotes)
open import PathSum.Size.Sparse M using
  (Rep; rep; terms; forms; Represents; volume-≤; ⟦_⟧ˢ)
open import PathSum.Syntactic M₀ using (id⇔syntactic)

import Data.List.Properties as List
import Data.Nat.Properties as ℕ
import PathSum.Clifford

private
  module Cliff = PathSum.Clifford M₀ semantics

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    n d k m : ℕ


------------------------------------------------------------------------
-- The final test against ≋

-- A representation without path variables passes the final test
-- exactly when every path-sum it stands for is the identity.

idTest-≋ : (ψ : PathSum n k 0) (R : Rep n 0) → Represents ψ R →
           (value (idTestᶜ k R) ≡ true ⇔ ψ ≋ idPS)
idTest-≋ ψ R rp = ⇔-trans (idTest-correct ψ R rp) (⇔-sym (id⇔syntactic ψ))


------------------------------------------------------------------------
-- The verdict on a normal form

-- A path variable left: no.  None left: the final test.  Reading the
-- number of path variables is one step.

verdictᶜ : Normal n → Cost Bool
verdictᶜ (normal k zero    R) = tick >> idTestᶜ k R
verdictᶜ (normal k (suc m) R) = step false

-- On the result of the normalisation of a path-sum with internal path
-- variables and a phase of order 2, the verdict is correct.

verdict-correct : {ξ : PathSum n k m} (r : Normal n) → Normalised 2 ξ r →
                  Internal ξ → (value (verdictᶜ r) ≡ true ⇔ ξ ≋ idPS)
verdict-correct {ξ = ξ} (normal k′ zero R′) N int =
  ⇔-trans (idTest-≋ (reduct N) R′ (reduct-represents N))
    (mk⇔ (λ e → ≋-trans {ξ = ξ} {ζ = reduct N} {χ = idPS} ξ≋ e)
         (λ e → ≋-trans {ξ = reduct N} {ζ = ξ} {χ = idPS}
                  (≋-sym {ξ = ξ} {ζ = reduct N} ξ≋) e))
  where
  ξ≋ : ξ ≋ reduct N
  ξ≋ = ⟶ᵍ*-sound (chain N)
verdict-correct {ξ = ξ} (normal k′ (suc m′) R′) N int =
  mk⇔ (λ ()) (λ ξ≋id → ⊥-elim (refute
    (≋-trans {ξ = reduct N} {ζ = ξ} {χ = idPS}
      (≋-sym {ξ = ξ} {ζ = reduct N} (⟶ᵍ*-sound (chain N))) ξ≋id)))
  where
  -- Lemma 4.3's progress cannot step an irreducible path-sum, so it
  -- refutes it.
  by-progress : Cliff.Progress (reduct N) → ¬ (reduct N ≋ idPS)
  by-progress (Cliff.reduces ξ′ s _ _) = ⊥-elim (irreducible N (plain s))
  by-progress (Cliff.not-id ¬id)       = ¬id

  refute : ¬ (reduct N ≋ idPS)
  refute = by-progress
    (Cliff.progress (reduct N) (normalise-Internal N int) (reduct-Ord≤ N))

-- The normalisation's result is canonical, whatever it started from.

private
  norm-canonical : (d k : ℕ) (R : Rep n m) → Canonical d (terms R) →
                   Canonical d (terms (nrep (value (normᶜ d k R))))
  norm-canonical {m = zero}  d k R can = can
  norm-canonical {n = n} {m = suc m} d k R can =
    next (value (searchᶜ d k R)) refl
    where
    next : (r : Maybe (ℕ × Rep n m)) → value (searchᶜ d k R) ≡ r →
           Canonical d (terms (nrep (value (normNext d k R r))))
    next nothing          e = can
    next (just (k′ , R′)) e =
      norm-canonical d k′ R′ (search-canonical d k R e)

normalise-canonical : (d k : ℕ) (R : Rep n m) →
                      Canonical d (terms (nrep (value (normaliseᶜ d k R))))
normalise-canonical d k R =
  norm-canonical d k _ (canonᶜ-Canonical d (terms R))


------------------------------------------------------------------------
-- The decision

-- The pipeline: count, interpret, normalise, read the verdict.

pipelineᶜ : Circuit n → Cost Bool
pipelineᶜ C = do
  k ← countHᶜ C
  p ← interpᴿᶜ C
  r ← normaliseᶜ 2 k (proj₂ p)
  verdictᶜ r

-- The empty circuit is the identity; any other goes through the
-- pipeline.

decideᶜ : Circuit n → Cost Bool
decideᶜ []      = step true
decideᶜ (g ∷ C) = pipelineᶜ (g ∷ C)

-- The empty circuit's path-sum is the identity, syntactically.  (Stated
-- as an equation of path-sums, so that no amplitude is compared.)

empty-id : ⟦ [] ⟧ ≡ idPS {n}
empty-id = refl

-- The pipeline answers true exactly for the identity circuits.

pipeline-correct : (C : Circuit n) →
                   (value (pipelineᶜ C) ≡ true ⇔ ⟦ C ⟧ ≋ idPS)
pipeline-correct {n} C = ⇔-trans
  (at (value (countHᶜ C)) (value-countHᶜ C) (value (interpᴿᶜ C))
      (interpᴿ-denotes C))
  (⇔-sym (lemma-4-1-circuit C))
  where
  at : (k : ℕ) → k ≡ norm C → (p : ∃ (Rep n)) → Denotes ⟦ C ⟧ᴿ p →
       (value (verdictᶜ (value (normaliseᶜ 2 k (proj₂ p)))) ≡ true ⇔
        ⟦ C ⟧ᴿ ≋ idPS)
  at .(norm C) refl .(paths C , R) (denotes R rp) =
    verdict-correct (value (normaliseᶜ 2 (norm C) R))
      (normalise-sound 2 (s≤s (s≤s z≤n)) ⟦ C ⟧ᴿ R rp (⟦⟧ᴿ-Ord≤ C))
      (⟦⟧ᴿ-Internal C)

decide-correct : (C : Circuit n) →
                 (value (decideᶜ C) ≡ true ⇔ ⟦ C ⟧ ≋ idPS)
decide-correct {n} []  = mk⇔
  (λ _ → subst (λ ξ → ξ ≋ idPS) (sym (empty-id {n})) (≋-refl {ξ = idPS}))
  (λ _ → refl)
decide-correct (g ∷ C) = pipeline-correct (g ∷ C)

-- As a decision procedure: the Dec is the program's answer.

decide? : (C : Circuit n) → Dec (⟦ C ⟧ ≋ idPS)
decide? C = by (value (decideᶜ C)) refl
  where
  by : ∀ b → value (decideᶜ C) ≡ b → Dec (⟦ C ⟧ ≋ idPS)
  by true  e = yes (Equivalence.to (decide-correct C) e)
  by false e = no (λ h → false≢true
    (trans (sym e) (Equivalence.from (decide-correct C) h)))
    where
    false≢true : false ≡ true → ⊥
    false≢true ()


------------------------------------------------------------------------
-- The explicit polynomials

-- They are opaque: Agda never unfolds a power of a numeral-headed
-- base, which it would do into unary numbers.  Their defining
-- equations are decideBound-def, volumeBound-def and equivBound-def.

opaque
  decideBound : ℕ → ℕ → ℕ
  decideBound n ℓ = 313 * (3 + (n + ℓ)) ^ 12

  decideBound-def : ∀ n ℓ → decideBound n ℓ ≡ 313 * (3 + (n + ℓ)) ^ 12
  decideBound-def n ℓ = refl

  volumeBound : ℕ → ℕ
  volumeBound v = 313 * (3 + 2 * v) ^ 12

  volumeBound-def : ∀ v → volumeBound v ≡ 313 * (3 + 2 * v) ^ 12
  volumeBound-def v = refl

  equivBound : ℕ → ℕ → ℕ → ℕ
  equivBound n a b = 315 * (3 + (n + 3 * (a + b))) ^ 12

  equivBound-def : ∀ n a b →
                   equivBound n a b ≡ 315 * (3 + (n + 3 * (a + b))) ^ 12
  equivBound-def n a b = refl

-- The bounds below are proved at a variable B standing for n + |C| + 3,
-- or anything larger.  (Agda must never compare two spellings of a
-- power of a numeral-headed base: it would unfold them into unary
-- numbers.)

private
  1≤ : ∀ {x B} → 3 + x ≤ B → 1 ≤ B
  1≤ le = ℕ.≤-trans (s≤s z≤n) le

  -- Anything below B is below B^e for e ≥ 1.
  below : ∀ {a B} e → 1 ≤ B → a ≤ B → 1 ≤ e → a ≤ B ^ e
  below {a} {B} e 1≤B a≤ 1≤e = ℕ.≤-trans a≤
    (ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.^-identityʳ B))) (^-mono 1≤B 1≤e))

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

-- The bounds are at least 1, and grow with the base.

one≤decide : ∀ n ℓ → 1 ≤ decideBound n ℓ
one≤decide n ℓ = subst (1 ≤_) (sym (decideBound-def n ℓ)) (ℕ.≤-trans
  (^-pos {B = 3 + (n + ℓ)} {k = 12} (s≤s z≤n))
  (ℕ.m≤n*m ((3 + (n + ℓ)) ^ 12) 313))

one≤volume : ∀ v → 1 ≤ volumeBound v
one≤volume v = subst (1 ≤_) (sym (volumeBound-def v)) (ℕ.≤-trans
  (^-pos {B = 3 + 2 * v} {k = 12} (s≤s z≤n))
  (ℕ.m≤n*m ((3 + 2 * v) ^ 12) 313))

decide≤ : ∀ n ℓ B → 3 + (n + ℓ) ≤ B → decideBound n ℓ ≤ 313 * B ^ 12
decide≤ n ℓ B le = subst (λ z → z ≤ 313 * B ^ 12) (sym (decideBound-def n ℓ))
  (ℕ.*-monoʳ-≤ 313 (ℕ.^-monoˡ-≤ 12 le))


------------------------------------------------------------------------
-- The cost of the verdict

-- On a canonical normal form: at most 7 B^12, for any B ≥ n + 3.

cost-verdict-at : (r : Normal n) → Canonical 2 (terms (nrep r)) →
                  (B : ℕ) → 3 + n ≤ B → cost (verdictᶜ r) ≤ 7 * B ^ 12
cost-verdict-at {n} (normal k zero R) can B le = ℕ.≤-trans
  (s≤s (ℕ.≤-trans (cost-idTest-poly k R)
    (ℕ.*-monoʳ-≤ 6 (ℕ.≤-trans
      (ℕ.^-monoˡ-≤ 3 (square n (length (terms R)) B L≤ le))
      (ℕ.≤-trans (ℕ.≤-reflexive (trans (cong (_^ 3) (B*B B))
                                       (ℕ.^-*-assoc B 2 3)))
                 (^-mono (1≤ le) (ℕ.m≤m+n 6 6)))))))
  (ℕ.≤-trans (ℕ.+-monoˡ-≤ (6 * B ^ 12) (^-pos {B = B} {k = 12} (1≤ le)))
             (ℕ.≤-reflexive (solve 1 (λ P → P :+ con 6 :* P := con 7 :* P)
                                    refl (B ^ 12))))
  where
  L≤ : length (terms R) ≤ suc (n + 0) ^ 2
  L≤ = subst (λ ts → length ts ≤ suc (n + 0) ^ 2) (sym can)
             (canonical-length {n = n} {m = 0} 2 ⟦ terms R ⟧ˢ)
cost-verdict-at (normal k (suc m) R) can B le =
  ℕ.≤-trans (^-pos {B = B} {k = 12} (1≤ le)) (ℕ.m≤n*m (B ^ 12) 7)

-- In particular at B = n + x + 3.

cost-verdictᶜ : (r : Normal n) → Canonical 2 (terms (nrep r)) → (x : ℕ) →
                cost (verdictᶜ r) ≤ 7 * (3 + (n + x)) ^ 12
cost-verdictᶜ {n} r can x =
  cost-verdict-at r can (3 + (n + x)) (ℕ.+-monoʳ-≤ 3 (ℕ.m≤m+n n x))


------------------------------------------------------------------------
-- The cost of the decision

-- The pipeline: 2 |C| to count, 19 (n + |C| + 1)^2 to interpret,
-- (|C| + 284)(n + m + 3)^11 to normalise, m ≤ |C| (PathSum.Cost.
-- Normalise), and the verdict; at most 313 B^12.

cost-pipeline-at : (C : Circuit n) (B : ℕ) → 3 + (n + length C) ≤ B →
                   cost (pipelineᶜ C) ≤ 313 * B ^ 12
cost-pipeline-at {n} C B le = ℕ.≤-trans
  (ℕ.+-mono-≤ c₁ (ℕ.+-mono-≤ c₂ (ℕ.+-mono-≤ c₃ c₄)))
  (ℕ.≤-reflexive (solve 1 (λ P → con 2 :* P :+ (con 19 :* P :+
                                  (con 285 :* P :+ con 7 :* P)) :=
                                con 313 :* P) refl (B ^ 12)))
  where
  kᴴ = value (countHᶜ C)
  p = value (interpᴿᶜ C)
  R = proj₂ p
  r = value (normaliseᶜ 2 kᴴ R)

  1≤B : 1 ≤ B
  1≤B = 1≤ le

  ℓ≤B : length C ≤ B
  ℓ≤B = ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤n+m (length C) n)
                             (ℕ.m≤n+m (n + length C) 3)) le

  c₁ : cost (countHᶜ C) ≤ 2 * B ^ 12
  c₁ = ℕ.≤-trans (cost-countHᶜ C)
    (ℕ.*-monoʳ-≤ 2 (below 12 1≤B ℓ≤B (s≤s z≤n)))

  c₂ : cost (interpᴿᶜ C) ≤ 19 * B ^ 12
  c₂ = ℕ.≤-trans (cost-interpᴿᶜ C) (ℕ.*-monoʳ-≤ 19
    (ℕ.≤-trans (ℕ.^-monoˡ-≤ 2 (ℕ.≤-trans (ℕ.≤-trans (ℕ.n≤1+n _)
                                                   (ℕ.n≤1+n _)) le))
               (^-mono 1≤B (ℕ.m≤m+n 2 10))))

  m≤ : 3 + (n + proj₁ p) ≤ B
  m≤ = ℕ.≤-trans (ℕ.+-monoʳ-≤ 3 (ℕ.+-monoʳ-≤ n (interpᴿ-paths≤ C))) le

  L≤ : length (terms R) + 284 ≤ 285 * B
  L≤ = ℕ.≤-trans (ℕ.≤-reflexive (cong (_+ 284) (interpᴿ-length C)))
    (ℕ.≤-trans (ℕ.+-mono-≤ ℓ≤B (ℕ.*-monoʳ-≤ 284 1≤B))
      (ℕ.≤-reflexive (solve 1 (λ B → B :+ con 284 :* B := con 285 :* B)
                             refl B)))

  c₃ : cost (normaliseᶜ 2 kᴴ R) ≤ 285 * B ^ 12
  c₃ = ℕ.≤-trans (cost-normalise-poly 2 kᴴ R)
    (ℕ.≤-trans (ℕ.*-mono-≤ L≤ (ℕ.^-monoˡ-≤ (3 * 2 + 5) m≤))
               (ℕ.≤-reflexive (ℕ.*-assoc 285 B (B ^ 11))))

  c₄ : cost (verdictᶜ r) ≤ 7 * B ^ 12
  c₄ = cost-verdict-at r (normalise-canonical 2 kᴴ R) B
         (ℕ.≤-trans (ℕ.+-monoʳ-≤ 3 (ℕ.m≤m+n n (length C))) le)

cost-pipelineᶜ : (C : Circuit n) → cost (pipelineᶜ C) ≤ decideBound n (length C)
cost-pipelineᶜ {n} C = subst (cost (pipelineᶜ C) ≤_)
  (sym (decideBound-def n (length C)))
  (cost-pipeline-at C (3 + (n + length C)) ℕ.≤-refl)

-- The decision.  (The case split on the circuit is made below the
-- variable B, so that no bound is ever read at a circuit of a given
-- shape.)

cost-decide-at : (C : Circuit n) (B : ℕ) → 3 + (n + length C) ≤ B →
                 cost (decideᶜ C) ≤ 313 * B ^ 12
cost-decide-at []      B le =
  ℕ.≤-trans (^-pos {B = B} {k = 12} (1≤ le)) (ℕ.m≤n*m (B ^ 12) 313)
cost-decide-at (g ∷ C) B le = cost-pipeline-at (g ∷ C) B le

cost-decideᶜ : (C : Circuit n) → cost (decideᶜ C) ≤ decideBound n (length C)
cost-decideᶜ {n} C = subst (cost (decideᶜ C) ≤_)
  (sym (decideBound-def n (length C)))
  (cost-decide-at C (3 + (n + length C)) ℕ.≤-refl)

-- In the volume n · |C|: a gate names a wire, so n ≥ 1 when |C| ≥ 1,
-- and then n + |C| ≤ 2 n |C|.

private
  gate-wire : Gate n → 1 ≤ n
  gate-wire (H w)    = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)
  gate-wire (S w)    = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)
  gate-wire (CZ w v) = ℕ.≤-trans (s≤s z≤n) (toℕ<n w)

  volume-at : (C : Circuit n) (v : ℕ) → v ≡ n * length C →
              cost (decideᶜ C) ≤ 313 * (3 + 2 * v) ^ 12
  volume-at []      v eq = ℕ.≤-trans (^-pos {B = 3 + 2 * v} {k = 12} (s≤s z≤n))
                                     (ℕ.m≤n*m ((3 + 2 * v) ^ 12) 313)
  volume-at {n} (g ∷ C) v eq = cost-pipeline-at (g ∷ C) (3 + 2 * v)
    (ℕ.+-monoʳ-≤ 3 (ℕ.≤-trans
      (volume-≤ n (length (g ∷ C)) (gate-wire g) (s≤s z≤n))
      (ℕ.≤-reflexive (cong (2 *_) (sym eq)))))

cost-decide-volume : (C : Circuit n) →
                     cost (decideᶜ C) ≤ volumeBound (n * length C)
cost-decide-volume {n} C = subst (cost (decideᶜ C) ≤_)
  (sym (volumeBound-def (n * length C)))
  (volume-at C (n * length C) refl)


------------------------------------------------------------------------
-- Corollary 4.4 in polynomial time

-- Whether ⟦ C ⟧ is the identity is decided by decideᶜ, at a cost
-- polynomial in n + |C| and in the volume n · |C|.

record Corollary-4-4 {n : ℕ} (C : Circuit n) : Set where
  field
    decides    : value (decideᶜ C) ≡ true ⇔ ⟦ C ⟧ ≋ idPS
    polynomial : cost (decideᶜ C) ≤ decideBound n (length C)
    volume     : cost (decideᶜ C) ≤ volumeBound (n * length C)

corollary-4-4-polytime : (C : Circuit n) → Corollary-4-4 C
corollary-4-4-polytime C = record
  { decides    = decide-correct C
  ; polynomial = cost-decideᶜ C
  ; volume     = cost-decide-volume C
  }


------------------------------------------------------------------------
-- The miter, in the monad

-- C† gate by gate, each inverted (S† is S³) and appended after the
-- inverse of the rest.

daggerᶜ : Circuit n → Cost (Circuit n)
daggerᶜ []      = pure []
daggerᶜ (g ∷ C) = do
  tick
  D ← daggerᶜ C
  appendᶜ D (inv g)

value-daggerᶜ : (C : Circuit n) → value (daggerᶜ C) ≡ C †
value-daggerᶜ []      = refl
value-daggerᶜ (g ∷ C) = trans (value-appendᶜ (value (daggerᶜ C)) (inv g))
                              (cong (_++ inv g) (value-daggerᶜ C))

length-inv : (g : Gate n) → length (inv g) ≤ 3
length-inv (H w)    = s≤s z≤n
length-inv (S w)    = ℕ.≤-refl
length-inv (CZ w v) = s≤s z≤n

length-† : (C : Circuit n) → length (C †) ≤ 3 * length C
length-† []      = z≤n
length-† (g ∷ C) = ℕ.≤-trans (ℕ.≤-reflexive (List.length-++ (C †)))
  (ℕ.≤-trans (ℕ.+-mono-≤ (length-† C) (length-inv g))
    (ℕ.≤-reflexive (solve 1 (λ L → con 3 :* L :+ con 3 :=
                                   con 3 :* (con 1 :+ L)) refl (length C))))

cost-daggerᶜ : (C : Circuit n) →
               cost (daggerᶜ C) ≤ length C * suc (3 * length C)
cost-daggerᶜ []      = z≤n
cost-daggerᶜ (g ∷ C) = ℕ.≤-trans (s≤s (ℕ.+-mono-≤ c≤ a≤))
  (ℕ.≤-reflexive (cong suc (ℕ.+-comm (L * suc (3 * suc L)) (3 * suc L))))
  where
  L = length C

  c≤ : cost (daggerᶜ C) ≤ L * suc (3 * suc L)
  c≤ = ℕ.≤-trans (cost-daggerᶜ C)
    (ℕ.*-monoʳ-≤ L (s≤s (ℕ.*-monoʳ-≤ 3 (ℕ.n≤1+n L))))

  a≤ : cost (appendᶜ (value (daggerᶜ C)) (inv g)) ≤ 3 * suc L
  a≤ = ℕ.≤-trans (cost-appendᶜ (value (daggerᶜ C)) (inv g))
    (ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-daggerᶜ C)))
      (ℕ.≤-trans (length-† C) (ℕ.*-monoʳ-≤ 3 (ℕ.n≤1+n L))))

-- The miter C₁ ++ C₂†.

miterᶜ : Circuit n → Circuit n → Cost (Circuit n)
miterᶜ C₁ C₂ = do
  D ← daggerᶜ C₂
  appendᶜ C₁ D

value-miterᶜ : (C₁ C₂ : Circuit n) → value (miterᶜ C₁ C₂) ≡ C₁ ++ C₂ †
value-miterᶜ C₁ C₂ = trans (value-appendᶜ C₁ (value (daggerᶜ C₂)))
                           (cong (C₁ ++_) (value-daggerᶜ C₂))

cost-miterᶜ : (C₁ C₂ : Circuit n) →
              cost (miterᶜ C₁ C₂) ≤
              length C₂ * suc (3 * length C₂) + length C₁
cost-miterᶜ C₁ C₂ =
  ℕ.+-mono-≤ (cost-daggerᶜ C₂) (cost-appendᶜ C₁ (value (daggerᶜ C₂)))

length-miter : (C₁ C₂ : Circuit n) →
               length (value (miterᶜ C₁ C₂)) ≤ length C₁ + 3 * length C₂
length-miter C₁ C₂ = ℕ.≤-trans
  (ℕ.≤-reflexive (trans (cong length (value-miterᶜ C₁ C₂))
                        (List.length-++ C₁)))
  (ℕ.+-monoʳ-≤ (length C₁) (length-† C₂))


------------------------------------------------------------------------
-- Equivalence of two Clifford circuits

equivᶜ : Circuit n → Circuit n → Cost Bool
equivᶜ C₁ C₂ = miterᶜ C₁ C₂ >>= decideᶜ

equiv-correct : (C₁ C₂ : Circuit n) →
                (value (equivᶜ C₁ C₂) ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equiv-correct {n} C₁ C₂ = ⇔-trans (decide-correct (value (miterᶜ C₁ C₂)))
  (⇔-trans (mk⇔ (subst P eq) (subst P (sym eq))) (⇔-sym (miter C₁ C₂)))
  where
  P : Circuit n → Set
  P D = ⟦ D ⟧ ≋ idPS

  eq = value-miterᶜ C₁ C₂

equiv? : (C₁ C₂ : Circuit n) → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
equiv? C₁ C₂ = by (value (equivᶜ C₁ C₂)) refl
  where
  by : ∀ b → value (equivᶜ C₁ C₂) ≡ b → Dec (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧)
  by true  e = yes (Equivalence.to (equiv-correct C₁ C₂) e)
  by false e = no (λ h → false≢true
    (trans (sym e) (Equivalence.from (equiv-correct C₁ C₂) h)))
    where
    false≢true : false ≡ true → ⊥
    false≢true ()

-- At most 315 (n + 3 (|C₁| + |C₂|) + 3)^12.

cost-equiv-at : (C₁ C₂ : Circuit n) (B : ℕ) →
                3 + (n + 3 * (length C₁ + length C₂)) ≤ B →
                cost (equivᶜ C₁ C₂) ≤ 315 * B ^ 12
cost-equiv-at {n} C₁ C₂ B le = ℕ.≤-trans
  (ℕ.+-mono-≤ (ℕ.≤-trans (cost-miterᶜ C₁ C₂) (ℕ.+-mono-≤ bb≤ a≤P))
    (ℕ.≤-trans (cost-decideᶜ D) (decide≤ n (length D) B lenD≤)))
  (ℕ.≤-reflexive (solve 1 (λ P → (P :+ P) :+ con 313 :* P := con 315 :* P)
                         refl (B ^ 12)))
  where
  a = length C₁
  b = length C₂
  D = value (miterᶜ C₁ C₂)

  1≤B : 1 ≤ B
  1≤B = 1≤ le

  a3b≤ : a + 3 * b ≤ 3 * (a + b)
  a3b≤ = ℕ.≤-trans (ℕ.+-monoˡ-≤ (3 * b) (ℕ.m≤n*m a 3))
                   (ℕ.≤-reflexive (sym (ℕ.*-distribˡ-+ 3 a b)))

  toB : ∀ {y} → y ≤ 3 * (a + b) → y ≤ B
  toB h = ℕ.≤-trans h (ℕ.≤-trans (ℕ.m≤n+m _ n)
                                 (ℕ.≤-trans (ℕ.m≤n+m _ 3) le))

  lenD≤ : 3 + (n + length D) ≤ B
  lenD≤ = ℕ.≤-trans
    (ℕ.+-monoʳ-≤ 3 (ℕ.+-monoʳ-≤ n (ℕ.≤-trans (length-miter C₁ C₂) a3b≤)))
    le

  b≤ : b ≤ 3 * (a + b)
  b≤ = ℕ.≤-trans (ℕ.m≤n+m b a) (ℕ.m≤n*m (a + b) 3)

  3b≤ : suc (3 * b) ≤ B
  3b≤ = ℕ.≤-trans (s≤s (ℕ.≤-trans (ℕ.*-monoʳ-≤ 3 (ℕ.m≤n+m b a))
                                  (ℕ.m≤n+m _ n)))
                  (ℕ.≤-trans (ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.n≤1+n _)) le)

  bb≤ : b * suc (3 * b) ≤ B ^ 12
  bb≤ = ℕ.≤-trans (ℕ.*-mono-≤ (toB b≤) 3b≤)
    (ℕ.≤-trans (ℕ.≤-reflexive (B*B B)) (^-mono 1≤B (ℕ.m≤m+n 2 10)))

  a≤P : a ≤ B ^ 12
  a≤P = below 12 1≤B (toB (ℕ.≤-trans (ℕ.m≤m+n a b) (ℕ.m≤n*m (a + b) 3)))
              (s≤s z≤n)

cost-equivᶜ : (C₁ C₂ : Circuit n) →
              cost (equivᶜ C₁ C₂) ≤ equivBound n (length C₁) (length C₂)
cost-equivᶜ {n} C₁ C₂ =
  subst (cost (equivᶜ C₁ C₂) ≤_)
    (sym (equivBound-def n (length C₁) (length C₂)))
    (cost-equiv-at C₁ C₂ (3 + (n + 3 * (length C₁ + length C₂))) ℕ.≤-refl)

-- Equivalence of Clifford circuits in polynomial time.

record PolyEquivalence {n : ℕ} (C₁ C₂ : Circuit n) : Set where
  field
    decides    : value (equivᶜ C₁ C₂) ≡ true ⇔ ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧
    polynomial : cost (equivᶜ C₁ C₂) ≤ equivBound n (length C₁) (length C₂)

equivalence-polytime : (C₁ C₂ : Circuit n) → PolyEquivalence C₁ C₂
equivalence-polytime C₁ C₂ = record
  { decides    = equiv-correct C₁ C₂
  ; polynomial = cost-equivᶜ C₁ C₂
  }
