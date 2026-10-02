------------------------------------------------------------------------
-- Presentations of groups
--
-- The sparse Gaussian elimination runs PathSum.Gauss's (Amy, QPL 2018,
-- section 4.1 and the proof of corollary 4.4)
--
-- PathSum.Cost.Gauss writes the elimination of section 4.1 as a
-- program in the cost model, gaussᶜ d R, on a sparse representation R
-- of a path-sum with Z₂-linear outputs.  This module proves it correct
-- against PathSum.Gauss, the dense elimination: R tracks a dense state
-- st of PathSum.CRK.Circuit (Tracks: its terms stand for the phase
-- modulo 2^M, coefficient by coefficient, and its forms are the
-- state's), the phase of st has order at most d, and then:
--
--  * gaussᶜ-lockstep: there is a result g : Gauss st of PathSum.Gauss's
--    type of eliminations in lockstep with the program's outcome
--    (Lockstep): a refutation is a refuted x of g, at the same input
--    x, and when the program reifies, the representation it returns
--    tracks the final state of g's Reified record.  The statement says
--    only that much -- Gauss st is a type of results, not of runs.
--    That g is the outcome of a run of PathSum.Gauss's step at the
--    program's pivots is a fact about the proof, which builds g
--    alongside the sparse run from PathSum.Gauss's public lemmas
--    (step-amp, val-step, miss-step, step-Ord≤, settled-step,
--    amp-miss; its own back is private and is restated here as back),
--    every step of the program tracking the dense step
--    st ↦ PathSum.Gauss.step st w j (step-tracks, public).
--  * The refutation (gaussᶜ-refutes, gaussᶜ-not-id): the input x that
--    the program returns has no solution -- f(x,y) ≠ x for every path
--    y, "no such solution exists" -- and the diagonal entry of st at x
--    vanishes, so toPS st ≢ |x⟩ ↦ |x⟩ (PathSum.Gauss.refute), with no
--    hypothesis.
--  * The reification (gaussᶜ-reifies, the record Reifiesᶜ): the
--    program's R′ represents a path-sum -- PathSum.Gauss's ξᴿ of the
--    run -- with the identity's outputs μ x_w, only internal path
--    variables, the diagonal of st, a phase of no higher order than
--    st's (lemma 2.13 at every substitution), at most n path variables
--    fewer, and every input solvable; by lemma 4.1 it is the identity
--    exactly when st is, if st is well-formed.  It is ≋ to every
--    reified restriction of st with the identity's outputs and st's
--    diagonal (reified-≋-any), in particular to PathSum.Gauss's own
--    (≋-gauss, through PathSum.Gauss.Corollary.restriction) and to the
--    path-sum psʳ k R′ that R′ stands for (reified-≋-psʳ).
--  * Exactness against the paper's criterion (refutes⇔no-solution):
--    the program refutes exactly when some input has no solution
--    y with f(x,y) = x; otherwise every input has one.  This criterion
--    does not depend on the choice of pivots.
--  * At a circuit C over {H, CNOT, R_k, R_k†} (circuit-refutes,
--    circuit-reifies, circuit-identity): the output of
--    PathSum.Cost.Interpreter.interpKᶜ C tracks the dense run of C
--    (PathSum.Cost.Gauss.interpK-tracks), whose path-sum is ⟦ C ⟧ and
--    whose phase has order at most max(2, level C) (proposition 2.14,
--    corrected), so elimination at any d ≥ max(2, level C) either
--    refutes ⟦ C ⟧ or reifies a restriction that is the identity
--    exactly when ⟦ C ⟧ is (lemma 4.1, ⟦ C ⟧ having unit columns).
--    PathSum.Cost.Gauss.Corollary builds the decision of corollary 4.4
--    on these three.
--
-- Departure, and why.  The brief asks that the program refute exactly
-- when PathSum.Gauss.gauss refutes.  That is true mathematically --
-- both refute exactly when some input has no solution -- but gauss's
-- half cannot be proved from outside PathSum.Gauss, and PathSum.Gauss
-- is not to be edited: its pivot choice (PathSum.Gauss.Forms.pivot?)
-- and its final verdict (a private finish) are defined through
-- where-local and private helpers that do not reduce on a symbolic
-- state, and a `with` on the term they are stuck on does not abstract
-- it (checked).  Nor does any public fact about a value of Gauss st
-- decide its constructor: a refuted x z carries only a vanishing
-- diagonal entry, which a reified restriction may have too (by
-- interference).  So the lockstep is with a run of PathSum.Gauss's
-- elimination built alongside the program's -- the first wire whose
-- form has a path variable, and its first path variable, the rule
-- pivot? follows, but with no proof that the two coincide -- and the
-- verdict's exactness is stated against the pivot-independent
-- criterion, which is what the paper's "if no such solution exists"
-- means.  What does hold of gauss's own run: when it reifies, its
-- restriction and the program's are ≋ (≋-gauss); and, st being
-- well-formed, the two never disagree about the identity
-- (gauss-refutes-agree, refutes-gauss-agree).
--
-- The cost of the program is PathSum.Cost.Gauss's (cost-gaussᶜ), in
-- the cost model of PathSum.Cost: a cost model, not a machine model;
-- nothing is claimed about Turing machines or complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Gauss.Correct (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Integer.Properties using ()
  renaming (≤-reflexive to ≤ᶻ-reflexive)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (zero; suc; _+_; _≤_; _⊔_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Vec.Base using (insertAt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Negation using (¬_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; same; same-true; same-intro)
open import PathSum.Base using (PathSum; phase; out; idPS; Internal)
open import PathSum.Cost using (value)
open import PathSum.Cost.Canon M using (canonᶜ; Ordᵀ)
open import PathSum.Cost.Gauss M using
  (Tracks; Tracksᵖ; tracks; interpK-tracks; stateᴿ; Solves; NoSolution;
   Solvable; Outcome; refutes; reifies; pivotᶜ; pivotᶜ-just;
   pivotᶜ-nothing; solᴸ; stepᶜ; stepᶜ-terms; stepᶜ-Ordᵀ; stepᶜ-forms;
   finishᶜ; finishᶜ-just; finishᶜ-nothing; finishBy; elimᶜ; elimBy;
   gaussᶜ)
open import PathSum.Cost.Interpreter M using (interpKᶜ)
open import PathSum.Cost.Rules M using (canon-represents)
open import PathSum.Cost.Subst M using (subst-≈)
open import PathSum.CRK.Amp M₀ using (toPS; ampᴸ)
open import PathSum.CRK.Circuit M using
  (State; poly; sig; Circuit; run; init; ⟦_⟧; norm; level; prop-2-14;
   Ord≤-weaken)
open import PathSum.Cyclotomic M₀ using (0ᴬ; _≐_; scale; scale-map)
open import PathSum.Denotation M₀ using
  (Assign; amp; _≋_; hits-elim; outBit-μ; amp-≗; eval-μ-val)
open import PathSum.Gauss M₀ using
  (Gauss; refuted; reduced; Reified; sol; pick; val-step; miss-step;
   step-amp; step-Ord≤; settled; settled-step; amp-miss; ξᴿ;
   reified-diag; reified-Ord≤; reified-Internal; reified-out;
   reified-removes; reified-≋; refute; gauss)
  renaming (step to stepᴳ)
open import PathSum.Gauss.Corollary M₀ using
  (restriction; Reifies; restriction-just; restriction-nothing)
open import PathSum.Gauss.Forms using (coefʸ; dropᴸ; elimᴸ; not-≢)
open import PathSum.Isometry M₀ using (WellFormed; Diagonal; amp-no-path)
open import PathSum.Linear using
  (Lin; valᴸ; liftᴸ; varᴸ; _⊕ᴸ_; par; par-cong; eval-liftᴸ)
open import PathSum.Order M using (Ord≤; pow)
open import PathSum.Polynomial using (x[_]; y[_]; μ; _≈[_]_)
  renaming (subst to psubst)
open import PathSum.Polynomial.Bind using (poly-ext)
open import PathSum.Polynomial.Product using (≈-trans)
open import PathSum.Reorder using (insertᵃ; _∖ʸ_)
open import PathSum.Size.Equivalence M₀ using (represents-≋)
open import PathSum.Size.Sparse M using
  (⟦_⟧ˢ; Rep; rep; terms; forms; Represents; psʳ)

import Data.Nat.Properties as ℕ
import PathSum.CRK.Semantics

private
  module Sem = PathSum.CRK.Semantics M₀

  variable
    d k n m m′ : ℕ


------------------------------------------------------------------------
-- Assignments split at a path variable

private
  -- An assignment is its value at j inserted into the rest.
  split-ᵃ : (j : Fin (suc m)) (y : Fin (suc m) → Bool) →
            ∀ i → insertᵃ j (y j) (λ l → y (punchIn j l)) i ≡ y i
  split-ᵃ         zero    y zero    = refl
  split-ᵃ         zero    y (suc i) = refl
  split-ᵃ {zero}  (suc ()) y i
  split-ᵃ {suc m} (suc j) y zero    = refl
  split-ᵃ {suc m} (suc j) y (suc i) = split-ᵃ j (λ l → y (suc l)) i

  -- A form reads an assignment only through its values.
  valᴸ-≗ : (l : Lin n m) (x : Fin n → Bool) {y y′ : Fin m → Bool} →
           (∀ i → y i ≡ y′ i) → valᴸ l x y ≡ valᴸ l x y′
  valᴸ-≗ (c , (α , β)) x h = cong (λ b → c xor (par α x xor b)) (par-cong β h)

  cases : ∀ p q → (p ≡ q) ⊎ (p ≡ not q)
  cases false false = inj₁ refl
  cases false true  = inj₂ refl
  cases true  false = inj₂ refl
  cases true  true  = inj₁ refl


------------------------------------------------------------------------
-- A step of the dense elimination, read backwards

-- No solution after the step, none before: on the path the step keeps
-- the outputs are the step's, and on the other wire w misses its input.

nosol-back : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
             coefʸ (sig st w) j ≡ true → (x : Fin n → Bool) →
             NoSolution (stepᴳ st w j) x → NoSolution st x
nosol-back st w j piv x none y solves =
  [ kept , lost ]′ (cases (pick st w j x g) b)
  where
  b = y j
  g = λ l → y (punchIn j l)

  at : Solves st x (insertᵃ j b g)
  at v = trans (valᴸ-≗ (sig st v) x (split-ᵃ j y)) (solves v)

  kept : pick st w j x g ≡ b → ⊥
  kept e = none g (λ v → trans (val-step st w j piv v x g b e) (at v))

  lost : pick st w j x g ≡ not b → ⊥
  lost e = not-≢ (x w) (trans (sym (miss-step st w j piv x g b e)) (at w))

-- A solution after the step gives one before.

solvable-back : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
                coefʸ (sig st w) j ≡ true →
                Solvable (stepᴳ st w j) → Solvable st
solvable-back st w j piv solv x =
  insertᵃ j (pick st w j x g) g ,
  λ v → trans (sym (val-step st w j piv v x g (pick st w j x g) refl))
              (proj₂ (solv x) v)
  where
  g = proj₁ (solv x)

-- PathSum.Gauss's step, carried back over the outcome of the rest of
-- the run (PathSum.Gauss does this privately; here it is in the open).

back-reified : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
               coefʸ (sig st w) j ≡ true → Reified (stepᴳ st w j) →
               Reified st
back-reified {m = m} st w j piv r = record
  { m′     = Reified.m′ r
  ; final  = Reified.final r
  ; diag   = λ x i → trans (step-amp st w j piv x x refl i)
                           (Reified.diag r x i)
  ; order  = λ {d} o → Reified.order r {d} (step-Ord≤ {d = d} st w j o)
  ; solved = Reified.solved r
  ; budget = ℕ.≤-trans
      (ℕ.≤-reflexive (sym (ℕ.+-suc m (settled st))))
      (ℕ.≤-trans (ℕ.+-monoʳ-≤ m (settled-step st w j piv))
                 (Reified.budget r))
  }

back : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m)) →
       coefʸ (sig st w) j ≡ true → Gauss (stepᴳ st w j) → Gauss st
back st w j piv (refuted x z) =
  refuted x (λ i → trans (step-amp st w j piv x x refl i) (z i))
back st w j piv (reduced r)   = reduced (back-reified st w j piv r)


------------------------------------------------------------------------
-- The lockstep

-- The program's outcome is the dense run's: the same refuting input,
-- which has no solution; or a representation tracking the final state
-- of the reified run, every input having a solution.

data Lockstep {n m : ℕ} {st : State n m} : Gauss st → Outcome n → Set where
  both-refute : ∀ {x} {z : ampᴸ st x x ≐ 0ᴬ} → NoSolution st x →
                Lockstep (refuted x z) (refutes x)
  both-reify  : (r : Reified st) {R′ : Rep n (Reified.m′ r)} →
                Tracks (Reified.final r) R′ → Solvable st →
                Lockstep (reduced r) (reifies R′)

back-lockstep : (st : State n (suc m)) (w : Fin n) (j : Fin (suc m))
                (piv : coefʸ (sig st w) j ≡ true)
                {g : Gauss (stepᴳ st w j)} {o : Outcome n} →
                Lockstep g o → Lockstep (back st w j piv g) o
back-lockstep st w j piv (both-refute {x} none) =
  both-refute (nosol-back st w j piv x none)
back-lockstep st w j piv (both-reify r tr solv) =
  both-reify (back-reified st w j piv r) tr (solvable-back st w j piv solv)

-- One sparse step tracks PathSum.Gauss's step, whose pivot is the
-- program's: the phase modulo 2^M, and the forms literally.

step-tracks : (d : ℕ) (st : State n (suc m)) (R : Rep n (suc m)) →
              Tracks st R → Ordᵀ d (terms R) →
              (w : Fin n) (j : Fin (suc m)) →
              Tracks (stepᴳ st w j) (value (stepᶜ d w j (sig st w) R))
step-tracks d st R (eqP , eqF) ord w j = phase′ , forms′
  where
  R′ = value (stepᶜ d w j (sig st w) R)
  s  = sol st w j

  sol≡ : solᴸ w j (sig st w) ≡ sol st w j
  sol≡ = refl

  first : poly (stepᴳ st w j) ≈[ pow M ]
          (psubst ⟦ terms R ⟧ˢ y[ j ] (proj₁ s) (proj₂ s) ∖ʸ j)
  first (α , β) = subst-≈ j (proj₁ s) (proj₂ s) {P = poly st}
                          {Q = ⟦ terms R ⟧ˢ} eqP (α , insertAt β j false)

  second : (psubst ⟦ terms R ⟧ˢ y[ j ] (proj₁ s) (proj₂ s) ∖ʸ j)
           ≈[ pow M ] ⟦ terms R′ ⟧ˢ
  second = subst (λ s′ → (psubst ⟦ terms R ⟧ˢ y[ j ] (proj₁ s′) (proj₂ s′)
                          ∖ʸ j) ≈[ pow M ] ⟦ terms R′ ⟧ˢ)
                 sol≡ (stepᶜ-terms d w j (sig st w) R ord)

  phase′ : poly (stepᴳ st w j) ≈[ pow M ] ⟦ terms R′ ⟧ˢ
  phase′ = ≈-trans {P = poly (stepᴳ st w j)}
                   {Q = psubst ⟦ terms R ⟧ˢ y[ j ] (proj₁ s) (proj₂ s) ∖ʸ j}
                   {R = ⟦ terms R′ ⟧ˢ} first second

  forms′ : ∀ v → forms R′ v ≡ sig (stepᴳ st w j) v
  forms′ v = trans (stepᶜ-forms d w j (sig st w) R v)
    (cong (λ l → dropᴸ j (elimᴸ j (sig st w ⊕ᴸ varᴸ x[ w ]) l)) (eqF v))

-- The finish: the program's verdict is a verdict of the dense run.

finish-lockstep : (st : State n m) (R : Rep n m) → Tracks st R →
                  (∀ w j → coefʸ (sig st w) j ≡ false) →
                  ∃ λ (g : Gauss st) →
                    Lockstep g (finishBy R (value (finishᶜ (forms R))))
finish-lockstep {n} {m} st R (eqP , eqF) free =
  by (value (finishᶜ (forms R))) refl
  where
  freeR : ∀ w j → coefʸ (forms R w) j ≡ false
  freeR w j = trans (cong (λ l → coefʸ l j) (eqF w)) (free w j)

  by : (r : Maybe (Fin n → Bool)) → value (finishᶜ (forms R)) ≡ r →
       ∃ λ (g : Gauss st) → Lockstep g (finishBy R r)
  by (just x) e =
    refuted x (amp-miss st w x miss) ,
    both-refute (λ y solves → not-≢ (x w) (trans (sym (miss y)) (solves w)))
    where
    wm = finishᶜ-just (forms R) freeR e
    w  = proj₁ wm

    miss : ∀ y → valᴸ (sig st w) x y ≡ not (x w)
    miss y = trans (cong (λ l → valᴸ l x y) (sym (eqF w))) (proj₂ wm y)
  by nothing  e =
    reduced r , both-reify r (eqP , eqF) (λ x → (λ _ → false) , λ w →
                                            solved w x (λ _ → false))
    where
    solved : ∀ w x y → valᴸ (sig st w) x y ≡ x w
    solved w x y = trans (cong (λ l → valᴸ l x y) (sym (eqF w)))
                         (finishᶜ-nothing (forms R) freeR e w x y)

    r : Reified st
    r = record
      { m′ = m ; final = st ; diag = λ _ _ → refl ; order = λ o → o
      ; solved = solved ; budget = ℕ.≤-refl }

-- The loop, by recursion on the number of path variables.

elim-lockstep : (d : ℕ) (st : State n m) (R : Rep n m) → Tracks st R →
                Ordᵀ d (terms R) →
                ∃ λ (g : Gauss st) → Lockstep g (value (elimᶜ d R))
elim-lockstep {n} {zero} d st R tr ord = by (value (pivotᶜ (forms R))) refl
  where
  by : (p : Maybe (Fin n × Fin 0 × Lin n 0)) →
       value (pivotᶜ (forms R)) ≡ p →
       ∃ λ (g : Gauss st) → Lockstep g (value (elimBy d R p))
  by (just (w , () , f)) e
  by nothing             e = finish-lockstep st R tr (λ w j →
    trans (cong (λ l → coefʸ l j) (sym (proj₂ tr w)))
          (pivotᶜ-nothing (forms R) e w j))
elim-lockstep {n} {suc m} d st R tr ord = by (value (pivotᶜ (forms R))) refl
  where
  by : (p : Maybe (Fin n × Fin (suc m) × Lin n (suc m))) →
       value (pivotᶜ (forms R)) ≡ p →
       ∃ λ (g : Gauss st) → Lockstep g (value (elimBy d R p))
  by (just (w , j , f)) e = at f (trans (proj₁ pj) (proj₂ tr w))
    where
    pj = pivotᶜ-just (forms R) e

    piv : coefʸ (sig st w) j ≡ true
    piv = subst (λ l → coefʸ l j ≡ true) (proj₂ tr w) (proj₂ pj)

    at : ∀ f′ → f′ ≡ sig st w →
         ∃ λ (g : Gauss st) →
           Lockstep g (value (elimᶜ d (value (stepᶜ d w j f′ R))))
    at _ refl =
      back st w j piv (proj₁ ih) , back-lockstep st w j piv (proj₂ ih)
      where
      ih = elim-lockstep d (stepᴳ st w j) (value (stepᶜ d w j (sig st w) R))
             (step-tracks d st R tr ord w j)
             (stepᶜ-Ordᵀ d w j (sig st w) R ord)
  by nothing             e = finish-lockstep st R tr (λ w j →
    trans (cong (λ l → coefʸ l j) (sym (proj₂ tr w)))
          (pivotᶜ-nothing (forms R) e w j))

-- The whole program: canonicalising first keeps the tracking and makes
-- the order bound hold term by term.

gaussᶜ-lockstep : (d : ℕ) (st : State n m) (R : Rep n m) → Tracks st R →
                  Ord≤ d (poly st) →
                  ∃ λ (g : Gauss st) → Lockstep g (value (gaussᶜ d R))
gaussᶜ-lockstep d st R (eqP , eqF) ord =
  elim-lockstep d st (rep ts (forms R)) (proj₁ cr , eqF) (proj₂ cr)
  where
  ts = value (canonᶜ d (terms R))
  cr = canon-represents d {X = poly st} (terms R) eqP ord


------------------------------------------------------------------------
-- The refutation

refutes-sound : {st : State n m} {g : Gauss st} {x : Fin n → Bool} →
                Lockstep g (refutes x) →
                (ampᴸ st x x ≐ 0ᴬ) × NoSolution st x
refutes-sound (both-refute {z = z} none) = z , none

-- The input returned has no solution, and the diagonal entry there
-- vanishes ...

gaussᶜ-refutes : (d : ℕ) (st : State n m) (R : Rep n m) → Tracks st R →
                 Ord≤ d (poly st) → ∀ {x} →
                 value (gaussᶜ d R) ≡ refutes x →
                 (ampᴸ st x x ≐ 0ᴬ) × NoSolution st x
gaussᶜ-refutes d st R tr ord eq =
  refutes-sound (subst (Lockstep (proj₁ ls)) eq (proj₂ ls))
  where
  ls = gaussᶜ-lockstep d st R tr ord

-- ... so the path-sum is not the identity.

gaussᶜ-not-id : (d : ℕ) (st : State n m) (R : Rep n m) → Tracks st R →
                Ord≤ d (poly st) → ∀ {x} →
                value (gaussᶜ d R) ≡ refutes x → ¬ (toPS {k = k} st ≋ idPS)
gaussᶜ-not-id {k = k} d st R tr ord {x} eq =
  refute {k = k} st x (proj₁ (gaussᶜ-refutes d st R tr ord eq))


------------------------------------------------------------------------
-- The reification

-- A form that reads x_w everywhere lifts to μ x_w, coefficient by
-- coefficient (Möbius, PathSum.Polynomial.Bind.poly-ext).

solved-lift : (l : Lin n m) (w : Fin n) → (∀ x y → valᴸ l x y ≡ x w) →
              ∀ γ → μ x[ w ] γ ≡ liftᴸ l γ
solved-lift l w h = poly-ext (μ x[ w ]) (liftᴸ l) (λ x y →
  trans (eval-μ-val x[ w ] x y)
        (sym (trans (eval-liftᴸ l x y) (cong [_]ᶻ (h x y)))))

-- What a reifying run returns, at normalisation k: R′ represents the
-- reified restriction of section 4.1, a path-sum with the identity's
-- outputs, only internal path variables and the diagonal of st.

record Reifiesᶜ (k : ℕ) {n m m′ : ℕ} (st : State n m) (R′ : Rep n m′) :
                Set where
  field
    reified    : PathSum n k m′
    represents : Represents reified R′
    internal   : Internal reified
    outputs    : ∀ w → out reified w ≡ μ x[ w ]
    diagonal   : ∀ x → amp (toPS {k = k} st) x x ≐ amp reified x x
    order      : ∀ {d} → Ord≤ d (poly st) → Ord≤ d (phase reified)
    identity   : WellFormed (toPS {k = k} st) →
                 (toPS {k = k} st ≋ idPS ⇔ reified ≋ idPS)
    removes    : m ≤ m′ + n
    solvable   : Solvable st

open Reifiesᶜ public

reifies-sound : {st : State n m} {g : Gauss st} {R′ : Rep n m′} →
                Lockstep g (reifies R′) → Reifiesᶜ k st R′
reifies-sound {k = k} (both-reify r {R′} tr solv) = record
  { reified    = ξᴿ r {k = k}
  ; represents = proj₁ tr , outs
  ; internal   = reified-Internal r {k = k}
  ; outputs    = reified-out r {k = k}
  ; diagonal   = reified-diag r {k = k}
  ; order      = λ {d} → reified-Ord≤ r {d = d} {k = k}
  ; identity   = reified-≋ r {k = k}
  ; removes    = reified-removes r
  ; solvable   = solv
  }
  where
  outs : ∀ w γ → out (ξᴿ r {k = k}) w γ ≡ liftᴸ (forms R′ w) γ
  outs w γ = trans
    (solved-lift (sig (Reified.final r) w) w (Reified.solved r w) γ)
    (cong (λ l → liftᴸ l γ) (sym (proj₂ tr w)))

gaussᶜ-reifies : (d : ℕ) (st : State n m) (R : Rep n m) → Tracks st R →
                 Ord≤ d (poly st) → ∀ {m′} {R′ : Rep n m′} →
                 value (gaussᶜ d R) ≡ reifies R′ → Reifiesᶜ k st R′
gaussᶜ-reifies d st R tr ord eq =
  reifies-sound (subst (Lockstep (proj₁ ls)) eq (proj₂ ls))
  where
  ls = gaussᶜ-lockstep d st R tr ord


------------------------------------------------------------------------
-- The verdict is the paper's criterion

-- The program refutes exactly when some input has no solution.

refutes⇔no-solution : (d : ℕ) (st : State n m) (R : Rep n m) →
                      Tracks st R → Ord≤ d (poly st) →
                      (∃ λ x → value (gaussᶜ d R) ≡ refutes x) ⇔
                      (∃ λ x → NoSolution st x)
refutes⇔no-solution {n} d st R tr ord = mk⇔
  (λ { (x , eq) → x , proj₂ (gaussᶜ-refutes d st R tr ord eq) })
  (λ { (x , none) → by x none (value (gaussᶜ d R)) refl })
  where
  by : ∀ x → NoSolution st x → (o : Outcome n) →
       value (gaussᶜ d R) ≡ o → ∃ λ x′ → value (gaussᶜ d R) ≡ refutes x′
  by x none (refutes x′) eq = x′ , eq
  by x none (reifies R′) eq =
    ⊥-elim (none (proj₁ (solv x)) (proj₂ (solv x)))
    where
    solv = solvable (gaussᶜ-reifies {k = 0} d st R tr ord eq)


------------------------------------------------------------------------
-- The reified restriction, up to ≋

-- A path-sum with the identity's outputs is diagonal.

diagonal-μ : (ξ : PathSum n k m) → (∀ w → out ξ w ≡ μ x[ w ]) → Diagonal ξ
diagonal-μ ξ o x y z h = same-intro x z (λ w →
  trans (sym (outBit-μ ξ x y w x[ w ] (o w))) (hits-elim ξ x y z h w))

-- Two of them with the same diagonal and normalisation are ≋.

diag-≋ : (ξ : PathSum n k m) (ζ : PathSum n k m′) →
         (∀ w → out ξ w ≡ μ x[ w ]) → (∀ w → out ζ w ≡ μ x[ w ]) →
         (∀ x → amp ξ x x ≐ amp ζ x x) → ξ ≋ ζ
diag-≋ {k = k} ξ ζ oξ oζ dg x z = by (same x z) refl
  where
  by : ∀ b → same x z ≡ b → scale k (amp ξ x z) ≐ scale k (amp ζ x z)
  by true  e = scale-map k (λ i → trans
    (amp-≗ ξ x (λ w → sym (same-true x z e w)) i)
    (trans (dg x i) (amp-≗ ζ x (same-true x z e) i)))
  by false e = scale-map k (λ i → trans
    (amp-no-path ξ x z (λ y → diagonal-μ ξ oξ x y z) e i)
    (sym (amp-no-path ζ x z (λ y → diagonal-μ ζ oζ x y z) e i)))

-- So the program's restriction is ≋ to every restriction of st with
-- the identity's outputs and the diagonal of st ...

reified-≋-any : {st : State n m} {R′ : Rep n m′} (rs : Reifiesᶜ k st R′)
                {m₀ : ℕ} (ξ₀ : PathSum n k m₀) →
                (∀ w → out ξ₀ w ≡ μ x[ w ]) →
                (∀ x → amp (toPS {k = k} st) x x ≐ amp ξ₀ x x) →
                reified rs ≋ ξ₀
reified-≋-any rs ξ₀ o₀ d₀ = diag-≋ (reified rs) ξ₀ (outputs rs) o₀
  (λ x i → trans (sym (diagonal rs x i)) (d₀ x i))

-- ... to the restriction of any run of PathSum.Gauss's elimination ...

≋-reified : {st : State n m} {R′ : Rep n m′} (rs : Reifiesᶜ k st R′)
            (r₀ : Reified st) → reified rs ≋ ξᴿ r₀ {k = k}
≋-reified {k = k} rs r₀ = reified-≋-any rs (ξᴿ r₀ {k = k})
  (reified-out r₀ {k = k}) (reified-diag r₀ {k = k})

-- ... in particular to PathSum.Gauss's own, whenever gauss reifies ...

≋-gauss : {st : State n m} {R′ : Rep n m′} (rs : Reifiesᶜ k st R′)
          {m₀ : ℕ} {ξ₀ : PathSum n k m₀} →
          restriction {k = k} (gauss st) ≡ just (m₀ , ξ₀) →
          reified rs ≋ ξ₀
≋-gauss {st = st} rs {ξ₀ = ξ₀} eq = reified-≋-any rs ξ₀
  (Reifies.outputs R₀) (Reifies.diagonal R₀)
  where
  R₀ = restriction-just (gauss st) eq

-- ... and to the path-sum R′ stands for.

reified-≋-psʳ : {st : State n m} {R′ : Rep n m′} (rs : Reifiesᶜ k st R′) →
                reified rs ≋ psʳ k R′
reified-≋-psʳ {R′ = R′} rs = represents-≋ (reified rs) R′ (represents rs)

-- The program and PathSum.Gauss's own run never disagree about the
-- identity, st being well-formed: if gauss refutes, the program's
-- restriction is not the identity; if the program refutes, gauss's
-- restriction is not.

gauss-refutes-agree : {st : State n m} {R′ : Rep n m′}
                      (rs : Reifiesᶜ k st R′) →
                      WellFormed (toPS {k = k} st) →
                      restriction {k = k} (gauss st) ≡ nothing →
                      ¬ (reified rs ≋ idPS)
gauss-refutes-agree {k = k} {st = st} rs wf eq id′ =
  refute {k = k} st (proj₁ z) (proj₂ z)
         (Equivalence.from (identity rs wf) id′)
  where
  z = restriction-nothing {k = k} (gauss st) eq

refutes-gauss-agree : (d : ℕ) (st : State n m) (R : Rep n m) →
                      Tracks st R → Ord≤ d (poly st) → ∀ {x} →
                      value (gaussᶜ d R) ≡ refutes x →
                      WellFormed (toPS {k = k} st) →
                      ∀ {m₀} {ξ₀ : PathSum n k m₀} →
                      restriction {k = k} (gauss st) ≡ just (m₀ , ξ₀) →
                      ¬ (ξ₀ ≋ idPS)
refutes-gauss-agree {k = k} d st R tr ord eq wf eq₀ id₀ =
  gaussᶜ-not-id {k = k} d st R tr ord eq
    (Equivalence.from (Reifies.identity (restriction-just (gauss st) eq₀) wf)
                      id₀)

-- Any representation tracks the state it spells out, whose path-sum is
-- the one it stands for: the theorems above apply to psʳ k R.

toPS-stateᴿ : (R : Rep n m) → toPS {k = k} (stateᴿ R) ≡ psʳ k R
toPS-stateᴿ R = refl


------------------------------------------------------------------------
-- At a circuit over {H, CNOT, R_k, R_k†}

-- The interpreter's output tracks the circuit's dense run
-- (PathSum.Cost.Gauss.interpK-tracks), whose path-sum is ⟦ C ⟧ by
-- definition and whose phase has order at most max(2, level C)
-- (proposition 2.14, corrected): elimination at any d ≥ max(2, level
-- C) refutes ⟦ C ⟧, or reifies its restriction.

private
  via-refutes : (d : ℕ) (p : ∃ (Rep n)) (q : ∃ (State n)) → Tracksᵖ p q →
                Ord≤ d (poly (proj₂ q)) → ∀ {x} →
                value (gaussᶜ d (proj₂ p)) ≡ refutes x →
                ¬ (toPS {k = k} (proj₂ q) ≋ idPS)
  via-refutes {k = k} d _ _ (tracks R st tr) ord eq =
    gaussᶜ-not-id {k = k} d st R tr ord eq

  via-reifies : (d : ℕ) (p : ∃ (Rep n)) (q : ∃ (State n)) → Tracksᵖ p q →
                Ord≤ d (poly (proj₂ q)) → ∀ {m′} {R′ : Rep n m′} →
                value (gaussᶜ d (proj₂ p)) ≡ reifies R′ →
                Reifiesᶜ k (proj₂ q) R′
  via-reifies d _ _ (tracks R st tr) ord eq = gaussᶜ-reifies d st R tr ord eq

circuit-refutes : (C : Circuit n) (d : ℕ) → 2 ⊔ level C ≤ d → ∀ {x} →
                  value (gaussᶜ d (proj₂ (value (interpKᶜ C)))) ≡ refutes x →
                  ¬ (⟦ C ⟧ ≋ idPS)
circuit-refutes C d le eq = via-refutes {k = norm C} d (value (interpKᶜ C))
  (run C init) (interpK-tracks C) (Ord≤-weaken le (prop-2-14 C)) eq

circuit-reifies : (C : Circuit n) (d : ℕ) → 2 ⊔ level C ≤ d →
                  ∀ {m′} {R′ : Rep n m′} →
                  value (gaussᶜ d (proj₂ (value (interpKᶜ C)))) ≡ reifies R′ →
                  Reifiesᶜ (norm C) (proj₂ (run C init)) R′
circuit-reifies C d le eq = via-reifies d (value (interpKᶜ C)) (run C init)
  (interpK-tracks C) (Ord≤-weaken le (prop-2-14 C)) eq

-- Lemma 4.1 at the circuit, whose columns have unit norm
-- (PathSum.CRK.Semantics): ⟦ C ⟧ is the identity exactly when the
-- reified restriction is.

circuit-identity : (C : Circuit n) (d : ℕ) (le : 2 ⊔ level C ≤ d)
                   {m′ : ℕ} {R′ : Rep n m′}
                   (eq : value (gaussᶜ d (proj₂ (value (interpKᶜ C)))) ≡
                         reifies R′) →
                   (⟦ C ⟧ ≋ idPS ⇔ reified (circuit-reifies C d le eq) ≋ idPS)
circuit-identity C d le eq = identity (circuit-reifies C d le eq)
  (λ x → ≤ᶻ-reflexive (Sem.⟦⟧-unit-columns C x))
