------------------------------------------------------------------------
-- Presentations of groups
--
-- Gaussian elimination on the sparse representation, in the cost
-- model (Amy, QPL 2018, section 4.1 and the proof of corollary 4.4)
--
-- The proof of corollary 4.4 reifies the isometry restriction
-- ξ|f(x,y)=x of section 4.1: "as f(x,y) is linear, we can compute via
-- Gaussian elimination a solution y so that f(x,y) = x for any x -- if
-- no such solution exists, ⟦C⟧ ≢ |x⟩ ↦ |x⟩", and each substitution
-- y_i ← f_i keeps the order of the phase (lemma 2.13).
-- PathSum.Gauss carries the elimination out on dense path-sums,
-- without cost.  Here the same elimination is written once, as a
-- program in the monad of PathSum.Cost, on PathSum.Size.Sparse's Rep:
-- a list of terms for the phase and a Z₂-linear form per wire, as
-- PathSum.Cost.Interpreter.interpKᶜ produces it for a circuit over
-- {H, CNOT, R_k, R_k†}.
--
-- The program, gaussᶜ d R:
--
--  0. Canonicalise the phase at degree d (PathSum.Cost.Canon), so that
--     it has at most (n + m + 1)^d terms.
--  1. Pivot (pivotᶜ): one sweep over the wires, in order, for the first
--     wire w whose form f_w has a path variable, and its first path
--     variable y_j -- the rule PathSum.Gauss.Forms.pivot? follows
--     (that the two coincide is not proved: see
--     PathSum.Cost.Gauss.Correct).
--  2. Step (stepᶜ): the solution sol = f_w ⊕ x_w ⊕ y_j (solᶜ), free of
--     y_j, is substituted for y_j in the phase -- the lifted linear
--     form, expanded and truncated at degree d, then re-canonicalised
--     (PathSum.Cost.Subst.substᶜ, exact by lemma 2.13) -- and in every
--     output form (PathSum.Cost.Subst.substFormsᶜ); then y_j, which no
--     longer occurs, is removed from both and the later path variables
--     renumbered (PathSum.Cost.Split.restᶜ, dropFormsᶜ).  On the forms
--     the substitution adds f_w ⊕ x_w to every form containing y_j,
--     which is PathSum.Gauss's row operation exactly (substForm-sol),
--     and wire w then reads x_w.  Repeat from 1.
--  3. Finish (finishᶜ): no form has a path variable left.  One sweep
--     over the wires reads each form c ⊕ ⨁α against x_w: if c = 1 the
--     all-zero input refutes it; otherwise, if α ⊕ {w} has an element
--     i, the unit vector at i (PathSum.Gauss.Forms.point) refutes it;
--     otherwise the wire reads x_w.  The first refuting input is
--     returned (refutes x): "no such solution exists".  If no wire
--     refutes, every output reads its input and the representation
--     left is that of the reified restriction (reifies R′).
--
-- The recursion is on the number of path variables, which every step
-- lowers by one, as in PathSum.Gauss.gauss; no fuel is needed.
--
-- What this module proves about the program, with M generic:
--
--  * pivotᶜ-just / pivotᶜ-nothing: the pivot is a path variable of the
--    form returned, or no form has one;
--  * value-solᶜ, stepᶜ-terms, stepᶜ-Ordᵀ, stepᶜ-forms: a step computes
--    the dense step's phase modulo 2^M, coefficient by coefficient
--    (P[y_j ← sol] with y_j removed, PathSum.Gauss.step's), keeps the
--    order bound term by term, and computes its forms literally
--    (dropᴸ j (elimᴸ j (f_w ⊕ x_w) f_v), PathSum.Gauss.step's);
--  * missᶜ-just / missᶜ-nothing, finishᶜ-just / finishᶜ-nothing: a
--    refuting input makes its wire read ¬x_w on every path, and when
--    none is found every wire reads x_w on every path;
--  * elimᶜ-shape, gaussᶜ-shape: a reification leaves no more path
--    variables than there were, and at most (n + m + 2)^d terms.
--
-- PathSum.Cost.Gauss.Correct runs this alongside PathSum.Gauss's
-- elimination and carries the dense theorems over.  Tracks st R says
-- that a representation stands for a dense State of
-- PathSum.CRK.Circuit: its terms for the phase modulo 2^M, its forms
-- for the forms, literally.  The output of PathSum.Cost.Interpreter's
-- interpKᶜ C tracks the dense run of C, whose path-sum is ⟦ C ⟧
-- (interpK-tracks, through PathSum.Size.Interpreter).  Solves,
-- NoSolution and Solvable state the paper's criterion: f(x,y) = x has
-- a solution y.  PathSum.Cost.Gauss.Corollary puts the program into the
-- pipeline of corollary 4.4 for Clifford circuits over {H, CNOT, R_k,
-- R_k†}: interpret, eliminate, normalise, conclude, in polynomial time.
--
-- The cost.  A round at m + 1 path variables with L terms, B = n + m +
-- 3 (PathSum.Cost.Rules.Bᴿ), costs at most 34 (L + 1) B^(2d+2): the
-- substitution dominates, as in [HH] (cost-stepᶜ, cost-pivotᶜ).  The
-- list a step leaves is the rest of a canonical one, so the next round
-- again has at most B^d terms, and the loop costs at most
-- (68 m + 6) B^(3d+2) (cost-elimᶜ, elimBound-≤); with the
-- canonicalisation the whole costs at most (L + 79)(n + m + 3)^(3d+3)
-- for an input of L terms (cost-gaussᶜ, through the opaque gaussBound
-- with its defining equation gaussBound-def, and cost-gaussᶜ-at at any
-- B ≥ n + m + 3), and at most 80 (n + m + 3)^(4d+3) when L ≤
-- (n + m + 1)^d (cost-gauss-small): polynomial in n + m for each fixed
-- order bound d.  For a Clifford circuit d = 2; for Clifford+R_k,
-- d = max(2, k) (proposition 2.14, corrected in PathSum.CRK.Circuit).
-- The bounds are upper bounds, not tight; that at most min(n, m)
-- rounds happen (each settles a wire, PathSum.Gauss.reified-removes)
-- is not used.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.  The conventions are PathSum.Cost's: the output
-- forms are the function view of a vector, read only in sweeps over
-- the wires charged one step per wire (the pivot's form is the one the
-- sweep returns, not read again); writing the constant of sol
-- (c ⊕ 0 ⊕ 0) is one step; a case on a value just computed -- the
-- pivot found or not, a form's constant, the refutation found or not,
-- the number of path variables -- is absorbed in the charged work
-- around it, as in PathSum.Cost.Rules and PathSum.Cost.Normalise; and
-- the refuting input is returned as the function point i, or the
-- all-zero input, named in no steps -- what the program computes is
-- the index i.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Gauss (M : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; ⊥; ⁅_⁆)
open import Data.Integer.Base using () renaming (_-_ to _-ℤ_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s; >-nonZero)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base using ([]; _∷_; lookup; zipWith; insertAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Cost
open import PathSum.Cost.Bound using
  (Bnd; _≤[_]_; unbound; ≤-1ᶜ; ≤-*ᶜ; ≤-+ᶜ; ≤-0ᶜ; ≤-weakenᶜ;
   lift-B; lift-LB; ^-pos; ^-mono; B*B; Bnd-small)
open import PathSum.Cost.Canon M using
  (canonᶜ; value-canonᶜ; canonical-length; Ordᵀ; cost-canonᶜ)
open import PathSum.Cost.Interpreter M using
  (StateK; initKᶜ; runKᶜ; interpKᶜ; SimK; simK; interpK-sim)
open import PathSum.Cost.Monomial using
  (varᶜ; value-varᶜ; cost-varᶜ; xorᵐᶜ; value-xorᵐᶜ; cost-xorᵐᶜ;
   singletonᶜ; value-singletonᶜ; cost-singletonᶜ; xorᶜ; value-xorᶜ;
   cost-xorᶜ; clear)
open import PathSum.Cost.Rules M using (Bᴿ)
open import PathSum.Cost.Split M using
  (restᶜ; value-restᶜ; ⟦rest⟧; rest-Ordᵀ; length-rest; dropForm;
   dropFormsᶜ; value-dropFormsᶜ; cost-restᶜ; cost-dropFormsᶜ)
open import PathSum.Cost.Subst M using
  (substᶜ; value-substᶜ; substᶜ-≈; substᶜ-Ordᵀ; substForm; substFormsᶜ;
   value-substFormsᶜ; cost-substᶜ; cost-substFormsᶜ; expand)
open import PathSum.CRK.Circuit M using (State; state; poly; sig)
open import PathSum.Gauss.Forms using
  (coefʸ; dropᴸ; elimᴸ; point; par-const-false; par-point; par-none;
   xor-solve)
open import PathSum.Linear using
  (Lin; valᴸ; varᴸ; _⊕ᴸ_; _⊕ᵐ_; par; par-⊕; par-⁅⁆)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (x[_]; y[_]; _≈[_]_)
  renaming (subst to psubst)
open import PathSum.Polynomial.Product using (≈-refl)
open import PathSum.Reorder using (_∖ʸ_)
open import PathSum.Size.Interpreter M using
  (Agree; agree; interpᴷ; interpᴷ-agree)
open import PathSum.Size.Sparse M using (⟦_⟧ˢ; Rep; rep; terms; forms)

import Data.Nat.Properties as ℕ
import PathSum.CRK.Circuit

private
  module K = PathSum.CRK.Circuit M

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- What a representation stands for, and the paper's criterion

-- R tracks the dense state st: its terms stand for the phase modulo
-- 2^M, coefficient by coefficient, and its forms are the state's.

Tracks : State n m → Rep n m → Set
Tracks st R = (poly st ≈[ pow M ] ⟦ terms R ⟧ˢ) × (∀ w → forms R w ≡ sig st w)

-- Every representation tracks the state it spells out.

stateᴿ : Rep n m → State n m
stateᴿ R = state ⟦ terms R ⟧ˢ (forms R)

tracks-stateᴿ : (R : Rep n m) → Tracks (stateᴿ R) R
tracks-stateᴿ R = ≈-refl {P = ⟦ terms R ⟧ˢ} , λ w → refl

-- With their numbers of path variables.

data Tracksᵖ {n : ℕ} : ∃ (Rep n) → ∃ (State n) → Set where
  tracks : ∀ {m} (R : Rep n m) (st : State n m) → Tracks st R →
           Tracksᵖ (m , R) (m , st)

-- The interpreter of PathSum.Cost.Interpreter tracks the dense run of
-- the circuit, whose path-sum ⟦ C ⟧ is by definition (PathSum.Gauss.
-- ⟦⟧-state): its terms stand for the phase and its forms are the
-- run's, through PathSum.Size.Interpreter's interpᴷ.

interpK-tracks : (C : K.Circuit n) →
                 Tracksᵖ (value (interpKᶜ C)) (K.run C K.init)
interpK-tracks {n} C = go (value (runKᶜ C (value (initKᶜ {n})))) (interpᴷ C)
  (K.run C K.init) (interpK-sim C) (interpᴷ-agree C)
  where
  go : (p : ∃ (StateK n)) (q : ∃ (Rep n)) (r : ∃ (State n)) →
       SimK p q → Agree q r →
       Tracksᵖ (proj₁ p , rep (proj₁ (proj₂ p)) (lookup (proj₂ (proj₂ p)))) r
  go _ _ _ (simK ts fs f h) (agree _ st h′) =
    tracks (rep ts (lookup fs)) st (h′ , h)

-- y solves f(x,y) = x; no y does; every x has a solution.

Solves : State n m → (Fin n → Bool) → (Fin m → Bool) → Set
Solves st x y = ∀ w → valᴸ (sig st w) x y ≡ x w

NoSolution : State n m → (Fin n → Bool) → Set
NoSolution st x = ∀ y → ¬ Solves st x y

Solvable : State n m → Set
Solvable st = ∀ x → ∃ λ y → Solves st x y


------------------------------------------------------------------------
-- The pivot

-- At one wire: its first path variable, if any, tagged with the wire
-- and its form.

tagᴹ : Fin n → Lin n m → Maybe (Fin m) → Maybe (Fin n × Fin m × Lin n m)
tagᴹ w f (just j) = just (w , j , f)
tagᴹ w f nothing  = nothing

pivotAtᶜ : (Fin n → Lin n m) → Fin n → Cost (Maybe (Fin n × Fin m × Lin n m))
pivotAtᶜ σ w = tagᴹ w (σ w) <$> firstᶜ (proj₂ (proj₂ (σ w)))

-- The first wire whose form has a path variable, in one sweep.

pivotᶜ : (Fin n → Lin n m) → Cost (Maybe (Fin n × Fin m × Lin n m))
pivotᶜ σ = firstJustᶜ (pivotAtᶜ σ)

private
  tag-just : (w′ : Fin n) (f′ : Lin n m) (r : Maybe (Fin m))
             {w : Fin n} {j : Fin m} {f : Lin n m} →
             tagᴹ w′ f′ r ≡ just (w , j , f) →
             (w′ ≡ w) × (r ≡ just j) × (f′ ≡ f)
  tag-just w′ f′ (just j′) refl = refl , refl , refl
  tag-just w′ f′ nothing   ()

  tag-nothing : (w′ : Fin n) (f′ : Lin n m) (r : Maybe (Fin m)) →
                tagᴹ w′ f′ r ≡ nothing → r ≡ nothing
  tag-nothing w′ f′ (just j) ()
  tag-nothing w′ f′ nothing  refl = refl

-- The pivot is a path variable of the form returned, which is the
-- form on its wire; and when there is none, no form has one.

pivotᶜ-just : (σ : Fin n → Lin n m) {w : Fin n} {j : Fin m}
              {f : Lin n m} → value (pivotᶜ σ) ≡ just (w , j , f) →
              (f ≡ σ w) × (coefʸ (σ w) j ≡ true)
pivotᶜ-just {n} {m} σ {w} {j} {f} eq = at (firstJustᶜ-just (pivotAtᶜ σ) eq)
  where
  by : ∀ w′ → (w′ ≡ w) × (value (firstᶜ (proj₂ (proj₂ (σ w′)))) ≡ just j) ×
              (σ w′ ≡ f) →
       (f ≡ σ w) × (coefʸ (σ w) j ≡ true)
  by w′ (refl , fj , e) = sym e , firstᶜ-just (proj₂ (proj₂ (σ w))) fj

  at : (∃ λ w′ → value (pivotAtᶜ σ w′) ≡ just (w , j , f)) →
       (f ≡ σ w) × (coefʸ (σ w) j ≡ true)
  at (w′ , e) =
    by w′ (tag-just w′ (σ w′) (value (firstᶜ (proj₂ (proj₂ (σ w′))))) e)

pivotᶜ-nothing : (σ : Fin n → Lin n m) → value (pivotᶜ σ) ≡ nothing →
                 ∀ w j → coefʸ (σ w) j ≡ false
pivotᶜ-nothing σ eq w = firstᶜ-nothing (proj₂ (proj₂ (σ w)))
  (tag-nothing w (σ w) (value (firstᶜ (proj₂ (proj₂ (σ w)))))
               (firstJustᶜ-nothing (pivotAtᶜ σ) eq w))


------------------------------------------------------------------------
-- One step

-- The value y_j must take for wire w to read x_w: f ⊕ x_w ⊕ y_j, for
-- the form f on wire w (PathSum.Gauss.sol).

solᴸ : Fin n → Fin m → Lin n m → Lin n m
solᴸ w j f = (f ⊕ᴸ varᴸ x[ w ]) ⊕ᴸ varᴸ y[ j ]

solᶜ : Fin n → Fin m → Lin n m → Cost (Lin n m)
solᶜ w j (c , S) = do
  X  ← varᶜ x[ w ]
  Y  ← varᶜ y[ j ]
  S₁ ← xorᵐᶜ S X
  S₂ ← xorᵐᶜ S₁ Y
  step ((c xor false) xor false , S₂)

value-solᶜ : (w : Fin n) (j : Fin m) (f : Lin n m) →
             value (solᶜ w j f) ≡ solᴸ w j f
value-solᶜ w j (c , S) = cong ((c xor false) xor false ,_)
  (trans (value-xorᵐᶜ (value (xorᵐᶜ S (value (varᶜ x[ w ]))))
                      (value (varᶜ y[ j ])))
         (cong₂ _⊕ᵐ_ (trans (value-xorᵐᶜ S (value (varᶜ x[ w ])))
                            (cong (S ⊕ᵐ_) (value-varᶜ x[ w ])))
                     (value-varᶜ y[ j ])))

-- Substitute the solution for y_j in the phase and in the forms, then
-- remove y_j.

stepᶜ : ℕ → Fin n → Fin (suc m) → Lin n (suc m) → Rep n (suc m) →
        Cost (Rep n m)
stepᶜ d w j f R = do
  s   ← solᶜ w j f
  ts₁ ← substᶜ d j s (terms R)
  ts₂ ← restᶜ j ts₁
  fs₁ ← substFormsᶜ j s (forms R)
  fs₂ ← dropFormsᶜ j fs₁
  pure (rep ts₂ fs₂)

-- The phase: P[y_j ← sol] with y_j removed, modulo 2^M and coefficient
-- by coefficient.

stepᶜ-terms : (d : ℕ) (w : Fin n) (j : Fin (suc m)) (f : Lin n (suc m))
              (R : Rep n (suc m)) → Ordᵀ d (terms R) →
              (psubst ⟦ terms R ⟧ˢ y[ j ] (proj₁ (solᴸ w j f))
                      (proj₂ (solᴸ w j f)) ∖ʸ j)
                ≈[ pow M ] ⟦ terms (value (stepᶜ d w j f R)) ⟧ˢ
stepᶜ-terms d w j f R ord = go (value (solᶜ w j f)) (value-solᶜ w j f)
  where
  c = proj₁ (solᴸ w j f)
  S = proj₂ (solᴸ w j f)

  go : ∀ s → s ≡ solᴸ w j f →
       (psubst ⟦ terms R ⟧ˢ y[ j ] c S ∖ʸ j)
         ≈[ pow M ] ⟦ value (restᶜ j (value (substᶜ d j s (terms R)))) ⟧ˢ
  go _ refl (α , β) =
    subst (λ z → pow M ∣ (psubst ⟦ terms R ⟧ˢ y[ j ] c S
                                 (α , insertAt β j false) -ℤ z))
          (sym (trans (cong (λ us → ⟦ us ⟧ˢ (α , β)) (value-restᶜ j ts₁))
                      (⟦rest⟧ j ts₁ α β)))
          (substᶜ-≈ d j c S (terms R) ord (α , insertAt β j false))
    where
    ts₁ = value (substᶜ d j (solᴸ w j f) (terms R))

-- The order bound is kept, term by term (lemma 2.13).

stepᶜ-Ordᵀ : (d : ℕ) (w : Fin n) (j : Fin (suc m)) (f : Lin n (suc m))
             (R : Rep n (suc m)) → Ordᵀ d (terms R) →
             Ordᵀ d (terms (value (stepᶜ d w j f R)))
stepᶜ-Ordᵀ d w j f R ord = go (value (solᶜ w j f)) (value-solᶜ w j f)
  where
  go : ∀ s → s ≡ solᴸ w j f →
       Ordᵀ d (value (restᶜ j (value (substᶜ d j s (terms R)))))
  go _ refl = subst (Ordᵀ d) (sym (value-restᶜ j ts₁))
    (rest-Ordᵀ d j ts₁ (substᶜ-Ordᵀ d j (proj₁ (solᴸ w j f))
                                    (proj₂ (solᴸ w j f)) (terms R) ord))
    where
    ts₁ = value (substᶜ d j (solᴸ w j f) (terms R))

-- The list a step leaves is the rest of a canonical one: at most
-- (n + m + 2)^d terms.

stepᶜ-length : (d : ℕ) (w : Fin n) (j : Fin (suc m)) (f : Lin n (suc m))
               (R : Rep n (suc m)) →
               length (terms (value (stepᶜ d w j f R))) ≤ suc (n + suc m) ^ d
stepᶜ-length {n} {m} d w j f R = ℕ.≤-trans
  (ℕ.≤-reflexive (cong length (value-restᶜ j ts₁)))
  (ℕ.≤-trans (length-rest j ts₁)
    (ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-substᶜ d j s (terms R))))
               (canonical-length {n} {suc m} d
                                 ⟦ expand d j s (terms R) ⟧ˢ)))
  where
  s   = value (solᶜ w j f)
  ts₁ = value (substᶜ d j s (terms R))

-- On a form, substituting the solution is PathSum.Gauss's row
-- operation: adding f ⊕ x_w where y_j occurs.  (Bit by bit: the y_j
-- of the form and the y_j of the solution cancel.)

private
  zip-⊥ : (p : Subset k) → zipWith _xor_ p ⊥ ≡ p
  zip-⊥ []      = refl
  zip-⊥ (b ∷ p) = cong₂ _∷_ (xor-identityʳ b) (zip-⊥ p)

  flip-head : ∀ u → false xor (u xor true) ≡ true xor u
  flip-head false = refl
  flip-head true  = refl

  clear-flip : (β u : Subset k) (j : Fin k) → lookup β j ≡ true →
               zipWith _xor_ (clear β j) (zipWith _xor_ u ⁅ j ⁆) ≡
               zipWith _xor_ β u
  clear-flip (true  ∷ β) (u ∷ us) zero    e =
    cong₂ _∷_ (flip-head u) (cong (zipWith _xor_ β) (zip-⊥ us))
  clear-flip (false ∷ β) (u ∷ us) zero    ()
  clear-flip (b     ∷ β) (u ∷ us) (suc j) e =
    cong₂ _∷_ (cong (b xor_) (xor-identityʳ u)) (clear-flip β us j e)

substForm-sol : (j : Fin m) (w : Fin n) (f g : Lin n m) →
                substForm j (solᴸ w j f) g ≡ elimᴸ j (f ⊕ᴸ varᴸ x[ w ]) g
substForm-sol j w (c , (αf , βf)) (c′ , (α , β)) = by (lookup β j) refl
  where
  by : ∀ b → lookup β j ≡ b →
       (if b then (c′ , (α , clear β j)) ⊕ᴸ solᴸ w j (c , (αf , βf))
        else (c′ , (α , β))) ≡
       (if b then (c′ , (α , β)) ⊕ᴸ ((c , (αf , βf)) ⊕ᴸ varᴸ x[ w ])
        else (c′ , (α , β)))
  by false _ = refl
  by true  e = cong₂ _,_ (cong (c′ xor_) (xor-identityʳ (c xor false)))
    (cong₂ _,_ (cong (zipWith _xor_ α) (zip-⊥ (zipWith _xor_ αf ⁅ w ⁆)))
               (clear-flip β (zipWith _xor_ βf ⊥) j e))

-- The forms: PathSum.Gauss.step's, literally.

stepᶜ-forms : (d : ℕ) (w : Fin n) (j : Fin (suc m)) (f : Lin n (suc m))
              (R : Rep n (suc m)) (v : Fin n) →
              forms (value (stepᶜ d w j f R)) v ≡
              dropᴸ j (elimᴸ j (f ⊕ᴸ varᴸ x[ w ]) (forms R v))
stepᶜ-forms d w j f R v = trans (value-dropFormsᶜ j fs₁ v)
  (cong (dropForm j)
    (trans (value-substFormsᶜ j s (forms R) v)
      (trans (cong (λ s′ → substForm j s′ (forms R v)) (value-solᶜ w j f))
             (substForm-sol j w f (forms R v)))))
  where
  s   = value (solᶜ w j f)
  fs₁ = value (substFormsᶜ j s (forms R))


------------------------------------------------------------------------
-- The finish

-- A form without path variables, read against x_w: the input that
-- refutes it, if any (PathSum.Gauss.Forms.verdict's case analysis).

pointᴹ : Maybe (Fin n) → Maybe (Fin n → Bool)
pointᴹ (just i) = just (point i)
pointᴹ nothing  = nothing

missInᶜ : Fin n → Subset n → Cost (Maybe (Fin n → Bool))
missInᶜ w α = do
  e  ← singletonᶜ w
  α′ ← xorᶜ α e
  pointᴹ <$> firstᶜ α′

missBranchᶜ : Fin n → Subset n → Bool → Cost (Maybe (Fin n → Bool))
missBranchᶜ w α true  = step (just (λ _ → false))
missBranchᶜ w α false = missInᶜ w α

missᶜ : Fin n → Lin n m → Cost (Maybe (Fin n → Bool))
missᶜ w (c , (α , β)) = missBranchᶜ w α c

-- The first wire that is refuted, in one sweep.

finishᶜ : (Fin n → Lin n m) → Cost (Maybe (Fin n → Bool))
finishᶜ σ = firstJustᶜ (λ w → missᶜ w (σ w))

private
  -- α ⊕ {w} reads α and x_w together.
  reads : (α : Subset n) (w : Fin n) (x : Fin n → Bool) →
          par (value (xorᶜ α (value (singletonᶜ w)))) x ≡ par α x xor x w
  reads α w x = trans
    (cong (λ p → par p x) (trans (value-xorᶜ α (value (singletonᶜ w)))
                                 (cong (zipWith _xor_ α) (value-singletonᶜ w))))
    (trans (par-⊕ α ⁅ w ⁆ x) (cong (par α x xor_) (par-⁅⁆ w x)))

  point-nothing : (r : Maybe (Fin n)) → pointᴹ r ≡ nothing → r ≡ nothing
  point-nothing (just i) ()
  point-nothing nothing  refl = refl

-- A refuting input makes the wire read ¬x_w on every path ...

missᶜ-just : (w : Fin n) (f : Lin n m) → (∀ j → coefʸ f j ≡ false) →
             ∀ {x} → value (missᶜ w f) ≡ just x →
             ∀ y → valᴸ f x y ≡ not (x w)
missᶜ-just w (true  , (α , β)) free refl y =
  cong not (cong₂ _xor_ (par-const-false α) (par-none β y free))
missᶜ-just w (false , (α , β)) free {x} eq y =
  by (value (firstᶜ α′)) x refl eq
  where
  α′ = value (xorᶜ α (value (singletonᶜ w)))

  by : ∀ r x′ → value (firstᶜ α′) ≡ r → pointᴹ r ≡ just x′ →
       valᴸ (false , (α , β)) x′ y ≡ not (x′ w)
  by (just i) _ e refl = trans
    (cong (par α (point i) xor_) (par-none β y free))
    (trans (xor-identityʳ (par α (point i)))
      (xor-solve (par α (point i)) (point i w) true
        (trans (sym (reads α w (point i)))
               (trans (par-point α′ i) (firstᶜ-just α′ e)))))
  by nothing  _ e ()

-- ... and when none is found the wire reads x_w on every path.

missᶜ-nothing : (w : Fin n) (f : Lin n m) → (∀ j → coefʸ f j ≡ false) →
                value (missᶜ w f) ≡ nothing →
                ∀ x y → valᴸ f x y ≡ x w
missᶜ-nothing w (true  , (α , β)) free ()
missᶜ-nothing w (false , (α , β)) free eq x y = trans
  (cong (par α x xor_) (par-none β y free))
  (trans (xor-identityʳ (par α x))
    (xor-solve (par α x) (x w) false
      (trans (sym (reads α w x))
        (par-none α′ x (firstᶜ-nothing α′
          (point-nothing (value (firstᶜ α′)) eq))))))
  where
  α′ = value (xorᶜ α (value (singletonᶜ w)))

finishᶜ-just : (σ : Fin n → Lin n m) → (∀ w j → coefʸ (σ w) j ≡ false) →
               ∀ {x} → value (finishᶜ σ) ≡ just x →
               ∃ λ w → ∀ y → valᴸ (σ w) x y ≡ not (x w)
finishᶜ-just σ free {x} eq = at (firstJustᶜ-just (λ w → missᶜ w (σ w)) eq)
  where
  at : (∃ λ w → value (missᶜ w (σ w)) ≡ just x) →
       ∃ λ w → ∀ y → valᴸ (σ w) x y ≡ not (x w)
  at (w , e) = w , missᶜ-just w (σ w) (free w) e

finishᶜ-nothing : (σ : Fin n → Lin n m) → (∀ w j → coefʸ (σ w) j ≡ false) →
                  value (finishᶜ σ) ≡ nothing →
                  ∀ w x y → valᴸ (σ w) x y ≡ x w
finishᶜ-nothing σ free eq w = missᶜ-nothing w (σ w) (free w)
  (firstJustᶜ-nothing (λ v → missᶜ v (σ v)) eq w)


------------------------------------------------------------------------
-- The elimination

-- What it returns: an input that refutes, or the representation left
-- once every output reads its input.

data Outcome (n : ℕ) : Set where
  refutes : (Fin n → Bool) → Outcome n
  reifies : {m : ℕ} → Rep n m → Outcome n

finishBy : Rep n m → Maybe (Fin n → Bool) → Outcome n
finishBy R (just x) = refutes x
finishBy R nothing  = reifies R

-- Pivot, step, repeat; by recursion on the number of path variables.

mutual
  elimᶜ : ℕ → Rep n m → Cost (Outcome n)
  elimᶜ d R = pivotᶜ (forms R) >>= elimBy d R

  elimBy : ℕ → Rep n m → Maybe (Fin n × Fin m × Lin n m) → Cost (Outcome n)
  elimBy             d R nothing            =
    finishBy R <$> finishᶜ (forms R)
  elimBy {m = zero}  d R (just (w , () , f))
  elimBy {m = suc m} d R (just (w , j , f)) =
    stepᶜ d w j f R >>= λ R′ → elimᶜ d R′

-- Canonicalise first.

gaussᶜ : ℕ → Rep n m → Cost (Outcome n)
gaussᶜ d R = canonᶜ d (terms R) >>= λ ts → elimᶜ d (rep ts (forms R))

-- What a reification leaves is small: no more path variables than
-- there were, and at most (n + m + 2)^d terms -- the canonical list,
-- or the rest of one.

private
  finish-shape : (R : Rep n m) {X : ℕ} → length (terms R) ≤ X →
                 ∀ r {m₁} {R₁ : Rep n m₁} → finishBy R r ≡ reifies R₁ →
                 (m₁ ≤ m) × (length (terms R₁) ≤ X)
  finish-shape R len (just x) ()
  finish-shape R len nothing  refl = ℕ.≤-refl , len

elimᶜ-shape : (d : ℕ) (R : Rep n m) →
              length (terms R) ≤ suc (suc (n + m)) ^ d →
              ∀ {m′} {R′ : Rep n m′} → value (elimᶜ d R) ≡ reifies R′ →
              (m′ ≤ m) × (length (terms R′) ≤ suc (suc (n + m)) ^ d)
elimᶜ-shape {n} {zero} d R len eq = by (value (pivotᶜ (forms R))) eq
  where
  by : (p : Maybe (Fin n × Fin 0 × Lin n 0)) {m₁ : ℕ} {R₁ : Rep n m₁} →
       value (elimBy d R p) ≡ reifies R₁ →
       (m₁ ≤ 0) × (length (terms R₁) ≤ suc (suc (n + 0)) ^ d)
  by nothing             e = finish-shape R len (value (finishᶜ (forms R))) e
  by (just (w , () , f)) e
elimᶜ-shape {n} {suc m} d R len eq = by (value (pivotᶜ (forms R))) eq
  where
  by : (p : Maybe (Fin n × Fin (suc m) × Lin n (suc m)))
       {m₁ : ℕ} {R₁ : Rep n m₁} →
       value (elimBy d R p) ≡ reifies R₁ →
       (m₁ ≤ suc m) × (length (terms R₁) ≤ suc (suc (n + suc m)) ^ d)
  by nothing             e = finish-shape R len (value (finishᶜ (forms R))) e
  by (just (w , j , f)) e =
    ℕ.m≤n⇒m≤1+n (proj₁ ih) ,
    ℕ.≤-trans (proj₂ ih)
      (ℕ.^-monoˡ-≤ d (s≤s (s≤s (ℕ.+-monoʳ-≤ n (ℕ.n≤1+n m)))))
    where
    ih = elimᶜ-shape d (value (stepᶜ d w j f R))
           (ℕ.≤-trans (stepᶜ-length d w j f R)
             (ℕ.≤-reflexive (cong (λ z → suc z ^ d) (ℕ.+-suc n m))))
           e

gaussᶜ-shape : (d : ℕ) (R : Rep n m) →
               ∀ {m′} {R′ : Rep n m′} → value (gaussᶜ d R) ≡ reifies R′ →
               (m′ ≤ m) × (length (terms R′) ≤ suc (suc (n + m)) ^ d)
gaussᶜ-shape {n} {m} d R eq = elimᶜ-shape d (rep ts (forms R))
  (ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-canonᶜ d (terms R))))
    (ℕ.≤-trans (canonical-length {n} {m} d ⟦ terms R ⟧ˢ)
               (ℕ.^-monoˡ-≤ d (ℕ.n≤1+n _))))
  eq
  where
  ts = value (canonᶜ d (terms R))


------------------------------------------------------------------------
-- Costs of the parts

cost-pivotᶜ : (σ : Fin n → Lin n m) → cost (pivotᶜ σ) ≤ n * suc m
cost-pivotᶜ σ = cost-firstJustᶜ (pivotAtᶜ σ)
  (λ w → cost-firstᶜ (proj₂ (proj₂ (σ w))))

cost-solᶜ : (w : Fin n) (j : Fin m) (f : Lin n m) →
            cost (solᶜ w j f) ≤ 4 * (n + m) + 1
cost-solᶜ {n} {m} w j (c , S) = ℕ.≤-trans
  (ℕ.+-mono-≤ (cost-varᶜ {n} {m} x[ w ]) (ℕ.+-mono-≤ (cost-varᶜ {n} {m} y[ j ])
    (ℕ.+-mono-≤ (cost-xorᵐᶜ S X) (ℕ.+-monoˡ-≤ 1 (cost-xorᵐᶜ S₁ Y)))))
  (ℕ.≤-reflexive (four (n + m)))
  where
  X  = value (varᶜ {n} {m} x[ w ])
  Y  = value (varᶜ {n} {m} y[ j ])
  S₁ = value (xorᵐᶜ S X)

  four : ∀ N → N + (N + (N + (N + 1))) ≡ 4 * N + 1
  four = solve 1 (λ N → N :+ (N :+ (N :+ (N :+ con 1))) :=
                        con 4 :* N :+ con 1) refl

cost-missᶜ : (w : Fin n) (f : Lin n m) →
             cost (missᶜ w f) ≤ suc (n + (n + n))
cost-missᶜ {n} w (true  , (α , β)) = s≤s z≤n
cost-missᶜ {n} w (false , (α , β)) = ℕ.≤-trans
  (ℕ.+-mono-≤ (cost-singletonᶜ w)
    (ℕ.+-mono-≤ (cost-xorᶜ α (value (singletonᶜ w)))
                (cost-firstᶜ (value (xorᶜ α (value (singletonᶜ w)))))))
  (ℕ.n≤1+n (n + (n + n)))

cost-finishᶜ : (σ : Fin n → Lin n m) →
               cost (finishᶜ σ) ≤ n * suc (suc (n + (n + n)))
cost-finishᶜ σ = cost-firstJustᶜ (λ w → missᶜ w (σ w))
  (λ w → cost-missᶜ w (σ w))

-- A round at n inputs and m + 1 path variables, with L terms: at most
-- 34 (L + 1) B^(2d+2), B = n + m + 3, the substitution dominating.

private
  module Sizes (n m : ℕ) where

    B : ℕ
    B = Bᴿ n m

    1≤B : 1 ≤ B
    1≤B = s≤s z≤n

    n≤B : n ≤ B
    n≤B = ℕ.≤-trans (ℕ.m≤m+n n m) (ℕ.m≤n+m (n + m) 3)

    m3≤B : 3 + m ≤ B
    m3≤B = ℕ.+-monoʳ-≤ 3 (ℕ.m≤n+m m n)

    sB₀≡B : suc (suc (n + suc m)) ≡ B
    sB₀≡B = cong (λ z → suc (suc z)) (ℕ.+-suc n m)

    B₀≤B : suc (n + suc m) ≤ B
    B₀≤B = ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.≤-reflexive sB₀≡B)

    N≤B : n + suc m ≤ B
    N≤B = ℕ.≤-trans (ℕ.n≤1+n _) B₀≤B

    B≤B¹ : B ≤ B ^ 1
    B≤B¹ = ℕ.≤-reflexive (sym (ℕ.*-identityʳ B))

    sq≤ : ∀ {a b} → a ≤ B → b ≤ B → a * b ≤ B ^ 2
    sq≤ a≤ b≤ = ℕ.≤-trans (ℕ.*-mono-≤ a≤ b≤) (ℕ.≤-reflexive (B*B B))

cost-stepᶜ : (d : ℕ) (w : Fin n) (j : Fin (suc m)) (f : Lin n (suc m))
             (R : Rep n (suc m)) →
             cost (stepᶜ d w j f R) ≤
             33 * Bnd (length (terms R)) (Bᴿ n m) (2 + (d + d))
cost-stepᶜ {n} {m} d w j f R = unbound
  (≤-+ᶜ sol≤ (≤-+ᶜ subst≤ (≤-+ᶜ rest≤ (≤-+ᶜ sforms≤ (≤-+ᶜ dforms≤ ≤-0ᶜ)))))
  where
  open Sizes n m

  L = length (terms R)
  e = 2 + (d + d)
  X = Bnd L B e
  B₀ = suc (n + suc m)

  s   = value (solᶜ w j f)
  ts₁ = value (substᶜ d j s (terms R))
  fs₁ = value (substFormsᶜ j s (forms R))

  1≤e : 1 ≤ e
  1≤e = s≤s z≤n

  2≤e : 2 ≤ e
  2≤e = ℕ.m≤m+n 2 (d + d)

  d1≤e : suc d ≤ e
  d1≤e = s≤s (ℕ.≤-trans (ℕ.m≤m+n d d) (ℕ.n≤1+n (d + d)))

  dd1≤e : suc (d + d) ≤ e
  dd1≤e = ℕ.n≤1+n (suc (d + d))

  -- The solution: four sweeps of n + m + 1 bits.
  sol≤ : cost (solᶜ w j f) ≤[ 5 ] X
  sol≤ = ≤-weakenᶜ
    (ℕ.≤-trans (cost-solᶜ w j f)
      (ℕ.≤-trans (ℕ.+-mono-≤ (ℕ.*-monoʳ-≤ 4 N≤B) 1≤B)
        (ℕ.≤-reflexive (solve 1 (λ B → con 4 :* B :+ B := con 5 :* B)
                                refl B))))
    (≤-*ᶜ 5 (lift-B L B 1 e 1≤B 1≤e B≤B¹))

  -- The substitution: [HH]'s, over the m + 1 path variables.
  fifteen : ∀ Y → Y + (13 * Y + Y) ≡ 15 * Y
  fifteen = solve 1 (λ Y → Y :+ (con 13 :* Y :+ Y) := con 15 :* Y) refl

  per≤ : suc (13 * (B * B ^ d) + B ^ d) ≤ 15 * (B * B ^ d)
  per≤ = ℕ.≤-trans
    (ℕ.+-mono-≤ (^-pos {k = suc d} 1≤B)
                (ℕ.+-monoʳ-≤ (13 * (B * B ^ d))
                  (^-mono {k = d} {e = suc d} 1≤B (ℕ.n≤1+n d))))
    (ℕ.≤-reflexive (fifteen (B * B ^ d)))

  exp≤ : L * suc (13 * (B₀ * B₀ ^ d) + B₀ ^ d) ≤[ 15 ] X
  exp≤ = ≤-weakenᶜ
    (ℕ.≤-trans (ℕ.*-monoʳ-≤ L
      (s≤s (ℕ.+-mono-≤ (ℕ.*-monoʳ-≤ 13 (ℕ.*-mono-≤ B₀≤B (ℕ.^-monoˡ-≤ d B₀≤B)))
                       (ℕ.^-monoˡ-≤ d B₀≤B))))
      (ℕ.≤-trans (ℕ.*-monoʳ-≤ L per≤)
        (ℕ.≤-reflexive (comm L (B * B ^ d)))))
    (≤-*ᶜ 15 (lift-LB L B (suc d) e 1≤B d1≤e ℕ.≤-refl))
    where
    comm : ∀ L Y → L * (15 * Y) ≡ 15 * (L * Y)
    comm = solve 2 (λ L Y → L :* (con 15 :* Y) := con 15 :* (L :* Y)) refl

  sq-split : ∀ L B P → (L * P + 5) * B * P ≡ L * (B * (P * P)) + 5 * (B * P)
  sq-split = solve 3 (λ L B P → (L :* P :+ con 5) :* B :* P :=
                                L :* (B :* (P :* P)) :+ con 5 :* (B :* P)) refl

  can≤ : (L * B₀ ^ d + 5) * suc B₀ * B₀ ^ d ≤[ 6 ] X
  can≤ = ≤-weakenᶜ
    (ℕ.≤-trans (ℕ.*-mono-≤ (ℕ.*-mono-≤ (ℕ.+-monoˡ-≤ 5
                              (ℕ.*-monoʳ-≤ L (ℕ.^-monoˡ-≤ d B₀≤B)))
                            (ℕ.≤-reflexive sB₀≡B))
                           (ℕ.^-monoˡ-≤ d B₀≤B))
      (ℕ.≤-reflexive (trans (sq-split L B (B ^ d))
        (cong (λ z → L * (B * z) + 5 * (B * B ^ d))
              (sym (ℕ.^-distribˡ-+-* B d d))))))
    (≤-+ᶜ (≤-1ᶜ (lift-LB L B (suc (d + d)) e 1≤B dd1≤e ℕ.≤-refl))
          (≤-*ᶜ 5 (lift-B L B (suc d) e 1≤B d1≤e ℕ.≤-refl)))

  subst≤ : cost (substᶜ d j s (terms R)) ≤[ 21 ] X
  subst≤ = ≤-weakenᶜ (cost-substᶜ d j s (terms R)) (≤-+ᶜ exp≤ can≤)

  -- Removing y_j: a canonical list over n + m + 1 variables, at most
  -- B^d terms, m + 3 steps each, twice.
  lenT : length ts₁ ≤ B ^ d
  lenT = ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-substᶜ d j s (terms R))))
    (ℕ.≤-trans (canonical-length {n} {suc m} d ⟦ expand d j s (terms R) ⟧ˢ)
               (ℕ.^-monoˡ-≤ d B₀≤B))

  rest≤ : cost (restᶜ j ts₁) ≤[ 2 ] X
  rest≤ = ≤-weakenᶜ
    (ℕ.≤-trans (cost-restᶜ j ts₁)
      (ℕ.*-monoʳ-≤ 2 (ℕ.*-mono-≤ lenT m3≤B)))
    (≤-*ᶜ 2 (lift-B L B (suc d) e 1≤B d1≤e
                    (ℕ.≤-reflexive (ℕ.*-comm (B ^ d) B))))

  -- The forms: a sweep over the wires, at most 3 (n + m + 2) + 1 steps
  -- each, and the removal.
  four : ∀ B → B * suc (3 * B) ≡ B + 3 * (B * B)
  four = solve 1 (λ B → B :* (con 1 :+ con 3 :* B) := B :+ con 3 :* (B :* B))
                 refl

  sforms≤ : cost (substFormsᶜ j s (forms R)) ≤[ 4 ] X
  sforms≤ = ≤-weakenᶜ
    (ℕ.≤-trans (cost-substFormsᶜ j s (forms R))
      (ℕ.≤-trans (ℕ.*-mono-≤ n≤B (s≤s (ℕ.*-monoʳ-≤ 3 B₀≤B)))
        (ℕ.≤-trans (ℕ.≤-reflexive (four B))
          (ℕ.≤-trans (ℕ.+-monoˡ-≤ (3 * (B * B))
                        (ℕ.m≤m*n B B {{>-nonZero 1≤B}}))
            (ℕ.≤-reflexive (trans (solve 1 (λ Y → Y :+ con 3 :* Y :=
                                              con 4 :* Y) refl (B * B))
                                  (cong (4 *_) (B*B B))))))))
    (≤-*ᶜ 4 (lift-B L B 2 e 1≤B 2≤e ℕ.≤-refl))

  dforms≤ : cost (dropFormsᶜ j fs₁) ≤[ 1 ] X
  dforms≤ = ≤-1ᶜ (lift-B L B 2 e 1≤B 2≤e
    (ℕ.≤-trans (cost-dropFormsᶜ j fs₁)
      (sq≤ n≤B (ℕ.≤-trans (ℕ.n≤1+n (suc (suc m))) m3≤B))))

-- The pivot at m + 1 path variables.

cost-pivot-round : (σ : Fin n → Lin n (suc m)) (L e : ℕ) → 2 ≤ e →
                   cost (pivotᶜ σ) ≤ 1 * Bnd L (Bᴿ n m) e
cost-pivot-round {n} {m} σ L e 2≤e = unbound (≤-1ᶜ (lift-B L B 2 e 1≤B 2≤e
  (ℕ.≤-trans (cost-pivotᶜ σ)
    (sq≤ n≤B (ℕ.≤-trans (ℕ.n≤1+n (suc (suc m))) m3≤B)))))
  where
  open Sizes n m


------------------------------------------------------------------------
-- The cost of the elimination

-- A round costs at most 68 B^(3d+2) when the list has at most B^d
-- terms; the finish, n (3n + 3).

roundBound : ℕ → ℕ → ℕ → ℕ
roundBound n m d = 68 * Bᴿ n m ^ (d + (2 + (d + d)))

finishCost : ℕ → ℕ
finishCost n = n * suc (suc (n + (n + n)))

elimBound : ℕ → ℕ → ℕ → ℕ
elimBound n zero    d = n * 1 + finishCost n
elimBound n (suc m) d = roundBound n m d + elimBound n m d

private
  finish≤ : ∀ n m d → finishCost n ≤ elimBound n m d
  finish≤ n zero    d = ℕ.m≤n+m (finishCost n) (n * 1)
  finish≤ n (suc m) d =
    ℕ.≤-trans (finish≤ n m d) (ℕ.m≤n+m (elimBound n m d) (roundBound n m d))

-- On a list with at most (n + m + 2)^d terms -- a canonical one, or one
-- a step leaves -- the loop costs at most elimBound n m d.

cost-elimᶜ : (d : ℕ) (R : Rep n m) →
             length (terms R) ≤ suc (suc (n + m)) ^ d →
             cost (elimᶜ d R) ≤ elimBound n m d
cost-elimᶜ {n} {zero} d R len =
  ℕ.+-mono-≤ (cost-pivotᶜ (forms R)) (by (value (pivotᶜ (forms R))))
  where
  by : (p : Maybe (Fin n × Fin 0 × Lin n 0)) →
       cost (elimBy d R p) ≤ finishCost n
  by (just (w , () , f))
  by nothing = cost-finishᶜ (forms R)
cost-elimᶜ {n} {suc m} d R len = ℕ.≤-trans
  (ℕ.+-mono-≤ (cost-pivot-round (forms R) L e (ℕ.m≤m+n 2 (d + d)))
              (by (value (pivotᶜ (forms R)))))
  (ℕ.≤-trans (ℕ.≤-reflexive (shuffle X (elimBound n m d)))
    (ℕ.+-monoˡ-≤ (elimBound n m d)
      (ℕ.≤-trans (ℕ.*-monoʳ-≤ 34 small)
        (ℕ.≤-reflexive (sym (ℕ.*-assoc 34 2 (B ^ (d + e))))))))
  where
  open Sizes n m

  L = length (terms R)
  e = 2 + (d + d)
  X = Bnd L B e

  shuffle : ∀ X E → 1 * X + (33 * X + E) ≡ 34 * X + E
  shuffle = solve 2 (λ X E → con 1 :* X :+ (con 33 :* X :+ E) :=
                             con 34 :* X :+ E) refl

  small : X ≤ 2 * B ^ (d + e)
  small = Bnd-small {B = B} {e = e} {L = L} {d = d} 1≤B
    (ℕ.≤-trans len (ℕ.≤-reflexive (cong (_^ d) sB₀≡B)))

  by : (p : Maybe (Fin n × Fin (suc m) × Lin n (suc m))) →
       cost (elimBy d R p) ≤ 33 * X + elimBound n m d
  by (just (w , j , f)) = ℕ.+-mono-≤ (cost-stepᶜ d w j f R)
    (cost-elimᶜ d (value (stepᶜ d w j f R))
      (ℕ.≤-trans (stepᶜ-length d w j f R)
        (ℕ.≤-reflexive (cong (λ z → suc z ^ d) (ℕ.+-suc n m)))))
  by nothing = ℕ.≤-trans (cost-finishᶜ (forms R))
    (ℕ.≤-trans (finish≤ n m d) (ℕ.m≤n+m (elimBound n m d) (33 * X)))

-- In closed form: at most (68 m + 6) (n + m + 3)^(3d+2).

private
  -- The exponent, d + (2 + 2d).
  Eˣ : ℕ → ℕ
  Eˣ d = d + (2 + (d + d))

  2≤Eˣ : ∀ d → 2 ≤ Eˣ d
  2≤Eˣ d = ℕ.≤-trans (ℕ.m≤m+n 2 (d + d)) (ℕ.m≤n+m (2 + (d + d)) d)

  -- The finish, at a variable B ≥ n: n (3n + 3) ≤ 6 B².
  finish-B : ∀ {n B} → n ≤ B → 1 ≤ B → n * 1 + finishCost n ≤ 6 * (B * B)
  finish-B {n} {B} n≤B 1≤B = ℕ.≤-trans
    (ℕ.+-mono-≤ (ℕ.*-monoˡ-≤ 1 n≤B)
      (ℕ.*-mono-≤ n≤B (s≤s (s≤s (ℕ.+-mono-≤ n≤B (ℕ.+-mono-≤ n≤B n≤B))))))
    (ℕ.≤-trans (ℕ.≤-reflexive (shape B))
      (ℕ.≤-trans (ℕ.+-monoʳ-≤ (3 * (B * B))
                   (ℕ.*-monoʳ-≤ 3 (ℕ.m≤m*n B B {{>-nonZero 1≤B}})))
                 (ℕ.≤-reflexive (six (B * B)))))
    where
    shape : ∀ B → B * 1 + B * suc (suc (B + (B + B))) ≡
                  3 * (B * B) + 3 * B
    shape = solve 1 (λ B → B :* con 1 :+ B :* (con 2 :+ (B :+ (B :+ B))) :=
                           con 3 :* (B :* B) :+ con 3 :* B) refl

    six : ∀ Y → 3 * Y + 3 * Y ≡ 6 * Y
    six = solve 1 (λ Y → con 3 :* Y :+ con 3 :* Y := con 6 :* Y) refl

elimBound-≤ : ∀ n m d →
              elimBound n m d ≤ (68 * m + 6) * Bᴿ n m ^ (d + (2 + (d + d)))
elimBound-≤ n zero d = ℕ.≤-trans
  (finish-B {n = n} {B = Bᴿ n 0}
    (ℕ.≤-trans (ℕ.m≤m+n n 0) (ℕ.m≤n+m (n + 0) 3)) (s≤s z≤n))
  (ℕ.*-monoʳ-≤ 6 (ℕ.≤-trans (ℕ.≤-reflexive (B*B (Bᴿ n 0)))
                            (^-mono {B = Bᴿ n 0} {k = 2} {e = Eˣ d}
                                    (s≤s z≤n) (2≤Eˣ d))))
elimBound-≤ n (suc m) d = ℕ.≤-trans
  (ℕ.+-monoʳ-≤ (roundBound n m d) (elimBound-≤ n m d))
  (ℕ.≤-trans (ℕ.≤-reflexive (join m (Bᴿ n m ^ Eˣ d)))
    (ℕ.*-monoʳ-≤ (68 * suc m + 6)
      (ℕ.^-monoˡ-≤ (Eˣ d) (ℕ.+-monoʳ-≤ 3 (ℕ.+-monoʳ-≤ n (ℕ.n≤1+n m))))))
  where
  join : ∀ m P → 68 * P + (68 * m + 6) * P ≡ (68 * suc m + 6) * P
  join = solve 2 (λ m P → con 68 :* P :+ (con 68 :* m :+ con 6) :* P :=
                          (con 68 :* (con 1 :+ m) :+ con 6) :* P) refl


------------------------------------------------------------------------
-- The cost of the whole

-- The canonicalisation and the loop: at most (L + 79) B^(3d+3) for
-- any B ≥ n + m + 3.

cost-gaussᶜ-at : (d : ℕ) (R : Rep n m) (B : ℕ) → 3 + (n + m) ≤ B →
                 cost (gaussᶜ d R) ≤
                 (length (terms R) + 79) * B ^ (3 * d + 3)
cost-gaussᶜ-at {n} {m} d R B le = ℕ.≤-trans
  (ℕ.+-mono-≤ canon≤ loop≤)
  (ℕ.≤-reflexive (join L (B ^ (3 * d + 3))))
  where
  L = length (terms R)
  N = n + m
  ts = value (canonᶜ d (terms R))
  P = B ^ (3 * d + 3)

  1≤B : 1 ≤ B
  1≤B = ℕ.≤-trans (s≤s z≤n) le

  m≤B : m ≤ B
  m≤B = ℕ.≤-trans (ℕ.m≤n+m m n) (ℕ.≤-trans (ℕ.m≤n+m N 3) le)

  1N≤B : suc N ≤ B
  1N≤B = ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.≤-trans (ℕ.n≤1+n _) le)

  2N≤B : suc (suc N) ≤ B
  2N≤B = ℕ.≤-trans (ℕ.n≤1+n _) le

  e≡ : suc (d + (2 + (d + d))) ≡ 3 * d + 3
  e≡ = solve 1 (λ d → con 1 :+ (d :+ (con 2 :+ (d :+ d))) :=
                      con 3 :* d :+ con 3) refl d

  d1≤ : suc d ≤ 3 * d + 3
  d1≤ = ℕ.≤-trans (ℕ.m≤m+n (suc d) (2 * d + 2))
    (ℕ.≤-reflexive (solve 1 (λ d → (con 1 :+ d) :+ (con 2 :* d :+ con 2) :=
                                   con 3 :* d :+ con 3) refl d))

  canon≤ : cost (canonᶜ d (terms R)) ≤ (L + 5) * P
  canon≤ = ℕ.≤-trans (cost-canonᶜ d (terms R))
    (ℕ.≤-trans (ℕ.*-mono-≤ (ℕ.*-monoʳ-≤ (L + 5) 2N≤B) (ℕ.^-monoˡ-≤ d 1N≤B))
      (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.*-assoc (L + 5) B (B ^ d)))
                 (ℕ.*-monoʳ-≤ (L + 5) (^-mono {k = suc d} 1≤B d1≤))))

  lents : length ts ≤ suc (suc N) ^ d
  lents = ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-canonᶜ d (terms R))))
    (ℕ.≤-trans (canonical-length {n} {m} d ⟦ terms R ⟧ˢ)
               (ℕ.^-monoˡ-≤ d (ℕ.n≤1+n _)))

  loop≤ : cost (elimᶜ d (rep ts (forms R))) ≤ 74 * P
  loop≤ = ℕ.≤-trans (cost-elimᶜ d (rep ts (forms R)) lents)
    (ℕ.≤-trans (elimBound-≤ n m d)
      (ℕ.≤-trans (ℕ.*-mono-≤ (ℕ.+-monoˡ-≤ 6 (ℕ.*-monoʳ-≤ 68 m≤B))
                             (ℕ.^-monoˡ-≤ (Eˣ d) le))
        (ℕ.≤-trans (ℕ.*-monoˡ-≤ (B ^ Eˣ d)
                     (ℕ.+-monoʳ-≤ (68 * B) (ℕ.*-monoʳ-≤ 6 (ℕ.≤-trans
                       (s≤s z≤n) le))))
          (ℕ.≤-reflexive (trans (spread B (B ^ Eˣ d))
                                (cong (74 *_) (cong (B ^_) e≡)))))))
    where
    spread : ∀ B Y → (68 * B + 6 * B) * Y ≡ 74 * (B * Y)
    spread = solve 2 (λ B Y → (con 68 :* B :+ con 6 :* B) :* Y :=
                              con 74 :* (B :* Y)) refl

  join : ∀ L P → (L + 5) * P + 74 * P ≡ (L + 79) * P
  join = solve 2 (λ L P → (L :+ con 5) :* P :+ con 74 :* P :=
                          (L :+ con 79) :* P) refl

-- The bound, opaque: Agda never unfolds a power of a numeral-headed
-- base, which it would do into unary numbers once d is a numeral.  Its
-- defining equation is gaussBound-def.

opaque
  gaussBound : ℕ → ℕ → ℕ → ℕ → ℕ
  gaussBound n m d L = (L + 79) * (3 + (n + m)) ^ (3 * d + 3)

  gaussBound-def : ∀ n m d L →
                   gaussBound n m d L ≡ (L + 79) * (3 + (n + m)) ^ (3 * d + 3)
  gaussBound-def n m d L = refl

cost-gaussᶜ : (d : ℕ) (R : Rep n m) →
              cost (gaussᶜ d R) ≤ gaussBound n m d (length (terms R))
cost-gaussᶜ {n} {m} d R = subst (cost (gaussᶜ d R) ≤_)
  (sym (gaussBound-def n m d (length (terms R))))
  (cost-gaussᶜ-at d R (3 + (n + m)) ℕ.≤-refl)

-- With at most (n + m + 1)^d terms -- a canonical list, or one that
-- PathSum.Size builds at degree d -- a polynomial in n and m alone.

cost-gauss-small : (d : ℕ) (R : Rep n m) →
                   length (terms R) ≤ suc (n + m) ^ d →
                   cost (gaussᶜ d R) ≤ 80 * (3 + (n + m)) ^ (4 * d + 3)
cost-gauss-small {n} {m} d R L≤ = ℕ.≤-trans
  (cost-gaussᶜ-at d R B ℕ.≤-refl)
  (ℕ.≤-trans (ℕ.*-monoˡ-≤ (B ^ (3 * d + 3)) L79≤)
    (ℕ.≤-reflexive (trans (ℕ.*-assoc 80 (B ^ d) (B ^ (3 * d + 3)))
      (cong (80 *_) (trans (sym (ℕ.^-distribˡ-+-* B d (3 * d + 3)))
        (cong (B ^_) (solve 1 (λ d → d :+ (con 3 :* d :+ con 3) :=
                                     con 4 :* d :+ con 3) refl d)))))))
  where
  B = 3 + (n + m)

  L79≤ : length (terms R) + 79 ≤ 80 * B ^ d
  L79≤ = ℕ.≤-trans
    (ℕ.+-mono-≤ (ℕ.≤-trans L≤ (ℕ.^-monoˡ-≤ d (ℕ.≤-trans (ℕ.n≤1+n _)
                                                        (ℕ.n≤1+n _))))
                (ℕ.*-monoʳ-≤ 79 (ℕ.m^n>0 B d)))
    (ℕ.≤-reflexive (solve 1 (λ Y → Y :+ con 79 :* Y := con 80 :* Y) refl
                            (B ^ d)))
