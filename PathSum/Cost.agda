------------------------------------------------------------------------
-- Presentations of groups
--
-- A cost-counting monad, and the plan for the paper's time bounds
-- (Amy, QPL 2018, corollary 2.15, proposition 3.2, corollary 4.4)
--
-- The paper makes three claims about running time: the path-sum of a
-- Clifford+R_k circuit "can be computed in polynomial time"
-- (corollary 2.15); "each rewrite rule can be matched against in
-- polynomial time, hence every path-sum reduces to a normal form in
-- polynomial time", "for an n-qubit path-sum ... polynomial in n and
-- m" (proposition 3.2); and the reductions give "a complete,
-- polynomial-time procedure for determining equivalence of Clifford
-- group circuits" (the abstract, section 4, corollary 4.4).  Running
-- time is a property of a machine, and no machine is formalised
-- here: no Turing machine, no RAM, no semantics of Agda's own
-- evaluation.  Nothing is claimed about Turing machines or about
-- complexity classes.  What is formalised instead is an explicit cost
-- model, and it is a cost model, not a machine model:
--
--  * every algorithm is written once, as a program in the monad Cost
--    below, which computes a value and a count of steps together, so
--    that the count cannot drift from the program it counts;
--  * a primitive step costs one: an arithmetic operation or a
--    comparison on numbers below 2^M (the coefficients of a phase,
--    Fin (2^M), M the precision), an operation on Booleans, a
--    comparison of Fin indices, and visiting one cell of a list or of
--    a vector (so a bit vector of length n costs n to compare, and a
--    monomial in n + m variables n + m); also one step each, as the
--    modules using them say: writing a constant coefficient (¼, ½, ⅛,
--    ±2^(M−k) modulo 2^M), reading or updating a counter (the
--    normalisation, the number of Hadamards or of path variables --
--    unbounded naturals, a word-RAM convention), and one small natural
--    operation on a degree;
--  * a representation's output forms are kept as the function view
--    lookup of a vector of forms (PathSum.Size.Sparse's
--    Fin n → Lin n m), built for free from the vector, and every
--    program reads them only
--    in an in-order sweep over the wires charged one step per wire plus
--    the work on each form -- the cost of traversing the vector itself;
--  * everything else is built from those with the monad's bind, whose
--    cost is the sum of the costs;
--  * the theorems come in pairs: the value is correct against the
--    existing dense semantics (PathSum.Size.Sparse.Represents, the
--    rules of PathSum.Reduction and PathSum.Anywhere, ≋), and the cost
--    is at most an explicit polynomial.
--
-- The dense development cannot say any of this: its polynomials are
-- functions on all 2^(n+m) monomials (PathSum.Polynomial), and
-- PathSum.Size bounds the size of a sparse representation, not the
-- work of computing with it.  The algorithms here compute on the
-- sparse representation only; the dense objects appear only in the
-- statements of correctness.
--
-- The plan, in three phases.
--
--  A. The cost model (this module) and sparse path-sums with the
--     linear rules on them.
--      - PathSum.Cost.Monomial: monomials as bit vectors, the steps on
--        them, and the enumeration of the (sub)monomials of degree at
--        most d, all in the monad.
--      - PathSum.Cost.Coeff: arithmetic modulo 2^M on the coefficients.
--      - PathSum.Cost.Canon: a phase of order at most d is kept as a
--        canonical list of terms (monomial, coefficient mod 2^M): one
--        term for each monomial of degree at most d whose coefficient
--        is not 0 modulo 2^M, so at most as many as there are such
--        monomials, (n + m + 1)^d, polynomial for fixed d.  Its
--        outputs are Z₂-linear forms.  This is PathSum.Size.Sparse's
--        Rep, read by its Represents.  canonᶜ merges equal monomials,
--        drops zero coefficients and drops the monomials of degree
--        above d, which vanish modulo 1 exactly when the phase has
--        degree at most d modulo 1 -- which lemma 2.13's order bound
--        keeps true under substitution.
--      - PathSum.Cost.Split: reading off a path variable's
--        coefficients (the constant of its quotient and its quadratic
--        partners: what lemma 4.3 and the rules match on), and
--        removing and renumbering a path variable.
--      - PathSum.Cost.Subst: substituting a lifted Z₂-linear form for a
--        path variable, the expansion truncated at degree d by the
--        order bound, and re-canonicalising.
--      - PathSum.Cost.Rules: [Elim], [ω] and [HH] with Z₂-linear
--        quotients at any path variable y_j, as PathSum.Anywhere's
--        _⟶ᵍ_ states them.  Each is a partial function on sparse
--        representations; when it succeeds, the dense path-sum the
--        input represents steps by that rule, at y_j, to the path-sum
--        the output represents, and the cost is polynomial in n + m
--        for fixed d.
--  B. Matching and normalisation (PathSum.Cost.Complete, which records
--     the design of this phase).
--      - PathSum.Cost.Complete: on a canonical representation the
--        sparse matchers are complete, not only sound.
--      - PathSum.Cost.Search: whether some rule applies at some
--        variable, sound, complete (nothing found means irreducible)
--        and polynomial.
--      - PathSum.Cost.Sequence: every sequence of sparse rewrites is a
--        dense chain and costs a polynomial.
--      - PathSum.Cost.Normalise: rewriting until no rule applies, with
--        a dense chain to an irreducible path-sum, at a total cost
--        polynomial in n and m for fixed d -- proposition 3.2's time
--        claim, in this cost model, for [Elim], [ω] and [HH] with
--        linear quotients; PathSum.Cost.Normalise.Equivalence: the
--        operator is preserved.
--      - PathSum.Cost.Excluded: why [Case] and non-linear quotients are
--        left out -- a step with a non-linear quotient can raise the
--        order that every bound rests on.
--  C. Circuits (PathSum.Cost.Identity, which records the design of
--     this phase).
--      - PathSum.Cost.Identity: whether a sparse path-sum without path
--        variables is the identity (no normalisation, the inputs as
--        outputs, phase 0 modulo 1), decided at polynomial cost.
--      - PathSum.Cost.Restriction: the isometry restriction ⟦ C ⟧ᴿ of a
--        circuit over {H, S, CZ} (section 4.1), computed sparsely.
--      - PathSum.Cost.Corollary: corollary 4.4 -- whether ⟦ C ⟧ is the
--        identity, decided at a cost polynomial in n + |C| and in the
--        volume n · |C| -- and the equivalence of two Clifford circuits
--        by their miter, both for circuits over {H, S, CZ}.
--      - PathSum.Cost.Gauss, Cost.Gauss.Correct, Cost.Gauss.Corollary:
--        the same for the paper's gate set {H, CNOT, R_k} at level
--        ≤ 2, by the paper's route -- Gaussian elimination (section
--        4.1) written in the monad, then the normaliser and the verdict.
--      - PathSum.Cost.Interpreter: the sparse interpreter of
--        PathSum.Size.Interpreter over {H, CNOT, R_k, R_k†} written in
--        the monad, at a cost polynomial in n + |C| for fixed k
--        (corollary 2.15's time half).
--
-- This module: the monad, its laws, and the traversals of lists and
-- vectors the algorithms are built from, each with the value it
-- computes and a bound on its cost.  The cost of a program is only
-- ever bounded above; the bounds are not claimed to be tight.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Cost where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using
  (List; []; _∷_; _++_; map; length; concatMap)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (∃; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (Vec; []; _∷_; tabulate; lookup)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.List.Properties as List
import Data.Vec.Base as V
import Data.Nat.Properties as ℕ

private
  variable
    A B C : Set
    k : ℕ


------------------------------------------------------------------------
-- The monad

-- A computation's value, together with the number of primitive steps
-- it took.

infixr 4 _,ᶜ_

record Cost (A : Set) : Set where
  constructor _,ᶜ_
  field
    value : A
    cost  : ℕ

open Cost public

-- No step, and one primitive step.

pure : A → Cost A
pure a = a ,ᶜ 0

step : A → Cost A
step a = a ,ᶜ 1

tick : Cost ⊤
tick = step tt

-- Sequencing adds the costs.  The value of a bind is, definitionally,
-- the value of the continuation at the value of the first program.

infixl 1 _>>=_ _>>_
infixl 4 _<$>_

_>>=_ : Cost A → (A → Cost B) → Cost B
m >>= f = value (f (value m)) ,ᶜ (cost m + cost (f (value m)))

_>>_ : Cost A → Cost B → Cost B
m >> m′ = value m′ ,ᶜ (cost m + cost m′)

-- Relabelling the result costs nothing.  It wraps a result in a
-- constructor, and it takes the free function view (lookup) of a
-- vector of output forms -- read afterwards only in charged sweeps,
-- as the header says (PathSum.Cost.Split.dropFormsᶜ,
-- PathSum.Cost.Subst.substFormsᶜ, PathSum.Cost.Restriction.toRepᶜ).

_<$>_ : (A → B) → Cost A → Cost B
f <$> m = f (value m) ,ᶜ cost m


------------------------------------------------------------------------
-- The monad laws

-- They hold on the nose: the values are the same by definition, and
-- the costs by the monoid laws of ℕ.

bind-identityˡ : (a : A) (f : A → Cost B) → (pure a >>= f) ≡ f a
bind-identityˡ a f = refl

bind-identityʳ : (m : Cost A) → (m >>= pure) ≡ m
bind-identityʳ m = cong (value m ,ᶜ_) (ℕ.+-identityʳ (cost m))

bind-assoc : (m : Cost A) (f : A → Cost B) (g : B → Cost C) →
             ((m >>= f) >>= g) ≡ (m >>= λ a → f a >>= g)
bind-assoc m f g = cong (value (g (value (f (value m)))) ,ᶜ_)
  (ℕ.+-assoc (cost m) (cost (f (value m)))
             (cost (g (value (f (value m))))))

-- Sequencing is bind ignoring the value.

then-bind : (m : Cost A) (m′ : Cost B) → (m >> m′) ≡ (m >>= λ _ → m′)
then-bind m m′ = refl

-- The value and the cost of a bind.

value-bind : (m : Cost A) (f : A → Cost B) →
             value (m >>= f) ≡ value (f (value m))
value-bind m f = refl

cost-bind : (m : Cost A) (f : A → Cost B) →
            cost (m >>= f) ≡ cost m + cost (f (value m))
cost-bind m f = refl

-- A bound on each part bounds the whole.

bind-≤ : (m : Cost A) (f : A → Cost B) {a b : ℕ} →
         cost m ≤ a → cost (f (value m)) ≤ b → cost (m >>= f) ≤ a + b
bind-≤ m f = ℕ.+-mono-≤


------------------------------------------------------------------------
-- Lists

-- A map visits every cell once: one step per cell, plus the cost of
-- the function there.

mapᶜ : (A → Cost B) → List A → Cost (List B)
mapᶜ f []       = pure []
mapᶜ f (a ∷ as) = do
  tick
  b  ← f a
  bs ← mapᶜ f as
  pure (b ∷ bs)

value-mapᶜ : (f : A → Cost B) (as : List A) →
             value (mapᶜ f as) ≡ map (λ a → value (f a)) as
value-mapᶜ f []       = refl
value-mapᶜ f (a ∷ as) = cong (value (f a) ∷_) (value-mapᶜ f as)

cost-mapᶜ : (f : A → Cost B) (as : List A) {b : ℕ} →
            (∀ a → cost (f a) ≤ b) → cost (mapᶜ f as) ≤ length as * suc b
cost-mapᶜ f []       h = z≤n
cost-mapᶜ f (a ∷ as) h = s≤s (ℕ.+-mono-≤ (h a)
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (mapᶜ f as))))
             (cost-mapᶜ f as h)))

-- Keeping the cells a test accepts.  Its specification, keep, is
-- stdlib's filterᵇ written with if_then_else_, so that its unfolding
-- is the program's.

keep : (A → Bool) → List A → List A
keep p []       = []
keep p (a ∷ as) = if p a then a ∷ keep p as else keep p as

keepᶜ : (A → Cost Bool) → List A → Cost (List A)
keepᶜ p []       = pure []
keepᶜ p (a ∷ as) = do
  tick
  b  ← p a
  rs ← keepᶜ p as
  pure (if b then a ∷ rs else rs)

value-keepᶜ : (p : A → Cost Bool) (as : List A) →
              value (keepᶜ p as) ≡ keep (λ a → value (p a)) as
value-keepᶜ p []       = refl
value-keepᶜ p (a ∷ as) =
  cong (λ rs → if value (p a) then a ∷ rs else rs) (value-keepᶜ p as)

cost-keepᶜ : (p : A → Cost Bool) (as : List A) {b : ℕ} →
             (∀ a → cost (p a) ≤ b) → cost (keepᶜ p as) ≤ length as * suc b
cost-keepᶜ p []       h = z≤n
cost-keepᶜ p (a ∷ as) h = s≤s (ℕ.+-mono-≤ (h a)
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (keepᶜ p as))))
             (cost-keepᶜ p as h)))

-- What keep keeps.

keep-cong : {p q : A → Bool} → (∀ a → p a ≡ q a) → (as : List A) →
            keep p as ≡ keep q as
keep-cong h []       = refl
keep-cong h (a ∷ as) =
  cong₂ (λ b rs → if b then a ∷ rs else rs) (h a) (keep-cong h as)

keep-length : (p : A → Bool) (as : List A) → length (keep p as) ≤ length as
keep-length p []       = z≤n
keep-length p (a ∷ as) with p a
... | true  = s≤s (keep-length p as)
... | false = ℕ.m≤n⇒m≤1+n (keep-length p as)

keep-All : {P : A → Set} (p : A → Bool) (as : List A) →
           All P as → All P (keep p as)
keep-All p []       []         = []
keep-All p (a ∷ as) (pa ∷ pas) with p a
... | true  = pa ∷ keep-All p as pas
... | false = keep-All p as pas

keep-true : (p : A → Bool) (as : List A) → All (λ a → p a ≡ true) (keep p as)
keep-true p []       = []
keep-true p (a ∷ as) with p a in eq
... | true  = eq ∷ keep-true p as
... | false = keep-true p as

-- Nothing is kept when the test fails on every cell.

keep-none : (p : A → Bool) (as : List A) → All (λ a → p a ≡ false) as →
            keep p as ≡ []
keep-none p []       []         = refl
keep-none p (a ∷ as) (pa ∷ pas) =
  trans (cong (λ b → if b then a ∷ keep p as else keep p as) pa)
        (keep-none p as pas)

-- Whether every cell passes a test.  There is no early exit: the whole
-- list is visited.  Its specification is allᵇ.

allᵇ : (A → Bool) → List A → Bool
allᵇ p []       = true
allᵇ p (a ∷ as) = p a ∧ allᵇ p as

allᶜ : (A → Cost Bool) → List A → Cost Bool
allᶜ p []       = pure true
allᶜ p (a ∷ as) = do
  tick
  b ← p a
  r ← allᶜ p as
  pure (b ∧ r)

value-allᶜ : (p : A → Cost Bool) (as : List A) →
             value (allᶜ p as) ≡ allᵇ (λ a → value (p a)) as
value-allᶜ p []       = refl
value-allᶜ p (a ∷ as) = cong (value (p a) ∧_) (value-allᶜ p as)

cost-allᶜ : (p : A → Cost Bool) (as : List A) {b : ℕ} →
            (∀ a → cost (p a) ≤ b) → cost (allᶜ p as) ≤ length as * suc b
cost-allᶜ p []       h = z≤n
cost-allᶜ p (a ∷ as) h = s≤s (ℕ.+-mono-≤ (h a)
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (allᶜ p as))))
             (cost-allᶜ p as h)))

-- When the test passes everywhere, every cell passes it.

all-true : (p : A → Bool) (as : List A) → allᵇ p as ≡ true →
           All (λ a → p a ≡ true) as
all-true p []       _  = []
all-true p (a ∷ as) eq with p a in pa
all-true p (a ∷ as) eq | true  = pa ∷ all-true p as eq
all-true p (a ∷ as) () | false

-- And conversely: when every cell passes, so does the list.

all-true⁻ : (p : A → Bool) (as : List A) → All (λ a → p a ≡ true) as →
            allᵇ p as ≡ true
all-true⁻ p []       []         = refl
all-true⁻ p (a ∷ as) (pa ∷ pas) = cong₂ _∧_ pa (all-true⁻ p as pas)

-- Appending visits the cells of the first list.

appendᶜ : List A → List A → Cost (List A)
appendᶜ []       bs = pure bs
appendᶜ (a ∷ as) bs = do
  tick
  rs ← appendᶜ as bs
  pure (a ∷ rs)

value-appendᶜ : (as bs : List A) → value (appendᶜ as bs) ≡ as ++ bs
value-appendᶜ []       bs = refl
value-appendᶜ (a ∷ as) bs = cong (a ∷_) (value-appendᶜ as bs)

cost-appendᶜ : (as bs : List A) → cost (appendᶜ as bs) ≤ length as
cost-appendᶜ []       bs = z≤n
cost-appendᶜ (a ∷ as) bs = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (appendᶜ as bs))))
             (cost-appendᶜ as bs))

-- A map whose results are lists, concatenated.

concatMapᶜ : (A → Cost (List B)) → List A → Cost (List B)
concatMapᶜ f []       = pure []
concatMapᶜ f (a ∷ as) = do
  tick
  bs ← f a
  cs ← concatMapᶜ f as
  appendᶜ bs cs

value-concatMapᶜ : (f : A → Cost (List B)) (as : List A) →
                   value (concatMapᶜ f as) ≡
                   concatMap (λ a → value (f a)) as
value-concatMapᶜ f []       = refl
value-concatMapᶜ f (a ∷ as) = trans
  (value-appendᶜ (value (f a)) (value (concatMapᶜ f as)))
  (cong (value (f a) ++_) (value-concatMapᶜ f as))

-- With every result of length at most l, computed at cost at most b:
-- the concatenation has length at most |as| · l, and costs at most
-- |as| · (1 + b + l).

length-concatMap : (f : A → List B) (as : List A) {l : ℕ} →
                   (∀ a → length (f a) ≤ l) →
                   length (concatMap f as) ≤ length as * l
length-concatMap f []       h = z≤n
length-concatMap f (a ∷ as) h = ℕ.≤-trans
  (ℕ.≤-reflexive (List.length-++ (f a)))
  (ℕ.+-mono-≤ (h a) (length-concatMap f as h))

cost-concatMapᶜ : (f : A → Cost (List B)) (as : List A) {b l : ℕ} →
                  (∀ a → cost (f a) ≤ b) →
                  (∀ a → length (value (f a)) ≤ l) →
                  cost (concatMapᶜ f as) ≤ length as * suc (b + l)
cost-concatMapᶜ f []       hb hl = z≤n
cost-concatMapᶜ f (a ∷ as) {b} {l} hb hl = s≤s (ℕ.≤-trans
  (ℕ.≤-reflexive (sym (ℕ.+-assoc (cost (f a)) (cost (concatMapᶜ f as))
    (cost (appendᶜ (value (f a)) (value (concatMapᶜ f as)))))))
  (ℕ.≤-trans
    (ℕ.+-mono-≤ (ℕ.+-mono-≤ (hb a) (cost-concatMapᶜ f as hb hl))
      (ℕ.≤-trans (cost-appendᶜ (value (f a)) (value (concatMapᶜ f as)))
                 (hl a)))
    (ℕ.≤-reflexive (shuffle b (length as * suc (b + l)) l))))
  where
  shuffle : ∀ x y z → x + y + z ≡ x + z + y
  shuffle x y z = trans (ℕ.+-assoc x y z)
    (trans (cong (x +_) (ℕ.+-comm y z)) (sym (ℕ.+-assoc x z y)))


------------------------------------------------------------------------
-- Vectors and indices

-- Tabulating over the k indices, in order.

tabulateᶜ : (Fin k → Cost A) → Cost (Vec A k)
tabulateᶜ {k = zero}  f = pure []
tabulateᶜ {k = suc k} f = do
  tick
  a  ← f zero
  as ← tabulateᶜ (λ i → f (suc i))
  pure (a ∷ as)

value-tabulateᶜ : (f : Fin k → Cost A) →
                  value (tabulateᶜ f) ≡ tabulate (λ i → value (f i))
value-tabulateᶜ {k = zero}  f = refl
value-tabulateᶜ {k = suc k} f =
  cong (value (f zero) ∷_) (value-tabulateᶜ (λ i → f (suc i)))

cost-tabulateᶜ : (f : Fin k → Cost A) {b : ℕ} →
                 (∀ i → cost (f i) ≤ b) → cost (tabulateᶜ f) ≤ k * suc b
cost-tabulateᶜ {k = zero}  f h = z≤n
cost-tabulateᶜ {k = suc k} f h = s≤s (ℕ.+-mono-≤ (h zero)
  (ℕ.≤-trans (ℕ.≤-reflexive
               (ℕ.+-identityʳ (cost (tabulateᶜ (λ i → f (suc i))))))
             (cost-tabulateᶜ (λ i → f (suc i)) (λ i → h (suc i)))))

-- Whether a test passes at every index.

allFinᶜ : (Fin k → Cost Bool) → Cost Bool
allFinᶜ {k = zero}  p = pure true
allFinᶜ {k = suc k} p = do
  tick
  b ← p zero
  r ← allFinᶜ (λ i → p (suc i))
  pure (b ∧ r)

allFinᶜ-true : (p : Fin k → Cost Bool) → value (allFinᶜ p) ≡ true →
               ∀ i → value (p i) ≡ true
allFinᶜ-true {k = suc k} p eq i with value (p zero) in e
allFinᶜ-true {k = suc k} p eq zero    | true  = e
allFinᶜ-true {k = suc k} p eq (suc i) | true  =
  allFinᶜ-true (λ l → p (suc l)) eq i
allFinᶜ-true {k = suc k} p () i       | false

allFinᶜ-complete : (p : Fin k → Cost Bool) → (∀ i → value (p i) ≡ true) →
                   value (allFinᶜ p) ≡ true
allFinᶜ-complete {k = zero}  p h = refl
allFinᶜ-complete {k = suc k} p h =
  cong₂ _∧_ (h zero) (allFinᶜ-complete (λ i → p (suc i)) (λ i → h (suc i)))

cost-allFinᶜ : (p : Fin k → Cost Bool) {b : ℕ} →
               (∀ i → cost (p i) ≤ b) → cost (allFinᶜ p) ≤ k * suc b
cost-allFinᶜ {k = zero}  p h = z≤n
cost-allFinᶜ {k = suc k} p h = s≤s (ℕ.+-mono-≤ (h zero)
  (ℕ.≤-trans (ℕ.≤-reflexive
               (ℕ.+-identityʳ (cost (allFinᶜ (λ i → p (suc i))))))
             (cost-allFinᶜ (λ i → p (suc i)) (λ i → h (suc i)))))

-- Mapping over a vector, and testing every entry: one step per entry
-- plus the cost of the function there.

mapVᶜ : (A → Cost B) → Vec A k → Cost (Vec B k)
mapVᶜ f []       = pure []
mapVᶜ f (a ∷ as) = do
  tick
  b  ← f a
  bs ← mapVᶜ f as
  pure (b ∷ bs)

value-mapVᶜ : (f : A → Cost B) (as : Vec A k) →
              value (mapVᶜ f as) ≡ V.map (λ a → value (f a)) as
value-mapVᶜ f []       = refl
value-mapVᶜ f (a ∷ as) = cong (value (f a) ∷_) (value-mapVᶜ f as)

cost-mapVᶜ : (f : A → Cost B) (as : Vec A k) {b : ℕ} →
             (∀ a → cost (f a) ≤ b) → cost (mapVᶜ f as) ≤ k * suc b
cost-mapVᶜ f []       h = z≤n
cost-mapVᶜ f (a ∷ as) h = s≤s (ℕ.+-mono-≤ (h a)
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (mapVᶜ f as))))
             (cost-mapVᶜ f as h)))

allVᶜ : (A → Cost Bool) → Vec A k → Cost Bool
allVᶜ p []       = pure true
allVᶜ p (a ∷ as) = do
  tick
  b ← p a
  r ← allVᶜ p as
  pure (b ∧ r)

allVᶜ-true : (p : A → Cost Bool) (as : Vec A k) → value (allVᶜ p as) ≡ true →
             ∀ i → value (p (lookup as i)) ≡ true
allVᶜ-true p (a ∷ as) eq i with value (p a) in e
allVᶜ-true p (a ∷ as) eq zero    | true  = e
allVᶜ-true p (a ∷ as) eq (suc i) | true  = allVᶜ-true p as eq i
allVᶜ-true p (a ∷ as) () i       | false

allVᶜ-complete : (p : A → Cost Bool) (as : Vec A k) →
                 (∀ i → value (p (lookup as i)) ≡ true) →
                 value (allVᶜ p as) ≡ true
allVᶜ-complete p []       h = refl
allVᶜ-complete p (a ∷ as) h =
  cong₂ _∧_ (h zero) (allVᶜ-complete p as (λ i → h (suc i)))

cost-allVᶜ : (p : A → Cost Bool) (as : Vec A k) {b : ℕ} →
             (∀ a → cost (p a) ≤ b) → cost (allVᶜ p as) ≤ k * suc b
cost-allVᶜ p []       h = z≤n
cost-allVᶜ p (a ∷ as) h = s≤s (ℕ.+-mono-≤ (h a)
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (allVᶜ p as))))
             (cost-allVᶜ p as h)))

-- Whether a list is empty: one look at its first cell.

nullᶜ : List A → Cost Bool
nullᶜ []      = step true
nullᶜ (_ ∷ _) = step false

nullᶜ-true : (as : List A) → value (nullᶜ as) ≡ true → as ≡ []
nullᶜ-true []      _  = refl
nullᶜ-true (_ ∷ _) ()

cost-nullᶜ : (as : List A) → cost (nullᶜ as) ≤ 1
cost-nullᶜ []      = ℕ.≤-refl
cost-nullᶜ (_ ∷ _) = ℕ.≤-refl

-- Looking up an index visits the cells before it.

lookupᶜ : Vec A k → Fin k → Cost A
lookupᶜ (a ∷ as) zero    = step a
lookupᶜ (a ∷ as) (suc i) = tick >> lookupᶜ as i

value-lookupᶜ : (as : Vec A k) (i : Fin k) →
                value (lookupᶜ as i) ≡ lookup as i
value-lookupᶜ (a ∷ as) zero    = refl
value-lookupᶜ (a ∷ as) (suc i) = value-lookupᶜ as i

cost-lookupᶜ : (as : Vec A k) (i : Fin k) → cost (lookupᶜ as i) ≤ k
cost-lookupᶜ (a ∷ as) zero    = s≤s z≤n
cost-lookupᶜ (a ∷ as) (suc i) = s≤s (cost-lookupᶜ as i)

-- The first index at which a bit vector holds true, if any.

sucᴹ : Maybe (Fin k) → Maybe (Fin (suc k))
sucᴹ (just i) = just (suc i)
sucᴹ nothing  = nothing

firstᶜ : Vec Bool k → Cost (Maybe (Fin k))
firstᶜ []           = pure nothing
firstᶜ (true  ∷ bs) = step (just zero)
firstᶜ (false ∷ bs) = do
  tick
  r ← firstᶜ bs
  pure (sucᴹ r)

-- It finds a true bit, and it finds one whenever there is one.

firstᶜ-just : (bs : Vec Bool k) {i : Fin k} → value (firstᶜ bs) ≡ just i →
              lookup bs i ≡ true
firstᶜ-just (true  ∷ bs) refl = refl
firstᶜ-just (false ∷ bs) eq with value (firstᶜ bs) in e
firstᶜ-just (false ∷ bs) refl | just j  = firstᶜ-just bs e
firstᶜ-just (false ∷ bs) ()   | nothing

firstᶜ-nothing : (bs : Vec Bool k) → value (firstᶜ bs) ≡ nothing →
                 ∀ i → lookup bs i ≡ false
firstᶜ-nothing (true  ∷ bs) () i
firstᶜ-nothing (false ∷ bs) eq i with value (firstᶜ bs) in e
firstᶜ-nothing (false ∷ bs) eq zero    | nothing = refl
firstᶜ-nothing (false ∷ bs) eq (suc i) | nothing = firstᶜ-nothing bs e i
firstᶜ-nothing (false ∷ bs) () i       | just j

cost-firstᶜ : (bs : Vec Bool k) → cost (firstᶜ bs) ≤ k
cost-firstᶜ []           = z≤n
cost-firstᶜ (true  ∷ bs) = s≤s z≤n
cost-firstᶜ (false ∷ bs) = s≤s
  (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (cost (firstᶜ bs))))
             (cost-firstᶜ bs))


------------------------------------------------------------------------
-- The first index with a result

-- Trying f at the indices in order and stopping at the first that
-- returns something: one step per index tried, plus the tries.
-- orElse r m is r when r is a result and m otherwise, so the cost of m
-- is paid only when it runs.

orElse : Maybe A → Cost (Maybe A) → Cost (Maybe A)
orElse (just a) m = pure (just a)
orElse nothing  m = m

firstJustᶜ : (Fin k → Cost (Maybe A)) → Cost (Maybe A)
firstJustᶜ {k = zero}  f = pure nothing
firstJustᶜ {k = suc k} f = do
  tick
  r ← f zero
  orElse r (firstJustᶜ (λ i → f (suc i)))

-- A result comes from some index, and there is none exactly when no
-- index gives one.

firstJustᶜ-just : (f : Fin k → Cost (Maybe A)) {a : A} →
                  value (firstJustᶜ f) ≡ just a →
                  ∃ λ i → value (f i) ≡ just a
firstJustᶜ-just {k = suc k} f {a} eq = go (value (f zero)) refl eq
  where
  go : ∀ r → value (f zero) ≡ r →
       value (orElse r (firstJustᶜ (λ i → f (suc i)))) ≡ just a →
       ∃ λ i → value (f i) ≡ just a
  go (just b) e refl = zero , e
  go nothing  e eq′  = suc (proj₁ rest) , proj₂ rest
    where
    rest = firstJustᶜ-just (λ i → f (suc i)) eq′

firstJustᶜ-nothing : (f : Fin k → Cost (Maybe A)) →
                     value (firstJustᶜ f) ≡ nothing →
                     ∀ i → value (f i) ≡ nothing
firstJustᶜ-nothing {k = suc k} f eq = go (value (f zero)) refl eq
  where
  go : ∀ r → value (f zero) ≡ r →
       value (orElse r (firstJustᶜ (λ i → f (suc i)))) ≡ nothing →
       ∀ i → value (f i) ≡ nothing
  go (just b) e ()
  go nothing  e eq′ zero    = e
  go nothing  e eq′ (suc i) = firstJustᶜ-nothing (λ l → f (suc l)) eq′ i

cost-firstJustᶜ : (f : Fin k → Cost (Maybe A)) {b : ℕ} →
                  (∀ i → cost (f i) ≤ b) → cost (firstJustᶜ f) ≤ k * suc b
cost-firstJustᶜ {k = zero}  f h = z≤n
cost-firstJustᶜ {k = suc k} f h = s≤s (ℕ.+-mono-≤ (h zero)
  (ℕ.≤-trans (orElse≤ (value (f zero)))
             (cost-firstJustᶜ (λ i → f (suc i)) (λ i → h (suc i)))))
  where
  orElse≤ : ∀ r → cost (orElse r (firstJustᶜ (λ i → f (suc i)))) ≤
                  cost (firstJustᶜ (λ i → f (suc i)))
  orElse≤ (just a) = z≤n
  orElse≤ nothing  = ℕ.≤-refl
