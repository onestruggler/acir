------------------------------------------------------------------------
-- Presentations of groups
--
-- Inequivalence of reversible netlists has short certificates, checked
-- by simulation (Amy, QPL 2018, section 4, footnote 2)
--
-- Footnote 2 of section 4: uniqueness of normal forms "would imply that
-- equivalence checking of reversible Boolean circuits is in P.  As this
-- problem is co-NP-complete, uniqueness of our normal forms would
-- indeed imply P = co-NP."  Phase A (PathSum.Hardness.CNF, .Netlist,
-- PathSum.Hardness) formalised the hardness half of "co-NP-complete":
-- unsatisfiability of CNF formulas reduces, with linear size, to
-- identity checking of reversible netlists over {NOT, CNOT, Toffoli}
-- and of their Clifford+T expansions.  Phase B formalises the rest of
-- the footnote's argument that can be stated without machines.  The
-- plan:
--
-- * Here (no M₀): membership, as a certificate check.  Two netlists
--   are inequivalent on the inputs whose ancillas are 0 exactly when
--   some such input tells them apart, and that is checked by one
--   classical simulation of each netlist (check: the ancillas read,
--   both netlists run, their outputs compared wire by wire).  The check
--   is sound (check-sound) and complete (check-complete), so
--   inequivalence is exactly the existence of an accepted certificate
--   (certificate⇔), a certificate being an input, N bits for N wires.
--   Its cost is counted in simulation steps -- one per gate applied,
--   one per ancilla read, one per wire compared -- by writing the check
--   in a counting monad (Counted): check-steps says it takes
--   j + |gs| + |hs| + N steps for j ancillas.  A reversible netlist has
--   an inverse, its reverse (runᴺ-reverse), so equivalence is identity
--   of the miter gs ++ reverse hs (miter⇔).  For the reduction of phase
--   A: φ is satisfiable exactly when its netlist has a certificate
--   against the empty netlist (sat⇔certificate; certificate builds it
--   from a satisfying assignment), checked in
--   n + 12 lits + 6 negs + 6 clauses + 10 ≤ n + 18‖φ‖ + 10 steps
--   (check-steps-cnf, check-steps-bound).
--
-- * PathSum.Hardness.Prepared (M₀): the same on the path-sum side, and
--   the form of the reduction whose normal forms can be compared with
--   the identity.  The expansions of two netlists into Clifford+T are
--   equivalent on the clean inputs exactly when the netlists are
--   (expandᴺ-equivalent⇔), so inequivalence of the expansions has the
--   same certificates (expansion-certificate, circuit-certificate).
--   The circuit of phase A has ancillas, and is the identity only on
--   the inputs where they are 0; PathSum.Expand's normal-form test asks
--   whether a path-sum is the identity on every input.  The prepared
--   path-sum (prepared a ξ) reads the ancilla inputs as 0 (set0ˢ, as
--   the paper does in section 5.2) and xors each ancilla input into its
--   output; if ξ computes F, it computes x ↦ F(x with ancillas 0) with
--   the ancillas xored back (prepared-computes), so it is equivalent to
--   the identity exactly when ξ is the identity on the clean inputs
--   (prepared-identity⇔) -- phase A's question, in the set0 form too
--   (prepared⇔set0).  For a CNF formula φ, cleanPS φ is the prepared
--   path-sum of phase A's circuit: it is the specification
--   |x⟩|a⟩|t⟩ ↦ |x⟩|a⟩|t ⊕ φ(x)⟩ on every input (cleanPS-spec), and
--   cleanPS φ ≋ idPS exactly when φ is unsatisfiable
--   (cleanPS-identity⇔unsat), exactly when phase A's set0 form is the
--   identity (cleanPS⇔set0).
--
-- * PathSum.Hardness.Conditional (M₀): the footnote's conditional.
--   NormalFormId ξ says that the normal form PathSum.Full.Match's
--   normal-formᶠ computes for ξ has no path variables and passes
--   PathSum.Expand's syntactic identity test.  It is sound on its own
--   (normal-form-id-sound) and decidable (normal-form-id?); under
--   PathSum.Expand.UniqueNormalForms -- the hypothesis of
--   Expand.unique⇒no-expansion, exactly -- it is complete:
--   ξ ≋ idPS ⇔ NormalFormId ξ (unique⇒normal-form-id).  Hence, under
--   that hypothesis, φ is unsatisfiable exactly when the normal form of
--   cleanPS φ is syntactically the identity (unsat-by-normalisation), a
--   decision of unsatisfiability by normalising a path-sum with
--   4‖φ‖ + 4 path variables on at most n + 3‖φ‖ + 3 wires (unsat?ᵘ),
--   and two netlists are equivalent exactly when the normal form of
--   their prepared miter is (equivalence-by-normalisation).  What
--   stands between this and P = co-NP is said there.
--
-- * PathSum.Hardness.Blowup (M₀): what the hypothesis would force.  For
--   a formula whose value is the OR of its variables -- the single
--   clause x₁ ∨ … ∨ x_n -- every reduct of cleanPS φ without path
--   variables has an odd coefficient on every nonempty monomial over
--   the inputs in its target output (reduct-odd-coefficients, by
--   Möbius inversion modulo 2), and under the hypothesis every normal
--   form is such a reduct (unique⇒odd-on-inputs): 2^n − 1 terms, a
--   count left in words, from a path-sum with 4n + 8 path variables,
--   so uniqueness and a polynomial-time normaliser that lists the terms
--   of its polynomials exclude each other on these instances -- an
--   argument in words, no time model being formalised.
--
-- What is not formalised: machines and complexity classes.  "Checked in
-- s steps" counts the steps of the simulation written here, not the
-- running time of a program on a machine; with assignments stored as
-- bit vectors each step reads at most three bits and writes at most
-- one.  No cost model of programs is used here; this count stands in
-- for one.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Hardness.Certificate where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _∨_; _xor_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; map; reverse; length)
open import Data.List.Properties using
  (length-++; length-reverse; reverse-involutive; unfold-reverse)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (m≤m+n; m≤n⇒∃[o]m+o≡n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Bool.Properties as Bool

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

open import PathSum.Assign using (_[_≔_]; ≔-here)
open import PathSum.Hardness.CNF using
  (Assignment; CNF; ⟦_⟧ᶠ; ⟦⟧ᶠ-cong; Satisfiable; Unsatisfiable;
   unsat⇔¬sat; sat?; search; cnf; nodes; lits; negs; clauses; ‖_‖;
   negs≤lits; nodes-cnf)
open import PathSum.Hardness.Netlist using
  (NCT; X; gate; ⟦_⟧ᴺ; runᴺ; runᴺ-++; runᴺ-gates; flip-cong; flip-flip;
   Clean; netlist; wires; inputs; ancillas; tgt; netlist-correct;
   netlist-identity⇔unsat; netlist-length; wires-exact; blank;
   blank-inp; blank-clean)
open import PathSum.Reversible using
  (Gate; ⟪⟫-cong; ⟪⟫-involutive; run)

private
  variable
    n N j : ℕ
    A B : Set

  -- Chaining equivalences of statements.

  infixr 5 _⟨⇔⟩_

  _⟨⇔⟩_ : {P Q R : Set} → P ⇔ Q → Q ⇔ R → P ⇔ R
  f ⟨⇔⟩ g = mk⇔ (λ a → Equivalence.to g (Equivalence.to f a))
                (λ c → Equivalence.from f (Equivalence.from g c))

  sym⇔ : {P Q : Set} → P ⇔ Q → Q ⇔ P
  sym⇔ f = mk⇔ (Equivalence.from f) (Equivalence.to f)

  ¬⇔ : {P Q : Set} → P ⇔ Q → (¬ P) ⇔ (¬ Q)
  ¬⇔ f = mk⇔ (λ np q → np (Equivalence.from f q))
             (λ nq p → nq (Equivalence.to f p))


------------------------------------------------------------------------
-- Bits

private
  ≢⇒xor : ∀ {a b} → a ≢ b → a xor b ≡ true
  ≢⇒xor {true}  {true}  ne = contradiction refl ne
  ≢⇒xor {true}  {false} _  = refl
  ≢⇒xor {false} {true}  _  = refl
  ≢⇒xor {false} {false} ne = contradiction refl ne

  xor⇒≢ : ∀ {a b} → a xor b ≡ true → a ≢ b
  xor⇒≢ {true}  {true}  ()
  xor⇒≢ {true}  {false} _ ()
  xor⇒≢ {false} {true}  _ ()
  xor⇒≢ {false} {false} ()

  ∨-true : ∀ a b → a ∨ b ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-true true  b _ = inj₁ refl
  ∨-true false b h = inj₂ h

  ∧-true : ∀ a b → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
  ∧-true true true _ = refl , refl

  not-true : ∀ {a} → not a ≡ true → a ≡ false
  not-true {false} _ = refl

  xor-not : ∀ a → a xor true ≢ a
  xor-not true  ()
  xor-not false ()

  bool-≟ : (a b : Bool) → Dec (a ≡ b)
  bool-≟ = Bool._≟_


------------------------------------------------------------------------
-- Counting steps

-- A computation's value and the number of steps it took.  Binding adds
-- the steps of the two parts; returning a value costs nothing, and
-- tick counts one step.

Counted : Set → Set
Counted A = A × ℕ

return : A → Counted A
return a = a , 0

infixl 1 _>>=_

_>>=_ : Counted A → (A → Counted B) → Counted B
r >>= f = proj₁ (f (proj₁ r)) , proj₂ r + proj₂ (f (proj₁ r))

tick : Counted A → Counted A
tick r = proj₁ r , suc (proj₂ r)

mapᶜ : (A → B) → Counted A → Counted B
mapᶜ f r = f (proj₁ r) , proj₂ r


------------------------------------------------------------------------
-- The three parts of the check

-- Simulating a netlist: one step per gate.

simulate : List (NCT N) → Assignment N → Counted (Assignment N)
simulate []       x = return x
simulate (g ∷ gs) x = tick (simulate gs (⟦ g ⟧ᴺ x))

simulate-run : (gs : List (NCT N)) (x : Assignment N) →
               proj₁ (simulate gs x) ≡ runᴺ gs x
simulate-run []       x = refl
simulate-run (g ∷ gs) x = simulate-run gs (⟦ g ⟧ᴺ x)

simulate-steps : (gs : List (NCT N)) (x : Assignment N) →
                 proj₂ (simulate gs x) ≡ length gs
simulate-steps []       x = refl
simulate-steps (g ∷ gs) x = cong suc (simulate-steps gs (⟦ g ⟧ᴺ x))

-- Comparing two states wire by wire: true when they differ somewhere,
-- one step per wire.

differs : Assignment N → Assignment N → Counted Bool
differs {zero}  u v = return false
differs {suc N} u v =
  tick (mapᶜ (λ b → (u zero xor v zero) ∨ b)
             (differs (λ w → u (suc w)) (λ w → v (suc w))))

differs-steps : (u v : Assignment N) → proj₂ (differs u v) ≡ N
differs-steps {zero}  u v = refl
differs-steps {suc N} u v =
  cong suc (differs-steps (λ w → u (suc w)) (λ w → v (suc w)))

differs-sound : (u v : Assignment N) → proj₁ (differs u v) ≡ true →
                ∃ λ w → u w ≢ v w
differs-sound {zero}  u v ()
differs-sound {suc N} u v h
  with ∨-true (u zero xor v zero)
              (proj₁ (differs (λ w → u (suc w)) (λ w → v (suc w)))) h
... | inj₁ d = zero , xor⇒≢ d
... | inj₂ d with differs-sound (λ w → u (suc w)) (λ w → v (suc w)) d
...   | w , ne = suc w , ne

differs-complete : (u v : Assignment N) (w : Fin N) → u w ≢ v w →
                   proj₁ (differs u v) ≡ true
differs-complete {zero}  u v ()      ne
differs-complete {suc N} u v zero    ne =
  cong (_∨ proj₁ (differs (λ w → u (suc w)) (λ w → v (suc w)))) (≢⇒xor ne)
differs-complete {suc N} u v (suc w) ne =
  trans (cong ((u zero xor v zero) ∨_)
              (differs-complete (λ w → u (suc w)) (λ w → v (suc w)) w ne))
        (∨-zeroʳ (u zero xor v zero))

differs-cong : {u u′ v v′ : Assignment N} → (∀ w → u w ≡ u′ w) →
               (∀ w → v w ≡ v′ w) →
               proj₁ (differs u v) ≡ proj₁ (differs u′ v′)
differs-cong {zero}  hu hv = refl
differs-cong {suc N} hu hv =
  cong₂ _∨_ (cong₂ _xor_ (hu zero) (hv zero))
            (differs-cong (λ w → hu (suc w)) (λ w → hv (suc w)))

-- Reading the ancillas: true when every one is 0, one step per
-- ancilla.

cleanᶜ : (Fin j → Fin N) → Assignment N → Counted Bool
cleanᶜ {zero}  a x = return true
cleanᶜ {suc j} a x =
  tick (mapᶜ (λ b → not (x (a zero)) ∧ b) (cleanᶜ (λ i → a (suc i)) x))

cleanᶜ-steps : (a : Fin j → Fin N) (x : Assignment N) →
               proj₂ (cleanᶜ a x) ≡ j
cleanᶜ-steps {zero}  a x = refl
cleanᶜ-steps {suc j} a x = cong suc (cleanᶜ-steps (λ i → a (suc i)) x)

cleanᶜ-sound : (a : Fin j → Fin N) (x : Assignment N) →
               proj₁ (cleanᶜ a x) ≡ true → Clean a x
cleanᶜ-sound {zero}  a x h ()
cleanᶜ-sound {suc j} a x h zero    =
  not-true (proj₁ (∧-true (not (x (a zero)))
                          (proj₁ (cleanᶜ (λ i → a (suc i)) x)) h))
cleanᶜ-sound {suc j} a x h (suc i) =
  cleanᶜ-sound (λ i → a (suc i)) x
    (proj₂ (∧-true (not (x (a zero))) (proj₁ (cleanᶜ (λ i → a (suc i)) x)) h))
    i

cleanᶜ-complete : (a : Fin j → Fin N) (x : Assignment N) → Clean a x →
                  proj₁ (cleanᶜ a x) ≡ true
cleanᶜ-complete {zero}  a x cl = refl
cleanᶜ-complete {suc j} a x cl =
  cong₂ _∧_ (cong not (cl zero))
            (cleanᶜ-complete (λ i → a (suc i)) x (λ i → cl (suc i)))

cleanᶜ-cong : (a : Fin j → Fin N) {x x′ : Assignment N} →
              (∀ w → x w ≡ x′ w) → proj₁ (cleanᶜ a x) ≡ proj₁ (cleanᶜ a x′)
cleanᶜ-cong {zero}  a h = refl
cleanᶜ-cong {suc j} a h =
  cong₂ _∧_ (cong not (h (a zero))) (cleanᶜ-cong (λ i → a (suc i)) h)


------------------------------------------------------------------------
-- Netlists over {NOT, CNOT, Toffoli}

-- A netlist only reads values.

⟦⟧ᴺ-cong : (g : NCT N) {x x′ : Assignment N} → (∀ w → x w ≡ x′ w) →
           ∀ w → ⟦ g ⟧ᴺ x w ≡ ⟦ g ⟧ᴺ x′ w
⟦⟧ᴺ-cong (X w)    h = flip-cong w h
⟦⟧ᴺ-cong (gate g) h = ⟪⟫-cong g h

runᴺ-cong : (gs : List (NCT N)) {x x′ : Assignment N} →
            (∀ w → x w ≡ x′ w) → ∀ w → runᴺ gs x w ≡ runᴺ gs x′ w
runᴺ-cong []       h = h
runᴺ-cong (g ∷ gs) h = runᴺ-cong gs (⟦⟧ᴺ-cong g h)

-- Every gate is an involution, so a netlist is undone by its reverse,
-- on either side.

⟦⟧ᴺ-involutive : (g : NCT N) (x : Assignment N) →
                 ∀ w → ⟦ g ⟧ᴺ (⟦ g ⟧ᴺ x) w ≡ x w
⟦⟧ᴺ-involutive (X w)    x = flip-flip w x
⟦⟧ᴺ-involutive (gate g) x = ⟪⟫-involutive g x

runᴺ-reverse : (gs : List (NCT N)) (x : Assignment N) →
               ∀ w → runᴺ (reverse gs) (runᴺ gs x) w ≡ x w
runᴺ-reverse []       x w = refl
runᴺ-reverse (g ∷ gs) x w =
  trans (cong (λ l → runᴺ l (runᴺ gs (⟦ g ⟧ᴺ x)) w) (unfold-reverse g gs))
  (trans (cong (λ f → f w)
               (runᴺ-++ (reverse gs) (g ∷ []) (runᴺ gs (⟦ g ⟧ᴺ x))))
  (trans (⟦⟧ᴺ-cong g (runᴺ-reverse gs (⟦ g ⟧ᴺ x)) w)
         (⟦⟧ᴺ-involutive g x w)))

runᴺ-reverse′ : (gs : List (NCT N)) (x : Assignment N) →
                ∀ w → runᴺ gs (runᴺ (reverse gs) x) w ≡ x w
runᴺ-reverse′ gs x w =
  trans (cong (λ l → runᴺ l (runᴺ (reverse gs) x) w)
              (sym (reverse-involutive gs)))
        (runᴺ-reverse (reverse gs) x w)

-- Equivalence on the inputs whose ancillas are 0; against the empty
-- netlist it is identity there.

Equivalentᴺ : (Fin j → Fin N) → List (NCT N) → List (NCT N) → Set
Equivalentᴺ a gs hs = ∀ x → Clean a x → ∀ w → runᴺ gs x w ≡ runᴺ hs x w

-- The miter: gs followed by the inverse of hs.  Two netlists are
-- equivalent exactly when their miter is the identity.

miterᴺ : List (NCT N) → List (NCT N) → List (NCT N)
miterᴺ gs hs = gs ++ reverse hs

length-miterᴺ : (gs hs : List (NCT N)) →
                length (miterᴺ gs hs) ≡ length gs + length hs
length-miterᴺ gs hs =
  trans (length-++ gs {reverse hs}) (cong (length gs +_) (length-reverse hs))

miter⇔ : (a : Fin j → Fin N) (gs hs : List (NCT N)) →
         Equivalentᴺ a gs hs ⇔ Equivalentᴺ a (miterᴺ gs hs) []
miter⇔ a gs hs = mk⇔ to from
  where
  to : Equivalentᴺ a gs hs → Equivalentᴺ a (miterᴺ gs hs) []
  to e x cl w =
    trans (cong (λ f → f w) (runᴺ-++ gs (reverse hs) x))
    (trans (runᴺ-cong (reverse hs) (e x cl) w) (runᴺ-reverse hs x w))

  from : Equivalentᴺ a (miterᴺ gs hs) [] → Equivalentᴺ a gs hs
  from i x cl w =
    trans (sym (runᴺ-reverse′ hs (runᴺ gs x) w))
          (runᴺ-cong hs (λ u → trans (sym (cong (λ f → f u)
                                              (runᴺ-++ gs (reverse hs) x)))
                                     (i x cl u)) w)


------------------------------------------------------------------------
-- The check

-- Read the ancillas, run both netlists, compare the outputs: accept
-- when the input is clean and the outputs differ.

check : (Fin j → Fin N) → List (NCT N) → List (NCT N) → Assignment N →
        Counted Bool
check a gs hs x = do
  c ← cleanᶜ a x
  u ← simulate gs x
  v ← simulate hs x
  d ← differs u v
  return (c ∧ d)

-- It takes j + |gs| + |hs| + N steps.

check-steps : (a : Fin j → Fin N) (gs hs : List (NCT N)) (x : Assignment N) →
              proj₂ (check a gs hs x) ≡ j + length gs + length hs + N
check-steps {j} {N} a gs hs x =
  trans (cong₂ _+_ (cleanᶜ-steps a x)
          (cong₂ _+_ (simulate-steps gs x)
            (cong₂ _+_ (simulate-steps hs x)
              (cong (_+ 0) (differs-steps (proj₁ (simulate gs x))
                                          (proj₁ (simulate hs x)))))))
        (solve 4 (λ a g h m → a :+ (g :+ (h :+ (m :+ con 0)))
                              := a :+ g :+ h :+ m)
               refl j (length gs) (length hs) N)

-- Sound: an accepted input is clean and tells the netlists apart ...

check-sound : (a : Fin j → Fin N) (gs hs : List (NCT N)) (x : Assignment N) →
              proj₁ (check a gs hs x) ≡ true →
              Clean a x × ∃ λ w → runᴺ gs x w ≢ runᴺ hs x w
check-sound a gs hs x h =
  cleanᶜ-sound a x (proj₁ acc) ,
  w , λ e → ne (trans (at gs) (trans e (sym (at hs))))
  where
  c d : Bool
  c = proj₁ (cleanᶜ a x)
  d = proj₁ (differs (proj₁ (simulate gs x)) (proj₁ (simulate hs x)))

  acc : (c ≡ true) × (d ≡ true)
  acc = ∧-true c d h

  found : ∃ λ w → proj₁ (simulate gs x) w ≢ proj₁ (simulate hs x) w
  found = differs-sound (proj₁ (simulate gs x)) (proj₁ (simulate hs x))
                        (proj₂ acc)

  w : Fin _
  w = proj₁ found

  ne : proj₁ (simulate gs x) w ≢ proj₁ (simulate hs x) w
  ne = proj₂ found

  at : (ks : List (NCT _)) → proj₁ (simulate ks x) w ≡ runᴺ ks x w
  at ks = cong (λ f → f w) (simulate-run ks x)

-- ... and complete: every clean input that tells them apart is
-- accepted.

check-complete : (a : Fin j → Fin N) (gs hs : List (NCT N))
                 (x : Assignment N) → Clean a x →
                 (w : Fin N) → runᴺ gs x w ≢ runᴺ hs x w →
                 proj₁ (check a gs hs x) ≡ true
check-complete a gs hs x cl w ne =
  cong₂ _∧_ (cleanᶜ-complete a x cl)
            (differs-complete (proj₁ (simulate gs x)) (proj₁ (simulate hs x))
               w (λ e → ne (trans (sym (at gs)) (trans e (at hs)))))
  where
  at : (ks : List (NCT _)) → proj₁ (simulate ks x) w ≡ runᴺ ks x w
  at ks = cong (λ f → f w) (simulate-run ks x)

-- Only the values of the input matter.

check-cong : (a : Fin j → Fin N) (gs hs : List (NCT N)) {x x′ : Assignment N} →
             (∀ w → x w ≡ x′ w) →
             proj₁ (check a gs hs x) ≡ proj₁ (check a gs hs x′)
check-cong a gs hs {x} {x′} h =
  cong₂ _∧_ (cleanᶜ-cong a h) (differs-cong (same gs) (same hs))
  where
  same : (ks : List (NCT _)) →
         ∀ w → proj₁ (simulate ks x) w ≡ proj₁ (simulate ks x′) w
  same ks w =
    trans (cong (λ f → f w) (simulate-run ks x))
    (trans (runᴺ-cong ks h w) (sym (cong (λ f → f w) (simulate-run ks x′))))


------------------------------------------------------------------------
-- Membership in co-NP, as certificates

-- Two netlists are inequivalent on the clean inputs exactly when some
-- input is accepted.  From right to left by soundness; from left to
-- right, the inputs are finitely many (PathSum.Hardness.CNF.search):
-- if none were accepted, completeness would make the netlists agree on
-- every clean input.

certificate⇔ : (a : Fin j → Fin N) (gs hs : List (NCT N)) →
               (¬ Equivalentᴺ a gs hs) ⇔
               (∃ λ x → proj₁ (check a gs hs x) ≡ true)
certificate⇔ a gs hs = mk⇔ to from
  where
  from : (∃ λ x → proj₁ (check a gs hs x) ≡ true) → ¬ Equivalentᴺ a gs hs
  from (x , h) e with check-sound a gs hs x h
  ... | cl , w , ne = ne (e x cl w)

  agree : ¬ (∃ λ x → proj₁ (check a gs hs x) ≡ true) → Equivalentᴺ a gs hs
  agree none x cl w with bool-≟ (runᴺ gs x w) (runᴺ hs x w)
  ... | yes e  = e
  ... | no ne′ = contradiction (x , check-complete a gs hs x cl w ne′) none

  to : ¬ Equivalentᴺ a gs hs → ∃ λ x → proj₁ (check a gs hs x) ≡ true
  to ne with search (λ x → proj₁ (check a gs hs x)) (check-cong a gs hs)
  ... | yes found = found
  ... | no none   = contradiction (agree none) ne

-- For netlists of Toffoli and CNOT gates (PathSum.Reversible, read by
-- run), through their embedding into netlists with NOT gates.

certificate⇔ʳ : (a : Fin j → Fin N) (gs hs : List (Gate N)) →
                (¬ (∀ x → Clean a x → ∀ w → run gs x w ≡ run hs x w)) ⇔
                (∃ λ x → proj₁ (check a (map gate gs) (map gate hs) x) ≡ true)
certificate⇔ʳ a gs hs = ¬⇔ embed ⟨⇔⟩ certificate⇔ a (map gate gs) (map gate hs)
  where
  at : (ks : List (Gate _)) (x : Assignment _) →
       ∀ w → runᴺ (map gate ks) x w ≡ run ks x w
  at ks x w = cong (λ f → f w) (runᴺ-gates ks x)

  embed : (∀ x → Clean a x → ∀ w → run gs x w ≡ run hs x w) ⇔
          Equivalentᴺ a (map gate gs) (map gate hs)
  embed = mk⇔ (λ e x cl w → trans (at gs x w) (trans (e x cl w)
                                                     (sym (at hs x w))))
              (λ e x cl w → trans (sym (at gs x w)) (trans (e x cl w)
                                                           (at hs x w)))


------------------------------------------------------------------------
-- The reduction's instances

-- φ is satisfiable exactly when its netlist has a certificate against
-- the empty netlist: satisfiability is decidable, so it is the
-- negation of unsatisfiability, which is identity of the netlist on the
-- clean inputs (PathSum.Hardness.Netlist.netlist-identity⇔unsat).

sat⇔certificate : (φ : CNF n) →
                  Satisfiable φ ⇔
                  (∃ λ x → proj₁ (check (ancillas φ) (netlist φ) [] x) ≡ true)
sat⇔certificate φ =
  sat⇔¬unsat
  ⟨⇔⟩ ¬⇔ (sym⇔ (netlist-identity⇔unsat φ))
  ⟨⇔⟩ certificate⇔ (ancillas φ) (netlist φ) []
  where
  sat⇔¬unsat : Satisfiable φ ⇔ (¬ Unsatisfiable φ)
  sat⇔¬unsat = mk⇔
    (λ s u → Equivalence.to (unsat⇔¬sat φ) u s)
    (λ nu → by (sat? φ) nu)
    where
    by : Dec (Satisfiable φ) → ¬ Unsatisfiable φ → Satisfiable φ
    by (yes s) _  = s
    by (no ns) nu = contradiction (Equivalence.from (unsat⇔¬sat φ) ns) nu

-- The certificate of a satisfying assignment v: the input |v⟩|0⟩|0⟩,
-- whose target the netlist flips.

certificate : (φ : CNF n) (v : Assignment n) → ⟦ φ ⟧ᶠ v ≡ true →
              proj₁ (check (ancillas φ) (netlist φ) []
                           (blank (nodes (cnf φ)) v)) ≡ true
certificate {n} φ v sat =
  check-complete (ancillas φ) (netlist φ) [] x (blank-clean s v) (tgt φ)
    (λ e → xor-not (x (tgt φ))
             (trans (cong (x (tgt φ) xor_) (sym value))
                    (trans (sym flipped) e)))
  where
  s : ℕ
  s = nodes (cnf φ)

  x : Assignment (wires φ)
  x = blank s v

  value : ⟦ φ ⟧ᶠ (λ u → x (inputs φ u)) ≡ true
  value = trans (⟦⟧ᶠ-cong φ (blank-inp s v)) sat

  flipped : runᴺ (netlist φ) x (tgt φ) ≡
            x (tgt φ) xor ⟦ φ ⟧ᶠ (λ u → x (inputs φ u))
  flipped = trans (netlist-correct φ x (blank-clean s v) (tgt φ))
                  (≔-here x (tgt φ) _)

-- The check of the reduction's instance takes
-- n + 12 lits + 6 negs + 6 clauses + 10 steps: 2 lits + negs +
-- 2 clauses + 2 ancillas read, the netlist's 8 lits + 4 negs +
-- 2 clauses + 5 gates, none for the empty netlist, and its
-- n + 2 lits + negs + 2 clauses + 3 wires compared.

check-steps-cnf : (φ : CNF n) (x : Assignment (wires φ)) →
                  proj₂ (check (ancillas φ) (netlist φ) [] x) ≡
                  n + 12 * lits φ + 6 * negs φ + 6 * clauses φ + 10
check-steps-cnf {n} φ x =
  trans (check-steps (ancillas φ) (netlist φ) [] x)
  (trans (cong₂ (λ s N → suc s + length (netlist φ) + 0 + N)
                (nodes-cnf φ) (wires-exact φ))
  (trans (cong (λ g → suc (2 * lits φ + negs φ + 2 * clauses φ + 1) + g + 0 +
                      (n + 2 * lits φ + negs φ + 2 * clauses φ + 3))
               (netlist-length φ))
         (solve 4 (λ n L Q m →
                     con 1 :+ (con 2 :* L :+ Q :+ con 2 :* m :+ con 1) :+
                     (con 8 :* L :+ con 4 :* Q :+ con 2 :* m :+ con 5) :+
                     con 0 :+
                     (n :+ con 2 :* L :+ Q :+ con 2 :* m :+ con 3)
                     := n :+ con 12 :* L :+ con 6 :* Q :+ con 6 :* m :+ con 10)
                refl n (lits φ) (negs φ) (clauses φ))))

-- Linear in the formula, since negs φ ≤ lits φ.

private
  ≤-via : ∀ {a b} c → b ≡ a + c → a ≤ b
  ≤-via {a} c refl = m≤m+n a c

check-steps-bound : (φ : CNF n) (x : Assignment (wires φ)) →
                    proj₂ (check (ancillas φ) (netlist φ) [] x) ≤
                    n + 18 * ‖ φ ‖ + 10
check-steps-bound {n} φ x =
  subst (_≤ n + 18 * ‖ φ ‖ + 10) (sym (check-steps-cnf φ x))
        (≤-via (6 * d + 12 * clauses φ)
          (subst (λ L → n + 18 * (L + clauses φ) + 10 ≡
                        (n + 12 * L + 6 * negs φ + 6 * clauses φ + 10) +
                        (6 * d + 12 * clauses φ))
                 (proj₂ split)
                 (solve 4 (λ n Q d m →
                             n :+ con 18 :* ((Q :+ d) :+ m) :+ con 10
                             := (n :+ con 12 :* (Q :+ d) :+ con 6 :* Q :+
                                 con 6 :* m :+ con 10) :+
                                (con 6 :* d :+ con 12 :* m))
                        refl n (negs φ) d (clauses φ))))
  where
  split : ∃ λ d → negs φ + d ≡ lits φ
  split = m≤n⇒∃[o]m+o≡n (negs≤lits φ)

  d : ℕ
  d = proj₁ split
