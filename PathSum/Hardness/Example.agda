------------------------------------------------------------------------
-- Presentations of groups
--
-- Small cross-checks of footnote 2's reduction (Amy, QPL 2018,
-- section 4)
--
-- The reduction of PathSum.Hardness is proved for every formula; here
-- it is run on three small ones, at M₀ = 0, as a check that the
-- definitions do what the proofs say.
--
--    φ₀ = x₀ ∧ ¬x₀         unsatisfiable, 13 wires;
--    φ₁ = x₀ ∨ ¬x₁         satisfiable, 12 wires;
--    φ¬ = ¬x₀              satisfiable, 9 wires.
--
-- Checked by computation: satisfiability by the brute-force decision
-- (sat?, unsat?); the netlist of φ¬ gate by gate (netlist-¬: the
-- constant wire set, x₀ copied, negated, the disjunction with false,
-- the constant 1, the conjunction, the copy into the target, the
-- reverse, the constant wire cleared); every netlist's run on every
-- input whose ancillas are 0, wire by wire, against
-- |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ φ(x)⟩ (run₀, run₁, run¬), and one input with
-- ancillas at 1 on which φ₀'s netlist is not the identity (dirty₀);
-- and the sizes of φ₀'s netlist and Clifford+T circuit, against the
-- general formulas of PathSum.Hardness.Netlist and PathSum.Hardness
-- (sizes₀).  Proved from the general lemmas: no netlist without NOT
-- gates computes ¬x₀ that way (needs-NOT-¬); and the Clifford+T
-- statements about φ₀ and φ₁ (circuit₀-identity, circuit₁-not-identity)
-- are the general theorem at these formulas -- the path-sums
-- themselves, with 20 and 16 path variables, are never computed.
--
-- Phase B's certificates (PathSum.Hardness.Certificate), by
-- computation: the input x₀ = 1 is accepted as a certificate that
-- φ₁'s netlist is not the identity, in 48 steps (certificate₁,
-- steps₁), as the general formula says; no clean input is accepted for
-- the unsatisfiable φ₀, and the dirty input of dirty₀ is rejected
-- because the check reads the ancillas (no-certificate₀, rejected₀,
-- steps₀).  From the general theorem: φ₁ is satisfiable because its
-- certificate is accepted (sat₁-by-certificate).  Nothing here states
-- an equivalence ≋ of a prepared path-sum at a closed formula:
-- PathSum.Hardness.Prepared.cleanPS-identity⇔unsat at φ₀ is the
-- general theorem, but taking the equivalence out of it at a closed
-- formula (Equivalence.from … : cleanPS φ₀ ≋ idPS) made Agda unfold the
-- 20 path variables of the amplitudes, and did not finish in 900 s.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Hardness.Example where

open import Data.Bool.Base using
  (Bool; true; false; not; _∨_; _xor_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.List.Base using (List; []; _∷_; map; length; allFin)
open import Data.Nat.Base using (ℕ; _≡ᵇ_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Ancillas 0 using (_≋[_]₀*_)
open import PathSum.Base using (idPS)
open import PathSum.CRK.Path 0 using (⟦_⟧; norm)
open import PathSum.Hardness 0 using (circuit; hardness)
open import PathSum.Hardness.Certificate using (check; sat⇔certificate)
open import PathSum.Hardness.CNF using
  (Assignment; _∷ᵃ_; pos; neg; CNF; Satisfiable; Unsatisfiable;
   unsat⇔¬sat; sat?; unsat?; ‖_‖; lits; negs; clauses; ⟦_⟧ᵇ; cnf)
open import PathSum.Hardness.Netlist using
  (NCT; X; gate; runᴺ; netlist; wires; ancillas; nots; toffolisᴺ; cnotsᴺ;
   Clean; needs-NOT)
open import PathSum.Reversible using (Gate; ccx; cx; run)
open import PathSum.Toffoli.Netlist 0 using (tcount)


------------------------------------------------------------------------
-- The formulas

-- x₀ ∧ ¬x₀.

φ₀ : CNF 1
φ₀ = (pos zero ∷ []) ∷ (neg zero ∷ []) ∷ []

-- x₀ ∨ ¬x₁.

φ₁ : CNF 2
φ₁ = (pos zero ∷ neg (suc zero) ∷ []) ∷ []

-- ¬x₀.

φ¬ : CNF 1
φ¬ = (neg zero ∷ []) ∷ []

-- Decided by trying every assignment.

unsat₀ : Unsatisfiable φ₀
unsat₀ = toWitness {a? = unsat? φ₀} tt

sat₁ : Satisfiable φ₁
sat₁ = toWitness {a? = sat? φ₁} tt

-- A satisfying assignment by hand: x₀ = 1.

sat₁′ : Satisfiable φ₁
sat₁′ = (true ∷ᵃ false ∷ᵃ (λ ())) , refl


------------------------------------------------------------------------
-- The netlist of ¬x₀, gate by gate

-- A gate as the numbers of its wires.

data Shape : Set where
  not′ : ℕ → Shape
  cnot : ℕ → ℕ → Shape
  toff : ℕ → ℕ → ℕ → Shape

shape : ∀ {N} → NCT N → Shape
shape (X w)                        = not′ (toℕ w)
shape (gate (cx c t _))            = cnot (toℕ c) (toℕ t)
shape (gate (ccx c₁ c₂ t _ _ _))  = toff (toℕ c₁) (toℕ c₂) (toℕ t)

-- On 9 wires: x₀ (wire 0), the constant wire (1), the scratch wires
-- 2 … 7 of the six nodes -- the conjunction (2), the disjunction (3),
-- the negation (4), the variable (5), false (6), true (7) -- and the
-- target (8).

netlist-¬ :
  map shape (netlist φ¬) ≡
  not′ 1 ∷
  cnot 0 5 ∷ cnot 5 4 ∷ cnot 1 4 ∷ cnot 4 3 ∷ cnot 6 3 ∷ toff 4 6 3 ∷
  cnot 1 7 ∷ toff 3 7 2 ∷
  cnot 2 8 ∷
  toff 3 7 2 ∷ cnot 1 7 ∷
  toff 4 6 3 ∷ cnot 6 3 ∷ cnot 4 3 ∷ cnot 1 4 ∷ cnot 5 4 ∷ cnot 0 5 ∷
  not′ 1 ∷ []
netlist-¬ = refl


------------------------------------------------------------------------
-- Runs on every input whose ancillas are 0

-- The input with the given bits on the given wires and 0 elsewhere.

set : ∀ {N} → List (ℕ × Bool) → Assignment N
set []            w = false
set ((i , b) ∷ l) w = if toℕ w ≡ᵇ i then b else set l w

-- x₀ ∧ ¬x₀ is never true: the netlist is the identity (x₀ on wire 0,
-- the target on wire 12).

run₀ : ∀ a t →
       map (runᴺ (netlist φ₀) (set ((0 , a) ∷ (12 , t) ∷ []))) (allFin 13) ≡
       map (set ((0 , a) ∷ (12 , t) ∷ [])) (allFin 13)
run₀ false false = refl
run₀ false true  = refl
run₀ true  false = refl
run₀ true  true  = refl

-- Off the clean inputs it is not: with the ancillas of the two false
-- nodes (wires 5 and 10) at 1, both clauses read 1 and the target
-- flips.  That is why the reduction is stated on the clean inputs.

dirty₀ :
  map (runᴺ (netlist φ₀) (set ((5 , true) ∷ (10 , true) ∷ []))) (allFin 13) ≡
  map (set ((5 , true) ∷ (10 , true) ∷ (12 , true) ∷ [])) (allFin 13)
dirty₀ = refl

-- x₀ ∨ ¬x₁ flips the target (wire 11) except at x₀ = 0, x₁ = 1.

run₁ : ∀ a b t →
       map (runᴺ (netlist φ₁) (set ((0 , a) ∷ (1 , b) ∷ (11 , t) ∷ [])))
           (allFin 12) ≡
       map (set ((0 , a) ∷ (1 , b) ∷ (11 , t xor (a ∨ not b)) ∷ [])) (allFin 12)
run₁ false false false = refl
run₁ false false true  = refl
run₁ false true  false = refl
run₁ false true  true  = refl
run₁ true  false false = refl
run₁ true  false true  = refl
run₁ true  true  false = refl
run₁ true  true  true  = refl

-- ¬x₀ flips the target (wire 8) at x₀ = 0.

run¬ : ∀ a t →
       map (runᴺ (netlist φ¬) (set ((0 , a) ∷ (8 , t) ∷ []))) (allFin 9) ≡
       map (set ((0 , a) ∷ (8 , t xor not a) ∷ [])) (allFin 9)
run¬ false false = refl
run¬ false true  = refl
run¬ true  false = refl
run¬ true  true  = refl

-- Its two NOT gates cannot be done without: no netlist of Toffoli and
-- CNOT gates, on any wires, computes ¬x₀ into a target on the inputs
-- whose ancillas are 0 (¬x₀ is true at 0).

private
  true≢false : ¬ (true ≡ false)
  true≢false ()

needs-NOT-¬ : ∀ {N j} (gs : List (Gate N)) (ι : Fin 1 → Fin N)
              (a : Fin j → Fin N) (t : Fin N) →
              ¬ (∀ x → Clean a x →
                 run gs x t ≡ x t xor ⟦ cnf φ¬ ⟧ᵇ (λ v → x (ι v)))
needs-NOT-¬ gs ι a t h = true≢false (needs-NOT (cnf φ¬) gs ι a t h)


------------------------------------------------------------------------
-- Sizes, against the general formulas

-- φ₀ has two literal occurrences, one negative, and two clauses:
-- ‖φ₀‖ = 4; 1 + 4 + 1 + 4 + 3 = 13 wires; 2 NOT gates, 8 Toffoli
-- gates, 6·2 + 4 + 3 = 19 CNOTs, 29 gates; over Clifford+T,
-- 36·2 + 4 + 30·2 + 9 = 145 gates, 14·4 = 56 T gates and 4·4 + 4 = 20
-- Hadamards, hence path variables.

sizes₀ : (‖ φ₀ ‖ ≡ 4) × (lits φ₀ ≡ 2) × (negs φ₀ ≡ 1) × (clauses φ₀ ≡ 2) ×
         (wires φ₀ ≡ 13) ×
         (nots (netlist φ₀) ≡ 2) × (toffolisᴺ (netlist φ₀) ≡ 8) ×
         (cnotsᴺ (netlist φ₀) ≡ 19) × (length (netlist φ₀) ≡ 29) ×
         (length (circuit φ₀) ≡ 145) × (tcount (circuit φ₀) ≡ 56) ×
         (norm (circuit φ₀) ≡ 20)
sizes₀ = refl , refl , refl , refl , refl , refl , refl , refl , refl ,
         refl , refl , refl


------------------------------------------------------------------------
-- The Clifford+T circuits

-- The general theorem at φ₀ and φ₁: the expansion of x₀ ∧ ¬x₀'s
-- netlist is the identity on the clean inputs, that of x₀ ∨ ¬x₁'s is
-- not.

circuit₀-identity : ⟦ circuit φ₀ ⟧ ≋[ ancillas φ₀ ]₀* idPS
circuit₀-identity = Equivalence.from (hardness φ₀) unsat₀

circuit₁-not-identity : ¬ (⟦ circuit φ₁ ⟧ ≋[ ancillas φ₁ ]₀* idPS)
circuit₁-not-identity eq =
  Equivalence.to (unsat⇔¬sat φ₁) (Equivalence.to (hardness φ₁) eq) sat₁


------------------------------------------------------------------------
-- Certificates

-- x₀ = 1 satisfies x₀ ∨ ¬x₁: the input with x₀ = 1 and every other
-- wire 0 is accepted, in 2 + 12·2 + 6·1 + 6·1 + 10 = 48 steps -- 9
-- ancillas read, 27 gates simulated, none for the empty netlist, 12
-- wires compared.

certificate₁ : proj₁ (check (ancillas φ₁) (netlist φ₁) []
                            (set ((0 , true) ∷ []))) ≡ true
certificate₁ = refl

steps₁ : proj₂ (check (ancillas φ₁) (netlist φ₁) []
                      (set ((0 , true) ∷ []))) ≡ 48
steps₁ = refl

-- The general theorem turns the certificate into satisfiability.

sat₁-by-certificate : Satisfiable φ₁
sat₁-by-certificate =
  Equivalence.from (sat⇔certificate φ₁) (set ((0 , true) ∷ []) , refl)

-- For the unsatisfiable x₀ ∧ ¬x₀ no clean input is accepted; the
-- dirty input of dirty₀, which the netlist does move, is rejected
-- because its ancillas are not 0.  53 steps each.

no-certificate₀ : ∀ a t →
                  proj₁ (check (ancillas φ₀) (netlist φ₀) []
                               (set ((0 , a) ∷ (12 , t) ∷ []))) ≡ false
no-certificate₀ false false = refl
no-certificate₀ false true  = refl
no-certificate₀ true  false = refl
no-certificate₀ true  true  = refl

rejected₀ : proj₁ (check (ancillas φ₀) (netlist φ₀) []
                         (set ((5 , true) ∷ (10 , true) ∷ []))) ≡ false
rejected₀ = refl

steps₀ : proj₂ (check (ancillas φ₀) (netlist φ₀) []
                      (set ((5 , true) ∷ (10 , true) ∷ []))) ≡ 53
steps₀ = refl


