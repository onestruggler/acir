------------------------------------------------------------------------
-- Presentations of groups
--
-- CNF formulas, and the Boolean formulas they are compiled through
-- (Amy, QPL 2018, section 4, footnote 2)
--
-- Footnote 2 of section 4 records a referee's observation: were the
-- normal forms of the calculus unique, "equivalence checking of
-- reversible Boolean circuits [would be] in P.  As this problem is
-- co-NP-complete, uniqueness of our normal forms would indeed imply
-- P = co-NP."  Its logical half -- unique normal forms would settle
-- equivalence by reduction alone, with no expansion of the remaining
-- variables -- is PathSum.Expand.unique⇒no-expansion.  This
-- development formalises the reduction behind its complexity half:
-- unsatisfiability of CNF formulas reduces, through circuits of size
-- linear in the formula, to identity checking of reversible circuits
-- and of Clifford+T circuits, the identity being checked on the inputs
-- whose ancillas are 0.  The plan:
--
-- * Here: CNF formulas over n variables -- lists of clauses, a clause
--   a list of literals x_v or ¬x_v -- their evaluation, satisfiability
--   (decidable by trying every assignment: sat?, unsat?), and their
--   sizes: literal occurrences (lits), negative ones (negs), clauses,
--   and ‖φ‖ = lits φ + clauses φ.  And Boolean formulas over variables,
--   constants, ¬, ∧ and ∨ (Formula), from which the netlist is
--   compiled: cnf φ is the CNF formula read as one (⟦cnf⟧), with
--   2 lits + negs + 2 clauses + 1 nodes (nodes-cnf).
--
-- * PathSum.Hardness.Netlist: a Boolean formula compiled into a
--   netlist of Toffoli and CNOT gates (PathSum.Reversible), one fresh
--   ancilla per node, which holds the node's value once the netlist has
--   run from ancillas at 0 (compile-correct): x_v copied by a CNOT,
--   e₁ ∧ e₂ by a Toffoli gate, e₁ ∨ e₂ = e₁ ⊕ e₂ ⊕ e₁e₂ by two CNOTs and
--   a Toffoli gate, ¬e and the constant 1 by CNOTs from an ancilla
--   holding 1.  Bennett's compute-copy-uncompute then xors the value
--   into a target and restores every other wire (core).  The ancilla
--   holding 1 is set by a NOT gate before and cleared by another after:
--   the only two NOT gates, so the netlist is over {NOT, CNOT, Toffoli}
--   (oracle; the netlists with NOT gates, NCT, are run by runᴺ).  On
--   the standard layout -- inputs, ancillas, target, as the paper's
--   |x⟩|0⟩|t⟩ -- it computes |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ e(x)⟩ on every input
--   whose ancillas are 0 (oracle-correct), so on those inputs it is the
--   identity exactly when e is unsatisfiable (oracle-identity⇔; for a
--   CNF formula, netlist and netlist-identity⇔unsat).  Its size is
--   linear in the formula: n + 2 lits + negs + 2 clauses + 3 wires, two
--   NOT gates, 2‖φ‖ Toffoli gates and 6 lits + 4 negs + 3 CNOTs.  The
--   NOT gates are needed: without them the input 0 stays 0 (needs-NOT).
--
-- * PathSum.Hardness: a netlist over {NOT, CNOT, Toffoli} expanded
--   into Clifford+T -- a Toffoli gate into PathSum.Toffoli's seven-T
--   circuit, a NOT into H R₁ H (X is not a gate of {H, CNOT, R_k}) --
--   computes the netlist's Boolean function (expandᴺ-computes, by
--   proposition 2.7 through PathSum.Classical); two path-sums that
--   compute Boolean functions are equivalent on the clean inputs
--   exactly when the functions agree there (≋[]₀*⇔agree); so the
--   expansion is the identity on the clean inputs exactly when the
--   netlist is (expandᴺ-identity⇔, and expandᴺ-≋id⇔ with no
--   ancillas), and for a CNF formula φ
--
--      ⟦ circuit φ ⟧ ≋[ ancillas φ ]₀* idPS  ⇔  φ is unsatisfiable
--
--   (hardness; hardness-set0 in the set0 form, hardness-[] against the
--   empty circuit).  Its resources: 4‖φ‖ + 4 path variables, 14‖φ‖ T
--   gates, at most 40‖φ‖ + 9 gates.
--
-- * PathSum.Hardness.Example: the definitions run on three small
--   formulas, as a check.
--
-- Phase B -- membership as a certificate check, and the footnote's
-- conditional under unique normal forms -- is planned in the header of
-- PathSum.Hardness.Certificate.
--
-- What is not formalised: machines and complexity classes.  The
-- reduction is a structurally recursive function whose output has the
-- size stated, but its running time is not a formal notion here, and
-- neither is the co-NP-completeness of unsatisfiability (Cook and
-- Levin), membership in co-NP as a statement about machines (phase B
-- gives the certificates and counts the simulation steps that check
-- them), nor the conclusion P = co-NP.  The footnote speaks of
-- equivalence checking; identity checking -- equivalence with the
-- empty circuit -- is a special case of it, so a reduction to identity
-- checking is one to equivalence checking too.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Hardness.CNF where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; +-mono-≤)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (∃; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Assignments

Assignment : ℕ → Set
Assignment n = Fin n → Bool

-- A value for the first variable, then the rest.

infixr 5 _∷ᵃ_

_∷ᵃ_ : Bool → Assignment n → Assignment (suc n)
(b ∷ᵃ x) zero    = b
(b ∷ᵃ x) (suc v) = x v


------------------------------------------------------------------------
-- CNF formulas

-- A literal is a variable or its negation; a clause is a list of
-- literals, a CNF formula a list of clauses.

data Literal (n : ℕ) : Set where
  pos neg : Fin n → Literal n

Clause : ℕ → Set
Clause n = List (Literal n)

CNF : ℕ → Set
CNF n = List (Clause n)

-- A clause is the disjunction of its literals and a formula the
-- conjunction of its clauses: the empty clause is false, the empty
-- formula true.

⟦_⟧ˡ : Literal n → Assignment n → Bool
⟦ pos v ⟧ˡ x = x v
⟦ neg v ⟧ˡ x = not (x v)

⟦_⟧ᶜ : Clause n → Assignment n → Bool
⟦ []    ⟧ᶜ x = false
⟦ l ∷ c ⟧ᶜ x = ⟦ l ⟧ˡ x ∨ ⟦ c ⟧ᶜ x

⟦_⟧ᶠ : CNF n → Assignment n → Bool
⟦ []    ⟧ᶠ x = true
⟦ c ∷ φ ⟧ᶠ x = ⟦ c ⟧ᶜ x ∧ ⟦ φ ⟧ᶠ x

-- Only the values of the assignment are read.

⟦⟧ˡ-cong : (l : Literal n) {x x′ : Assignment n} →
           (∀ v → x v ≡ x′ v) → ⟦ l ⟧ˡ x ≡ ⟦ l ⟧ˡ x′
⟦⟧ˡ-cong (pos v) h = h v
⟦⟧ˡ-cong (neg v) h = cong not (h v)

⟦⟧ᶜ-cong : (c : Clause n) {x x′ : Assignment n} →
           (∀ v → x v ≡ x′ v) → ⟦ c ⟧ᶜ x ≡ ⟦ c ⟧ᶜ x′
⟦⟧ᶜ-cong []      h = refl
⟦⟧ᶜ-cong (l ∷ c) h = cong₂ _∨_ (⟦⟧ˡ-cong l h) (⟦⟧ᶜ-cong c h)

⟦⟧ᶠ-cong : (φ : CNF n) {x x′ : Assignment n} →
           (∀ v → x v ≡ x′ v) → ⟦ φ ⟧ᶠ x ≡ ⟦ φ ⟧ᶠ x′
⟦⟧ᶠ-cong []      h = refl
⟦⟧ᶠ-cong (c ∷ φ) h = cong₂ _∧_ (⟦⟧ᶜ-cong c h) (⟦⟧ᶠ-cong φ h)


------------------------------------------------------------------------
-- Satisfiability

Satisfiable Unsatisfiable : CNF n → Set
Satisfiable   φ = ∃ λ x → ⟦ φ ⟧ᶠ x ≡ true
Unsatisfiable φ = ∀ x → ⟦ φ ⟧ᶠ x ≡ false

private
  not-true : ∀ b → ¬ (b ≡ true) → b ≡ false
  not-true true  f = contradiction refl f
  not-true false f = refl

unsat⇔¬sat : (φ : CNF n) → Unsatisfiable φ ⇔ (¬ Satisfiable φ)
unsat⇔¬sat φ = mk⇔
  (λ u s → contradiction (trans (sym (proj₂ s)) (u (proj₁ s))) λ ())
  (λ ns x → not-true (⟦ φ ⟧ᶠ x) (λ s → ns (x , s)))

-- Satisfiability is decidable, by trying every assignment: some
-- assignment makes f true, or none does, for any f that reads only
-- values.  (Decidability is elementary; the footnote is about its
-- cost, which is not formalised.)

private
  ∷ᵃ-cong : (b : Bool) {x x′ : Assignment n} → (∀ v → x v ≡ x′ v) →
            ∀ v → (b ∷ᵃ x) v ≡ (b ∷ᵃ x′) v
  ∷ᵃ-cong b h zero    = refl
  ∷ᵃ-cong b h (suc v) = h v

  ∷ᵃ-η : (x : Assignment (suc n)) (b : Bool) → x zero ≡ b →
         ∀ v → (b ∷ᵃ (λ u → x (suc u))) v ≡ x v
  ∷ᵃ-η x b e zero    = sym e
  ∷ᵃ-η x b e (suc v) = refl

search : (f : Assignment n → Bool) →
         (∀ {x x′} → (∀ v → x v ≡ x′ v) → f x ≡ f x′) →
         Dec (∃ λ x → f x ≡ true)
search {zero} f resp = at (f (λ ())) refl
  where
  at : ∀ b → f (λ ()) ≡ b → Dec (∃ λ x → f x ≡ true)
  at true  e = yes ((λ ()) , e)
  at false e = no λ s → contradiction
    (trans (sym (proj₂ s)) (trans (resp {proj₁ s} {λ ()} (λ ())) e)) λ ()
search {suc n} f resp =
  both (search (λ x → f (false ∷ᵃ x)) (λ h → resp (∷ᵃ-cong false h)))
       (search (λ x → f (true ∷ᵃ x)) (λ h → resp (∷ᵃ-cong true h)))
  where
  both : Dec (∃ λ x → f (false ∷ᵃ x) ≡ true) →
         Dec (∃ λ x → f (true ∷ᵃ x) ≡ true) →
         Dec (∃ λ x → f x ≡ true)
  both (yes (x , h)) _             = yes (false ∷ᵃ x , h)
  both (no _)        (yes (x , h)) = yes (true ∷ᵃ x , h)
  both (no ¬₀)       (no ¬₁)       =
    no λ s → back (proj₁ s) (proj₁ s zero) refl (proj₂ s)
    where
    back : (x : Assignment (suc n)) (b : Bool) → x zero ≡ b → ¬ (f x ≡ true)
    back x false e h =
      ¬₀ ((λ u → x (suc u)) , trans (resp (∷ᵃ-η x false e)) h)
    back x true  e h =
      ¬₁ ((λ u → x (suc u)) , trans (resp (∷ᵃ-η x true e)) h)

sat? : (φ : CNF n) → Dec (Satisfiable φ)
sat? φ = search ⟦ φ ⟧ᶠ (⟦⟧ᶠ-cong φ)

unsat? : (φ : CNF n) → Dec (Unsatisfiable φ)
unsat? φ with sat? φ
... | yes s = no λ u → Equivalence.to (unsat⇔¬sat φ) u s
... | no ns = yes (Equivalence.from (unsat⇔¬sat φ) ns)


------------------------------------------------------------------------
-- Boolean formulas

infixr 6 _∧ᶠ_
infixr 5 _∨ᶠ_

data Formula (n : ℕ) : Set where
  var       : Fin n → Formula n
  cst       : Bool → Formula n
  ¬ᶠ_       : Formula n → Formula n
  _∧ᶠ_ _∨ᶠ_ : Formula n → Formula n → Formula n

⟦_⟧ᵇ : Formula n → Assignment n → Bool
⟦ var v    ⟧ᵇ x = x v
⟦ cst b    ⟧ᵇ x = b
⟦ ¬ᶠ e     ⟧ᵇ x = not (⟦ e ⟧ᵇ x)
⟦ e₁ ∧ᶠ e₂ ⟧ᵇ x = ⟦ e₁ ⟧ᵇ x ∧ ⟦ e₂ ⟧ᵇ x
⟦ e₁ ∨ᶠ e₂ ⟧ᵇ x = ⟦ e₁ ⟧ᵇ x ∨ ⟦ e₂ ⟧ᵇ x

⟦⟧ᵇ-cong : (e : Formula n) {x x′ : Assignment n} →
           (∀ v → x v ≡ x′ v) → ⟦ e ⟧ᵇ x ≡ ⟦ e ⟧ᵇ x′
⟦⟧ᵇ-cong (var v)    h = h v
⟦⟧ᵇ-cong (cst b)    h = refl
⟦⟧ᵇ-cong (¬ᶠ e)     h = cong not (⟦⟧ᵇ-cong e h)
⟦⟧ᵇ-cong (e₁ ∧ᶠ e₂) h = cong₂ _∧_ (⟦⟧ᵇ-cong e₁ h) (⟦⟧ᵇ-cong e₂ h)
⟦⟧ᵇ-cong (e₁ ∨ᶠ e₂) h = cong₂ _∨_ (⟦⟧ᵇ-cong e₁ h) (⟦⟧ᵇ-cong e₂ h)

-- The number of nodes: the compiled netlist gives each its own
-- ancilla.

nodes : Formula n → ℕ
nodes (var _)    = 1
nodes (cst _)    = 1
nodes (¬ᶠ e)     = suc (nodes e)
nodes (e₁ ∧ᶠ e₂) = suc (nodes e₁ + nodes e₂)
nodes (e₁ ∨ᶠ e₂) = suc (nodes e₁ + nodes e₂)

-- A CNF formula as a Boolean formula: a clause is a chain of
-- disjunctions ending in false, the formula a chain of conjunctions
-- ending in true.

literal : Literal n → Formula n
literal (pos v) = var v
literal (neg v) = ¬ᶠ var v

clause : Clause n → Formula n
clause []      = cst false
clause (l ∷ c) = literal l ∨ᶠ clause c

cnf : CNF n → Formula n
cnf []      = cst true
cnf (c ∷ φ) = clause c ∧ᶠ cnf φ

⟦literal⟧ : (l : Literal n) (x : Assignment n) →
            ⟦ literal l ⟧ᵇ x ≡ ⟦ l ⟧ˡ x
⟦literal⟧ (pos v) x = refl
⟦literal⟧ (neg v) x = refl

⟦clause⟧ : (c : Clause n) (x : Assignment n) → ⟦ clause c ⟧ᵇ x ≡ ⟦ c ⟧ᶜ x
⟦clause⟧ []      x = refl
⟦clause⟧ (l ∷ c) x = cong₂ _∨_ (⟦literal⟧ l x) (⟦clause⟧ c x)

⟦cnf⟧ : (φ : CNF n) (x : Assignment n) → ⟦ cnf φ ⟧ᵇ x ≡ ⟦ φ ⟧ᶠ x
⟦cnf⟧ []      x = refl
⟦cnf⟧ (c ∷ φ) x = cong₂ _∧_ (⟦clause⟧ c x) (⟦cnf⟧ φ x)

-- So φ is unsatisfiable exactly when cnf φ is false everywhere.

unsat⇔cnf : (φ : CNF n) →
            Unsatisfiable φ ⇔ (∀ x → ⟦ cnf φ ⟧ᵇ x ≡ false)
unsat⇔cnf φ = mk⇔ (λ u x → trans (⟦cnf⟧ φ x) (u x))
                  (λ u x → trans (sym (⟦cnf⟧ φ x)) (u x))


------------------------------------------------------------------------
-- Sizes

-- Literal occurrences, the negative ones among them, and clauses; the
-- size of a formula is ‖φ‖ = lits φ + clauses φ.

negsᶜ : Clause n → ℕ
negsᶜ []          = 0
negsᶜ (pos _ ∷ c) = negsᶜ c
negsᶜ (neg _ ∷ c) = suc (negsᶜ c)

lits negs clauses : CNF n → ℕ
lits []      = 0
lits (c ∷ φ) = length c + lits φ
negs []      = 0
negs (c ∷ φ) = negsᶜ c + negs φ
clauses      = length

‖_‖ : CNF n → ℕ
‖ φ ‖ = lits φ + clauses φ

negsᶜ≤length : (c : Clause n) → negsᶜ c ≤ length c
negsᶜ≤length []          = z≤n
negsᶜ≤length (pos _ ∷ c) = m≤n⇒m≤1+n (negsᶜ≤length c)
negsᶜ≤length (neg _ ∷ c) = s≤s (negsᶜ≤length c)

negs≤lits : (φ : CNF n) → negs φ ≤ lits φ
negs≤lits []      = z≤n
negs≤lits (c ∷ φ) = +-mono-≤ (negsᶜ≤length c) (negs≤lits φ)

-- The nodes of cnf φ: per clause of k literals, q of them negative,
-- k disjunctions, k + q literal nodes and the final false; per
-- formula, one conjunction per clause and the final true.

nodes-clause : (c : Clause n) →
               nodes (clause c) ≡ 2 * length c + negsᶜ c + 1
nodes-clause []          = refl
nodes-clause (pos _ ∷ c) =
  trans (cong (λ m → suc (suc m)) (nodes-clause c))
        (solve 2 (λ k q → con 2 :+ (con 2 :* k :+ q :+ con 1)
                          := con 2 :* (con 1 :+ k) :+ q :+ con 1)
               refl (length c) (negsᶜ c))
nodes-clause (neg _ ∷ c) =
  trans (cong (λ m → suc (suc (suc m))) (nodes-clause c))
        (solve 2 (λ k q → con 3 :+ (con 2 :* k :+ q :+ con 1)
                          := con 2 :* (con 1 :+ k) :+ (con 1 :+ q) :+ con 1)
               refl (length c) (negsᶜ c))

nodes-cnf : (φ : CNF n) →
            nodes (cnf φ) ≡ 2 * lits φ + negs φ + 2 * clauses φ + 1
nodes-cnf []      = refl
nodes-cnf (c ∷ φ) =
  trans (cong suc (cong₂ _+_ (nodes-clause c) (nodes-cnf φ)))
        (solve 5 (λ k q L Q m →
                    con 1 :+ ((con 2 :* k :+ q :+ con 1) :+
                              (con 2 :* L :+ Q :+ con 2 :* m :+ con 1))
                    := con 2 :* (k :+ L) :+ (q :+ Q) :+
                       con 2 :* (con 1 :+ m) :+ con 1)
               refl (length c) (negsᶜ c) (lits φ) (negs φ) (clauses φ))
