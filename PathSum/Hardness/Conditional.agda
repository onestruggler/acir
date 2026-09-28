------------------------------------------------------------------------
-- Presentations of groups
--
-- Footnote 2's conditional: unique normal forms would decide
-- unsatisfiability by normalisation (Amy, QPL 2018, section 4)
--
-- Footnote 2: uniqueness of the normal forms "would imply that
-- equivalence checking of reversible Boolean circuits is in P.  As this
-- problem is co-NP-complete, uniqueness of our normal forms would
-- indeed imply P = co-NP."  The plan of phase B is in the header of
-- PathSum.Hardness.Certificate; this module states the conditional.
--
-- The test.  normal-formᶠ (PathSum.Full.Match) rewrites a path-sum
-- with all of figure 2 until no rule applies.  NormalFormId ξ says that
-- the normal form it reaches from ξ has no path variables and passes
-- PathSum.Expand's syntactic test -- no normalisation, outputs the
-- inputs modulo 2, phase 0 modulo 1 (SyntacticId) -- the test the
-- paper's verifier applies.  It is decidable (normal-form-id?) and
-- sound (normal-form-id-sound: by proposition 3.1 along the chain and
-- PathSum.Syntactic.id⇔syntactic).
--
-- The hypothesis.  UniqueNormalForms is PathSum.Expand's, the one
-- behind Expand.unique⇒no-expansion: equivalent irreducible path-sums
-- have as many path variables.  (It is the weakest uniqueness up to
-- equivalence, implied by uniqueness up to syntax, so what follows
-- holds under that too.  It is false -- Examples.Incomplete.normal-
-- forms-not-unique refutes it at M₀ = 0 -- so this is a conditional
-- whose hypothesis is known to fail, like the footnote's.)  Under it
-- the test is complete: an irreducible path-sum with a path variable
-- is never the identity, so if ξ is, its normal form has none and is
-- syntactically the identity (unique⇒normal-form-id).
--
-- The conditional.  With PathSum.Hardness.Prepared.cleanPS -- phase A's
-- circuit of φ with its ancillas prepared, equivalent to the identity
-- exactly when φ is unsatisfiable -- under the hypothesis
--
--    φ is unsatisfiable  ⇔  the normal form of cleanPS φ is
--                           syntactically the identity
--                                              (unsat-by-normalisation)
--
-- which decides unsatisfiability by normalising cleanPS φ (unsat?ᵘ);
-- without the hypothesis the right-hand side still refutes
-- satisfiability (normal-form-refutes).  The same holds for any two
-- netlists over {NOT, CNOT, Toffoli} and their prepared miter:
-- equivalence on the clean inputs is decided by normalising it
-- (equivalence-by-normalisation, equivalent?ᵘ) -- the footnote's
-- equivalence checking of reversible Boolean circuits, done by
-- normalisation.
--
-- The size of what is normalised.  cleanPS φ has the path variables and
-- normalisation of phase A's circuit, 4‖φ‖ + 4 of each, on at most
-- n + 3‖φ‖ + 3 wires (cleanPS-size).  The circuit's path-sum is
-- represented, in the sense of PathSum.Size.Sparse, by at most
-- (n + 43‖φ‖ + 13)^3 terms (circuit-size, circuit-size-bound):
-- corollary 2.15 at level 3, the T gates of the Toffoli expansion
-- (circuit-level).  cleanPS φ's polynomials are the circuit's with the
-- ancilla inputs set to 0 -- terms dropped -- and one input variable
-- added to each ancilla output; a sparse representation of cleanPS φ
-- itself is not built (those outputs are liftings of linear forms only
-- modulo 2, which PathSum.Size.Sparse does not allow).
--
-- What stands between this and P = co-NP -- none of it formalised:
--
--  * Machines.  P, NP and co-NP, and polynomial time, are not defined;
--    "decides" means a function to Dec, and sizes are counted.
--  * Cook and Levin.  That unsatisfiability of CNF formulas is
--    co-NP-hard.  Phase A reduces it to identity checking of
--    reversible netlists with linear size, and
--    PathSum.Hardness.Certificate puts that problem's complement in the
--    form of NP (short certificates, checked in a linear number of
--    simulation steps); "co-NP-complete" needs both on a machine.
--  * The reduction's running time.  cleanPS φ is computed by structural
--    recursion from φ; only the sizes above are proved.
--  * The normaliser's running time.  normal-formᶠ is exponential here:
--    PathSum.Full.Match decides each rule's premises by comparing
--    polynomials over all their monomials.  The paper's proposition 3.2
--    says rewriting takes polynomial time.  Beyond Clifford that cannot
--    be taken for granted, and on these instances it fails under the
--    hypothesis itself: every irreducible reduct of cleanPS φ then has
--    no path variables (unique⇒no-paths), and every reduct without
--    path variables outputs x_t ⊕ φ(x) on the target at every input
--    (reduct-outputs).  For the single clause x₁ ∨ … ∨ x_n its target
--    output polynomial then has an odd coefficient on each nonempty
--    monomial over the inputs, the algebraic normal form of the OR
--    (PathSum.Hardness.Blowup: reduct-odd-coefficients,
--    unique⇒odd-on-inputs) -- 2^n − 1 terms, a count left in words.  So
--    under the hypothesis the normal forms of these path-sums, which
--    have linearly many path variables and wires, have exponentially
--    many terms as polynomials, and normalisation to polynomials
--    listed term by term cannot be polynomial on them: uniqueness and
--    proposition 3.2 as stated are incompatible here whatever P and
--    co-NP are -- an argument in words over the formal theorem.
--  * The conclusion P = co-NP itself.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hardness.Conditional (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; _xor_; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (0ℤ)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (zero; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ⊔-lub; +-mono-≤; ^-monoˡ-≤; ^-monoʳ-≤; *-monoʳ-≤)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (∃; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; map′)
open import Relation.Nullary.Negation using (¬_; contradiction)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using (_[_≔_]; same-refl)
open import PathSum.Base using (PathSum; phase; idPS)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (_computes_; amp-computes; ≋-computes; none; outBit-none)
open import PathSum.CRK.Adjoint M using (level-++)
open import PathSum.CRK.Circuit M using (level; paths≡norm)
open import PathSum.CRK.Path M₀ using (⟦_⟧; norm; paths)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; scale; scale-map; scale-injective; √2·-map;
   √2·-0ᴬ; zpow-0≢0ᴬ)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; _≋_; ≋-sym; ≋-trans; hits-elim)
open import PathSum.Expand M₀ using
  (SyntacticId; UniqueNormalForms; unique⇒no-expansion; reduct-⇔)
open import PathSum.Full M using (_⟶ᶠ*_)
open import PathSum.Full.Match M using (Irreducibleᶠ; normal-formᶠ)
open import PathSum.Full.Obstruction M using (no-paths-irreducible)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Gauss.Corollary M₀ using (syntactic?)
open import PathSum.Hardness M₀ using
  (expandᴺ; circuit; circuitˢ; circuitˢ-computes; circuit-paths;
   circuit-length-bound)
open import PathSum.Hardness.Certificate using (Equivalentᴺ)
open import PathSum.Hardness.CNF using
  (CNF; ⟦_⟧ᶠ; Unsatisfiable; ‖_‖)
open import PathSum.Hardness.Netlist using
  (NCT; X; gate; netlist; wires; inputs; tgt; wires-bound)
open import PathSum.Hardness.Prepared M₀ using
  (cleanPS; cleanPS-identity⇔unsat; cleanPS-spec; miterPS;
   miterPS-identity⇔)
open import PathSum.Polynomial using (eval)
open import PathSum.Reversible using (ccx; cx; recover)
open import PathSum.Size M using
  (repᴷ; repᴷ-represents; repᴷ-length; repᴷ-size)
open import PathSum.Size.Sparse M using (Represents; terms; size)
open import PathSum.Syntactic M₀ using (id⇔syntactic)
open import PathSum.Toffoli M₀ using (tof)

private
  variable
    n k m j : ℕ

  infixr 5 _⟨⇔⟩_

  _⟨⇔⟩_ : {P Q R : Set} → P ⇔ Q → Q ⇔ R → P ⇔ R
  f ⟨⇔⟩ g = mk⇔ (λ a → Equivalence.to g (Equivalence.to f a))
                (λ c → Equivalence.from f (Equivalence.from g c))

  sym⇔ : {P Q : Set} → P ⇔ Q → Q ⇔ P
  sym⇔ f = mk⇔ (Equivalence.from f) (Equivalence.to f)


------------------------------------------------------------------------
-- The syntactic test on normal forms

-- What normalisation reaches from ξ: an irreducible reduct.

NormalForm : PathSum n k m → Set
NormalForm {n} ξ = ∃ λ k′ → ∃ λ m′ → ∃ λ (ξ′ : PathSum n k′ m′) →
                   (ξ ⟶ᶠ* ξ′) × Irreducibleᶠ ξ′

-- It passes the test when it has no path variables and is
-- syntactically the identity.

SyntacticNF : {ξ : PathSum n k m} → NormalForm ξ → Set
SyntacticNF (_ , zero  , ξ′ , _ , _) = SyntacticId ξ′
SyntacticNF (_ , suc _ , _  , _ , _) = ⊥

-- The test on the normal form that normal-formᶠ computes.

NormalFormId : PathSum n k m → Set
NormalFormId ξ = SyntacticNF {ξ = ξ} (normal-formᶠ ξ)

-- It is sound, by proposition 3.1 along the chain ...

syntacticNF-sound : {ξ : PathSum n k m} (r : NormalForm ξ) →
                    SyntacticNF {ξ = ξ} r → ξ ≋ idPS
syntacticNF-sound {ξ = ξ} (_ , zero , ξ′ , steps , _) s =
  Equivalence.from (reduct-⇔ {ξ = ξ} {ξ′ = ξ′} steps)
                   (Equivalence.from (id⇔syntactic ξ′) s)

normal-form-id-sound : (ξ : PathSum n k m) → NormalFormId ξ → ξ ≋ idPS
normal-form-id-sound ξ = syntacticNF-sound {ξ = ξ} (normal-formᶠ ξ)

-- ... and decidable, coefficient by coefficient.

syntacticNF? : {ξ : PathSum n k m} (r : NormalForm ξ) →
               Dec (SyntacticNF {ξ = ξ} r)
syntacticNF? (_ , zero  , ξ′ , _ , _) = syntactic? ξ′
syntacticNF? (_ , suc _ , _  , _ , _) = no λ ()

normal-form-id? : (ξ : PathSum n k m) → Dec (NormalFormId ξ)
normal-form-id? ξ = syntacticNF? {ξ = ξ} (normal-formᶠ ξ)


------------------------------------------------------------------------
-- Under the hypothesis of unique normal forms

-- A normal form that keeps a path variable is then never the identity
-- (PathSum.Expand.unique⇒no-expansion), so the test is complete.

unique⇒syntacticNF : UniqueNormalForms → {ξ : PathSum n k m}
                     (r : NormalForm ξ) → ξ ≋ idPS → SyntacticNF {ξ = ξ} r
unique⇒syntacticNF u {ξ} (_ , zero  , ξ′ , steps , _)   e =
  Equivalence.to (id⇔syntactic ξ′)
                 (Equivalence.to (reduct-⇔ {ξ = ξ} {ξ′ = ξ′} steps) e)
unique⇒syntacticNF u {ξ} (_ , suc _ , ξ′ , steps , irr) e =
  unique⇒no-expansion u ξ′ irr
    (Equivalence.to (reduct-⇔ {ξ = ξ} {ξ′ = ξ′} steps) e)

unique⇒normal-form-id : UniqueNormalForms → (ξ : PathSum n k m) →
                        (ξ ≋ idPS) ⇔ NormalFormId ξ
unique⇒normal-form-id u ξ =
  mk⇔ (unique⇒syntacticNF u {ξ = ξ} (normal-formᶠ ξ))
      (normal-form-id-sound ξ)

-- Unsatisfiability, decided by normalising cleanPS φ.

unsat-by-normalisation : UniqueNormalForms → (φ : CNF n) →
                         Unsatisfiable φ ⇔ NormalFormId (cleanPS φ)
unsat-by-normalisation u φ =
  sym⇔ (cleanPS-identity⇔unsat φ) ⟨⇔⟩ unique⇒normal-form-id u (cleanPS φ)

unsat?ᵘ : UniqueNormalForms → (φ : CNF n) → Dec (Unsatisfiable φ)
unsat?ᵘ u φ = map′ (Equivalence.from (unsat-by-normalisation u φ))
                   (Equivalence.to (unsat-by-normalisation u φ))
                   (normal-form-id? (cleanPS φ))

-- Without the hypothesis, a normal form that is syntactically the
-- identity still refutes satisfiability.

normal-form-refutes : (φ : CNF n) → NormalFormId (cleanPS φ) →
                      Unsatisfiable φ
normal-form-refutes φ nf =
  Equivalence.to (cleanPS-identity⇔unsat φ)
                 (normal-form-id-sound (cleanPS φ) nf)

-- Equivalence of two netlists on the clean inputs, decided by
-- normalising their prepared miter.

equivalence-by-normalisation :
  UniqueNormalForms → (a : Fin j → Fin n) (gs hs : List (NCT n)) →
  Equivalentᴺ a gs hs ⇔ NormalFormId (miterPS a gs hs)
equivalence-by-normalisation u a gs hs =
  sym⇔ (miterPS-identity⇔ a gs hs)
  ⟨⇔⟩ unique⇒normal-form-id u (miterPS a gs hs)

equivalent?ᵘ : UniqueNormalForms → (a : Fin j → Fin n)
               (gs hs : List (NCT n)) → Dec (Equivalentᴺ a gs hs)
equivalent?ᵘ u a gs hs =
  map′ (Equivalence.from (equivalence-by-normalisation u a gs hs))
       (Equivalence.to (equivalence-by-normalisation u a gs hs))
       (normal-form-id? (miterPS a gs hs))


------------------------------------------------------------------------
-- What the hypothesis would force on these instances

-- The specification: the target xored with φ of the inputs.

specFun : (φ : CNF n) → Assign (wires φ) → Assign (wires φ)
specFun φ x = x [ tgt φ ≔ x (tgt φ) xor ⟦ φ ⟧ᶠ (λ v → x (inputs φ v)) ]


-- Every reduct of cleanPS φ is equivalent to the specification
-- circuitˢ φ (proposition 3.1 and PathSum.Hardness.Prepared.cleanPS-spec).

reduct-spec : (φ : CNF n) → ∀ {k′ m′} (ξ′ : PathSum (wires φ) k′ m′) →
              cleanPS φ ⟶ᶠ* ξ′ → ξ′ ≋ circuitˢ φ
reduct-spec φ ξ′ steps =
  ≋-trans {ξ = ξ′} {ζ = cleanPS φ} {χ = circuitˢ φ}
    (≋-sym {ξ = cleanPS φ} {ζ = ξ′}
           (⟶ᶠ*-sound {ξ = cleanPS φ} {ζ = ξ′} steps))
    (cleanPS-spec φ)

-- circuitˢ φ has no path variables, so it is irreducible: under the
-- hypothesis every irreducible reduct of cleanPS φ -- the normal form
-- normal-formᶠ computes among them -- has none either.

unique⇒no-paths : UniqueNormalForms → (φ : CNF n) →
                  ∀ {k′ m′} (ξ′ : PathSum (wires φ) k′ m′) →
                  cleanPS φ ⟶ᶠ* ξ′ → Irreducibleᶠ ξ′ → m′ ≡ 0
unique⇒no-paths u φ ξ′ steps irr =
  u ξ′ (circuitˢ φ) irr (no-paths-irreducible (circuitˢ φ))
    (reduct-spec φ ξ′ steps)

-- A path-sum without path variables that computes F outputs F: its
-- single path must hit F x, where the amplitude is not 0.

private
  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  scale-0ᴬ : ∀ i → scale i 0ᴬ ≐ 0ᴬ
  scale-0ᴬ zero    c = refl
  scale-0ᴬ (suc i) c = trans (√2·-map (scale-0ᴬ i) c) (√2·-0ᴬ c)

computes-outputs : (ξ : PathSum n k 0) {F : Assign n → Assign n} →
                   ξ computes F → ∀ x w → outBit ξ x none w ≡ F x w
computes-outputs {k = k} ξ {F} c x w = at (λ ()) (amp-computes c x (F x))
  where
  unit : δ (F x) (F x) ≐ zpow 0ℤ
  unit i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) (same-refl (F x))

  at : (y : Assign 0) →
       (if hits ξ x y (F x) then zpow (eval (phase ξ) x y) else 0ᴬ) ≐
       scale k (δ (F x) (F x)) →
       outBit ξ x none w ≡ F x w
  at y eq = go (hits ξ x y (F x)) refl
    where
    go : ∀ b → hits ξ x y (F x) ≡ b → outBit ξ x none w ≡ F x w
    go true  h = trans (sym (outBit-none ξ x y w)) (hits-elim ξ x y (F x) h w)
    go false h = contradiction
      (scale-injective k (zpow 0ℤ) 0ᴬ
         (≐-sym (scale-map k unit) ∙ ≐-sym eq ∙ gone ∙ ≐-sym (scale-0ᴬ k)))
      zpow-0≢0ᴬ
      where
      gone : (if hits ξ x y (F x) then zpow (eval (phase ξ) x y) else 0ᴬ) ≐ 0ᴬ
      gone i = cong (λ b → (if b then zpow (eval (phase ξ) x y) else 0ᴬ) i) h

-- So every reduct of cleanPS φ without path variables writes
-- x_t ⊕ φ(x) on the target and leaves every other wire, at every
-- input: its output polynomials compute φ.

reduct-outputs : (φ : CNF n) → ∀ {k′} (ξ′ : PathSum (wires φ) k′ 0) →
                 cleanPS φ ⟶ᶠ* ξ′ → ∀ x w → outBit ξ′ x none w ≡ specFun φ x w
reduct-outputs φ ξ′ steps =
  computes-outputs ξ′
    (≋-computes ξ′ (circuitˢ φ) (reduct-spec φ ξ′ steps) (circuitˢ-computes φ))


------------------------------------------------------------------------
-- The size of what is normalised

-- cleanPS φ has the circuit's path variables and normalisation,
-- 4‖φ‖ + 4 of each, on at most n + 3‖φ‖ + 3 wires.

cleanPS-size : (φ : CNF n) →
               (paths (circuit φ) ≡ 4 * ‖ φ ‖ + 4) ×
               (norm (circuit φ) ≡ 4 * ‖ φ ‖ + 4) ×
               (wires φ ≤ n + 3 * ‖ φ ‖ + 3)
cleanPS-size φ =
  circuit-paths φ ,
  trans (sym (paths≡norm (circuit φ))) (circuit-paths φ) ,
  wires-bound φ

-- The expansion has level 3: H R₁ H for NOT, T and T† in the Toffoli
-- gates.

level-expandᴺ : (gs : List (NCT n)) → level (expandᴺ gs) ≤ 3
level-expandᴺ []                              = z≤n
level-expandᴺ (X w ∷ gs)                      =
  ⊔-lub (s≤s z≤n) (level-expandᴺ gs)
level-expandᴺ (gate (ccx c₁ c₂ t p q r) ∷ gs) =
  subst (_≤ 3)
        (sym (level-++ (tof c₁ c₂ t (recover p) (recover q) (recover r))
                       (expandᴺ gs)))
        (⊔-lub ≤-refl (level-expandᴺ gs))
level-expandᴺ (gate (cx c t p) ∷ gs)          = level-expandᴺ gs

circuit-level : (φ : CNF n) → level (circuit φ) ≤ 3
circuit-level φ = level-expandᴺ (netlist φ)

-- Corollary 2.15 at level 3: the circuit's path-sum is represented by
-- at most (N + |C| + 1)^3 terms, and 2 (N + |C| + M + 1)^4 bits, for
-- N wires and |C| gates ...

circuit-size : (φ : CNF n) →
               Represents ⟦ circuit φ ⟧ (repᴷ (circuit φ)) ×
               length (terms (repᴷ (circuit φ))) ≤
               suc (wires φ + length (circuit φ)) ^ 3 ×
               size (repᴷ (circuit φ)) ≤
               2 * suc (wires φ + length (circuit φ) + M) ^ 4
circuit-size φ =
  repᴷ-represents (circuit φ) ,
  ≤-trans (repᴷ-length (circuit φ))
          (^-monoʳ-≤ (suc (wires φ + length (circuit φ))) d≤3) ,
  ≤-trans (repᴷ-size (circuit φ))
          (*-monoʳ-≤ 2 (^-monoʳ-≤ (suc (wires φ + length (circuit φ) + M))
                                  (s≤s d≤3)))
  where
  d≤3 : 2 ⊔ level (circuit φ) ≤ 3
  d≤3 = ⊔-lub (s≤s (s≤s z≤n)) (circuit-level φ)

-- ... so, in the formula: at most (n + 43‖φ‖ + 13)^3 terms and
-- 2 (n + 43‖φ‖ + 13 + M)^4 bits.

circuit-size-bound : (φ : CNF n) →
                     length (terms (repᴷ (circuit φ))) ≤
                     (n + 43 * ‖ φ ‖ + 13) ^ 3 ×
                     size (repᴷ (circuit φ)) ≤
                     2 * (n + 43 * ‖ φ ‖ + 13 + M) ^ 4
circuit-size-bound {n} φ =
  ≤-trans (proj₁ (proj₂ (circuit-size φ))) (^-monoˡ-≤ 3 vol) ,
  ≤-trans (proj₂ (proj₂ (circuit-size φ)))
          (*-monoʳ-≤ 2 (^-monoˡ-≤ 4 (+-mono-≤ vol (≤-refl {M}))))
  where
  eq : suc (n + 3 * ‖ φ ‖ + 3 + (40 * ‖ φ ‖ + 9)) ≡ n + 43 * ‖ φ ‖ + 13
  eq = solve 2 (λ n s → con 1 :+ (n :+ con 3 :* s :+ con 3 :+
                                   (con 40 :* s :+ con 9))
                        := n :+ con 43 :* s :+ con 13)
             refl n ‖ φ ‖

  vol : suc (wires φ + length (circuit φ)) ≤ n + 43 * ‖ φ ‖ + 13
  vol = subst (suc (wires φ + length (circuit φ)) ≤_) eq
              (s≤s (+-mono-≤ (wires-bound φ) (circuit-length-bound φ)))
