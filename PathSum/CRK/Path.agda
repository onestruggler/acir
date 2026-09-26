------------------------------------------------------------------------
-- Presentations of groups
--
-- The path-sum of a circuit over {H, CNOT, R_k, R_k†}, read along one
-- path (Amy, QPL 2018, definition 2.9)
--
-- PathSum.CRK.Circuit interprets a circuit by running a state through
-- it: a phase polynomial, and on each wire a Z₂-linear form.  Along one
-- path y -- one assignment to the path variables -- each form takes a
-- Boolean value and the phase an integer, the numerator of its value
-- over 2^M, and each gate changes those values by a rule that mentions
-- no polynomial:
--
--    R_k on w     adds 2^(M-k) a_w to the phase,  R_k† subtracts it;
--    CNOT c t     sets a_t to a_t ⊕ a_c;
--    H on w       adds ½ a_w b to the phase and sets a_w to b, b being
--                 the value of the fresh path variable (the new y₀).
--
-- Reads st x y a says that along y the wires of st read a; eval-R,
-- eval-R† and eval-H are the phase rules (Φ-R, Φ-R† and Φ-H read the
-- wire's value off Reads), Reads-R, Reads-R†, Reads-CNOT and Reads-H
-- the wire rules.  Trace st x y a e adds that the phase takes the
-- value e, and Trace-R, Trace-R†, Trace-CNOT and Trace-H carry both
-- through a gate.  At the end of a circuit the outputs are the
-- liftings of the wires' forms, which read as the forms' values (lemma
-- 2.5), so a path hits z exactly when the wires read z (hits-⟦⟧), and
-- its summand in the amplitude is then ζ to the phase value
-- (term-⟦⟧).
--
-- These are the per-path facts that PathSum.CRK.Amp proves on the way
-- to the gate matrices, stated here for a single path so that a
-- concrete circuit can be read path by path: PathSum.Toffoli reads the
-- seven-T Toffoli circuit this way, on any three wires of any number.
-- No polynomial is ever computed or compared; every fact is an
-- evaluation.
--
-- A whole circuit is read through a simulation, Sim: the wire values
-- and the phase value before each gate, each step justified by that
-- gate's rule, the Hadamards' fresh variables read off the path by
-- restrict.  Its soundness, sim-trace, is proved once, for every
-- circuit, by induction, and so are its consequences for ⟦ C ⟧: the
-- outputs (sim-outBit), the phase (sim-phase) and, from simulations
-- along every path, the amplitudes (amp-sim).
--
-- That design is forced by a pitfall.  A state after a CNOT mentions
-- the state before it three times (in its target's new form and on the
-- other wires), so when Agda compares two syntactically different
-- descriptions of one state of a concrete circuit it unfolds both, and
-- takes time exponential in the number of CNOTs.  Such descriptions
-- arise easily: a name for the state; the same run from another
-- instance of PathSum.CRK.Circuit; or the same run written in two
-- modules, whose applications of this parameterised module name the
-- initial state differently.  (A draft that passed a Trace of the
-- seven-T Toffoli circuit's run from one module to another did not
-- finish checking in ten minutes.)  So a client states nothing about
-- the run of a concrete circuit: it builds a Sim, whose indices are
-- the circuit and the initial state only, and draws its conclusions
-- through sim-outBit, sim-phase and amp-sim, whose statements mention
-- ⟦ C ⟧ and no state.  For the same reason the circuit vocabulary is
-- re-exported from here: ⟦ C ⟧ from another instance of
-- PathSum.CRK.Circuit is a different term, however equal its
-- parameter.  (⟦ C ⟧ itself, taken from two applications of this
-- module, compares cheaply, even for two Toffoli circuits in a row:
-- both copies unfold at once to the same term.  It is statements that
-- unfold into amplitudes when compared that cost -- hence
-- PathSum.Classical's _computes_ is a record.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _∸_)

module PathSum.CRK.Path (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; if_then_else_; _∧_; _xor_)
open import Data.Bool.Properties using (∧-zeroʳ; ∧-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-zeroʳ)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)

import Data.Fin.Properties as Fin

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; same; same-≗)
open import PathSum.Base using (phase; out; head-part; tail-part)
open import PathSum.Circuit M using (wkPoly)
open import PathSum.Compose.Properties M₀ using (hits-same)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.CRK.Amp M₀ using (outBit-liftᴸ)
open import PathSum.CRK.Circuit M public using
  (Gate; H; CNOT; R; R†; Circuit; norm; State; poly; sig; init; stepR;
   stepR†; stepCNOT; stepH; run; paths; ⟦_⟧)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; extend; zpow; Σᴮ; Σᴮ-cong)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; eval-true; eval-false; eval-0ᴾ-val)
open import PathSum.Linear using
  (Lin; valᴸ; liftᴸ; varᴸ; wkLin; mul-y₀; _⊕ᴸ_; eval-liftᴸ; valᴸ-var;
   valᴸ-⊕; valᴸ-wk; par; par-cong)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (Poly; x[_]; y[_]; 0ᴾ; _·ᴾ_; eval)
open import PathSum.Polynomial.Properties using
  (eval-+ᴾ; eval-−ᴾ; eval-·ᴾ; eval-ext; eval-cong)
open import PathSum.Reduction M using (½)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The wires along a path

-- Along the path y (and at the input x) the wires of st read a.  A
-- record, so that st, x, y and a can be read off its type.

record Reads {n m : ℕ} (st : State n m) (x : Assign n) (y : Assign m)
             (a : Assign n) : Set where
  constructor reads
  field
    read : ∀ u → valᴸ (sig st u) x y ≡ a u

open Reads public

-- Before any gate, wire u holds the input variable x_u.

Reads-init : (x : Assign n) (y : Assign 0) → Reads (init {n}) x y x
Reads-init x y = reads (λ u → valᴸ-var x[ u ] x y)

-- Only the values read matter.

Reads-≗ : {st : State n m} {x : Assign n} {y : Assign m} {a a′ : Assign n} →
          Reads st x y a → (∀ u → a u ≡ a′ u) → Reads st x y a′
Reads-≗ r h = reads (λ u → trans (read r u) (h u))

-- Phase gates leave the wires alone.

Reads-R : (k : ℕ) (w : Fin n) {st : State n m} {x : Assign n}
          {y : Assign m} {a : Assign n} →
          Reads st x y a → Reads (stepR k w st) x y a
Reads-R k w r = reads (read r)

Reads-R† : (k : ℕ) (w : Fin n) {st : State n m} {x : Assign n}
           {y : Assign m} {a : Assign n} →
           Reads st x y a → Reads (stepR† k w st) x y a
Reads-R† k w r = reads (read r)

-- CNOT sets the target to the sum of its value and the control's.

Reads-CNOT : (c t : Fin n) {st : State n m} {x : Assign n} {y : Assign m}
             {a : Assign n} → Reads st x y a →
             Reads (stepCNOT c t st) x y (a [ t ≔ a t xor a c ])
Reads-CNOT c t {st} {x} {y} {a} r = reads (λ u → go u ⌊ u Fin.≟ t ⌋)
  where
  go : ∀ u d → valᴸ (if d then sig st t ⊕ᴸ sig st c else sig st u) x y ≡
               (if d then a t xor a c else a u)
  go u true  = trans (valᴸ-⊕ (sig st t) (sig st c) x y)
                     (cong₂ _xor_ (read r t) (read r c))
  go u false = read r u

-- A Hadamard puts its fresh variable on its wire; the others read, on
-- the path extended by any value b of that variable, what they read
-- before.

Reads-H : (w : Fin n) (b : Bool) {st : State n m} {x : Assign n}
          {y : Assign m} {a : Assign n} → Reads st x y a →
          Reads (stepH w st) x (extend b y) (a [ w ≔ b ])
Reads-H w b {st} {x} {y} {a} r = reads (λ u → go u ⌊ u Fin.≟ w ⌋)
  where
  go : ∀ u d → valᴸ (if d then varᴸ y[ zero ] else wkLin (sig st u))
                    x (extend b y) ≡
               (if d then b else a u)
  go u true  = valᴸ-var y[ zero ] x (extend b y)
  go u false =
    trans (valᴸ-wk (sig st u) x y (extend b y) (λ _ → refl)) (read r u)


------------------------------------------------------------------------
-- The phase along a path

-- Weakening by a fresh head variable does not change a value.

private
  eval-wk : (b : Bool) (P : Poly n m) (x : Assign n) (y : Assign m) →
            eval (wkPoly P) x (extend b y) ≡ eval P x y
  eval-wk false P x y = trans (eval-false (wkPoly P) x y)
    (eval-ext (tail-part (wkPoly P)) P (λ _ → refl) x y)
  eval-wk true  P x y = trans (eval-true (wkPoly P) x y)
    (trans (cong₂ _+_
             (trans (eval-ext (head-part (wkPoly P)) 0ᴾ (λ _ → refl) x y)
                    (eval-0ᴾ-val x y))
             (eval-ext (tail-part (wkPoly P)) P (λ _ → refl) x y))
           (+-identityˡ (eval P x y)))

-- R_k adds 2^(M-k) times the value on its wire, R_k† subtracts it.

eval-R : (k : ℕ) (w : Fin n) (st : State n m) (x : Assign n)
         (y : Assign m) →
         eval (poly (stepR k w st)) x y ≡
         eval (poly st) x y + pow (M ∸ k) * [ valᴸ (sig st w) x y ]ᶻ
eval-R k w st x y =
  trans (eval-+ᴾ (poly st) (pow (M ∸ k) ·ᴾ liftᴸ (sig st w)) x y)
    (cong (eval (poly st) x y +_)
      (trans (eval-·ᴾ (pow (M ∸ k)) (liftᴸ (sig st w)) x y)
             (cong (pow (M ∸ k) *_) (eval-liftᴸ (sig st w) x y))))

eval-R† : (k : ℕ) (w : Fin n) (st : State n m) (x : Assign n)
          (y : Assign m) →
          eval (poly (stepR† k w st)) x y ≡
          eval (poly st) x y - pow (M ∸ k) * [ valᴸ (sig st w) x y ]ᶻ
eval-R† k w st x y =
  trans (eval-−ᴾ (poly st) (pow (M ∸ k) ·ᴾ liftᴸ (sig st w)) x y)
    (cong (λ a → eval (poly st) x y - a)
      (trans (eval-·ᴾ (pow (M ∸ k)) (liftᴸ (sig st w)) x y)
             (cong (pow (M ∸ k) *_) (eval-liftᴸ (sig st w) x y))))

-- A Hadamard adds half the product of the old value on its wire with
-- its fresh variable: nothing on the branch where the variable is 0,
-- ½ times the old value on the other.

eval-H : (w : Fin n) (st : State n m) (x : Assign n) (b : Bool)
         (y : Assign m) →
         eval (poly (stepH w st)) x (extend b y) ≡
         eval (poly st) x y + ½ * [ valᴸ (sig st w) x y ∧ b ]ᶻ
eval-H w st x b y = trans
  (eval-+ᴾ (wkPoly (poly st)) (mul-y₀ (½ ·ᴾ liftᴸ (sig st w)))
           x (extend b y))
  (cong₂ _+_ (eval-wk b (poly st) x y) (fresh b))
  where
  v = valᴸ (sig st w) x y
  Q = ½ ·ᴾ liftᴸ (sig st w)

  eval-Q : eval Q x y ≡ ½ * [ v ]ᶻ
  eval-Q = trans (eval-·ᴾ ½ (liftᴸ (sig st w)) x y)
                 (cong (½ *_) (eval-liftᴸ (sig st w) x y))

  tail-0 : eval (tail-part (mul-y₀ Q)) x y ≡ 0ℤ
  tail-0 = trans (eval-ext (tail-part (mul-y₀ Q)) 0ᴾ (λ _ → refl) x y)
                 (eval-0ᴾ-val x y)

  fresh : (b : Bool) → eval (mul-y₀ Q) x (extend b y) ≡ ½ * [ v ∧ b ]ᶻ
  fresh false = trans (eval-false (mul-y₀ Q) x y)
    (trans tail-0
      (sym (trans (cong (λ c → ½ * [ c ]ᶻ) (∧-zeroʳ v)) (*-zeroʳ ½))))
  fresh true  = trans (eval-true (mul-y₀ Q) x y)
    (trans (cong₂ _+_ (eval-ext (head-part (mul-y₀ Q)) Q (λ _ → refl) x y)
                      tail-0)
      (trans (+-identityʳ (eval Q x y))
        (trans eval-Q (cong (λ c → ½ * [ c ]ᶻ) (sym (∧-identityʳ v))))))

-- The same, reading the wire's value off Reads.

Φ-R : (k : ℕ) (w : Fin n) {st : State n m} {x : Assign n} {y : Assign m}
      {a : Assign n} {v : Bool} → Reads st x y a → a w ≡ v →
      eval (poly (stepR k w st)) x y ≡
      eval (poly st) x y + pow (M ∸ k) * [ v ]ᶻ
Φ-R k w {st} {x} {y} r e = trans (eval-R k w st x y)
  (cong (λ b → eval (poly st) x y + pow (M ∸ k) * [ b ]ᶻ)
        (trans (read r w) e))

Φ-R† : (k : ℕ) (w : Fin n) {st : State n m} {x : Assign n} {y : Assign m}
       {a : Assign n} {v : Bool} → Reads st x y a → a w ≡ v →
       eval (poly (stepR† k w st)) x y ≡
       eval (poly st) x y - pow (M ∸ k) * [ v ]ᶻ
Φ-R† k w {st} {x} {y} r e = trans (eval-R† k w st x y)
  (cong (λ b → eval (poly st) x y - pow (M ∸ k) * [ b ]ᶻ)
        (trans (read r w) e))

Φ-H : (w : Fin n) (b : Bool) {st : State n m} {x : Assign n}
      {y : Assign m} {a : Assign n} {v : Bool} → Reads st x y a → a w ≡ v →
      eval (poly (stepH w st)) x (extend b y) ≡
      eval (poly st) x y + ½ * [ v ∧ b ]ᶻ
Φ-H w b {st} {x} {y} r e = trans (eval-H w st x b y)
  (cong (λ c → eval (poly st) x y + ½ * [ c ∧ b ]ᶻ) (trans (read r w) e))


------------------------------------------------------------------------
-- Traces

-- Along y the wires of st read a and its phase takes the value e: the
-- invariant a circuit is read by, one gate at a time.

record Trace {n m : ℕ} (st : State n m) (x : Assign n) (y : Assign m)
             (a : Assign n) (e : ℤ) : Set where
  constructor trace
  field
    wires : Reads st x y a
    value : eval (poly st) x y ≡ e

open Trace public

Trace-init : (x : Assign n) (y : Assign 0) → Trace (init {n}) x y x 0ℤ
Trace-init x y = trace (Reads-init x y) (eval-0ᴾ-val x y)

-- Only the values matter.

Trace-≗ : {st : State n m} {x : Assign n} {y : Assign m} {a a′ : Assign n}
          {e : ℤ} → Trace st x y a e → (∀ u → a u ≡ a′ u) →
          Trace st x y a′ e
Trace-≗ tr h = trace (Reads-≗ (wires tr) h) (value tr)

Trace-≡ : {st : State n m} {x : Assign n} {y : Assign m} {a : Assign n}
          {e e′ : ℤ} → Trace st x y a e → e ≡ e′ → Trace st x y a e′
Trace-≡ tr eq = trace (wires tr) (trans (value tr) eq)

-- The gates.

Trace-R : (k : ℕ) (w : Fin n) {st : State n m} {x : Assign n}
          {y : Assign m} {a : Assign n} {e : ℤ} {v : Bool} →
          Trace st x y a e → a w ≡ v →
          Trace (stepR k w st) x y a (e + pow (M ∸ k) * [ v ]ᶻ)
Trace-R k w {v = v} tr av = trace (Reads-R k w (wires tr))
  (trans (Φ-R k w (wires tr) av)
         (cong (_+ pow (M ∸ k) * [ v ]ᶻ) (value tr)))

Trace-R† : (k : ℕ) (w : Fin n) {st : State n m} {x : Assign n}
           {y : Assign m} {a : Assign n} {e : ℤ} {v : Bool} →
           Trace st x y a e → a w ≡ v →
           Trace (stepR† k w st) x y a (e - pow (M ∸ k) * [ v ]ᶻ)
Trace-R† k w {v = v} tr av = trace (Reads-R† k w (wires tr))
  (trans (Φ-R† k w (wires tr) av)
         (cong (_- pow (M ∸ k) * [ v ]ᶻ) (value tr)))

Trace-CNOT : (c t : Fin n) {st : State n m} {x : Assign n}
             {y : Assign m} {a : Assign n} {e : ℤ} →
             Trace st x y a e →
             Trace (stepCNOT c t st) x y (a [ t ≔ a t xor a c ]) e
Trace-CNOT c t tr = trace (Reads-CNOT c t (wires tr)) (value tr)

Trace-H : (w : Fin n) (b : Bool) {st : State n m} {x : Assign n}
          {y : Assign m} {a : Assign n} {e : ℤ} {v : Bool} →
          Trace st x y a e → a w ≡ v →
          Trace (stepH w st) x (extend b y) (a [ w ≔ b ])
                (e + ½ * [ v ∧ b ]ᶻ)
Trace-H w b {v = v} tr av = trace (Reads-H w b (wires tr))
  (trans (Φ-H w b (wires tr) av) (cong (_+ ½ * [ v ∧ b ]ᶻ) (value tr)))


-- A trace reads the path only through its values.

private
  valᴸ-cong : (l : Lin n m) (x : Assign n) {y y′ : Assign m} →
              (∀ j → y j ≡ y′ j) → valᴸ l x y ≡ valᴸ l x y′
  valᴸ-cong (c , α , β) x h = cong (λ b → c xor (par α x xor b)) (par-cong β h)

Trace-path : {st : State n m} {x : Assign n} {y y′ : Assign m}
             {a : Assign n} {e : ℤ} → Trace st x y a e →
             (∀ j → y j ≡ y′ j) → Trace st x y′ a e
Trace-path {st = st} {x} tr h = trace
  (reads (λ u → trans (sym (valᴸ-cong (sig st u) x h)) (read (wires tr) u)))
  (trans (sym (eval-cong (poly st) (λ _ → refl) h)) (value tr))

-- A Hadamard at any path, not only one written extend b y.

Trace-H′ : (w : Fin n) {st : State n m} {x : Assign n}
           {y : Assign (suc m)} {a : Assign n} {e : ℤ} {v : Bool} →
           Trace st x (λ j → y (suc j)) a e → a w ≡ v →
           Trace (stepH w st) x y (a [ w ≔ y zero ]) (e + ½ * [ v ∧ y zero ]ᶻ)
Trace-H′ w {y = y} tr av = Trace-path (Trace-H w (y zero) tr av) λ where
  zero    → refl
  (suc j) → refl


------------------------------------------------------------------------
-- Tracing a whole circuit

-- The path of the state st that a path y of the run of C from st
-- extends: y without the variables C's Hadamards allocate, which come
-- first.

restrict : (C : Circuit n) (st : State n m) →
           Assign (proj₁ (run C st)) → Assign m
restrict []               st y   = y
restrict (H w ∷ C)        st y j = restrict C (stepH w st) y (suc j)
restrict (CNOT c t _ ∷ C) st y   = restrict C (stepCNOT c t st) y
restrict (R k w ∷ C)      st y   = restrict C (stepR k w st) y
restrict (R† k w ∷ C)     st y   = restrict C (stepR† k w st) y

-- A simulation of the circuit C from st, along its path y and at the
-- input x, ending with the values a′ and e′: the wire values a and the
-- phase value e before each gate, each step justified by the gate's
-- rule, the new values being any the rule's are equal to.  A
-- Hadamard's fresh variable takes the value restrict C (stepH w st) y
-- zero, the head of the path of the state after it.
--
-- Clients build one gate by gate, top down; the states in its indices
-- come from its constructors and are never compared with anything.

data Sim {n : ℕ} (x a′ : Assign n) (e′ : ℤ) :
         (C : Circuit n) {m : ℕ} (st : State n m) →
         Assign (proj₁ (run C st)) → Assign n → ℤ → Set where
  end   : {st : State n m} {y : Assign m} {a : Assign n} {e : ℤ} →
          (∀ u → a u ≡ a′ u) → e ≡ e′ → Sim x a′ e′ [] st y a e
  R-sim : {k : ℕ} {w : Fin n} {C : Circuit n} {st : State n m}
          {y : Assign (proj₁ (run C (stepR k w st)))} {a : Assign n}
          {e e₁ : ℤ} {v : Bool} →
          a w ≡ v → e + pow (M ∸ k) * [ v ]ᶻ ≡ e₁ →
          Sim x a′ e′ C (stepR k w st) y a e₁ →
          Sim x a′ e′ (R k w ∷ C) st y a e
  R†-sim : {k : ℕ} {w : Fin n} {C : Circuit n} {st : State n m}
           {y : Assign (proj₁ (run C (stepR† k w st)))} {a : Assign n}
           {e e₁ : ℤ} {v : Bool} →
           a w ≡ v → e - pow (M ∸ k) * [ v ]ᶻ ≡ e₁ →
           Sim x a′ e′ C (stepR† k w st) y a e₁ →
           Sim x a′ e′ (R† k w ∷ C) st y a e
  CNOT-sim : {c t : Fin n} {p : c ≢ t} {C : Circuit n} {st : State n m}
             {y : Assign (proj₁ (run C (stepCNOT c t st)))} {a b : Assign n}
             {e : ℤ} →
             (∀ u → (a [ t ≔ a t xor a c ]) u ≡ b u) →
             Sim x a′ e′ C (stepCNOT c t st) y b e →
             Sim x a′ e′ (CNOT c t p ∷ C) st y a e
  H-sim : {w : Fin n} {C : Circuit n} {st : State n m}
          {y : Assign (proj₁ (run C (stepH w st)))} {a b : Assign n}
          {e e₁ : ℤ} {v : Bool} →
          a w ≡ v →
          (∀ u → (a [ w ≔ restrict C (stepH w st) y zero ]) u ≡ b u) →
          e + ½ * [ v ∧ restrict C (stepH w st) y zero ]ᶻ ≡ e₁ →
          Sim x a′ e′ C (stepH w st) y b e₁ →
          Sim x a′ e′ (H w ∷ C) st y a e

-- A simulation is sound: it turns a trace of the starting state along
-- the restricted path into a trace of the run.

sim-trace : {x a′ : Assign n} {e′ : ℤ} {C : Circuit n} {st : State n m}
            {y : Assign (proj₁ (run C st))} {a : Assign n} {e : ℤ} →
            Sim x a′ e′ C st y a e → Trace st x (restrict C st y) a e →
            Trace (proj₂ (run C st)) x y a′ e′
sim-trace (end h eq)           tr = Trace-≡ (Trace-≗ tr h) eq
sim-trace (R-sim {k = k} {w} av eq s) tr =
  sim-trace s (Trace-≡ (Trace-R k w tr av) eq)
sim-trace (R†-sim {k = k} {w} av eq s) tr =
  sim-trace s (Trace-≡ (Trace-R† k w tr av) eq)
sim-trace (CNOT-sim {c = c} {t} h s) tr =
  sim-trace s (Trace-≗ (Trace-CNOT c t tr) h)
sim-trace (H-sim {w = w} av h eq s) tr =
  sim-trace s (Trace-≡ (Trace-≗ (Trace-H′ w tr av) h) eq)


------------------------------------------------------------------------
-- The path-sum of a circuit along a path

-- Its outputs are the liftings of the final state's forms, which read
-- as the forms' values; so along a path the outputs are what the wires
-- read, and the path hits z exactly when that is z.

outBit-⟦⟧ : (C : Circuit n) (x : Assign n) (y : Assign (paths C))
            {a : Assign n} → Reads (proj₂ (run C init)) x y a →
            ∀ u → outBit ⟦ C ⟧ x y u ≡ a u
outBit-⟦⟧ C x y r u =
  trans (outBit-liftᴸ ⟦ C ⟧ x y u (sig (proj₂ (run C init)) u) refl)
        (read r u)

hits-⟦⟧ : (C : Circuit n) (x : Assign n) (y : Assign (paths C))
          {a : Assign n} → Reads (proj₂ (run C init)) x y a →
          ∀ z → hits ⟦ C ⟧ x y z ≡ same a z
hits-⟦⟧ C x y r z = trans (hits-same ⟦ C ⟧ x y z)
  (same-≗ (outBit-⟦⟧ C x y r) (λ _ → refl))

-- Its phase is the final state's.

value-⟦⟧ : (C : Circuit n) (x : Assign n) (y : Assign (paths C))
           {a : Assign n} {e : ℤ} → Trace (proj₂ (run C init)) x y a e →
           eval (phase ⟦ C ⟧) x y ≡ e
value-⟦⟧ C x y tr = value tr

-- The summand of the amplitude from x to z at the path y: ζ to the
-- phase value if the wires read z, and 0 otherwise.

term-⟦⟧ : (C : Circuit n) (x z : Assign n) (y : Assign (paths C))
          {a : Assign n} {e : ℤ} → Trace (proj₂ (run C init)) x y a e →
          (if hits ⟦ C ⟧ x y z then zpow (eval (phase ⟦ C ⟧) x y) else 0ᴬ) ≐
          (if same a z then zpow e else 0ᴬ)
term-⟦⟧ C x z y tr =
  if-cong (hits-⟦⟧ C x y (wires tr) z) (zpow-≡ (value tr))


------------------------------------------------------------------------
-- A circuit read through its simulations

-- A simulation from the initial state, which along any path reads the
-- inputs and the phase 0, is a trace of the whole run.

sim-run : {x a′ : Assign n} {e′ : ℤ} {C : Circuit n}
          {y : Assign (paths C)} →
          Sim x a′ e′ C init y x 0ℤ → Trace (proj₂ (run C init)) x y a′ e′
sim-run {x = x} {C = C} {y} s = sim-trace s (Trace-init x (restrict C init y))

-- So a simulation along y gives the outputs and the phase of ⟦ C ⟧
-- along y, and simulations along every path give its amplitudes: the
-- sum over the paths of ζ to the phase value, at the paths whose
-- outputs are z.  These are the forms in which a concrete circuit is
-- read: the only terms of a client's that they compare with anything
-- are the circuit and the initial state.

sim-outBit : (C : Circuit n) (x : Assign n) (y : Assign (paths C))
             {a′ : Assign n} {e′ : ℤ} → Sim x a′ e′ C init y x 0ℤ →
             ∀ u → outBit ⟦ C ⟧ x y u ≡ a′ u
sim-outBit C x y s = outBit-⟦⟧ C x y (wires (sim-run s))

sim-phase : (C : Circuit n) (x : Assign n) (y : Assign (paths C))
            {a′ : Assign n} {e′ : ℤ} → Sim x a′ e′ C init y x 0ℤ →
            eval (phase ⟦ C ⟧) x y ≡ e′
sim-phase C x y s = value (sim-run s)

amp-sim : (C : Circuit n) (x z : Assign n)
          (a′ : Assign (paths C) → Assign n) (e′ : Assign (paths C) → ℤ) →
          (∀ y → Sim x (a′ y) (e′ y) C init y x 0ℤ) →
          amp ⟦ C ⟧ x z ≐ Σᴮ (λ y → if same (a′ y) z then zpow (e′ y) else 0ᴬ)
amp-sim C x z a′ e′ s = Σᴮ-cong (λ y → term-⟦⟧ C x z y (sim-run (s y)))
