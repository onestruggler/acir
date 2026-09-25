------------------------------------------------------------------------
-- Presentations of groups
--
-- The amplitudes of a circuit over {H, CNOT, R_k, R_k†}, gate by gate
--
-- PathSum.CRK.Circuit interprets a circuit by running a state through
-- it: a phase polynomial, and on each wire the Z₂-linear form the wire
-- holds.  A state stands for a path-sum, its outputs the liftings of
-- those forms, and this module computes how the matrix entries of that
-- path-sum change as each gate is applied.  The answer is the gate's
-- own matrix, unnormalised: R_k multiplies the entry at z by
-- ζ^(2^(M-k) z_w) and R_k† by its inverse; CNOT with control c and
-- target t moves the entry at z[t ≔ z_t ⊕ z_c] to z; and a Hadamard on
-- w sends the entry at z to the old entry at z[w≔0] plus (-1)^(z_w)
-- times the old entry at z[w≔1].
--
-- Every proof goes path by path, as in PathSum.CircuitAmp, whose
-- arguments are ported here with a wire's single variable replaced by
-- its linear form.  A path hits an output when every wire's form takes
-- that output's value along it -- the lifting of a form reads, modulo
-- 2, as the form's value (outBit-liftᴸ, by lemma 2.5 for linear forms,
-- PathSum.Linear.eval-liftᴸ).  So a phase gate changes no set of
-- hitting paths and adds to each surviving phase a term the output
-- fixes.  CNOT changes no phase, and a path hits z after it exactly
-- when it hit z[t ≔ z_t ⊕ z_c] before, since the control's value is
-- z_c either way.  After a Hadamard the wire reads the gate's fresh
-- variable, while the old value on the wire decides which of the two
-- old entries the path used to count towards; the phase gains a half
-- exactly when both values are 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _∸_)

module PathSum.CRK.Amp (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _xor_)
open import Data.Bool.Properties using
  (∧-zeroʳ; ∧-identityʳ; xor-assoc; xor-same; xor-identityʳ)
open import Data.Fin.Base using (Fin; zero)
open import Data.Integer.Base using (ℤ; 0ℤ; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣?_)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; +-identityʳ; *-zeroʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; same; same-true; same-intro)
open import PathSum.Base using (PathSum; ⟨_,_⟩; out; head-part; tail-part)
open import PathSum.Circuit M using (wkPoly)
open import PathSum.CRK.Circuit M using
  (State; poly; sig; init; stepR; stepR†; stepCNOT; stepH; ↦-here;
   ↦-there)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _≐_; extend; Σᴮ; Σᴮ-cong; Σᴮ-+; Σᴮ-0; zpow; rot;
   rot-map; rot-zpow; rot-0ᴬ; rot-Σᴮ)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; outBit; hits-intro; hits-elim; eval-0ᴾ-val;
   eval-true; eval-false)
open import PathSum.Linear using
  (Lin; valᴸ; liftᴸ; varᴸ; _⊕ᴸ_; wkLin; mul-y₀; eval-liftᴸ; valᴸ-var;
   valᴸ-⊕; valᴸ-wk)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (Poly; x[_]; y[_]; 0ᴾ; _·ᴾ_; eval)
open import PathSum.Polynomial.Properties using
  (eval-+ᴾ; eval-−ᴾ; eval-·ᴾ; eval-ext)
open import PathSum.Reduction M using (½)

import Data.Fin.Properties as Fin
import Data.Integer.Base as ℤ
import Relation.Binary.PropositionalEquality as Eq

private
  variable
    n m m′ : ℕ


------------------------------------------------------------------------
-- The path-sum of a state

-- The phase of the state, and on each wire the lifting of the form the
-- wire holds.  The normalisation is left free: the amplitude does not
-- read it.

toPS : ∀ {n m k} → State n m → PathSum n k m
toPS st = ⟨ poly st , (λ w → liftᴸ (sig st w)) ⟩

ampᴸ : ∀ {n m} → State n m → Assign n → Assign n → Amp
ampᴸ st x z = amp (toPS {k = 0} st) x z


------------------------------------------------------------------------
-- Booleans, guards and powers of ζ

private
  true≢false : true ≢ false
  true≢false ()

  false≢true : false ≢ true
  false≢true ()

  not-true : {b : Bool} → ¬ (b ≡ true) → b ≡ false
  not-true {true}  ne = contradiction refl ne
  not-true {false} _  = refl

  bool-iff : {a b : Bool} → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) →
             a ≡ b
  bool-iff {true}  {true}  _ _ = refl
  bool-iff {true}  {false} f _ = sym (f refl)
  bool-iff {false} {true}  _ g = g refl
  bool-iff {false} {false} _ _ = refl

  -- Adding the same bit twice adds nothing.

  xor-cancel : ∀ a b → (a xor b) xor b ≡ a
  xor-cancel a b = trans (xor-assoc a b b)
    (trans (cong (a xor_) (xor-same b)) (xor-identityʳ a))

  -- Deciding whether a wire is w, in a context too small for the
  -- decision to be worth abstracting anywhere else.

  wire : {A : Set} (u w : Fin n) → (u ≡ w → A) → (u ≢ w → A) → A
  wire u w f g with u Fin.≟ w
  ... | yes p = f p
  ... | no ¬p = g ¬p

  -- A property of every wire, from the wire w and all the others.

  at-wire : (P : Fin n → Set) (w : Fin n) → P w → (∀ u → u ≢ w → P u) →
            ∀ u → P u
  at-wire P w pw off u = wire u w (λ u≡w → Eq.subst P (sym u≡w) pw) (off u)

  if-cong : {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
            (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
  if-cong {p = true}  refl a≐b = a≐b
  if-cong {p = false} refl _   = λ _ → refl

  if-false : (p : Bool) (a : Amp) → p ≡ false → (if p then a else 0ᴬ) ≐ 0ᴬ
  if-false false _ _ _ = refl
  if-false true  _ () _

  zpow-≡ : {a b : ℤ} → a ≡ b → zpow a ≐ zpow b
  zpow-≡ refl _ = refl

  -- Multiplying a guarded power of ζ by ζ^e adds e to its exponent.

  rot-if : (p : Bool) (e a : ℤ) →
           rot e (if p then zpow a else 0ᴬ) ≐ (if p then zpow (e + a) else 0ᴬ)
  rot-if true  e a = rot-zpow e a
  rot-if false e a = rot-0ᴬ e


------------------------------------------------------------------------
-- Reading an output

-- Outputs are read modulo 2, and the lifting of a linear form takes
-- the form's value, 0 or 1 (lemma 2.5); so an output that is the
-- lifting of a form reads as the form's value.  (Denotation's outBit ξ
-- x y w is, by definition, whether eval (out ξ w) x y is odd.)

private
  bit-[] : ∀ b → not ⌊ (ℤ.+ 2) ∣? [ b ]ᶻ ⌋ ≡ b
  bit-[] true  = refl
  bit-[] false = refl

outBit-liftᴸ : ∀ {n m k} (ξ : PathSum n k m) (x : Assign n) (y : Assign m)
               (w : Fin n) (l : Lin n m) → out ξ w ≡ liftᴸ l →
               outBit ξ x y w ≡ valᴸ l x y
outBit-liftᴸ ξ x y w l eq =
  trans (cong (λ P → not ⌊ (ℤ.+ 2) ∣? eval P x y ⌋) eq)
    (trans (cong (λ e → not ⌊ (ℤ.+ 2) ∣? e ⌋) (eval-liftᴸ l x y))
           (bit-[] (valᴸ l x y)))


------------------------------------------------------------------------
-- Values of the polynomials a gate adds

-- Weakening shifts the path variables up past the fresh head one, so
-- at a path extended by any value it reads what it read before.

private
  val-wk : (b : Bool) (l : Lin n m) (x : Assign n) (y : Assign m) →
           valᴸ (wkLin l) x (extend b y) ≡ valᴸ l x y
  val-wk b l x y = valᴸ-wk l x y (extend b y) (λ _ → refl)

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

-- The phase after each gate, at a path: the old phase plus the term
-- the gate adds, read off the old value on its wire.

private
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

  -- A Hadamard multiplies half the lifted form by the fresh variable:
  -- the term vanishes on the branch where it is 0, and is ½ times the
  -- form's value on the other.

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


------------------------------------------------------------------------
-- The paths of a state

private
  -- The summand of ampᴸ st x z at the path y.

  term : State n m → Assign n → Assign n → Assign m → Amp
  term st x z y =
    if hits (toPS {k = 0} st) x y z then zpow (eval (poly st) x y) else 0ᴬ

  -- Along a path each wire reads the value of its form, so the path
  -- hits z exactly when every wire reads z's value.

  outBit-st : (st : State n m) (x : Assign n) (y : Assign m) (u : Fin n) →
              outBit (toPS {k = 0} st) x y u ≡ valᴸ (sig st u) x y
  outBit-st st x y u = outBit-liftᴸ (toPS {k = 0} st) x y u (sig st u) refl

  hits-val : (st : State n m) (x : Assign n) (y : Assign m) (z : Assign n) →
             hits (toPS {k = 0} st) x y z ≡ true →
             ∀ u → valᴸ (sig st u) x y ≡ z u
  hits-val st x y z h u =
    trans (sym (outBit-st st x y u)) (hits-elim (toPS {k = 0} st) x y z h u)

  val-hits : (st : State n m) (x : Assign n) (y : Assign m) (z : Assign n) →
             (∀ u → valᴸ (sig st u) x y ≡ z u) →
             hits (toPS {k = 0} st) x y z ≡ true
  val-hits st x y z h =
    hits-intro (toPS {k = 0} st) x y z (λ u → trans (outBit-st st x y u) (h u))

  hits-miss : (st : State n m) (x : Assign n) (y : Assign m) (z : Assign n)
              (w : Fin n) → ¬ (valᴸ (sig st w) x y ≡ z w) →
              hits (toPS {k = 0} st) x y z ≡ false
  hits-miss st x y z w ne = not-true (λ h → ne (hits-val st x y z h w))

  -- Two paths, of two states, hit two outputs alike when each reads
  -- its own output on a wire w, and away from w they read the same
  -- values and the outputs agree.

  hits-off→ : (st : State n m) (st′ : State n m′) (x : Assign n)
              (y : Assign m) (y′ : Assign m′) (z z′ : Assign n) (w : Fin n) →
              valᴸ (sig st′ w) x y′ ≡ z′ w →
              (∀ u → u ≢ w → valᴸ (sig st u) x y ≡ valᴸ (sig st′ u) x y′) →
              (∀ u → u ≢ w → z u ≡ z′ u) →
              hits (toPS {k = 0} st) x y z ≡ true →
              hits (toPS {k = 0} st′) x y′ z′ ≡ true
  hits-off→ st st′ x y y′ z z′ w hw′ sv sz h = val-hits st′ x y′ z′
    (at-wire (λ u → valᴸ (sig st′ u) x y′ ≡ z′ u) w hw′ (λ u u≢w →
      trans (sym (sv u u≢w)) (trans (hits-val st x y z h u) (sz u u≢w))))

  hits-off : (st : State n m) (st′ : State n m′) (x : Assign n)
             (y : Assign m) (y′ : Assign m′) (z z′ : Assign n) (w : Fin n) →
             valᴸ (sig st w) x y ≡ z w → valᴸ (sig st′ w) x y′ ≡ z′ w →
             (∀ u → u ≢ w → valᴸ (sig st u) x y ≡ valᴸ (sig st′ u) x y′) →
             (∀ u → u ≢ w → z u ≡ z′ u) →
             hits (toPS {k = 0} st) x y z ≡ hits (toPS {k = 0} st′) x y′ z′
  hits-off st st′ x y y′ z z′ w hw hw′ sv sz = bool-iff
    (hits-off→ st st′ x y y′ z z′ w hw′ sv sz)
    (hits-off→ st′ st x y′ y z′ z w hw
      (λ u u≢w → sym (sv u u≢w)) (λ u u≢w → sym (sz u u≢w)))


------------------------------------------------------------------------
-- The starting state

-- There are no path variables, and wire w holds x_w, so the single
-- path hits z exactly when z is x, with phase 0.

ampᴸ-init : ∀ {n} (x z : Assign n) →
            ampᴸ (init {n}) x z ≐ (if same x z then zpow 0ℤ else 0ᴬ)
ampᴸ-init {n} x z = at (λ ())
  where
  at : (y : Assign 0) →
       (if hits (toPS {k = 0} (init {n})) x y z
        then zpow (eval (0ᴾ {n} {0}) x y) else 0ᴬ) ≐
       (if same x z then zpow 0ℤ else 0ᴬ)
  at y = if-cong
    (bool-iff
      (λ h → same-intro x z (λ u →
        trans (sym (valᴸ-var x[ u ] x y)) (hits-val (init {n}) x y z h u)))
      (λ h → val-hits (init {n}) x y z (λ u →
        trans (valᴸ-var x[ u ] x y) (same-true x z h u))))
    (zpow-≡ (eval-0ᴾ-val x y))


------------------------------------------------------------------------
-- Phase gates

-- A gate that leaves every wire alone hits the same paths, so if on
-- those paths it adds e to the phase, it multiplies the entry by ζ^e.

private
  phase-gate : (st′ st : State n m) (x z : Assign n) (e : ℤ) →
               (∀ y → hits (toPS {k = 0} st′) x y z ≡
                      hits (toPS {k = 0} st) x y z) →
               (∀ y → hits (toPS {k = 0} st) x y z ≡ true →
                      eval (poly st′) x y ≡ e + eval (poly st) x y) →
               ampᴸ st′ x z ≐ rot e (ampᴸ st x z)
  phase-gate st′ st x z e hh shift i =
    trans (Σᴮ-cong per i) (sym (rot-Σᴮ e (term st x z) i))
    where
    guard : (y : Assign _) (p : Bool) → hits (toPS {k = 0} st) x y z ≡ p →
            (if p then zpow (eval (poly st′) x y) else 0ᴬ) ≐
            (if p then zpow (e + eval (poly st) x y) else 0ᴬ)
    guard y true  hp = zpow-≡ (shift y hp)
    guard y false _  = λ _ → refl

    per : ∀ y → term st′ x z y ≐ rot e (term st x z y)
    per y j = trans
      (cong (λ p → (if p then zpow (eval (poly st′) x y) else 0ᴬ) j) (hh y))
      (trans (guard y (hits (toPS {k = 0} st) x y z) refl j)
             (sym (rot-if (hits (toPS {k = 0} st) x y z) e
                          (eval (poly st) x y) j)))

-- R_k multiplies each entry by ζ^(2^(M-k) z_w).

ampᴸ-R : ∀ {n m} (k : ℕ) (w : Fin n) (st : State n m) (x z : Assign n) →
         ampᴸ (stepR k w st) x z ≐ rot (pow (M ∸ k) * [ z w ]ᶻ) (ampᴸ st x z)
ampᴸ-R k w st x z =
  phase-gate (stepR k w st) st x z (pow (M ∸ k) * [ z w ]ᶻ) (λ _ → refl)
    (λ y h → trans (eval-R k w st x y)
      (trans (cong (λ b → eval (poly st) x y + pow (M ∸ k) * [ b ]ᶻ)
                   (hits-val st x y z h w))
             (+-comm (eval (poly st) x y) (pow (M ∸ k) * [ z w ]ᶻ))))

-- R_k† multiplies each entry by ζ^(-2^(M-k) z_w).

ampᴸ-R† : ∀ {n m} (k : ℕ) (w : Fin n) (st : State n m) (x z : Assign n) →
          ampᴸ (stepR† k w st) x z ≐
          rot (- (pow (M ∸ k) * [ z w ]ᶻ)) (ampᴸ st x z)
ampᴸ-R† k w st x z =
  phase-gate (stepR† k w st) st x z (- (pow (M ∸ k) * [ z w ]ᶻ))
    (λ _ → refl)
    (λ y h → trans (eval-R† k w st x y)
      (trans (cong (λ b → eval (poly st) x y - pow (M ∸ k) * [ b ]ᶻ)
                   (hits-val st x y z h w))
             (+-comm (eval (poly st) x y) (- (pow (M ∸ k) * [ z w ]ᶻ)))))


------------------------------------------------------------------------
-- CNOT

-- The phase is unchanged, and the target now holds the sum of its old
-- form and the control's.  A path reads z_c on the control either way,
-- so it reads z_t on the target after the gate exactly when it read
-- z_t ⊕ z_c there before: it hits z after the gate exactly when it hit
-- z[t ≔ z_t ⊕ z_c] before.

ampᴸ-CNOT : ∀ {n m} (c t : Fin n) → c ≢ t → (st : State n m)
            (x z : Assign n) →
            ampᴸ (stepCNOT c t st) x z ≐ ampᴸ st x (z [ t ≔ z t xor z c ])
ampᴸ-CNOT {n} {m} c t c≢t st x z i = Σᴮ-cong per i
  where
  z′ : Assign n
  z′ = z [ t ≔ z t xor z c ]

  new : State n m
  new = stepCNOT c t st

  new-t : (y : Assign m) →
          valᴸ (sig new t) x y ≡ valᴸ (sig st t) x y xor valᴸ (sig st c) x y
  new-t y = trans
    (cong (λ l → valᴸ l x y) (↦-here (sig st) t (sig st t ⊕ᴸ sig st c)))
    (valᴸ-⊕ (sig st t) (sig st c) x y)

  new-off : (y : Assign m) (u : Fin n) → u ≢ t →
            valᴸ (sig new u) x y ≡ valᴸ (sig st u) x y
  new-off y u u≢t =
    cong (λ l → valᴸ l x y) (↦-there (sig st) (sig st t ⊕ᴸ sig st c) u≢t)

  z′-off : (u : Fin n) → u ≢ t → z′ u ≡ z u
  z′-off u u≢t = ≔-there z (z t xor z c) u≢t

  to : (y : Assign m) → hits (toPS {k = 0} new) x y z ≡ true →
       hits (toPS {k = 0} st) x y z′ ≡ true
  to y h = val-hits st x y z′
    (at-wire (λ u → valᴸ (sig st u) x y ≡ z′ u) t tgt off)
    where
    hn : ∀ u → valᴸ (sig new u) x y ≡ z u
    hn = hits-val new x y z h

    vc : valᴸ (sig st c) x y ≡ z c
    vc = trans (sym (new-off y c c≢t)) (hn c)

    tgt : valᴸ (sig st t) x y ≡ z′ t
    tgt = trans (sym (xor-cancel (valᴸ (sig st t) x y) (valᴸ (sig st c) x y)))
      (trans (cong₂ _xor_ (trans (sym (new-t y)) (hn t)) vc)
             (sym (≔-here z t (z t xor z c))))

    off : ∀ u → u ≢ t → valᴸ (sig st u) x y ≡ z′ u
    off u u≢t =
      trans (sym (new-off y u u≢t)) (trans (hn u) (sym (z′-off u u≢t)))

  from : (y : Assign m) → hits (toPS {k = 0} st) x y z′ ≡ true →
         hits (toPS {k = 0} new) x y z ≡ true
  from y h = val-hits new x y z
    (at-wire (λ u → valᴸ (sig new u) x y ≡ z u) t tgt off)
    where
    ho : ∀ u → valᴸ (sig st u) x y ≡ z′ u
    ho = hits-val st x y z′ h

    tgt : valᴸ (sig new t) x y ≡ z t
    tgt = trans (new-t y)
      (trans (cong₂ _xor_ (trans (ho t) (≔-here z t (z t xor z c)))
                          (trans (ho c) (z′-off c c≢t)))
             (xor-cancel (z t) (z c)))

    off : ∀ u → u ≢ t → valᴸ (sig new u) x y ≡ z u
    off u u≢t = trans (new-off y u u≢t) (trans (ho u) (z′-off u u≢t))

  per : ∀ y → term new x z y ≐ term st x z′ y
  per y j = cong (λ p → (if p then zpow (eval (poly st) x y) else 0ᴬ) j)
                 (bool-iff (to y) (from y))


------------------------------------------------------------------------
-- Hadamards

-- One path y′ of a Hadamard's state st′, lying over the path y of the
-- state st before it.  The wire w now reads z w, the other wires read
-- what they did, and the phase has gained ½ o d, o being the old value
-- on w.  Whichever o is, y′ hits z exactly when y hits z with w set to
-- o, and it misses z with w set to the other value; so it contributes
-- to exactly one of the two old entries, the one at o = 1 carrying the
-- sign (-1)^d.

private
  H-term : (st : State n m) (st′ : State n m′) (w : Fin n) (x z : Assign n)
           (y : Assign m) (y′ : Assign m′) (d : Bool) →
           valᴸ (sig st′ w) x y′ ≡ z w →
           (∀ u → u ≢ w → valᴸ (sig st u) x y ≡ valᴸ (sig st′ u) x y′) →
           eval (poly st′) x y′ ≡
           eval (poly st) x y + ½ * [ valᴸ (sig st w) x y ∧ d ]ᶻ →
           term st′ x z y′ ≐
           (term st x (z [ w ≔ false ]) y +ᴬ
            rot (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ]) y))
  H-term st st′ w x z y y′ d hw sv ph = split (valᴸ (sig st w) x y) refl
    where
    P : ℤ
    P = eval (poly st) x y

    -- y′ hits z as y hits z with w set to the old value on w.

    moved : (o : Bool) → valᴸ (sig st w) x y ≡ o →
            hits (toPS {k = 0} st′) x y′ z ≡
            hits (toPS {k = 0} st) x y (z [ w ≔ o ])
    moved o eo = hits-off st′ st x y′ y z (z [ w ≔ o ]) w hw
      (trans eo (sym (≔-here z w o)))
      (λ u u≢w → sym (sv u u≢w))
      (λ u u≢w → sym (≔-there z o u≢w))

    split : (o : Bool) → valᴸ (sig st w) x y ≡ o →
            term st′ x z y′ ≐
            (term st x (z [ w ≔ false ]) y +ᴬ
             rot (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ]) y))
    split false eo i = trans
      (if-cong (moved false eo) (zpow-≡ ph′) i)
      (trans (sym (+-identityʳ (term st x (z [ w ≔ false ]) y i)))
             (cong (term st x (z [ w ≔ false ]) y i +_) (sym dead)))
      where
      ph′ : eval (poly st′) x y′ ≡ P
      ph′ = trans ph (trans (cong (λ o → P + ½ * [ o ∧ d ]ᶻ) eo)
                            (trans (cong (P +_) (*-zeroʳ ½)) (+-identityʳ P)))

      dead : rot (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ]) y) i ≡ 0ℤ
      dead = trans
        (rot-map (½ * [ d ]ᶻ)
          (if-false (hits (toPS {k = 0} st) x y (z [ w ≔ true ])) (zpow P)
            (hits-miss st x y (z [ w ≔ true ]) w (λ q →
              false≢true (trans (sym eo) (trans q (≔-here z w true)))))) i)
        (rot-0ᴬ (½ * [ d ]ᶻ) i)
    split true eo i = trans
      (if-cong (moved true eo) (zpow-≡ ph′) i)
      (trans (sym (rot-if (hits (toPS {k = 0} st) x y (z [ w ≔ true ]))
                          (½ * [ d ]ᶻ) P i))
        (trans (sym (+-identityˡ
                      (rot (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ]) y) i)))
               (cong (_+ rot (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ]) y) i)
                     (sym dead))))
      where
      ph′ : eval (poly st′) x y′ ≡ ½ * [ d ]ᶻ + P
      ph′ = trans ph (trans (cong (λ o → P + ½ * [ o ∧ d ]ᶻ) eo)
                            (+-comm P (½ * [ d ]ᶻ)))

      dead : term st x (z [ w ≔ false ]) y i ≡ 0ℤ
      dead = if-false (hits (toPS {k = 0} st) x y (z [ w ≔ false ])) (zpow P)
        (hits-miss st x y (z [ w ≔ false ]) w (λ q →
          true≢false (trans (sym eo) (trans q (≔-here z w false))))) i

  -- Summing that over the old paths.

  H-sum : (st : State n m) (w : Fin n) (x z : Assign n) (d : Bool)
          (F : Assign m → Amp) →
          (∀ y → F y ≐ (term st x (z [ w ≔ false ]) y +ᴬ
                        rot (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ]) y))) →
          Σᴮ F ≐ (ampᴸ st x (z [ w ≔ false ]) +ᴬ
                  rot (½ * [ d ]ᶻ) (ampᴸ st x (z [ w ≔ true ])))
  H-sum st w x z d F h i = trans (Σᴮ-cong h i)
    (trans (Σᴮ-+ (term st x (z [ w ≔ false ]))
                 (λ y → rot (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ]) y)) i)
           (cong (Σᴮ (term st x (z [ w ≔ false ])) i +_)
                 (sym (rot-Σᴮ (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ])) i))))

-- The sum over the new state's paths splits at the fresh variable,
-- which is the new value on w: only the branch in which it is z w can
-- hit z, and that branch is the old paths, each read as above with
-- d = z w.
--
-- The sign is written (-1)^(z w) from the start, and only the phase
-- is rewritten along z w ≡ b: rewriting inside rot would make Agda
-- compare two exponents that differ syntactically, and it does that
-- by unfolding the proofs that classify carries.

ampᴸ-H : ∀ {n m} (w : Fin n) (st : State n m) (x z : Assign n) →
         ampᴸ (stepH w st) x z ≐
         (ampᴸ st x (z [ w ≔ false ]) +ᴬ
          rot (½ * [ z w ]ᶻ) (ampᴸ st x (z [ w ≔ true ])))
ampᴸ-H {n} {m} w st x z = by-wire (z w) refl
  where
  -- The paths whose fresh variable takes the value b.

  branch : Bool → Amp
  branch b = Σᴮ (λ y → term (stepH w st) x z (extend b y))

  new : (b : Bool) (y : Assign m) →
        valᴸ (sig (stepH w st) w) x (extend b y) ≡ b
  new b y = trans
    (cong (λ l → valᴸ l x (extend b y))
          (↦-here (λ v → wkLin (sig st v)) w (varᴸ y[ zero ])))
    (valᴸ-var y[ zero ] x (extend b y))

  live : (b : Bool) → z w ≡ b →
         branch b ≐ (ampᴸ st x (z [ w ≔ false ]) +ᴬ
                     rot (½ * [ z w ]ᶻ) (ampᴸ st x (z [ w ≔ true ])))
  live b zb = H-sum st w x z (z w) (λ y → term (stepH w st) x z (extend b y))
    (λ y → H-term st (stepH w st) w x z y (extend b y) (z w)
      (trans (new b y) (sym zb))
      (λ u u≢w → sym (trans
        (cong (λ l → valᴸ l x (extend b y))
              (↦-there (λ v → wkLin (sig st v)) (varᴸ y[ zero ]) u≢w))
        (val-wk b (sig st u) x y)))
      (trans (eval-H w st x b y)
        (cong (λ c → eval (poly st) x y + ½ * [ valᴸ (sig st w) x y ∧ c ]ᶻ)
              {x = b} {y = z w} (sym zb))))

  dead : (b : Bool) → ¬ (z w ≡ b) → branch b ≐ 0ᴬ
  dead b ne i = trans
    (Σᴮ-cong (λ y →
      if-false (hits (toPS {k = 0} (stepH w st)) x (extend b y) z)
               (zpow (eval (poly (stepH w st)) x (extend b y)))
               (hits-miss (stepH w st) x (extend b y) z w
                 (λ q → ne (trans (sym q) (new b y))))) i)
    (Σᴮ-0 {m} i)

  by-wire : (b : Bool) → z w ≡ b →
            ampᴸ (stepH w st) x z ≐
            (ampᴸ st x (z [ w ≔ false ]) +ᴬ
             rot (½ * [ z w ]ᶻ) (ampᴸ st x (z [ w ≔ true ])))
  by-wire true zb i = trans
    (cong₂ _+_ (live true zb i)
               (dead false (λ q → true≢false (trans (sym zb) q)) i))
    (+-identityʳ ((ampᴸ st x (z [ w ≔ false ]) +ᴬ
                   rot (½ * [ z w ]ᶻ) (ampᴸ st x (z [ w ≔ true ]))) i))
  by-wire false zb i = trans
    (cong₂ _+_ (dead true (λ q → false≢true (trans (sym zb) q)) i)
               (live false zb i))
    (+-identityˡ ((ampᴸ st x (z [ w ≔ false ]) +ᴬ
                   rot (½ * [ z w ]ᶻ) (ampᴸ st x (z [ w ≔ true ]))) i))
