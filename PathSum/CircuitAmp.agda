------------------------------------------------------------------------
-- Presentations of groups
--
-- The amplitudes of a circuit's path-sum, gate by gate
--
-- PathSum.Circuit interprets a circuit by a state machine: a phase
-- polynomial, together with the variable each wire currently holds.
-- A state stands for a path-sum, and this module computes how the
-- matrix entries of that path-sum change as each gate is applied.
-- The answer is the gate's own matrix, unnormalised: S multiplies the
-- entry at z by i^(z_w) = ζ^(¼ z_w), CZ multiplies it by
-- (-1)^(z_w z_v), and a Hadamard on w sends the entry at z to the
-- old entry at z[w≔0] plus (-1)^(z_w) times the old entry at z[w≔1].  A
-- Hadamard whose variable the isometry restriction has forced to be
-- x_w reads x_w in place of z_w, and keeps only the entries with
-- z_w = x_w.
--
-- Every proof goes path by path.  A path hits an output exactly when
-- each wire's variable takes that output's value along it, so a phase
-- gate changes no set of hitting paths, and adds to each phase that
-- survives a term which the output fixes.  After a Hadamard the wire
-- reads the gate's variable, while the old value on the wire decides
-- which of the two old entries the path used to count towards; the
-- phase gains a half exactly when both values are 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CircuitAmp (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; zero)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; _+_; _*_)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; +-identityʳ; *-zeroʳ)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; _=ᵇ_; =ᵇ-true; =ᵇ-false; same;
   same-true; same-intro)
open import PathSum.Base using (PathSum; ⟨_,_⟩; head-part; tail-part)
open import PathSum.Circuit M using
  (State; poly; sig; init; stepS; stepCZ; allocH; finalH; mono; wkVar;
   wkPoly; _[_↦_])
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _≐_; extend; Σᴮ; Σᴮ-cong; Σᴮ-+; Σᴮ-0; zpow; rot;
   rot-map; rot-zpow; rot-0ᴬ; rot-Σᴮ)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; outBit; hits-intro; hits-elim; outBit-μ;
   eval-0ᴾ-val; eval-true; eval-false)
open import PathSum.Polynomial using
  (Poly; Mon; Var; x[_]; y[_]; ⟪_⟫; _∪ᵐ_; μ; 0ᴾ; _·ᴾ_; eval; satᵐ)
open import PathSum.Polynomial.Properties using
  (valᵛ; satᵐ-∪; satᵐ-⟪⟫; eval-+ᴾ; eval-·ᴾ; eval-ext; Σmon-cong;
   Σmon-delta; ⌊≟ᵐ⌋; if-swap; _≡ᵐᵇ_)
open import PathSum.Reduction M using (¼; ½)

import Data.Fin.Properties as Fin
import Relation.Binary.PropositionalEquality as Eq

private
  variable
    n m m′ : ℕ


------------------------------------------------------------------------
-- The path-sum of a state

-- The phase of the state, and on each wire the variable the wire
-- holds.  The normalisation is left free: the amplitude does not read
-- it.

toPS : ∀ {n m k} → State n m → PathSum n k m
toPS st = ⟨ poly st , (λ w → μ (sig st w)) ⟩

ampˢ : ∀ {n m} → State n m → Assign n → Assign n → Amp
ampˢ st x z = amp (toPS {k = 0} st) x z


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

  -- Deciding whether a wire is w, in a context too small for the
  -- decision to be worth abstracting anywhere else.

  wire : {A : Set} (u w : Fin n) → (u ≡ w → A) → (u ≢ w → A) → A
  wire u w f g with u Fin.≟ w
  ... | yes p = f p
  ... | no ¬p = g ¬p

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
-- Redirecting a wire

private
  ↦-here : (σ : Fin n → Var n m) (w : Fin n) (v : Var n m) →
           (σ [ w ↦ v ]) w ≡ v
  ↦-here σ w v with w Fin.≟ w
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  ↦-there : (σ : Fin n → Var n m) {u w : Fin n} (v : Var n m) → u ≢ w →
            (σ [ w ↦ v ]) u ≡ σ u
  ↦-there σ {u} {w} v u≢w with u Fin.≟ w
  ... | yes p = contradiction p u≢w
  ... | no  _ = refl


------------------------------------------------------------------------
-- Values of the polynomials a gate adds

-- A monomial's indicator polynomial takes the value 1 exactly where
-- the monomial is satisfied; for a variable, or a product of two,
-- that is where the variables are true.

private
  eval-mono : (δ : Mon n m) (x : Assign n) (y : Assign m) →
              eval (mono δ) x y ≡ [ satᵐ δ x y ]ᶻ
  eval-mono δ x y = trans
    (Σmon-cong (λ γ → trans
      (cong (λ b → if satᵐ γ x y then (if b then 1ℤ else 0ℤ) else 0ℤ)
            (⌊≟ᵐ⌋ γ δ))
      (if-swap (satᵐ γ x y) (γ ≡ᵐᵇ δ) 1ℤ)))
    (Σmon-delta δ (λ γ → if satᵐ γ x y then 1ℤ else 0ℤ))

  eval-μ₁ : (v : Var n m) (x : Assign n) (y : Assign m) →
            eval (mono ⟪ v ⟫) x y ≡ [ valᵛ v x y ]ᶻ
  eval-μ₁ v x y = trans (eval-mono ⟪ v ⟫ x y) (cong [_]ᶻ (satᵐ-⟪⟫ v x y))

  eval-μ₂ : (u v : Var n m) (x : Assign n) (y : Assign m) →
            eval (mono (⟪ u ⟫ ∪ᵐ ⟪ v ⟫)) x y ≡ [ valᵛ u x y ∧ valᵛ v x y ]ᶻ
  eval-μ₂ u v x y = trans (eval-mono (⟪ u ⟫ ∪ᵐ ⟪ v ⟫) x y)
    (cong [_]ᶻ (trans (satᵐ-∪ ⟪ u ⟫ ⟪ v ⟫ x y)
                      (cong₂ _∧_ (satᵐ-⟪⟫ u x y) (satᵐ-⟪⟫ v x y))))

-- Weakening shifts the path variables up past the fresh head one, so
-- at a path extended by any value it reads what it read before.

private
  val-wk : (b : Bool) (v : Var n m) (x : Assign n) (y : Assign m) →
           valᵛ (wkVar v) x (extend b y) ≡ valᵛ v x y
  val-wk b x[ i ] x y = refl
  val-wk b y[ j ] x y = refl

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
-- the gate adds, read off the old values on the wires.

private
  eval-S : (w : Fin n) (st : State n m) (x : Assign n) (y : Assign m) →
           eval (poly (stepS w st)) x y ≡
           eval (poly st) x y + ¼ * [ valᵛ (sig st w) x y ]ᶻ
  eval-S w st x y = trans (eval-+ᴾ (poly st) (¼ ·ᴾ mono ⟪ sig st w ⟫) x y)
    (cong (eval (poly st) x y +_)
      (trans (eval-·ᴾ ¼ (mono ⟪ sig st w ⟫) x y)
             (cong (¼ *_) (eval-μ₁ (sig st w) x y))))

  eval-CZ : (w v : Fin n) (st : State n m) (x : Assign n) (y : Assign m) →
            eval (poly (stepCZ w v st)) x y ≡
            eval (poly st) x y +
            ½ * [ valᵛ (sig st w) x y ∧ valᵛ (sig st v) x y ]ᶻ
  eval-CZ w v st x y =
    trans (eval-+ᴾ (poly st) (½ ·ᴾ mono (⟪ sig st w ⟫ ∪ᵐ ⟪ sig st v ⟫)) x y)
      (cong (eval (poly st) x y +_)
        (trans (eval-·ᴾ ½ (mono (⟪ sig st w ⟫ ∪ᵐ ⟪ sig st v ⟫)) x y)
               (cong (½ *_) (eval-μ₂ (sig st w) (sig st v) x y))))

  eval-allocH : (w : Fin n) (st : State n m) (x : Assign n) (b : Bool)
                (y : Assign m) →
                eval (poly (allocH w st)) x (extend b y) ≡
                eval (poly st) x y + ½ * [ valᵛ (sig st w) x y ∧ b ]ᶻ
  eval-allocH w st x b y = trans
    (eval-+ᴾ (wkPoly (poly st))
             (½ ·ᴾ mono (⟪ wkVar (sig st w) ⟫ ∪ᵐ ⟪ y[ zero ] ⟫)) x (extend b y))
    (cong₂ _+_ (eval-wk b (poly st) x y)
      (trans (eval-·ᴾ ½ (mono (⟪ wkVar (sig st w) ⟫ ∪ᵐ ⟪ y[ zero ] ⟫))
                      x (extend b y))
             (cong (½ *_)
               (trans (eval-μ₂ (wkVar (sig st w)) y[ zero ] x (extend b y))
                      (cong (λ o → [ o ∧ b ]ᶻ) (val-wk b (sig st w) x y))))))

  eval-finalH : (w : Fin n) (st : State n m) (x : Assign n) (y : Assign m) →
                eval (poly (finalH w st)) x y ≡
                eval (poly st) x y + ½ * [ valᵛ (sig st w) x y ∧ x w ]ᶻ
  eval-finalH w st x y =
    trans (eval-+ᴾ (poly st) (½ ·ᴾ mono (⟪ sig st w ⟫ ∪ᵐ ⟪ x[ w ] ⟫)) x y)
      (cong (eval (poly st) x y +_)
        (trans (eval-·ᴾ ½ (mono (⟪ sig st w ⟫ ∪ᵐ ⟪ x[ w ] ⟫)) x y)
               (cong (½ *_) (eval-μ₂ (sig st w) x[ w ] x y))))


------------------------------------------------------------------------
-- The paths of a state

private
  -- The summand of ampˢ st x z at the path y.

  term : State n m → Assign n → Assign n → Assign m → Amp
  term st x z y =
    if hits (toPS {k = 0} st) x y z then zpow (eval (poly st) x y) else 0ᴬ

  -- Along a path each wire reads the value of the variable it holds,
  -- so the path hits z exactly when every wire reads z's value.

  outBit-st : (st : State n m) (x : Assign n) (y : Assign m) (u : Fin n) →
              outBit (toPS {k = 0} st) x y u ≡ valᵛ (sig st u) x y
  outBit-st st x y u = outBit-μ (toPS {k = 0} st) x y u (sig st u) refl

  hits-val : (st : State n m) (x : Assign n) (y : Assign m) (z : Assign n) →
             hits (toPS {k = 0} st) x y z ≡ true →
             ∀ u → valᵛ (sig st u) x y ≡ z u
  hits-val st x y z h u =
    trans (sym (outBit-st st x y u)) (hits-elim (toPS {k = 0} st) x y z h u)

  val-hits : (st : State n m) (x : Assign n) (y : Assign m) (z : Assign n) →
             (∀ u → valᵛ (sig st u) x y ≡ z u) →
             hits (toPS {k = 0} st) x y z ≡ true
  val-hits st x y z h =
    hits-intro (toPS {k = 0} st) x y z (λ u → trans (outBit-st st x y u) (h u))

  hits-miss : (st : State n m) (x : Assign n) (y : Assign m) (z : Assign n)
              (w : Fin n) → ¬ (valᵛ (sig st w) x y ≡ z w) →
              hits (toPS {k = 0} st) x y z ≡ false
  hits-miss st x y z w ne = not-true (λ h → ne (hits-val st x y z h w))

  -- Two paths, of two states, hit two outputs alike when each reads
  -- its own output on a wire w, and away from w they read the same
  -- values and the outputs agree.

  hits-off→ : (st : State n m) (st′ : State n m′) (x : Assign n)
              (y : Assign m) (y′ : Assign m′) (z z′ : Assign n) (w : Fin n) →
              valᵛ (sig st′ w) x y′ ≡ z′ w →
              (∀ u → u ≢ w → valᵛ (sig st u) x y ≡ valᵛ (sig st′ u) x y′) →
              (∀ u → u ≢ w → z u ≡ z′ u) →
              hits (toPS {k = 0} st) x y z ≡ true →
              hits (toPS {k = 0} st′) x y′ z′ ≡ true
  hits-off→ st st′ x y y′ z z′ w hw′ sv sz h = val-hits st′ x y′ z′ (λ u →
    wire u w
      (λ u≡w → Eq.subst (λ v → valᵛ (sig st′ v) x y′ ≡ z′ v) (sym u≡w) hw′)
      (λ u≢w → trans (sym (sv u u≢w))
                     (trans (hits-val st x y z h u) (sz u u≢w))))

  hits-off : (st : State n m) (st′ : State n m′) (x : Assign n)
             (y : Assign m) (y′ : Assign m′) (z z′ : Assign n) (w : Fin n) →
             valᵛ (sig st w) x y ≡ z w → valᵛ (sig st′ w) x y′ ≡ z′ w →
             (∀ u → u ≢ w → valᵛ (sig st u) x y ≡ valᵛ (sig st′ u) x y′) →
             (∀ u → u ≢ w → z u ≡ z′ u) →
             hits (toPS {k = 0} st) x y z ≡ hits (toPS {k = 0} st′) x y′ z′
  hits-off st st′ x y y′ z z′ w hw hw′ sv sz = bool-iff
    (hits-off→ st st′ x y y′ z z′ w hw′ sv sz)
    (hits-off→ st′ st x y′ y z′ z w hw
      (λ u u≢w → sym (sv u u≢w)) (λ u u≢w → sym (sz u u≢w)))


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
               ampˢ st′ x z ≐ rot e (ampˢ st x z)
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

-- S multiplies each entry by i^(z_w).

ampˢ-S : ∀ {n m} (w : Fin n) (st : State n m) (x z : Assign n) →
         ampˢ (stepS w st) x z ≐ rot (¼ * [ z w ]ᶻ) (ampˢ st x z)
ampˢ-S w st x z =
  phase-gate (stepS w st) st x z (¼ * [ z w ]ᶻ) (λ _ → refl) (λ y h →
    trans (eval-S w st x y)
      (trans (cong (λ b → eval (poly st) x y + ¼ * [ b ]ᶻ)
                   (hits-val st x y z h w))
             (+-comm (eval (poly st) x y) (¼ * [ z w ]ᶻ))))

-- CZ multiplies each entry by (-1)^(z_w z_v).

ampˢ-CZ : ∀ {n m} (w v : Fin n) (st : State n m) (x z : Assign n) →
          ampˢ (stepCZ w v st) x z ≐ rot (½ * [ z w ∧ z v ]ᶻ) (ampˢ st x z)
ampˢ-CZ w v st x z =
  phase-gate (stepCZ w v st) st x z (½ * [ z w ∧ z v ]ᶻ) (λ _ → refl)
    (λ y h → trans (eval-CZ w v st x y)
      (trans (cong₂ (λ a b → eval (poly st) x y + ½ * [ a ∧ b ]ᶻ)
                    (hits-val st x y z h w) (hits-val st x y z h v))
             (+-comm (eval (poly st) x y) (½ * [ z w ∧ z v ]ᶻ))))


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
           valᵛ (sig st′ w) x y′ ≡ z w →
           (∀ u → u ≢ w → valᵛ (sig st u) x y ≡ valᵛ (sig st′ u) x y′) →
           eval (poly st′) x y′ ≡
           eval (poly st) x y + ½ * [ valᵛ (sig st w) x y ∧ d ]ᶻ →
           term st′ x z y′ ≐
           (term st x (z [ w ≔ false ]) y +ᴬ
            rot (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ]) y))
  H-term st st′ w x z y y′ d hw sv ph = split (valᵛ (sig st w) x y) refl
    where
    P : ℤ
    P = eval (poly st) x y

    -- y′ hits z as y hits z with w set to the old value on w.

    moved : (o : Bool) → valᵛ (sig st w) x y ≡ o →
            hits (toPS {k = 0} st′) x y′ z ≡
            hits (toPS {k = 0} st) x y (z [ w ≔ o ])
    moved o eo = hits-off st′ st x y′ y z (z [ w ≔ o ]) w hw
      (trans eo (sym (≔-here z w o)))
      (λ u u≢w → sym (sv u u≢w))
      (λ u u≢w → sym (≔-there z o u≢w))

    split : (o : Bool) → valᵛ (sig st w) x y ≡ o →
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
          Σᴮ F ≐ (ampˢ st x (z [ w ≔ false ]) +ᴬ
                  rot (½ * [ d ]ᶻ) (ampˢ st x (z [ w ≔ true ])))
  H-sum st w x z d F h i = trans (Σᴮ-cong h i)
    (trans (Σᴮ-+ (term st x (z [ w ≔ false ]))
                 (λ y → rot (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ]) y)) i)
           (cong (Σᴮ (term st x (z [ w ≔ false ])) i +_)
                 (sym (rot-Σᴮ (½ * [ d ]ᶻ) (term st x (z [ w ≔ true ])) i))))

-- A Hadamard that allocates a path variable.  The sum over the new
-- state's paths splits at that variable, which is the new value on w:
-- only the branch in which it is z w can hit z, and that branch is
-- the old paths, each read as above with d = z w.
--
-- The sign is written (-1)^(z w) from the start, and only the phase
-- is rewritten along z w ≡ b: rewriting inside rot would make Agda
-- compare two exponents that differ syntactically, and it does that
-- by unfolding the proofs that classify carries.

ampˢ-allocH : ∀ {n m} (w : Fin n) (st : State n m) (x z : Assign n) →
              ampˢ (allocH w st) x z ≐
              (ampˢ st x (z [ w ≔ false ]) +ᴬ
               rot (½ * [ z w ]ᶻ) (ampˢ st x (z [ w ≔ true ])))
ampˢ-allocH {n} {m} w st x z = by-wire (z w) refl
  where
  -- The paths whose new variable takes the value b.

  branch : Bool → Amp
  branch b = Σᴮ (λ y → term (allocH w st) x z (extend b y))

  new : (b : Bool) (y : Assign m) →
        valᵛ (sig (allocH w st) w) x (extend b y) ≡ b
  new b y = cong (λ v → valᵛ v x (extend b y))
                 (↦-here (λ v → wkVar (sig st v)) w y[ zero ])

  live : (b : Bool) → z w ≡ b →
         branch b ≐ (ampˢ st x (z [ w ≔ false ]) +ᴬ
                     rot (½ * [ z w ]ᶻ) (ampˢ st x (z [ w ≔ true ])))
  live b zb = H-sum st w x z (z w) (λ y → term (allocH w st) x z (extend b y))
    (λ y → H-term st (allocH w st) w x z y (extend b y) (z w)
      (trans (new b y) (sym zb))
      (λ u u≢w → sym (trans
        (cong (λ v → valᵛ v x (extend b y))
              (↦-there (λ v → wkVar (sig st v)) y[ zero ] u≢w))
        (val-wk b (sig st u) x y)))
      (trans (eval-allocH w st x b y)
        (cong (λ c → eval (poly st) x y + ½ * [ valᵛ (sig st w) x y ∧ c ]ᶻ)
              {x = b} {y = z w} (sym zb))))

  dead : (b : Bool) → ¬ (z w ≡ b) → branch b ≐ 0ᴬ
  dead b ne i = trans
    (Σᴮ-cong (λ y →
      if-false (hits (toPS {k = 0} (allocH w st)) x (extend b y) z)
               (zpow (eval (poly (allocH w st)) x (extend b y)))
               (hits-miss (allocH w st) x (extend b y) z w
                 (λ q → ne (trans (sym q) (new b y))))) i)
    (Σᴮ-0 {m} i)

  by-wire : (b : Bool) → z w ≡ b →
            ampˢ (allocH w st) x z ≐
            (ampˢ st x (z [ w ≔ false ]) +ᴬ
             rot (½ * [ z w ]ᶻ) (ampˢ st x (z [ w ≔ true ])))
  by-wire true zb i = trans
    (cong₂ _+_ (live true zb i)
               (dead false (λ q → true≢false (trans (sym zb) q)) i))
    (+-identityʳ ((ampˢ st x (z [ w ≔ false ]) +ᴬ
                   rot (½ * [ z w ]ᶻ) (ampˢ st x (z [ w ≔ true ]))) i))
  by-wire false zb i = trans
    (cong₂ _+_ (dead true (λ q → false≢true (trans (sym zb) q)) i)
               (live false zb i))
    (+-identityˡ ((ampˢ st x (z [ w ≔ false ]) +ᴬ
                   rot (½ * [ z w ]ᶻ) (ampˢ st x (z [ w ≔ true ]))) i))

-- A Hadamard whose variable is forced to be x_w.  The wire w now reads
-- x w, so no path hits z unless z w = x w, and when it does every
-- path is read as above with d = x w.

ampˢ-finalH : ∀ {n m} (w : Fin n) (st : State n m) (x z : Assign n) →
              ampˢ (finalH w st) x z ≐
              (if (z w =ᵇ x w)
               then (ampˢ st x (z [ w ≔ false ]) +ᴬ
                     rot (½ * [ x w ]ᶻ) (ampˢ st x (z [ w ≔ true ])))
               else 0ᴬ)
ampˢ-finalH {n} {m} w st x z = by-diag (z w =ᵇ x w) refl
  where
  new : (y : Assign m) → valᵛ (sig (finalH w st) w) x y ≡ x w
  new y = cong (λ v → valᵛ v x y) (↦-here (sig st) w x[ w ])

  by-diag : (c : Bool) → (z w =ᵇ x w) ≡ c →
            ampˢ (finalH w st) x z ≐
            (if c
             then (ampˢ st x (z [ w ≔ false ]) +ᴬ
                   rot (½ * [ x w ]ᶻ) (ampˢ st x (z [ w ≔ true ])))
             else 0ᴬ)
  by-diag true eq = H-sum st w x z (x w) (term (finalH w st) x z)
    (λ y → H-term st (finalH w st) w x z y y (x w)
      (trans (new y) (sym (=ᵇ-true {z w} {x w} eq)))
      (λ u u≢w → sym (cong (λ v → valᵛ v x y)
                           (↦-there (sig st) x[ w ] u≢w)))
      (eval-finalH w st x y))
  by-diag false eq i = trans
    (Σᴮ-cong (λ y →
      if-false (hits (toPS {k = 0} (finalH w st)) x y z)
               (zpow (eval (poly (finalH w st)) x y))
               (hits-miss (finalH w st) x y z w (λ q →
                 =ᵇ-false {z w} {x w} eq (sym (trans (sym (new y)) q))))) i)
    (Σᴮ-0 {m} i)


------------------------------------------------------------------------
-- The starting state

-- There are no path variables, so the single path hits z exactly when
-- z is x, with phase 0.

ampˢ-init : ∀ {n} (x z : Assign n) →
            ampˢ (init {n}) x z ≐ (if same x z then zpow 0ℤ else 0ᴬ)
ampˢ-init {n} x z = at (λ ())
  where
  at : (y : Assign 0) →
       (if hits (toPS {k = 0} (init {n})) x y z
        then zpow (eval (0ᴾ {n} {0}) x y) else 0ᴬ) ≐
       (if same x z then zpow 0ℤ else 0ᴬ)
  at y = if-cong
    (bool-iff (λ h → same-intro x z (hits-val (init {n}) x y z h))
              (λ h → val-hits (init {n}) x y z (same-true x z h)))
    (zpow-≡ (eval-0ᴾ-val x y))
