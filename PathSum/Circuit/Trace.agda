------------------------------------------------------------------------
-- Presentations of groups
--
-- The path-sums of a circuit over {H, S, CZ}, and its isometry
-- restriction, one path at a time (Amy, QPL 2018, definition 2.9 and
-- section 4.1)
--
-- PathSum.Circuit interprets a circuit over {H, S, CZ} by running an
-- interpretation state through it -- a phase polynomial and, on each
-- wire, the variable it holds -- in two ways: ⟦ C ⟧, definition 2.9's
-- path-sum, in which every Hadamard allocates a path variable, and
-- ⟦ C ⟧ᴿ, its isometry restriction already reified, in which the last
-- Hadamard on a wire puts the input x_w there instead.  This module
-- reads both along a single path, as PathSum.CRK.Trace does for
-- {H, CNOT, R_k, R_k†}: the phase is an integer and each wire holds a
-- bit, and the gates update that configuration,
--
--    H on w   adds ½ · v_w · b to the phase and puts b on w,
--    S on w   adds ¼ · v_w,
--    CZ w u   adds ½ · v_w · v_u,
--
-- b being the bit the Hadamard reads.  For ⟦ C ⟧ (trace) the gate g of
-- g ∷ C reads the stream's bit s (norm C), the number of Hadamards
-- after it: the state machine allocates a Hadamard's variable at the
-- head, so the first Hadamard owns the last path variable.  For
-- ⟦ C ⟧ᴿ (traceᴿ) a Hadamard that is not the last on its wire reads
-- s (allocs C), allocs C counting the Hadamards after it that allocate,
-- and the last one on its wire reads x_w, the input on that wire.
--
-- run-traceᵁ and run-traceᴿ are the invariants, for any starting state
-- with path variables of its own; at the initial state they read the
-- two path-sums path by path (eval-⟦⟧, eval-out-⟦⟧, eval-⟦⟧ᴿ,
-- eval-out-⟦⟧ᴿ), and paths≡allocs counts the path variables of the
-- restriction.  The traces read only the first norm C (allocs C) bits
-- of the stream (trace-below, traceᴿ-below).  The configurations, the
-- streams and the conversions between paths and streams are
-- PathSum.CRK.Trace's.  PathSum.Circuit.Structural uses all of this to
-- show that exchanging gates on disjoint wires renames path variables
-- and changes nothing else.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Circuit.Trace (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; _+_; _*_)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (zero; suc; _<_) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; _[_≔_])
open import PathSum.Base using (phase; out; head-part; tail-part)
open import PathSum.Circuit M using
  (Gate; H; S; CZ; Circuit; norm; hasH; State; poly; sig; init; stepS;
   stepCZ; allocH; finalH; stepH; mono; wkVar; wkPoly; _[_↦_]; run; runᵁ;
   paths; pathsᵁ; ⟦_⟧; ⟦_⟧ᴿ)
open import PathSum.CRK.Trace M₀ using
  (Stream; Conf; _≈ᶜ_; conf≈; ≈φ; ≈v; ≈ᶜ-refl; ≈ᶜ-sym; ≈ᶜ-trans; ≔-cong₂;
   str; pathOf; pathOf-str; after; start)
open import PathSum.Cyclotomic M₀ using (extend)
open import PathSum.Denotation M₀ using
  (Assign; eval-true; eval-false; eval-0ᴾ-val; eval-μ-val)
open import PathSum.Polynomial using
  (Poly; Mon; Var; x[_]; y[_]; ⟪_⟫; _∪ᵐ_; 0ᴾ; _·ᴾ_; eval; satᵐ)
open import PathSum.Polynomial.Properties using
  (valᵛ; satᵐ-∪; satᵐ-⟪⟫; eval-+ᴾ; eval-·ᴾ; eval-ext; eval-cong;
   Σmon-cong; Σmon-delta; ⌊≟ᵐ⌋; if-swap; _≡ᵐᵇ_)
open import PathSum.Reduction M using (¼; ½)

private
  variable
    n m K : ℕ


------------------------------------------------------------------------
-- The gates on a configuration

-- One gate, b the bit a Hadamard reads (the others read none).

gateᶜ : Gate n → Bool → Conf n → Conf n
gateᶜ (H w)    b (φ , v) = φ + ½ * [ v w ∧ b ]ᶻ , v [ w ≔ b ]
gateᶜ (S w)    b (φ , v) = φ + ¼ * [ v w ]ᶻ , v
gateᶜ (CZ w u) b (φ , v) = φ + ½ * [ v w ∧ v u ]ᶻ , v

gateᶜ-cong : (g : Gate n) {b b′ : Bool} {a a′ : Conf n} → b ≡ b′ →
             a ≈ᶜ a′ → gateᶜ g b a ≈ᶜ gateᶜ g b′ a′
gateᶜ-cong (H w) {a = φ , v} {φ′ , v′} b≡b′ (conf≈ p q) = conf≈
  (cong₂ (λ e d → e + ½ * [ d ]ᶻ) p (cong₂ _∧_ (q w) b≡b′))
  (≔-cong₂ w b≡b′ q)
gateᶜ-cong (S w) {a = φ , v} {φ′ , v′} b≡b′ (conf≈ p q) = conf≈
  (cong₂ (λ e d → e + ¼ * [ d ]ᶻ) p (q w)) q
gateᶜ-cong (CZ w u) {a = φ , v} {φ′ , v′} b≡b′ (conf≈ p q) = conf≈
  (cong₂ (λ e d → e + ½ * [ d ]ᶻ) p (cong₂ _∧_ (q w) (q u))) q


------------------------------------------------------------------------
-- The trace of ⟦ C ⟧

-- The gate g of g ∷ C reads the bit s (norm C).

trace : Circuit n → Stream → Conf n → Conf n
trace []      s a = a
trace (g ∷ C) s a = trace C s (gateᶜ g (s (norm C)) a)

trace-cong : (C : Circuit n) {s s′ : Stream} {a a′ : Conf n} →
             (∀ i → s i ≡ s′ i) → a ≈ᶜ a′ → trace C s a ≈ᶜ trace C s′ a′
trace-cong []      s≗ a≈ = a≈
trace-cong (g ∷ C) s≗ a≈ = trace-cong C s≗ (gateᶜ-cong g (s≗ (norm C)) a≈)

-- It reads only the first norm C bits.

trace-below : (C : Circuit n) {s s′ : Stream} {a a′ : Conf n} →
              (∀ i → i < norm C → s i ≡ s′ i) → a ≈ᶜ a′ →
              trace C s a ≈ᶜ trace C s′ a′
trace-below []         h a≈ = a≈
trace-below (H w ∷ C)  h a≈ =
  trace-below C (λ i i< → h i (ℕ.m<n⇒m<1+n i<))
              (gateᶜ-cong (H w) (h (norm C) (ℕ.n<1+n (norm C))) a≈)
trace-below (S w ∷ C)  {s} h a≈ =
  trace-below C h (gateᶜ-cong (S w) {s (norm C)} {s (norm C)} refl a≈)
trace-below (CZ w u ∷ C) {s} h a≈ =
  trace-below C h (gateᶜ-cong (CZ w u) {s (norm C)} {s (norm C)} refl a≈)


------------------------------------------------------------------------
-- The trace of ⟦ C ⟧ᴿ

-- The number of Hadamards of C that allocate a path variable in the
-- restriction: those that are not the last on their wire.

allocs : Circuit n → ℕ
allocs []           = 0
allocs (H w ∷ C)    = if hasH w C then suc (allocs C) else allocs C
allocs (S _ ∷ C)    = allocs C
allocs (CZ _ _ ∷ C) = allocs C

-- The bit a Hadamard reads: the stream's, at position i, if it
-- allocates, and the input on its wire if it is the last there.

hbit : Bool → Stream → ℕ → Bool → Bool
hbit true  s i c = s i
hbit false s i c = c

bitᴿ : Gate n → Circuit n → Stream → Assign n → Bool
bitᴿ (H w)    C s x = hbit (hasH w C) s (allocs C) (x w)
bitᴿ (S _)    C s x = false
bitᴿ (CZ _ _) C s x = false

traceᴿ : Circuit n → Stream → Assign n → Conf n → Conf n
traceᴿ []      s x a = a
traceᴿ (g ∷ C) s x a = traceᴿ C s x (gateᶜ g (bitᴿ g C s x) a)

traceᴿ-cong : (C : Circuit n) {s s′ : Stream} (x : Assign n)
              {a a′ : Conf n} → (∀ i → s i ≡ s′ i) → a ≈ᶜ a′ →
              traceᴿ C s x a ≈ᶜ traceᴿ C s′ x a′
traceᴿ-cong []            x s≗ a≈ = a≈
traceᴿ-cong (H w ∷ C) {s} {s′} x s≗ a≈ =
  traceᴿ-cong C x s≗ (gateᶜ-cong (H w) (bit (hasH w C)) a≈)
  where
  bit : ∀ b → hbit b s (allocs C) (x w) ≡ hbit b s′ (allocs C) (x w)
  bit true  = s≗ (allocs C)
  bit false = refl
traceᴿ-cong (S w ∷ C)     x s≗ a≈ =
  traceᴿ-cong C x s≗ (gateᶜ-cong (S w) {false} {false} refl a≈)
traceᴿ-cong (CZ w u ∷ C)  x s≗ a≈ =
  traceᴿ-cong C x s≗ (gateᶜ-cong (CZ w u) {false} {false} refl a≈)

-- It reads only the first allocs C bits.

traceᴿ-below : (C : Circuit n) {s s′ : Stream} (x : Assign n)
               {a a′ : Conf n} → (∀ i → i < allocs C → s i ≡ s′ i) →
               a ≈ᶜ a′ → traceᴿ C s x a ≈ᶜ traceᴿ C s′ x a′
traceᴿ-below []           x h a≈ = a≈
traceᴿ-below (H w ∷ C) {s} {s′} x {a} {a′} h a≈ = go (hasH w C) h
  where
  go : ∀ b → (∀ i → i < (if b then suc (allocs C) else allocs C) →
                    s i ≡ s′ i) →
       traceᴿ C s x (gateᶜ (H w) (hbit b s (allocs C) (x w)) a) ≈ᶜ
       traceᴿ C s′ x (gateᶜ (H w) (hbit b s′ (allocs C) (x w)) a′)
  go true  h′ = traceᴿ-below C x (λ i i< → h′ i (ℕ.m<n⇒m<1+n i<))
    (gateᶜ-cong (H w) (h′ (allocs C) (ℕ.n<1+n (allocs C))) a≈)
  go false h′ = traceᴿ-below C x h′ (gateᶜ-cong (H w) refl a≈)
traceᴿ-below (S w ∷ C)    x h a≈ =
  traceᴿ-below C x h (gateᶜ-cong (S w) {false} {false} refl a≈)
traceᴿ-below (CZ w u ∷ C) x h a≈ =
  traceᴿ-below C x h (gateᶜ-cong (CZ w u) {false} {false} refl a≈)


------------------------------------------------------------------------
-- Values of the polynomials a gate adds

-- Re-proved from PathSum.CircuitAmp, where they are private.

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

  -- The value of a redirected wire.
  val-↦ : (σ : Fin n → Var n m) (w : Fin n) (v : Var n m) (x : Assign n)
          (y : Assign m) (u : Fin n) →
          valᵛ ((σ [ w ↦ v ]) u) x y ≡
          ((λ u′ → valᵛ (σ u′) x y) [ w ≔ valᵛ v x y ]) u
  val-↦ σ w v x y u with u Fin.≟ w
  ... | yes _ = refl
  ... | no  _ = refl

-- A variable reads its assignments only through their values.

valᵛ-≗ : (v : Var n m) (x : Assign n) {y y′ : Assign m} →
         (∀ j → y j ≡ y′ j) → valᵛ v x y ≡ valᵛ v x y′
valᵛ-≗ x[ i ] x y≗ = refl
valᵛ-≗ y[ j ] x y≗ = y≗ j


------------------------------------------------------------------------
-- The traces compute the path-sums

-- What a state stands for at a path: its phase and its wires' values.

confOf : State n m → Assign n → Assign m → Conf n
confOf st x y = eval (poly st) x y , (λ w → valᵛ (sig st w) x y)

-- One gate.

private
  step-allocH : (w : Fin n) (st : State n m) (x : Assign n) (s : Stream)
                (d : ℕ) →
                confOf (allocH w st) x (after d s) ≈ᶜ
                gateᶜ (H w) (s d) (confOf st x (after (suc d) s))
  step-allocH w st x s d = conf≈
    (trans (eval-cong (poly (allocH w st)) (λ _ → refl) ext)
           (eval-allocH w st x (s d) y))
    (λ u → trans (val-↦ (λ v → wkVar (sig st v)) w y[ zero ] x y′ u)
                 (≔-cong₂ w (ext zero)
                    (λ v → trans (valᵛ-≗ (wkVar (sig st v)) x ext)
                                 (val-wk (s d) (sig st v) x y)) u))
    where
    y′ = after d s
    y  = after (suc d) s

    ext : ∀ j → y′ j ≡ extend (s d) y j
    ext zero    = cong s (ℕ.+-identityʳ d)
    ext (suc j) = cong s (ℕ.+-suc d (toℕ j))

  step-finalH : (w : Fin n) (st : State n m) (x : Assign n) (y : Assign m) →
                confOf (finalH w st) x y ≈ᶜ gateᶜ (H w) (x w) (confOf st x y)
  step-finalH w st x y =
    conf≈ (eval-finalH w st x y) (val-↦ (sig st) w x[ w ] x y)

  step-S : (w : Fin n) (st : State n m) (x : Assign n) (y : Assign m)
           (b : Bool) →
           confOf (stepS w st) x y ≈ᶜ gateᶜ (S w) b (confOf st x y)
  step-S w st x y b = conf≈ (eval-S w st x y) (λ _ → refl)

  step-CZ : (w u : Fin n) (st : State n m) (x : Assign n) (y : Assign m)
            (b : Bool) →
            confOf (stepCZ w u st) x y ≈ᶜ gateᶜ (CZ w u) b (confOf st x y)
  step-CZ w u st x y b = conf≈ (eval-CZ w u st x y) (λ _ → refl)

-- Every Hadamard allocating: ⟦ C ⟧.

run-traceᵁ : (C : Circuit n) (st : State n m) (x : Assign n) (s : Stream) →
             confOf (proj₂ (runᵁ C st)) x (pathOf s) ≈ᶜ
             trace C s (confOf st x (after (norm C) s))
run-traceᵁ []             st x s = ≈ᶜ-refl
run-traceᵁ (H w ∷ C)      st x s = ≈ᶜ-trans
  (run-traceᵁ C (allocH w st) x s)
  (trace-cong C (λ _ → refl) (step-allocH w st x s (norm C)))
run-traceᵁ (S w ∷ C)      st x s = ≈ᶜ-trans
  (run-traceᵁ C (stepS w st) x s)
  (trace-cong C (λ _ → refl)
    (step-S w st x (after (norm C) s) (s (norm C))))
run-traceᵁ (CZ w u ∷ C)   st x s = ≈ᶜ-trans
  (run-traceᵁ C (stepCZ w u st) x s)
  (trace-cong C (λ _ → refl)
    (step-CZ w u st x (after (norm C) s) (s (norm C))))

-- The last Hadamard on a wire reading the input: ⟦ C ⟧ᴿ.

run-traceᴿ : (C : Circuit n) (st : State n m) (x : Assign n) (s : Stream) →
             confOf (proj₂ (run C st)) x (pathOf s) ≈ᶜ
             traceᴿ C s x (confOf st x (after (allocs C) s))
run-traceᴿ []             st x s = ≈ᶜ-refl
run-traceᴿ (H w ∷ C)      st x s = go (hasH w C)
  where
  go : ∀ b → confOf (proj₂ (run C (proj₂ (stepH b w st)))) x (pathOf s) ≈ᶜ
             traceᴿ C s x (gateᶜ (H w) (hbit b s (allocs C) (x w))
               (confOf st x (after (if b then suc (allocs C) else allocs C) s)))
  go true  = ≈ᶜ-trans (run-traceᴿ C (allocH w st) x s)
    (traceᴿ-cong C x (λ _ → refl) (step-allocH w st x s (allocs C)))
  go false = ≈ᶜ-trans (run-traceᴿ C (finalH w st) x s)
    (traceᴿ-cong C x (λ _ → refl)
      (step-finalH w st x (after (allocs C) s)))
run-traceᴿ (S w ∷ C)      st x s = ≈ᶜ-trans
  (run-traceᴿ C (stepS w st) x s)
  (traceᴿ-cong C x (λ _ → refl)
    (step-S w st x (after (allocs C) s) false))
run-traceᴿ (CZ w u ∷ C)   st x s = ≈ᶜ-trans
  (run-traceᴿ C (stepCZ w u st) x s)
  (traceᴿ-cong C x (λ _ → refl)
    (step-CZ w u st x (after (allocs C) s) false))

-- The restriction has allocs C path variables.

paths≡allocs : (C : Circuit n) → paths C ≡ allocs C
paths≡allocs {n} C = trans (count C (init {n})) (ℕ.+-identityʳ (allocs C))
  where
  count : ∀ {m} (C : Circuit n) (st : State n m) →
          proj₁ (run C st) ≡ allocs C ℕ+ m
  count []            st = refl
  count {m} (H w ∷ C) st = go (hasH w C)
    where
    go : ∀ b → proj₁ (run C (proj₂ (stepH b w st))) ≡
               (if b then suc (allocs C) else allocs C) ℕ+ m
    go true  = trans (count C (allocH w st)) (ℕ.+-suc (allocs C) m)
    go false = count C (finalH w st)
  count (S w ∷ C)     st = count C (stepS w st)
  count (CZ w u ∷ C)  st = count C (stepCZ w u st)


------------------------------------------------------------------------
-- The two path-sums, path by path

private
  init≈ : (x : Assign n) (y : Assign 0) → confOf (init {n}) x y ≈ᶜ start x
  init≈ x y = conf≈ (eval-0ᴾ-val x y) (λ w → refl)

  start-ᵁ : (C : Circuit n) (x : Assign n) (s : Stream) →
            confOf (proj₂ (runᵁ C init)) x (pathOf s) ≈ᶜ trace C s (start x)
  start-ᵁ C x s = ≈ᶜ-trans (run-traceᵁ C init x s)
    (trace-cong C (λ _ → refl) (init≈ x (after (norm C) s)))

  start-ᴿ : (C : Circuit n) (x : Assign n) (s : Stream) →
            confOf (proj₂ (run C init)) x (pathOf s) ≈ᶜ traceᴿ C s x (start x)
  start-ᴿ C x s = ≈ᶜ-trans (run-traceᴿ C init x s)
    (traceᴿ-cong C x (λ _ → refl) (init≈ x (after (allocs C) s)))

-- ⟦ C ⟧: its phase and its outputs along the path y.

eval-⟦⟧ : (C : Circuit n) (x : Assign n) (y : Assign (pathsᵁ C)) →
          eval (phase ⟦ C ⟧) x y ≡ proj₁ (trace C (str y) (start x))
eval-⟦⟧ C x y = trans
  (eval-cong (phase ⟦ C ⟧) (λ _ → refl) (λ i → sym (pathOf-str y i)))
  (≈φ (start-ᵁ C x (str y)))

eval-out-⟦⟧ : (C : Circuit n) (x : Assign n) (y : Assign (pathsᵁ C))
              (w : Fin n) →
              eval (out ⟦ C ⟧ w) x y ≡
              [ proj₂ (trace C (str y) (start x)) w ]ᶻ
eval-out-⟦⟧ {n} C x y w = trans (eval-μ-val (sig r w) x y)
  (cong [_]ᶻ (trans (valᵛ-≗ (sig r w) x (λ i → sym (pathOf-str y i)))
                    (≈v (start-ᵁ C x (str y)) w)))
  where
  r = proj₂ (runᵁ C (init {n}))

-- ⟦ C ⟧ᴿ: its phase and its outputs along the path y.

eval-⟦⟧ᴿ : (C : Circuit n) (x : Assign n) (y : Assign (paths C)) →
           eval (phase ⟦ C ⟧ᴿ) x y ≡ proj₁ (traceᴿ C (str y) x (start x))
eval-⟦⟧ᴿ C x y = trans
  (eval-cong (phase ⟦ C ⟧ᴿ) (λ _ → refl) (λ i → sym (pathOf-str y i)))
  (≈φ (start-ᴿ C x (str y)))

eval-out-⟦⟧ᴿ : (C : Circuit n) (x : Assign n) (y : Assign (paths C))
               (w : Fin n) →
               eval (out ⟦ C ⟧ᴿ w) x y ≡
               [ proj₂ (traceᴿ C (str y) x (start x)) w ]ᶻ
eval-out-⟦⟧ᴿ {n} C x y w = trans (eval-μ-val (sig r w) x y)
  (cong [_]ᶻ (trans (valᵛ-≗ (sig r w) x (λ i → sym (pathOf-str y i)))
                    (≈v (start-ᴿ C x (str y)) w)))
  where
  r = proj₂ (run C (init {n}))
