------------------------------------------------------------------------
-- Presentations of groups
--
-- The path-sum of a circuit over {H, X, CNOT, R_k, R_k†}, one path at
-- a time
--
-- PathSum.CRK.Trace reads the path-sum of a circuit over
-- {H, CNOT, R_k, R_k†} (definition 2.9) along a single path: the phase
-- is an integer, each wire a bit, and every Hadamard reads the path's
-- bit at its own position, the number of Hadamards after it.
-- PathSum.CRK.WithX adds the Pauli X gate, which negates the constant
-- of the form on its wire and allocates no path variable; along a path
-- it negates the wire's bit and leaves the phase alone.  This module
-- extends the trace to that gate set (traceˣ) and proves that it
-- computes the path-sum (run-traceˣ, and at the initial state
-- eval-⟦⟧ˣ, outBit-⟦⟧ˣ): an old gate's step is PathSum.CRK.Trace's,
-- obtained from its run-trace on the one-gate circuit, and X's is a
-- direct computation on forms.  Concatenation is sequential
-- composition, the first circuit reading the stream past the second's
-- Hadamards (trace-++ˣ), and an embedded circuit traces as it did
-- (traceˣ-embed).
--
-- PathSum.HiddenShift.Runs reads a layer of the hidden shift circuits
-- along a path: Runs C s v β v′ says that along the stream s, from any
-- phase φ and wires v, C ends with phase φ + ½β modulo 1 and wires v′.
-- The same reading here (Runsˣ) composes along concatenation
-- (Runsˣ-++), holds of an embedded circuit whenever Runs held of the
-- circuit (Runsˣ-embed), and the X layer X^s of
-- PathSum.HiddenShift.LayersX adds nothing to the phase -- exactly --
-- and leaves v ⊕ s on the wires (Runsˣ-flips), where Runs's H R₁ H
-- version of X reads two bits of the path for every X.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.TraceX (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n; ∣n⇒∣m*n)
open import Data.Integer.Properties using
  (+-identityʳ; +-inverseʳ; *-zeroʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using (phase)
open import PathSum.CRK.Amp M₀ using (outBit-liftᴸ)
open import PathSum.CRK.Trace M₀ using
  (Stream; Conf; _≈ᶜ_; conf≈; ≈φ; ≈v; ≈ᶜ-refl; ≈ᶜ-trans; ≔-cong₂; gateᶜ;
   gateᶜ-cong; trace; trace-cong; run-trace; confOf; pathOf; after; str;
   pathOf-str; start; valᴸ-≗; shift)
open import PathSum.Denotation M₀ using (Assign; outBit; eval-0ᴾ-val)
open import PathSum.HiddenShift.Runs M₀ using (Runs; runs-φ; runs-v)
open import PathSum.HiddenShift.Walsh using (_⊕ᵃ_)
open import PathSum.Linear using (Lin; valᴸ; valᴸ-var)
open import PathSum.Polynomial using (x[_]; eval)
open import PathSum.Polynomial.Properties using (eval-cong; i∣0)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

import PathSum.CRK.Circuit

private
  module CRK = PathSum.CRK.Circuit M

open CRK using (State; poly; sig; init; stepH; _[_↦_])
open import PathSum.CRK.WithX M₀ using
  (Gate; H; X; CNOT; R; R†; Circuit; norm; run; paths; ⟦_⟧; embed; notᴸ;
   valᴸ-not; stepX; norm-embed)
open import PathSum.Full.Canonical M using (pow∣½·2)
open import PathSum.HiddenShift.LayersX M₀ using
  (norm-++ˣ; selʰ; sel; flipsˣ)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The trace

-- One gate, b being the bit of the path variable it allocates if it is
-- a Hadamard: PathSum.CRK.Trace's step for the old gates; X negates the
-- bit on its wire.

gateᶜˣ : Gate n → Bool → Conf n → Conf n
gateᶜˣ (H w)        b a       = gateᶜ (CRK.H w) b a
gateᶜˣ (X w)        b (φ , v) = φ , v [ w ≔ not (v w) ]
gateᶜˣ (CNOT c t p) b a       = gateᶜ (CRK.CNOT c t p) b a
gateᶜˣ (R k w)      b a       = gateᶜ (CRK.R k w) b a
gateᶜˣ (R† k w)     b a       = gateᶜ (CRK.R† k w) b a

-- A whole circuit; the gate g of g ∷ C reads the bit s (norm C).

traceˣ : Circuit n → Stream → Conf n → Conf n
traceˣ []      s a = a
traceˣ (g ∷ C) s a = traceˣ C s (gateᶜˣ g (s (norm C)) a)

-- Only values are read.

gateᶜˣ-cong : (g : Gate n) {b b′ : Bool} {a a′ : Conf n} → b ≡ b′ →
              a ≈ᶜ a′ → gateᶜˣ g b a ≈ᶜ gateᶜˣ g b′ a′
gateᶜˣ-cong (H w)        bb aa = gateᶜ-cong (CRK.H w) bb aa
gateᶜˣ-cong (X w) {a = φ , v} {φ′ , v′} bb (conf≈ p q) =
  conf≈ p (≔-cong₂ w (cong not (q w)) q)
gateᶜˣ-cong (CNOT c t p) bb aa = gateᶜ-cong (CRK.CNOT c t p) bb aa
gateᶜˣ-cong (R k w)      bb aa = gateᶜ-cong (CRK.R k w) bb aa
gateᶜˣ-cong (R† k w)     bb aa = gateᶜ-cong (CRK.R† k w) bb aa

traceˣ-cong : (C : Circuit n) {s s′ : Stream} {a a′ : Conf n} →
              (∀ i → s i ≡ s′ i) → a ≈ᶜ a′ → traceˣ C s a ≈ᶜ traceˣ C s′ a′
traceˣ-cong []      s≗ a≈ = a≈
traceˣ-cong (g ∷ C) s≗ a≈ =
  traceˣ-cong C s≗ (gateᶜˣ-cong g (s≗ (norm C)) a≈)


------------------------------------------------------------------------
-- The trace computes the path-sum

private
  -- The value of a redirected wire (PathSum.CRK.Trace's, private).

  val-↦ : (σ : Fin n → Lin n m) (w : Fin n) (l : Lin n m) (x : Assign n)
          (y : Assign m) (u : Fin n) →
          valᴸ ((σ [ w ↦ l ]) u) x y ≡
          ((λ v → valᴸ (σ v) x y) [ w ≔ valᴸ l x y ]) u
  val-↦ σ w l x y u with u Fin.≟ w
  ... | yes _ = refl
  ... | no  _ = refl

  confOf-≗ : (st : State n m) (x : Assign n) {y y′ : Assign m} →
             (∀ j → y j ≡ y′ j) → confOf st x y ≈ᶜ confOf st x y′
  confOf-≗ st x h =
    conf≈ (eval-cong (poly st) (λ _ → refl) h) (λ w → valᴸ-≗ (sig st w) x h)

  -- X: the phase is unchanged, and the form on its wire negated.

  step-X : (w : Fin n) (st : State n m) (x : Assign n) (y : Assign m)
           (b : Bool) →
           confOf (stepX w st) x y ≈ᶜ gateᶜˣ (X w) b (confOf st x y)
  step-X w st x y b = conf≈ refl (λ u →
    trans (val-↦ (sig st) w (notᴸ (sig st w)) x y u)
          (≔-cong₂ {z = λ v → valᴸ (sig st v) x y}
                   {z′ = λ v → valᴸ (sig st v) x y}
                   w (valᴸ-not (sig st w) x y) (λ _ → refl) u))

  -- An old gate: PathSum.CRK.Trace's run-trace on the one-gate circuit,
  -- read on the stream past the d Hadamards after it.

  step-old : (g : CRK.Gate n) (st : State n m) (x : Assign n) (s : Stream)
             (d : ℕ) →
             confOf (proj₂ (CRK.run (g ∷ []) st)) x (after d s) ≈ᶜ
             gateᶜ g (s d) (confOf st x (after (CRK.norm (g ∷ []) ℕ+ d) s))
  step-old g st x s d = ≈ᶜ-trans
    (run-trace (g ∷ []) st x (λ i → s (d ℕ+ i)))
    (gateᶜ-cong g (cong s (ℕ.+-identityʳ d))
      (confOf-≗ st x (λ j → cong s (sh (CRK.norm (g ∷ [])) (toℕ j)))))
    where
    sh : ∀ k j → d ℕ+ (k ℕ+ j) ≡ (k ℕ+ d) ℕ+ j
    sh k j = trans (sym (ℕ.+-assoc d k j)) (cong (_ℕ+ j) (ℕ.+-comm d k))

-- From any state with m path variables of its own: the phase and the
-- wire values at the path of the stream are the trace's.

run-traceˣ : (C : Circuit n) (st : State n m) (x : Assign n) (s : Stream) →
             confOf (proj₂ (run C st)) x (pathOf s) ≈ᶜ
             traceˣ C s (confOf st x (after (norm C) s))
run-traceˣ []                st x s = ≈ᶜ-refl
run-traceˣ (H w ∷ C)         st x s = ≈ᶜ-trans
  (run-traceˣ C (stepH w st) x s)
  (traceˣ-cong C (λ _ → refl) (step-old (CRK.H w) st x s (norm C)))
run-traceˣ (X w ∷ C)         st x s = ≈ᶜ-trans
  (run-traceˣ C (stepX w st) x s)
  (traceˣ-cong C (λ _ → refl)
    (step-X w st x (after (norm C) s) (s (norm C))))
run-traceˣ (CNOT c t p ∷ C)  st x s = ≈ᶜ-trans
  (run-traceˣ C (CRK.stepCNOT c t st) x s)
  (traceˣ-cong C (λ _ → refl) (step-old (CRK.CNOT c t p) st x s (norm C)))
run-traceˣ (R k w ∷ C)       st x s = ≈ᶜ-trans
  (run-traceˣ C (CRK.stepR k w st) x s)
  (traceˣ-cong C (λ _ → refl) (step-old (CRK.R k w) st x s (norm C)))
run-traceˣ (R† k w ∷ C)      st x s = ≈ᶜ-trans
  (run-traceˣ C (CRK.stepR† k w st) x s)
  (traceˣ-cong C (λ _ → refl) (step-old (CRK.R† k w) st x s (norm C)))

private
  init≈ : (x : Assign n) (y : Assign 0) → confOf (init {n}) x y ≈ᶜ start x
  init≈ x y = conf≈ (eval-0ᴾ-val x y) (λ w → valᴸ-var x[ w ] x y)

  run-startˣ : (C : Circuit n) (x : Assign n) (s : Stream) →
               confOf (proj₂ (run C init)) x (pathOf s) ≈ᶜ
               traceˣ C s (start x)
  run-startˣ C x s = ≈ᶜ-trans (run-traceˣ C init x s)
    (traceˣ-cong C (λ _ → refl) (init≈ x (after (norm C) s)))

-- The phase and the outputs of ⟦ C ⟧ along the path y.

eval-⟦⟧ˣ : (C : Circuit n) (x : Assign n) (y : Assign (paths C)) →
           eval (phase ⟦ C ⟧) x y ≡ proj₁ (traceˣ C (str y) (start x))
eval-⟦⟧ˣ C x y = trans
  (eval-cong (phase ⟦ C ⟧) (λ _ → refl) (λ i → sym (pathOf-str y i)))
  (≈φ (run-startˣ C x (str y)))

outBit-⟦⟧ˣ : (C : Circuit n) (x : Assign n) (y : Assign (paths C))
             (w : Fin n) →
             outBit ⟦ C ⟧ x y w ≡ proj₂ (traceˣ C (str y) (start x)) w
outBit-⟦⟧ˣ C x y w = trans
  (outBit-liftᴸ ⟦ C ⟧ x y w (sig r w) refl)
  (trans (valᴸ-≗ (sig r w) x (λ i → sym (pathOf-str y i)))
         (≈v (run-startˣ C x (str y)) w))
  where
  r = proj₂ (run C init)


------------------------------------------------------------------------
-- Concatenation and embedding

-- C's Hadamards come before D's, so they own the bits after D's.

trace-++ˣ : (C D : Circuit n) (s : Stream) (a : Conf n) →
            traceˣ (C ++ D) s a ≈ᶜ traceˣ D s (traceˣ C (shift (norm D) s) a)
trace-++ˣ []      D s a = ≈ᶜ-refl
trace-++ˣ (g ∷ C) D s a = ≈ᶜ-trans
  (trace-++ˣ C D s (gateᶜˣ g (s (norm (C ++ D))) a))
  (traceˣ-cong D (λ _ → refl) (traceˣ-cong C (λ _ → refl)
    (gateᶜˣ-cong g (cong s (norm-++ˣ C D)) (≈ᶜ-refl {a = a}))))

-- A circuit without X traces as it did.

private
  gate-embed : (g : CRK.Gate n) (b : Bool) (a : Conf n) →
               gateᶜˣ (embed g) b a ≈ᶜ gateᶜ g b a
  gate-embed (CRK.H w)        b a = ≈ᶜ-refl
  gate-embed (CRK.CNOT c t p) b a = ≈ᶜ-refl
  gate-embed (CRK.R k w)      b a = ≈ᶜ-refl
  gate-embed (CRK.R† k w)     b a = ≈ᶜ-refl

traceˣ-embed : (C : CRK.Circuit n) (s : Stream) (a : Conf n) →
               traceˣ (map embed C) s a ≈ᶜ trace C s a
traceˣ-embed []      s a = ≈ᶜ-refl
traceˣ-embed (g ∷ C) s a = ≈ᶜ-trans
  (traceˣ-embed C s (gateᶜˣ (embed g) (s (norm (map embed C))) a))
  (trace-cong C (λ _ → refl)
    (≈ᶜ-trans (gate-embed g (s (norm (map embed C))) a)
              (gateᶜ-cong g (cong s (norm-embed C)) (≈ᶜ-refl {a = a}))))


------------------------------------------------------------------------
-- Arithmetic

-- PathSum.HiddenShift.Runs's, private there.

private
  diff-0 : ∀ a b → a ≡ b → pow M ∣ (a - b)
  diff-0 a b refl = subst (pow M ∣_) (sym (+-inverseʳ a)) i∣0

  half-even : ∀ t → (+ 2) ∣ t → pow M ∣ (½ * t)
  half-even t (divides r eq) =
    subst (pow M ∣_) (sym (trans (cong (½ *_) eq) (swap ½ r)))
          (∣n⇒∣m*n r pow∣½·2)
    where
    swap : ∀ h r → h * (r * (+ 2)) ≡ r * (h * (+ 2))
    swap = solve 2 (λ h r → h :* (r :* con (+ 2)) := r :* (h :* con (+ 2)))
                   refl

  bits-sum-even : ∀ a b → (+ 2) ∣ (([ a ]ᶻ + [ b ]ᶻ) - [ a xor b ]ᶻ)
  bits-sum-even false false = divides 0ℤ refl
  bits-sum-even false true  = divides 0ℤ refl
  bits-sum-even true  false = divides 0ℤ refl
  bits-sum-even true  true  = divides 1ℤ refl

  xor-half : ∀ a b →
             pow M ∣ ((½ * [ a ]ᶻ + ½ * [ b ]ᶻ) - ½ * [ a xor b ]ᶻ)
  xor-half a b = subst (pow M ∣_) (shape ½ [ a ]ᶻ [ b ]ᶻ [ a xor b ]ᶻ)
    (half-even _ (bits-sum-even a b))
    where
    shape : ∀ h A B C → h * ((A + B) - C) ≡ (h * A + h * B) - h * C
    shape = solve 4 (λ h A B C →
      h :* ((A :+ B) :- C) := (h :* A :+ h :* B) :- h :* C) refl

  plus-half-0 : ∀ φ → pow M ∣ (φ - (φ + ½ * [ false ]ᶻ))
  plus-half-0 φ =
    diff-0 φ (φ + ½ * [ false ]ᶻ)
           (sym (trans (cong (λ t → φ + t) (*-zeroʳ ½)) (+-identityʳ φ)))


------------------------------------------------------------------------
-- A circuit read along one path

-- From any phase φ and wires v, along the stream s, C ends with phase
-- φ + ½β modulo 1 and wires v′.

record Runsˣ (C : Circuit n) (s : Stream) (v : Assign n) (β : Bool)
             (v′ : Assign n) : Set where
  constructor runsˣ
  field
    runsˣ-φ : ∀ φ → pow M ∣ (proj₁ (traceˣ C s (φ , v)) - (φ + ½ * [ β ]ᶻ))
    runsˣ-v : ∀ φ w → proj₂ (traceˣ C s (φ , v)) w ≡ v′ w

open Runsˣ public

-- Concatenation: C reads the stream past D's Hadamards, and the
-- parities add.

Runsˣ-++ : (C D : Circuit n) {s : Stream} {v v₁ v₂ : Assign n}
           {β₁ β₂ : Bool} →
           Runsˣ C (shift (norm D) s) v β₁ v₁ → Runsˣ D s v₁ β₂ v₂ →
           Runsˣ (C ++ D) s v (β₁ xor β₂) v₂
Runsˣ-++ C D {s} {v} {v₁} {v₂} {β₁} {β₂} rC rD = runsˣ φ-part v-part
  where
  φ₁ : ℤ → ℤ
  φ₁ φ = proj₁ (traceˣ C (shift (norm D) s) (φ , v))

  e : ∀ φ → traceˣ (C ++ D) s (φ , v) ≈ᶜ traceˣ D s (φ₁ φ , v₁)
  e φ = ≈ᶜ-trans (trace-++ˣ C D s (φ , v))
                 (traceˣ-cong D (λ _ → refl) (conf≈ refl (runsˣ-v rC φ)))

  shape : ∀ T f₁ f x₁ x₂ x₁₂ →
          T - (f + x₁₂) ≡
          (T - (f₁ + x₂)) + ((f₁ - (f + x₁)) + ((x₁ + x₂) - x₁₂))
  shape = solve 6 (λ T f₁ f x₁ x₂ x₁₂ →
    T :- (f :+ x₁₂) :=
    (T :- (f₁ :+ x₂)) :+ ((f₁ :- (f :+ x₁)) :+ ((x₁ :+ x₂) :- x₁₂))) refl

  φ-part : ∀ φ → pow M ∣ (proj₁ (traceˣ (C ++ D) s (φ , v)) -
                          (φ + ½ * [ β₁ xor β₂ ]ᶻ))
  φ-part φ = subst (pow M ∣_)
    (sym (trans (cong (_- (φ + ½ * [ β₁ xor β₂ ]ᶻ)) (≈φ (e φ)))
                (shape (proj₁ (traceˣ D s (φ₁ φ , v₁))) (φ₁ φ) φ
                       (½ * [ β₁ ]ᶻ) (½ * [ β₂ ]ᶻ) (½ * [ β₁ xor β₂ ]ᶻ))))
    (∣m∣n⇒∣m+n (runsˣ-φ rD (φ₁ φ))
               (∣m∣n⇒∣m+n (runsˣ-φ rC φ) (xor-half β₁ β₂)))

  v-part : ∀ φ w → proj₂ (traceˣ (C ++ D) s (φ , v)) w ≡ v₂ w
  v-part φ w = trans (≈v (e φ) w) (runsˣ-v rD (φ₁ φ) w)

-- Only the values of the input wires, of the parity and of the output
-- wires matter.

Runsˣ-cong : {C : Circuit n} {s : Stream} {v u : Assign n} {β : Bool}
             {v′ : Assign n} →
             (∀ w → u w ≡ v w) → Runsˣ C s v β v′ → Runsˣ C s u β v′
Runsˣ-cong {C = C} {s} {v} {u} {β} h r = runsˣ
  (λ φ → subst (λ t → pow M ∣ (t - (φ + ½ * [ β ]ᶻ))) (sym (≈φ (e φ)))
               (runsˣ-φ r φ))
  (λ φ w → trans (≈v (e φ) w) (runsˣ-v r φ w))
  where
  e : ∀ φ → traceˣ C s (φ , u) ≈ᶜ traceˣ C s (φ , v)
  e φ = traceˣ-cong C (λ _ → refl) (conf≈ refl h)

Runsˣ-resp : {C : Circuit n} {s : Stream} {v : Assign n} {β β′ : Bool}
             {v′ v″ : Assign n} →
             β ≡ β′ → (∀ w → v′ w ≡ v″ w) → Runsˣ C s v β v′ →
             Runsˣ C s v β′ v″
Runsˣ-resp refl h r =
  runsˣ (runsˣ-φ r) (λ φ w → trans (runsˣ-v r φ w) (h w))

-- An embedded circuit runs as the circuit did.

Runsˣ-embed : (C : CRK.Circuit n) {s : Stream} {v : Assign n} {β : Bool}
              {v′ : Assign n} → Runs C s v β v′ → Runsˣ (map embed C) s v β v′
Runsˣ-embed C {s} {v} {β} r = runsˣ
  (λ φ → subst (λ t → pow M ∣ (t - (φ + ½ * [ β ]ᶻ))) (sym (≈φ (e φ)))
               (runs-φ r φ))
  (λ φ w → trans (≈v (e φ) w) (runs-v r φ w))
  where
  e : ∀ φ → traceˣ (map embed C) s (φ , v) ≈ᶜ trace C s (φ , v)
  e φ = traceˣ-embed C s (φ , v)


------------------------------------------------------------------------
-- The X layer

-- X gates on the wires ws, in order: each negates its wire's bit.

flipAll : List (Fin n) → Assign n → Assign n
flipAll []       v = v
flipAll (w ∷ ws) v = flipAll ws (v [ w ≔ not (v w) ])

trace-Xs : (ws : List (Fin n)) (s : Stream) (φ : ℤ) (v : Assign n) →
           traceˣ (map X ws) s (φ , v) ≡ (φ , flipAll ws v)
trace-Xs []       s φ v = refl
trace-Xs (w ∷ ws) s φ v = trace-Xs ws s φ (v [ w ≔ not (v w) ])

private
  flipAll-cong : (ws : List (Fin n)) {v v′ : Assign n} →
                 (∀ i → v i ≡ v′ i) → ∀ i → flipAll ws v i ≡ flipAll ws v′ i
  flipAll-cong []       h = h
  flipAll-cong (w ∷ ws) h = flipAll-cong ws (≔-cong₂ w (cong not (h w)) h)

  -- Overwriting wire suc w, read on the wires 1 … n.

  ≔-suc : (u : Assign (suc n)) (w : Fin n) (b : Bool) (i : Fin n) →
          (u [ suc w ≔ b ]) (suc i) ≡ ((λ j → u (suc j)) [ w ≔ b ]) i
  ≔-suc u w b i = go (i Fin.≟ w)
    where
    go : Dec (i ≡ w) →
         (u [ suc w ≔ b ]) (suc i) ≡ ((λ j → u (suc j)) [ w ≔ b ]) i
    go (yes e) = trans (cong (λ k → (u [ suc w ≔ b ]) (suc k)) e)
      (trans (≔-here u (suc w) b)
             (sym (trans (cong ((λ j → u (suc j)) [ w ≔ b ]) e)
                         (≔-here (λ j → u (suc j)) w b))))
    go (no i≢w) = trans (≔-there u b (λ e → i≢w (Fin.suc-injective e)))
                        (sym (≔-there (λ j → u (suc j)) b i≢w))

  -- X gates on the wires 1 … n leave wire 0 alone and act on the rest.

  flip-suc-0 : (ws : List (Fin n)) (u : Assign (suc n)) →
               flipAll (map suc ws) u zero ≡ u zero
  flip-suc-0 []       u = refl
  flip-suc-0 (w ∷ ws) u =
    trans (flip-suc-0 ws (u [ suc w ≔ not (u (suc w)) ]))
          (≔-there u {i = suc w} (not (u (suc w))) (λ ()))

  flip-suc-s : (ws : List (Fin n)) (u : Assign (suc n)) (j : Fin n) →
               flipAll (map suc ws) u (suc j) ≡ flipAll ws (λ i → u (suc i)) j
  flip-suc-s []       u j = refl
  flip-suc-s (w ∷ ws) u j =
    trans (flip-suc-s ws (u [ suc w ≔ not (u (suc w)) ]) j)
          (flipAll-cong ws (≔-suc u w (not (u (suc w)))) j)

  not-xor : ∀ a → not a ≡ a xor true
  not-xor false = refl
  not-xor true  = refl

-- The X gates of X^s shift the wires by s.

flipAll-sel : (s v : Assign n) → ∀ w → flipAll (sel s) v w ≡ (v ⊕ᵃ s) w
flipAll-sel {zero}  s v ()
flipAll-sel {suc n} s v w = go (s zero) refl w
  where
  ts tv : Assign n
  ts i = s (suc i)
  tv i = v (suc i)

  go : ∀ b → s zero ≡ b →
       ∀ w → flipAll (selʰ b (map suc (sel ts))) v w ≡ (v ⊕ᵃ s) w
  go false e zero    = trans (flip-suc-0 (sel ts) v)
    (trans (sym (xor-identityʳ (v zero))) (cong (v zero xor_) (sym e)))
  go false e (suc j) = trans (flip-suc-s (sel ts) v j) (flipAll-sel ts tv j)
  go true  e zero    =
    trans (flip-suc-0 (sel ts) (v [ zero ≔ not (v zero) ]))
      (trans (≔-here v zero (not (v zero)))
        (trans (not-xor (v zero)) (cong (v zero xor_) (sym e))))
  go true  e (suc j) =
    trans (flip-suc-s (sel ts) (v [ zero ≔ not (v zero) ]) j)
      (trans (flipAll-cong (sel ts)
                           (λ i → ≔-there v {i = zero} (not (v zero)) (λ ())) j)
             (flipAll-sel ts tv j))

-- So X^s adds nothing to the phase and leaves v ⊕ s on the wires.

Runsˣ-flips : (s : Assign n) (st : Stream) (v : Assign n) →
              Runsˣ (flipsˣ s) st v false (v ⊕ᵃ s)
Runsˣ-flips s st v = runsˣ
  (λ φ → subst (λ t → pow M ∣ (t - (φ + ½ * [ false ]ᶻ)))
               (sym (cong proj₁ (trace-Xs (sel s) st φ v)))
               (plus-half-0 φ))
  (λ φ w → trans (cong (λ a → proj₂ a w) (trace-Xs (sel s) st φ v))
                 (flipAll-sel s v w))
