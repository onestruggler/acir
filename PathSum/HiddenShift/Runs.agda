------------------------------------------------------------------------
-- Presentations of groups
--
-- The layers of the hidden shift circuits, read along one path
--
-- The circuits of figure 3 (Amy, QPL 2018, section 5.2;
-- PathSum.HiddenShift.Circuit and Symbolic) are lists of gates over
-- {H, CNOT, R_k, R_k†}, and their path-sums (definition 2.9) have
-- polynomials that are never computed here.  PathSum.CRK.Trace reads
-- a circuit's path-sum along one path instead: the phase is an integer
-- and each wire a bit, and a Hadamard reads the path's bit at its own
-- position, the number of Hadamards after it.  This module computes
-- that reading for the layers the two circuits are built from, as
-- needed to reduce their path-sums by the rules of figure 2
-- (PathSum.HiddenShift.ExistsSymbolic and ExistsCircuit): which bits
-- each layer's Hadamards read, what it leaves on the wires, and the
-- parity of the phase it adds.
--
-- Runs C s v β v′ says that along the stream s, from any phase φ and
-- wires v, the circuit C ends with phase φ + ½β modulo 1 and wires v′.
-- Runs compose along concatenation, the first circuit reading the
-- stream past the second's Hadamards (Runs-++, from Trace's trace-++),
-- and a circuit moved one wire down or onto the first block of wires
-- runs as before on those wires (Runs-lift, Runs-upper, from Trace's
-- trace-map).  The phase gadgets need their phases exactly (RunsE: a
-- CZ's S gates add quarters, a CCZ's T gates eighths), which then sum
-- to ½ times the monomial (Runs-term).  The layers:
--
--  * H^{⊗n} (hadamards): wire w reads the bit at position n-1-w
--    (hbits), which it then holds; the phase adds ½ v·b.
--  * X^s (flips): X = H R₁ H on every wire w with s_w = 1 reads two
--    bits c₁, c₂ (xbits, at positions xrev), adds ½ (v_w c₁ + c₁ +
--    c₁ c₂) (xβ) and leaves c₂ on the wire (xout); other wires are
--    untouched.  A reduction later sets c₁ = 0 and c₂ = v_w ⊕ 1, which
--    is X.
--  * an oracle of monomials (oracle): adds ½ g(v), wires untouched.
--  * CNOTs from a second register (cnots): the data wires become
--    v_i ⊕ v_(ρ i), no phase.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Runs (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _xor_; if_then_else_)
open import Data.Fin.Base using
  (Fin; zero; suc; toℕ; opposite; fromℕ; inject₁; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; divides; ∣m∣n⇒∣m+n; ∣n⇒∣m*n)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; +-inverseʳ; *-zeroʳ; +-assoc; *-assoc)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (zero; suc; _∸_) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.AssignSum using (_∷ᵃ_)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.CRK.Trace M₀ using
  (Stream; Conf; _≈ᶜ_; conf≈; ≈φ; ≈v; ≈ᶜ-refl; ≈ᶜ-trans; trace;
   trace-cong; shift; trace-++; mapG; mapC; pull; pull-cong; trace-map;
   trace-map-off)
open import PathSum.HiddenShift.Gates M₀ using
  (↑g; lift; norm-lift; ◂g; upper; par⁻; par⁺; CZᶜ; CCZᶜ; Term; Z; CZ;
   CCZ; mono; sumᵇ; termᶜ; oracle; cnot-twice)
open import PathSum.HiddenShift.Layers M₀ using
  (hadamards; norm-hadamards; flipʰ; flips)
open import PathSum.HiddenShift.Symbolic M₀ using (cnots; ⧺-cong₂)
open import PathSum.HiddenShift.Walsh using (dot; dot-cong; _⧺_; ⧺-split)
open import PathSum.Polynomial.Properties using (i∣0)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; :-_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; norm)
open import PathSum.Full.Canonical M using (pow∣½·2)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Reduction M using (½)

private
  variable
    n k l : ℕ


------------------------------------------------------------------------
-- Arithmetic

private
  -- A difference of equal integers is divisible by anything.

  diff-0 : ∀ a b → a ≡ b → pow M ∣ (a - b)
  diff-0 a b refl = subst (pow M ∣_) (sym (+-inverseʳ a)) i∣0

  -- Half of an even number is a multiple of 2^M.

  half-even : ∀ t → (+ 2) ∣ t → pow M ∣ (½ * t)
  half-even t (divides r eq) =
    subst (pow M ∣_) (sym (trans (cong (½ *_) eq) (swap ½ r)))
          (∣n⇒∣m*n r pow∣½·2)
    where
    swap : ∀ h r → h * (r * (+ 2)) ≡ r * (h * (+ 2))
    swap = solve 2 (λ h r → h :* (r :* con (+ 2)) := r :* (h :* con (+ 2)))
                   refl

  -- ½a + ½b is ½(a ⊕ b) modulo 1.

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

  -- Adding ½ · 0 changes nothing.

  plus-half-0 : ∀ φ → pow M ∣ (φ - (φ + ½ * [ false ]ᶻ))
  plus-half-0 φ =
    diff-0 φ (φ + ½ * [ false ]ᶻ)
           (sym (trans (cong (λ t → φ + t) (*-zeroʳ ½)) (+-identityʳ φ)))


------------------------------------------------------------------------
-- A circuit read along one path

-- From any phase φ and wires v, along the stream s, C ends with phase
-- φ + ½β modulo 1 and wires v′.

record Runs (C : Circuit n) (s : Stream) (v : Assign n) (β : Bool)
            (v′ : Assign n) : Set where
  constructor runs
  field
    runs-φ : ∀ φ → pow M ∣ (proj₁ (trace C s (φ , v)) - (φ + ½ * [ β ]ᶻ))
    runs-v : ∀ φ w → proj₂ (trace C s (φ , v)) w ≡ v′ w

open Runs public

-- Concatenation: C reads the stream past D's Hadamards, and the
-- parities add.

Runs-++ : (C D : Circuit n) {s : Stream} {v v₁ v₂ : Assign n}
          {β₁ β₂ : Bool} →
          Runs C (shift (norm D) s) v β₁ v₁ → Runs D s v₁ β₂ v₂ →
          Runs (C ++ D) s v (β₁ xor β₂) v₂
Runs-++ C D {s} {v} {v₁} {v₂} {β₁} {β₂} rC rD = runs φ-part v-part
  where
  φ₁ : ℤ → ℤ
  φ₁ φ = proj₁ (trace C (shift (norm D) s) (φ , v))

  e : ∀ φ → trace (C ++ D) s (φ , v) ≈ᶜ trace D s (φ₁ φ , v₁)
  e φ = ≈ᶜ-trans (trace-++ C D s (φ , v))
                 (trace-cong D (λ _ → refl) (conf≈ refl (runs-v rC φ)))

  shape : ∀ T f₁ f x₁ x₂ x₁₂ →
          T - (f + x₁₂) ≡
          (T - (f₁ + x₂)) + ((f₁ - (f + x₁)) + ((x₁ + x₂) - x₁₂))
  shape = solve 6 (λ T f₁ f x₁ x₂ x₁₂ →
    T :- (f :+ x₁₂) :=
    (T :- (f₁ :+ x₂)) :+ ((f₁ :- (f :+ x₁)) :+ ((x₁ :+ x₂) :- x₁₂))) refl

  φ-part : ∀ φ → pow M ∣ (proj₁ (trace (C ++ D) s (φ , v)) -
                          (φ + ½ * [ β₁ xor β₂ ]ᶻ))
  φ-part φ = subst (pow M ∣_)
    (sym (trans (cong (_- (φ + ½ * [ β₁ xor β₂ ]ᶻ)) (≈φ (e φ)))
                (shape (proj₁ (trace D s (φ₁ φ , v₁))) (φ₁ φ) φ
                       (½ * [ β₁ ]ᶻ) (½ * [ β₂ ]ᶻ) (½ * [ β₁ xor β₂ ]ᶻ))))
    (∣m∣n⇒∣m+n (runs-φ rD (φ₁ φ))
               (∣m∣n⇒∣m+n (runs-φ rC φ) (xor-half β₁ β₂)))

  v-part : ∀ φ w → proj₂ (trace (C ++ D) s (φ , v)) w ≡ v₂ w
  v-part φ w = trans (≈v (e φ) w) (runs-v rD (φ₁ φ) w)

-- The empty circuit.

Runs-[] : (s : Stream) (v : Assign n) → Runs [] s v false v
Runs-[] s v = runs plus-half-0 (λ φ w → refl)

-- Only the values of the input wires, of the stream, of the parity and
-- of the output wires matter.

Runs-cong : {C : Circuit n} {s : Stream} {v u : Assign n} {β : Bool}
            {v′ : Assign n} →
            (∀ w → u w ≡ v w) → Runs C s v β v′ → Runs C s u β v′
Runs-cong {C = C} {s} {v} {u} {β} h r = runs
  (λ φ → subst (λ t → pow M ∣ (t - (φ + ½ * [ β ]ᶻ))) (sym (≈φ (e φ)))
               (runs-φ r φ))
  (λ φ w → trans (≈v (e φ) w) (runs-v r φ w))
  where
  e : ∀ φ → trace C s (φ , u) ≈ᶜ trace C s (φ , v)
  e φ = trace-cong C (λ _ → refl) (conf≈ refl h)

Runs-stream : {C : Circuit n} {s s′ : Stream} {v : Assign n} {β : Bool}
              {v′ : Assign n} →
              (∀ i → s′ i ≡ s i) → Runs C s v β v′ → Runs C s′ v β v′
Runs-stream {C = C} {s} {s′} {v} {β} h r = runs
  (λ φ → subst (λ t → pow M ∣ (t - (φ + ½ * [ β ]ᶻ))) (sym (≈φ (e φ)))
               (runs-φ r φ))
  (λ φ w → trans (≈v (e φ) w) (runs-v r φ w))
  where
  e : ∀ φ → trace C s′ (φ , v) ≈ᶜ trace C s (φ , v)
  e φ = trace-cong C h ≈ᶜ-refl

Runs-resp : {C : Circuit n} {s : Stream} {v : Assign n} {β β′ : Bool}
            {v′ v″ : Assign n} →
            β ≡ β′ → (∀ w → v′ w ≡ v″ w) → Runs C s v β v′ →
            Runs C s v β′ v″
Runs-resp {β = β} refl h r =
  runs (runs-φ r) (λ φ w → trans (runs-v r φ w) (h w))


------------------------------------------------------------------------
-- Exact phases

-- The same with the phase exactly φ + Δ.

record RunsE (C : Circuit n) (s : Stream) (v : Assign n) (Δ : ℤ)
             (v′ : Assign n) : Set where
  constructor runsE
  field
    exact-φ : ∀ φ → proj₁ (trace C s (φ , v)) ≡ φ + Δ
    exact-v : ∀ φ w → proj₂ (trace C s (φ , v)) w ≡ v′ w

open RunsE public

RunsE-++ : (C D : Circuit n) {s : Stream} {v v₁ v₂ : Assign n}
           {Δ₁ Δ₂ : ℤ} →
           RunsE C (shift (norm D) s) v Δ₁ v₁ → RunsE D s v₁ Δ₂ v₂ →
           RunsE (C ++ D) s v (Δ₁ + Δ₂) v₂
RunsE-++ C D {s} {v} {v₁} {v₂} {Δ₁} {Δ₂} rC rD = runsE
  (λ φ → trans (≈φ (e φ))
    (trans (exact-φ rD (φ₁ φ))
      (trans (cong (_+ Δ₂) (exact-φ rC φ)) (+-assoc φ Δ₁ Δ₂))))
  (λ φ w → trans (≈v (e φ) w) (exact-v rD (φ₁ φ) w))
  where
  φ₁ : ℤ → ℤ
  φ₁ φ = proj₁ (trace C (shift (norm D) s) (φ , v))

  e : ∀ φ → trace (C ++ D) s (φ , v) ≈ᶜ trace D s (φ₁ φ , v₁)
  e φ = ≈ᶜ-trans (trace-++ C D s (φ , v))
                 (trace-cong D (λ _ → refl) (conf≈ refl (exact-v rC φ)))

RunsE-exp : {C : Circuit n} {s : Stream} {v : Assign n} {Δ Δ′ : ℤ}
            {v′ : Assign n} → Δ ≡ Δ′ → RunsE C s v Δ v′ → RunsE C s v Δ′ v′
RunsE-exp refl r = r

RunsE-out : {C : Circuit n} {s : Stream} {v : Assign n} {Δ : ℤ}
            {v′ v″ : Assign n} → (∀ w → v′ w ≡ v″ w) → RunsE C s v Δ v′ →
            RunsE C s v Δ v″
RunsE-out h r = runsE (exact-φ r) (λ φ w → trans (exact-v r φ w) (h w))

-- An exact phase of ½β is a phase of ½β modulo 1.

RunsE⇒Runs : {C : Circuit n} {s : Stream} {v : Assign n} {Δ : ℤ}
             {v′ : Assign n} {β : Bool} →
             RunsE C s v Δ v′ → Δ ≡ ½ * [ β ]ᶻ → Runs C s v β v′
RunsE⇒Runs {C = C} {s} {v} {Δ} {β = β} r eq = runs
  (λ φ → diff-0 (proj₁ (trace C s (φ , v))) (φ + ½ * [ β ]ᶻ)
                (trans (exact-φ r φ) (cong (λ t → φ + t) eq)))
  (exact-v r)


------------------------------------------------------------------------
-- Single gates

RunsE-R : ∀ k (w : Fin n) (s : Stream) (v : Assign n) →
          RunsE (R k w ∷ []) s v (pow (M ∸ k) * [ v w ]ᶻ) v
RunsE-R k w s v = runsE (λ φ → refl) (λ φ u → refl)

RunsE-R† : ∀ k (w : Fin n) (s : Stream) (v : Assign n) →
           RunsE (R† k w ∷ []) s v (- (pow (M ∸ k) * [ v w ]ᶻ)) v
RunsE-R† k w s v = runsE (λ φ → refl) (λ φ u → refl)

RunsE-CNOT : (c t : Fin n) (p : c ≢ t) (s : Stream) (v : Assign n) →
             RunsE (CNOT c t p ∷ []) s v 0ℤ (v [ t ≔ v t xor v c ])
RunsE-CNOT c t p s v = runsE (λ φ → sym (+-identityʳ φ)) (λ φ u → refl)

Runs-H : (w : Fin n) (s : Stream) (v : Assign n) →
         Runs (H w ∷ []) s v (v w ∧ s 0) (v [ w ≔ s 0 ])
Runs-H w s v = runs
  (λ φ → diff-0 (φ + ½ * [ v w ∧ s 0 ]ᶻ) (φ + ½ * [ v w ∧ s 0 ]ᶻ) refl)
  (λ φ u → refl)


------------------------------------------------------------------------
-- Circuits on other wires

private
  ≡⇒≈ᶜ : {a b : Conf n} → a ≡ b → a ≈ᶜ b
  ≡⇒≈ᶜ refl = ≈ᶜ-refl

  ↑g-map : (g : Gate n) → ↑g g ≡ mapG suc Fin.suc-injective g
  ↑g-map (H w)        = refl
  ↑g-map (CNOT c t p) = refl
  ↑g-map (R k w)      = refl
  ↑g-map (R† k w)     = refl

  ◂g-map : ∀ l (g : Gate k) →
           ◂g l g ≡ mapG (λ i → i ↑ˡ l) (λ {a} {b} → Fin.↑ˡ-injective l a b) g
  ◂g-map l (H w)        = refl
  ◂g-map l (CNOT c t p) = refl
  ◂g-map l (R k w)      = refl
  ◂g-map l (R† k w)     = refl

-- A circuit moved one wire down, or onto the first block of wires, is
-- a relabelling in the sense of PathSum.CRK.Trace.

lift-map : (C : Circuit n) → lift C ≡ mapC suc Fin.suc-injective C
lift-map []      = refl
lift-map (g ∷ C) = cong₂ _∷_ (↑g-map g) (lift-map C)

upper-map : ∀ l (C : Circuit k) →
            upper l C ≡
            mapC (λ i → i ↑ˡ l) (λ {a} {b} → Fin.↑ˡ-injective l a b) C
upper-map l []      = refl
upper-map l (g ∷ C) = cong₂ _∷_ (◂g-map l g) (upper-map l C)

-- Moved one wire down, C runs as before on the wires below, and wire 0
-- keeps its value.

Runs-lift : (C : Circuit n) {s : Stream} {v : Assign (suc n)} {β : Bool}
            {v′ : Assign n} →
            Runs C s (λ i → v (suc i)) β v′ →
            Runs (lift C) s v β (v zero ∷ᵃ v′)
Runs-lift C {s} {v} {β} {v′} r = runs φ-part v-part
  where
  eqC : ∀ φ → trace (lift C) s (φ , v) ≡
              trace (mapC suc Fin.suc-injective C) s (φ , v)
  eqC φ = cong (λ C′ → trace C′ s (φ , v)) (lift-map C)

  tm : ∀ φ → pull suc (trace (lift C) s (φ , v)) ≈ᶜ
             trace C s (φ , λ i → v (suc i))
  tm φ = ≈ᶜ-trans (pull-cong suc (≡⇒≈ᶜ (eqC φ)))
                  (trace-map suc Fin.suc-injective C s (φ , v))

  φ-part : ∀ φ → pow M ∣ (proj₁ (trace (lift C) s (φ , v)) -
                          (φ + ½ * [ β ]ᶻ))
  φ-part φ = subst (λ t → pow M ∣ (t - (φ + ½ * [ β ]ᶻ)))
                   (sym (≈φ (tm φ))) (runs-φ r φ)

  v-part : ∀ φ w → proj₂ (trace (lift C) s (φ , v)) w ≡ (v zero ∷ᵃ v′) w
  v-part φ zero    = trans (cong (λ a → proj₂ a zero) (eqC φ))
    (trace-map-off suc Fin.suc-injective C s (φ , v) zero (λ w ()))
  v-part φ (suc w) = trans (≈v (tm φ) w) (runs-v r φ w)

-- On the first k of k + l wires, C runs as before there, and the last
-- l wires keep their values.

private
  ↑ˡ≢↑ʳ : (i : Fin k) (j : Fin l) → i ↑ˡ l ≢ k ↑ʳ j
  ↑ˡ≢↑ʳ {k} {l} i j e = ℕ.<⇒≢
    (ℕ.<-≤-trans (Fin.toℕ<n i) (ℕ.m≤m+n k (toℕ j)))
    (trans (sym (Fin.toℕ-↑ˡ i l)) (trans (cong toℕ e) (Fin.toℕ-↑ʳ k j)))

Runs-upper : ∀ l (C : Circuit k) {s : Stream} {V : Assign (k ℕ+ l)}
             {β : Bool} {u′ : Assign k} →
             Runs C s (λ i → V (i ↑ˡ l)) β u′ →
             Runs (upper l C) s V β (u′ ⧺ (λ j → V (k ↑ʳ j)))
Runs-upper {k} l C {s} {V} {β} {u′} r = runs φ-part v-part
  where
  inj : ∀ {a b} → a ↑ˡ l ≡ b ↑ˡ l → a ≡ b
  inj {a} {b} = Fin.↑ˡ-injective l a b

  eqC : ∀ φ → trace (upper l C) s (φ , V) ≡
              trace (mapC (λ i → i ↑ˡ l) inj C) s (φ , V)
  eqC φ = cong (λ C′ → trace C′ s (φ , V)) (upper-map l C)

  tm : ∀ φ → pull (λ i → i ↑ˡ l) (trace (upper l C) s (φ , V)) ≈ᶜ
             trace C s (φ , λ i → V (i ↑ˡ l))
  tm φ = ≈ᶜ-trans (pull-cong (λ i → i ↑ˡ l) (≡⇒≈ᶜ (eqC φ)))
                  (trace-map (λ i → i ↑ˡ l) inj C s (φ , V))

  φ-part : ∀ φ → pow M ∣ (proj₁ (trace (upper l C) s (φ , V)) -
                          (φ + ½ * [ β ]ᶻ))
  φ-part φ = subst (λ t → pow M ∣ (t - (φ + ½ * [ β ]ᶻ)))
                   (sym (≈φ (tm φ))) (runs-φ r φ)

  v-part : ∀ φ w → proj₂ (trace (upper l C) s (φ , V)) w ≡
                   (u′ ⧺ (λ j → V (k ↑ʳ j))) w
  v-part φ w = trans (sym (⧺-split k l T w)) (⧺-cong₂ left right w)
    where
    T : Assign (k ℕ+ l)
    T = proj₂ (trace (upper l C) s (φ , V))

    left : ∀ i → T (i ↑ˡ l) ≡ u′ i
    left i = trans (≈v (tm φ) i) (runs-v r φ i)

    right : ∀ j → T (k ↑ʳ j) ≡ V (k ↑ʳ j)
    right j = trans (cong (λ a → proj₂ a (k ↑ʳ j)) (eqC φ))
      (trace-map-off (λ i → i ↑ˡ l) inj C s (φ , V) (k ↑ʳ j)
                     (λ w → ↑ˡ≢↑ʳ w j))


------------------------------------------------------------------------
-- The Hadamard layer

-- Wire w's Hadamard is followed by n-1-w others: it reads that bit.

hbits : ∀ n → Stream → Assign n
hbits n s w = s (toℕ (opposite w))

Runs-hadamards : ∀ n (s : Stream) (v : Assign n) →
                 Runs (hadamards n) s v (dot v (hbits n s)) (hbits n s)
Runs-hadamards zero    s v = runs plus-half-0 (λ φ ())
Runs-hadamards (suc n) s v =
  Runs-resp βeq out
    (Runs-++ (H zero ∷ []) (lift (hadamards n))
      (Runs-H zero (shift (norm (lift (hadamards n))) s) v)
      (Runs-lift (hadamards n) (Runs-hadamards n s (λ i → v (suc i)))))
  where
  pos0 : norm (lift (hadamards n)) ≡ toℕ (opposite {suc n} zero)
  pos0 = trans (trans (norm-lift (hadamards n)) (norm-hadamards n))
               (sym (Fin.toℕ-fromℕ n))

  pos-suc : ∀ i → toℕ (opposite i) ≡ toℕ (opposite {suc n} (suc i))
  pos-suc i = sym (Fin.toℕ-inject₁ (opposite i))

  βeq : (v zero ∧ s (norm (lift (hadamards n)))) xor
        dot (λ i → v (suc i)) (hbits n s) ≡
        dot v (hbits (suc n) s)
  βeq = cong₂ _xor_ (cong (λ p → v zero ∧ s p) pos0)
                    (dot-cong {u = λ i → v (suc i)} {u′ = λ i → v (suc i)}
                              (λ _ → refl) (λ i → cong s (pos-suc i)))

  out : ∀ w → (s (norm (lift (hadamards n))) ∷ᵃ hbits n s) w ≡
              hbits (suc n) s w
  out zero    = cong s pos0
  out (suc w) = cong s (pos-suc w)


------------------------------------------------------------------------
-- The X layer

-- X^s has the Hadamards of the X gates: norm (flips s) of them, two
-- for each wire with s_w = 1, the wire-0 gate first.  Its first
-- Hadamard reads the bit after all the others' (xrev s w true), its
-- second the bit after the later gates' (xrev s w false).

nF : Assign n → ℕ
nF s = norm (flips s)

xrev : Assign n → Fin n → Bool → ℕ
xrev {suc n} s zero    true  = suc (nF (λ i → s (suc i)))
xrev {suc n} s zero    false = nF (λ i → s (suc i))
xrev {suc n} s (suc w) t     = xrev (λ i → s (suc i)) w t

xbits : Assign n → Stream → Bool → Assign n
xbits s str t w = str (xrev s w t)

-- The parity X^s adds, gate by gate: H, R₁, H on a wire holding a add
-- ½ (a c₁ + c₁ + c₁ c₂).

xβʰ : Bool → Bool → Bool → Bool → Bool → Bool
xβʰ false a c₁ c₂ r = r
xβʰ true  a c₁ c₂ r = (a ∧ c₁) xor (c₁ xor ((c₁ ∧ c₂) xor r))

xβ : Assign n → Assign n → Assign n → Assign n → Bool
xβ {zero}  s v b₁ b₂ = false
xβ {suc n} s v b₁ b₂ =
  xβʰ (s zero) (v zero) (b₁ zero) (b₂ zero)
      (xβ (λ i → s (suc i)) (λ i → v (suc i)) (λ i → b₁ (suc i))
          (λ i → b₂ (suc i)))

-- What it leaves on the wires: the second bit where there is an X.

xout : Assign n → Assign n → Assign n → Assign n
xout s v b₂ w = if s w then b₂ w else v w

private
  Runs-flipsʰ :
    ∀ (b : Bool) (s′ : Assign n) (str : Stream) (v : Assign (suc n)) →
    Runs (flips s′) str (λ i → v (suc i))
         (xβ s′ (λ i → v (suc i)) (xbits s′ str true) (xbits s′ str false))
         (xout s′ (λ i → v (suc i)) (xbits s′ str false)) →
    Runs (flipʰ b (lift (flips s′))) str v
         (xβʰ b (v zero) (str (suc (nF s′))) (str (nF s′))
              (xβ s′ (λ i → v (suc i)) (xbits s′ str true)
                  (xbits s′ str false)))
         ((if b then str (nF s′) else v zero) ∷ᵃ
          xout s′ (λ i → v (suc i)) (xbits s′ str false))
  Runs-flipsʰ false s′ str v ih = Runs-lift (flips s′) ih
  Runs-flipsʰ true  s′ str v ih = Runs-resp βeq out
    (Runs-++ (H zero ∷ []) (R 1 zero ∷ H zero ∷ lift C′)
      (Runs-H zero (shift (norm (R 1 zero ∷ H zero ∷ lift C′)) str) v)
      (Runs-++ (R 1 zero ∷ []) (H zero ∷ lift C′)
        (RunsE⇒Runs (RunsE-R 1 zero (shift (norm (H zero ∷ lift C′)) str)
                               (v [ zero ≔ c₁ ]))
                    refl)
        (Runs-++ (H zero ∷ []) (lift C′)
          (Runs-H zero (shift (norm (lift C′)) str) (v [ zero ≔ c₁ ]))
          (Runs-lift C′ ih))))
    where
    C′ : Circuit _
    C′ = flips s′

    c₁ c₂ : Bool
    c₁ = str (suc (norm (lift C′)))
    c₂ = str (norm (lift C′))

    nl : norm (lift C′) ≡ nF s′
    nl = norm-lift C′

    r : Bool
    r = xβ s′ (λ i → v (suc i)) (xbits s′ str true) (xbits s′ str false)

    βeq : (v zero ∧ c₁) xor (c₁ xor ((c₁ ∧ c₂) xor r)) ≡
          xβʰ true (v zero) (str (suc (nF s′))) (str (nF s′)) r
    βeq = cong₂ (λ a b → (v zero ∧ a) xor (a xor ((a ∧ b) xor r)))
                (cong (λ p → str (suc p)) nl) (cong str nl)

    out : ∀ w → (c₂ ∷ᵃ xout s′ (λ i → v (suc i)) (xbits s′ str false)) w ≡
                ((if true then str (nF s′) else v zero) ∷ᵃ
                 xout s′ (λ i → v (suc i)) (xbits s′ str false)) w
    out zero    = cong str nl
    out (suc w) = refl

Runs-flips : ∀ (s : Assign n) (str : Stream) (v : Assign n) →
             Runs (flips s) str v
                  (xβ s v (xbits s str true) (xbits s str false))
                  (xout s v (xbits s str false))
Runs-flips {zero}  s str v = runs plus-half-0 (λ φ ())
Runs-flips {suc n} s str v =
  Runs-resp refl out
    (Runs-flipsʰ (s zero) (λ i → s (suc i)) str v
                 (Runs-flips (λ i → s (suc i)) str (λ i → v (suc i))))
  where
  out : ∀ w → ((if s zero then str (nF (λ i → s (suc i))) else v zero) ∷ᵃ
               xout (λ i → s (suc i)) (λ i → v (suc i))
                    (xbits (λ i → s (suc i)) str false)) w ≡
              xout s v (xbits s str false) w
  out zero    = refl
  out (suc w) = refl


------------------------------------------------------------------------
-- The phase gadgets

-- A CNOT, a circuit that leaves the wires as it found them, and the
-- CNOT again.

private
  RunsE-conj : (c t : Fin n) (p : c ≢ t) (D : Circuit n) {Δ : ℤ}
               (v : Assign n) →
               (∀ s → RunsE D s (v [ t ≔ v t xor v c ]) Δ
                            (v [ t ≔ v t xor v c ])) →
               ∀ s → RunsE (CNOT c t p ∷ D ++ CNOT c t p ∷ []) s v Δ v
  RunsE-conj c t p D {Δ} v hD s =
    RunsE-exp (trans (+-identityˡ (Δ + 0ℤ)) (+-identityʳ Δ))
      (RunsE-out (cnot-twice v p)
        (RunsE-++ (CNOT c t p ∷ []) (D ++ CNOT c t p ∷ [])
          (RunsE-CNOT c t p _ v)
          (RunsE-++ D (CNOT c t p ∷ []) (hD _)
            (RunsE-CNOT c t p s (v [ t ≔ v t xor v c ])))))

RunsE-par⁻ : ∀ k (c t : Fin n) (p : c ≢ t) (s : Stream) (v : Assign n) →
             RunsE (par⁻ k c t p) s v (- (pow (M ∸ k) * [ v t xor v c ]ᶻ)) v
RunsE-par⁻ k c t p s v =
  RunsE-exp (cong (λ b → - (pow (M ∸ k) * [ b ]ᶻ))
                  (≔-here v t (v t xor v c)))
    (RunsE-conj c t p (R† k t ∷ []) v
       (λ s′ → RunsE-R† k t s′ (v [ t ≔ v t xor v c ])) s)

RunsE-par⁺ : ∀ k (a b c : Fin n) (q : a ≢ c) (r : b ≢ c) (s : Stream)
             (v : Assign n) →
             RunsE (par⁺ k a b c q r) s v
                   (pow (M ∸ k) * [ (v c xor v a) xor v b ]ᶻ) v
RunsE-par⁺ k a b c q r s v =
  RunsE-exp (cong (λ x → pow (M ∸ k) * [ x ]ᶻ)
                  (trans (≔-here v₁ c (v₁ c xor v₁ b))
                         (cong₂ _xor_ (≔-here v c (v c xor v a))
                                      (≔-there v (v c xor v a) r))))
    (RunsE-conj a c q (CNOT b c r ∷ R k c ∷ CNOT b c r ∷ []) v
       (λ s′ → RunsE-conj b c r (R k c ∷ []) v₁
                 (λ s″ → RunsE-R k c s″ (v₁ [ c ≔ v₁ c xor v₁ b ])) s′)
       s)
  where
  v₁ : Assign _
  v₁ = v [ c ≔ v c xor v a ]

-- Their phases, as integers: ½ times the monomial.

private
  xor-bits : ∀ a b → [ b xor a ]ᶻ ≡ ([ a ]ᶻ + [ b ]ᶻ) - (+ 2) * [ a ∧ b ]ᶻ
  xor-bits false false = refl
  xor-bits false true  = refl
  xor-bits true  false = refl
  xor-bits true  true  = refl

  cz-Δ : ∀ a b →
         pow (M ∸ 2) * [ a ]ᶻ +
           (pow (M ∸ 2) * [ b ]ᶻ + - (pow (M ∸ 2) * [ b xor a ]ᶻ)) ≡
         ½ * [ a ∧ b ]ᶻ
  cz-Δ a b = trans
    (cong (λ X → q * [ a ]ᶻ + (q * [ b ]ᶻ + - (q * X))) (xor-bits a b))
    (trans (shape q [ a ]ᶻ [ b ]ᶻ [ a ∧ b ]ᶻ)
           (cong (_* [ a ∧ b ]ᶻ) (sym (pow-suc (M ∸ 2)))))
    where
    q : ℤ
    q = pow (M ∸ 2)

    shape : ∀ q A B C →
            q * A + (q * B + - (q * ((A + B) - (+ 2) * C))) ≡
            (q * (+ 2)) * C
    shape = solve 4 (λ q A B C →
      q :* A :+ (q :* B :+ :- (q :* ((A :+ B) :- con (+ 2) :* C))) :=
      (q :* con (+ 2)) :* C) refl

  and-bits : ∀ a b c →
    [ a ]ᶻ + ([ b ]ᶻ + ([ c ]ᶻ + (- [ c xor b ]ᶻ + ([ (c xor a) xor b ]ᶻ +
      (- [ c xor a ]ᶻ + - [ b xor a ]ᶻ))))) ≡
    (+ 4) * [ a ∧ (b ∧ c) ]ᶻ
  and-bits false false false = refl
  and-bits false false true  = refl
  and-bits false true  false = refl
  and-bits false true  true  = refl
  and-bits true  false false = refl
  and-bits true  false true  = refl
  and-bits true  true  false = refl
  and-bits true  true  true  = refl

  ccz-Δ : ∀ a b c →
    pow (M ∸ 3) * [ a ]ᶻ + (pow (M ∸ 3) * [ b ]ᶻ + (pow (M ∸ 3) * [ c ]ᶻ +
      (- (pow (M ∸ 3) * [ c xor b ]ᶻ) +
       (pow (M ∸ 3) * [ (c xor a) xor b ]ᶻ +
        (- (pow (M ∸ 3) * [ c xor a ]ᶻ) + - (pow (M ∸ 3) * [ b xor a ]ᶻ)))))) ≡
    ½ * [ a ∧ (b ∧ c) ]ᶻ
  ccz-Δ a b c = trans
    (shape e [ a ]ᶻ [ b ]ᶻ [ c ]ᶻ [ c xor b ]ᶻ [ (c xor a) xor b ]ᶻ
           [ c xor a ]ᶻ [ b xor a ]ᶻ)
    (trans (cong (e *_) (and-bits a b c))
      (trans (sym (*-assoc e (+ 4) [ a ∧ (b ∧ c) ]ᶻ))
             (cong (_* [ a ∧ (b ∧ c) ]ᶻ) e·4)))
    where
    e : ℤ
    e = pow (M ∸ 3)

    shape : ∀ e A B C D X Y W →
      e * A + (e * B + (e * C + (- (e * D) +
        (e * X + (- (e * Y) + - (e * W)))))) ≡
      e * (A + (B + (C + (- D + (X + (- Y + - W))))))
    shape = solve 8 (λ e A B C D X Y W →
      e :* A :+ (e :* B :+ (e :* C :+ (:- (e :* D) :+ (e :* X :+
        (:- (e :* Y) :+ :- (e :* W)))))) :=
      e :* (A :+ (B :+ (C :+ (:- D :+ (X :+ (:- Y :+ :- W))))))) refl

    -- ⅛ · 4 = ½.
    e·4 : e * (+ 4) ≡ ½
    e·4 = trans (shape₄ e)
      (trans (cong (_* (+ 2)) (sym (pow-suc M₀))) (sym (pow-suc (suc M₀))))
      where
      shape₄ : ∀ q → q * (+ 4) ≡ (q * (+ 2)) * (+ 2)
      shape₄ = solve 1 (λ q → q :* con (+ 4) := (q :* con (+ 2)) :* con (+ 2))
                       refl

-- Each gadget adds ½ times its monomial and leaves the wires alone.

Runs-term : (t : Term n) (s : Stream) (v : Assign n) →
            Runs (termᶜ t) s v (mono t v) v
Runs-term (Z a) s v = RunsE⇒Runs (RunsE-R 1 a s v) refl
Runs-term (CZ a b p) s v = RunsE⇒Runs
  (RunsE-++ (R 2 a ∷ []) (R 2 b ∷ par⁻ 2 a b p) (RunsE-R 2 a _ v)
    (RunsE-++ (R 2 b ∷ []) (par⁻ 2 a b p) (RunsE-R 2 b _ v)
      (RunsE-par⁻ 2 a b p s v)))
  (cz-Δ (v a) (v b))
Runs-term (CCZ a b c p q r) s v = RunsE⇒Runs
  (RunsE-++ (R 3 a ∷ []) rest₁ (RunsE-R 3 a _ v)
    (RunsE-++ (R 3 b ∷ []) rest₂ (RunsE-R 3 b _ v)
      (RunsE-++ (R 3 c ∷ []) rest₃ (RunsE-R 3 c _ v)
        (RunsE-++ (par⁻ 3 b c r) rest₄ (RunsE-par⁻ 3 b c r _ v)
          (RunsE-++ (par⁺ 3 a b c q r) rest₅ (RunsE-par⁺ 3 a b c q r _ v)
            (RunsE-++ (par⁻ 3 a c q) (par⁻ 3 a b p) (RunsE-par⁻ 3 a c q _ v)
              (RunsE-par⁻ 3 a b p s v)))))))
  (ccz-Δ (v a) (v b) (v c))
  where
  rest₅ rest₄ rest₃ rest₂ rest₁ : Circuit _
  rest₅ = par⁻ 3 a c q ++ par⁻ 3 a b p
  rest₄ = par⁺ 3 a b c q r ++ rest₅
  rest₃ = par⁻ 3 b c r ++ rest₄
  rest₂ = R 3 c ∷ rest₃
  rest₁ = R 3 b ∷ rest₂

-- An oracle adds ½ times the sum of its monomials.

Runs-oracle : (ts : List (Term n)) (s : Stream) (v : Assign n) →
              Runs (oracle ts) s v (sumᵇ ts v) v
Runs-oracle []       s v = Runs-[] s v
Runs-oracle (t ∷ ts) s v =
  Runs-++ (termᶜ t) (oracle ts) (Runs-term t (shift (norm (oracle ts)) s) v)
          (Runs-oracle ts s v)


------------------------------------------------------------------------
-- CNOTs from a second register

-- The i-th of the first k wires becomes itself xor the control ρ i of
-- the last l; no phase.

Runs-cnots : ∀ {k l} (ρ : Fin k → Fin l) (s : Stream) (V : Assign (k ℕ+ l)) →
             Runs (cnots ρ) s V false
                  ((λ i → V (i ↑ˡ l) xor V (k ↑ʳ ρ i)) ⧺ (λ j → V (k ↑ʳ j)))
Runs-cnots {zero}      ρ s V = runs plus-half-0 (λ φ w → refl)
Runs-cnots {suc k} {l} ρ s V =
  Runs-resp refl out
    (Runs-++ (CNOT (suc (k ↑ʳ ρ zero)) zero (λ ()) ∷ [])
             (lift (cnots (λ i → ρ (suc i))))
      (RunsE⇒Runs {β = false} (RunsE-CNOT (suc (k ↑ʳ ρ zero)) zero (λ ()) _ V)
                  (sym (*-zeroʳ ½)))
      (Runs-lift (cnots (λ i → ρ (suc i)))
        (Runs-cnots (λ i → ρ (suc i)) s (λ i → V (suc i)))))
  where
  out : ∀ w →
    ((V zero xor V (suc (k ↑ʳ ρ zero))) ∷ᵃ
     ((λ i → V (suc (i ↑ˡ l)) xor V (suc (k ↑ʳ ρ (suc i)))) ⧺
      (λ j → V (suc (k ↑ʳ j))))) w ≡
    ((λ i → V (i ↑ˡ l) xor V (suc k ↑ʳ ρ i)) ⧺ (λ j → V (suc k ↑ʳ j))) w
  out zero    = refl
  out (suc w) = refl
