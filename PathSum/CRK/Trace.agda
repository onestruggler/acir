------------------------------------------------------------------------
-- Presentations of groups
--
-- The path-sum of a circuit over {H, CNOT, R_k, R_k†}, one path at a
-- time
--
-- Definition 2.9 (PathSum.CRK.Circuit) builds the path-sum of a
-- circuit by running an interpretation state through it: a phase
-- polynomial and, on each wire, a Z₂-linear form.  Along a single path
-- -- a single assignment to the path variables -- all of that
-- collapses to numbers: the phase is an integer (the numerator of the
-- phase over 2^M) and each wire holds a bit.  trace runs a circuit on
-- such a configuration directly, gate by gate:
--
--    H on w    adds ½ · v_w · b to the phase and puts b on w,
--    R_k on w  adds 2^(M-k) · v_w,   R_k† on w subtracts it,
--    CNOT c t  replaces v_t by v_t ⊕ v_c,
--
-- where b is the bit the Hadamard's path variable takes along the
-- path.  The bits come from a stream s : ℕ → Bool, and the gate g of
-- a circuit g ∷ C reads s (norm C), the number of Hadamards after it.
-- That is exactly how run numbers the path variables: a Hadamard
-- allocates its variable at the head, y₀, and every later Hadamard
-- pushes it one place further, so after the whole circuit the
-- variable of a Hadamard followed by j others is y_j.  The first
-- Hadamard of a circuit therefore owns the last path variable, and
-- the last one owns y₀.
--
-- run-trace is the invariant, for any starting state with m path
-- variables of its own (those come after the circuit's, at
-- norm C + j): the phase and the wire values of the final state, read
-- at the path whose bits are the stream's, are the trace's.  At the
-- initial state (phase 0, wire w holding x_w) this reads the path-sum
-- ⟦ C ⟧ path by path (eval-⟦⟧, outBit-⟦⟧), and so its amplitudes as a
-- sum over paths of ζ^phase, counted when the path ends at z
-- (amp-⟦⟧).  From then on a circuit can be reasoned about with
-- integers and bits alone, no polynomial being ever normalised: that
-- is what makes statements about whole families of circuits (the
-- quantum Fourier transform, PathSum.QFT) provable by induction.
--
-- Two laws make the trace compositional.  A concatenation runs its
-- halves in turn, the first reading the stream shifted past the
-- second's Hadamards (trace-++), which is definition 2.9's clause
-- ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧ read path by path.  And a circuit relabelled
-- along an injection of wires ρ (mapC) runs as the original on the
-- wires in the image and leaves the others alone (trace-map,
-- trace-map-off).
--
-- Also here: Σᴮ-str, a sum over the paths of one length read through
-- the stream is the same sum at any equal length (the number of path
-- variables of ⟦ C ⟧ is paths C, equal to norm C only
-- propositionally); and Σᴮ-opposite, a sum over assignments is
-- unchanged when the variables are read in reverse order.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.CRK.Trace (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ; ∧-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; opposite; inject₁)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_; _-_; _*_)
open import Data.Integer.Properties using (+-identityˡ; +-identityʳ; *-zeroʳ)
open import Data.List.Base using ([]; _∷_; _++_; map)
open import Data.Nat.Base using (zero; suc; _∸_) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere.Sound M₀ using (Σᴮ-insert)
open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-cong; same; same-≗)
open import PathSum.Base using (phase; head-part; tail-part)
open import PathSum.Circuit M using (wkPoly)
open import PathSum.CRK.Amp M₀ using (outBit-liftᴸ)
open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; norm; State; poly; sig; init; stepH;
   stepR; stepR†; stepCNOT; run; paths; ⟦_⟧; _[_↦_])
open import PathSum.Compose.Properties M₀ using (hits-same)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; extend; Σᴮ; Σᴮ-cong; Respects; zpow)
open import PathSum.Denotation M₀ using
  (Assign; amp; outBit; eval-true; eval-false; eval-0ᴾ-val)
open import PathSum.Linear using
  (Lin; par; par-cong; valᴸ; liftᴸ; varᴸ; _⊕ᴸ_; wkLin; mul-y₀;
   eval-liftᴸ; valᴸ-var; valᴸ-⊕; valᴸ-wk)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (Poly; x[_]; y[_]; 0ᴾ; _·ᴾ_; eval)
open import PathSum.Polynomial.Properties using
  (eval-+ᴾ; eval-−ᴾ; eval-·ᴾ; eval-ext; eval-cong)
open import PathSum.Reduction M using (½)
open import PathSum.Reorder using (insertᵃ; insertᵃ-here)

private
  variable
    n n′ m K : ℕ


------------------------------------------------------------------------
-- Configurations

-- The bits of a path, one for each Hadamard, as a stream.

Stream : Set
Stream = ℕ → Bool

-- Along a path: the phase so far (a numerator over 2^M) and the bit on
-- each wire.

Conf : ℕ → Set
Conf n = ℤ × Assign n

-- The same phase and the same bits.  A record, so that the two
-- configurations can be recovered from its type.

infix 4 _≈ᶜ_

record _≈ᶜ_ (a b : Conf n) : Set where
  constructor conf≈
  field
    ≈φ : proj₁ a ≡ proj₁ b
    ≈v : ∀ w → proj₂ a w ≡ proj₂ b w

open _≈ᶜ_ public

≈ᶜ-refl : {a : Conf n} → a ≈ᶜ a
≈ᶜ-refl = conf≈ refl (λ _ → refl)

≈ᶜ-sym : {a b : Conf n} → a ≈ᶜ b → b ≈ᶜ a
≈ᶜ-sym (conf≈ p q) = conf≈ (sym p) (λ w → sym (q w))

≈ᶜ-trans : {a b c : Conf n} → a ≈ᶜ b → b ≈ᶜ c → a ≈ᶜ c
≈ᶜ-trans (conf≈ p q) (conf≈ p′ q′) =
  conf≈ (trans p p′) (λ w → trans (q w) (q′ w))

-- Overwriting a bit respects equality of the bit and of the rest.

≔-cong₂ : {z z′ : Assign n} (i : Fin n) {b b′ : Bool} → b ≡ b′ →
          (∀ j → z j ≡ z′ j) → ∀ j → (z [ i ≔ b ]) j ≡ (z′ [ i ≔ b′ ]) j
≔-cong₂ {z′ = z′} i {b′ = b′} refl z≗z′ j = ≔-cong i b′ z≗z′ j


------------------------------------------------------------------------
-- The trace

-- One gate, b being the bit of the path variable it allocates if it is
-- a Hadamard.

gateᶜ : Gate n → Bool → Conf n → Conf n
gateᶜ (H w)        b (φ , v) = φ + ½ * [ v w ∧ b ]ᶻ , v [ w ≔ b ]
gateᶜ (CNOT c t _) b (φ , v) = φ , v [ t ≔ v t xor v c ]
gateᶜ (R k w)      b (φ , v) = φ + pow (M ∸ k) * [ v w ]ᶻ , v
gateᶜ (R† k w)     b (φ , v) = φ - pow (M ∸ k) * [ v w ]ᶻ , v

-- A whole circuit.  The gate g of g ∷ C reads the bit s (norm C).

trace : Circuit n → Stream → Conf n → Conf n
trace []      s a = a
trace (g ∷ C) s a = trace C s (gateᶜ g (s (norm C)) a)

-- Only values are read.

gateᶜ-cong : (g : Gate n) {b b′ : Bool} {a a′ : Conf n} → b ≡ b′ →
             a ≈ᶜ a′ → gateᶜ g b a ≈ᶜ gateᶜ g b′ a′
gateᶜ-cong (H w) {a = φ , v} {φ′ , v′} b≡b′ (conf≈ p q) = conf≈
  (cong₂ (λ e d → e + ½ * [ d ]ᶻ) p (cong₂ _∧_ (q w) b≡b′))
  (≔-cong₂ w b≡b′ q)
gateᶜ-cong (CNOT c t _) {a = φ , v} {φ′ , v′} b≡b′ (conf≈ p q) = conf≈ p
  (≔-cong₂ t (cong₂ _xor_ (q t) (q c)) q)
gateᶜ-cong (R k w) {a = φ , v} {φ′ , v′} b≡b′ (conf≈ p q) = conf≈
  (cong₂ (λ e d → e + pow (M ∸ k) * [ d ]ᶻ) p (q w)) q
gateᶜ-cong (R† k w) {a = φ , v} {φ′ , v′} b≡b′ (conf≈ p q) = conf≈
  (cong₂ (λ e d → e - pow (M ∸ k) * [ d ]ᶻ) p (q w)) q

trace-cong : (C : Circuit n) {s s′ : Stream} {a a′ : Conf n} →
             (∀ i → s i ≡ s′ i) → a ≈ᶜ a′ → trace C s a ≈ᶜ trace C s′ a′
trace-cong []      s≗ a≈ = a≈
trace-cong (g ∷ C) s≗ a≈ = trace-cong C s≗ (gateᶜ-cong g (s≗ (norm C)) a≈)


------------------------------------------------------------------------
-- Values of the polynomials a gate adds

-- Ported from PathSum.CRK.Amp, where they are private.

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

  -- The value of a redirected wire.

  val-↦ : (σ : Fin n → Lin n m) (w : Fin n) (l : Lin n m) (x : Assign n)
          (y : Assign m) (u : Fin n) →
          valᴸ ((σ [ w ↦ l ]) u) x y ≡
          ((λ v → valᴸ (σ v) x y) [ w ≔ valᴸ l x y ]) u
  val-↦ σ w l x y u with u Fin.≟ w
  ... | yes _ = refl
  ... | no  _ = refl

-- A form reads its assignments only through their values.

valᴸ-≗ : (l : Lin n m) (x : Assign n) {y y′ : Assign m} →
         (∀ j → y j ≡ y′ j) → valᴸ l x y ≡ valᴸ l x y′
valᴸ-≗ (c , α , β) x y≗ = cong (λ b → c xor (par α x xor b)) (par-cong β y≗)


------------------------------------------------------------------------
-- The trace computes the path-sum

-- What a state stands for at a path: its phase and its wires' values.

confOf : State n m → Assign n → Assign m → Conf n
confOf st x y = eval (poly st) x y , (λ w → valᴸ (sig st w) x y)

-- The path whose bits are the first ones of the stream, and the one
-- whose bits come after the first d.

pathOf : Stream → Assign K
pathOf s i = s (toℕ i)

after : ℕ → Stream → Assign K
after d s j = s (d ℕ+ toℕ j)

-- One gate: the state after it, at the path whose head is the gate's
-- bit, is the configuration after it.

private
  step-H : (w : Fin n) (st : State n m) (x : Assign n) (s : Stream)
           (d : ℕ) →
           confOf (stepH w st) x (after d s) ≈ᶜ
           gateᶜ (H w) (s d) (confOf st x (after (suc d) s))
  step-H w st x s d = conf≈
    (trans (eval-cong (poly (stepH w st)) (λ _ → refl) ext)
           (eval-H w st x (s d) y))
    (λ u → trans (val-↦ (λ v → wkLin (sig st v)) w (varᴸ y[ zero ]) x y′ u)
                 (≔-cong₂ w (trans (valᴸ-var y[ zero ] x y′) (ext zero))
                    (λ v → valᴸ-wk (sig st v) x y y′ (λ j → ext (suc j))) u))
    where
    y′ = after d s
    y  = after (suc d) s

    ext : ∀ j → y′ j ≡ extend (s d) y j
    ext zero    = cong s (ℕ.+-identityʳ d)
    ext (suc j) = cong s (ℕ.+-suc d (toℕ j))

  step-CNOT : (c t : Fin n) (st : State n m) (x : Assign n) (y : Assign m)
              (p : c ≢ t) (b : Bool) →
              confOf (stepCNOT c t st) x y ≈ᶜ
              gateᶜ (CNOT c t p) b (confOf st x y)
  step-CNOT c t st x y p b = conf≈ refl (λ u →
    trans (val-↦ (sig st) t (sig st t ⊕ᴸ sig st c) x y u)
          (≔-cong₂ {z = λ v → valᴸ (sig st v) x y}
                   {z′ = λ v → valᴸ (sig st v) x y}
                   t (valᴸ-⊕ (sig st t) (sig st c) x y) (λ _ → refl) u))

run-trace : (C : Circuit n) (st : State n m) (x : Assign n) (s : Stream) →
            confOf (proj₂ (run C st)) x (pathOf s) ≈ᶜ
            trace C s (confOf st x (after (norm C) s))
run-trace []                st x s = ≈ᶜ-refl
run-trace (H w ∷ C)         st x s = ≈ᶜ-trans
  (run-trace C (stepH w st) x s)
  (trace-cong C (λ _ → refl) (step-H w st x s (norm C)))
run-trace (CNOT c t p ∷ C)  st x s = ≈ᶜ-trans
  (run-trace C (stepCNOT c t st) x s)
  (trace-cong C (λ _ → refl)
    (step-CNOT c t st x (after (norm C) s) p (s (norm C))))
run-trace (R k w ∷ C)       st x s = ≈ᶜ-trans
  (run-trace C (stepR k w st) x s)
  (trace-cong C (λ _ → refl)
    (conf≈ (eval-R k w st x (after (norm C) s)) (λ _ → refl)))
run-trace (R† k w ∷ C)      st x s = ≈ᶜ-trans
  (run-trace C (stepR† k w st) x s)
  (trace-cong C (λ _ → refl)
    (conf≈ (eval-R† k w st x (after (norm C) s)) (λ _ → refl)))


------------------------------------------------------------------------
-- The path-sum of a circuit, path by path

-- A path as a stream: its bits, then false.

str : Assign K → Stream
str {zero}  y i       = false
str {suc K} y zero    = y zero
str {suc K} y (suc i) = str (λ j → y (suc j)) i

pathOf-str : (y : Assign K) (i : Fin K) → pathOf (str y) i ≡ y i
pathOf-str y zero    = refl
pathOf-str y (suc i) = pathOf-str (λ j → y (suc j)) i

str-≗ : {y y′ : Assign K} → (∀ j → y j ≡ y′ j) → ∀ i → str y i ≡ str y′ i
str-≗ {zero}  y≗ i       = refl
str-≗ {suc K} y≗ zero    = y≗ zero
str-≗ {suc K} y≗ (suc i) = str-≗ (λ j → y≗ (suc j)) i

-- The initial configuration: phase 0, wire w holding x_w.

start : Assign n → Conf n
start x = 0ℤ , x

private
  init≈ : (x : Assign n) (y : Assign 0) → confOf (init {n}) x y ≈ᶜ start x
  init≈ x y = conf≈ (eval-0ᴾ-val x y) (λ w → valᴸ-var x[ w ] x y)

  run-start : (C : Circuit n) (x : Assign n) (s : Stream) →
              confOf (proj₂ (run C init)) x (pathOf s) ≈ᶜ trace C s (start x)
  run-start C x s = ≈ᶜ-trans (run-trace C init x s)
    (trace-cong C (λ _ → refl) (init≈ x (after (norm C) s)))

-- The phase and the outputs of ⟦ C ⟧ along the path y.

eval-⟦⟧ : (C : Circuit n) (x : Assign n) (y : Assign (paths C)) →
          eval (phase ⟦ C ⟧) x y ≡ proj₁ (trace C (str y) (start x))
eval-⟦⟧ C x y = trans
  (eval-cong (phase ⟦ C ⟧) (λ _ → refl) (λ i → sym (pathOf-str y i)))
  (≈φ (run-start C x (str y)))

outBit-⟦⟧ : (C : Circuit n) (x : Assign n) (y : Assign (paths C))
            (w : Fin n) →
            outBit ⟦ C ⟧ x y w ≡ proj₂ (trace C (str y) (start x)) w
outBit-⟦⟧ C x y w = trans
  (outBit-liftᴸ ⟦ C ⟧ x y w (sig r w) refl)
  (trans (valᴸ-≗ (sig r w) x (λ i → sym (pathOf-str y i)))
         (≈v (run-start C x (str y)) w))
  where
  r = proj₂ (run C init)

-- The amplitude from x to z: a path contributes ζ^phase when it ends
-- at z.

pathAmp : Circuit n → Assign n → Assign n → Stream → Amp
pathAmp C x z s =
  if same (proj₂ (trace C s (start x))) z
  then zpow (proj₁ (trace C s (start x))) else 0ᴬ

amp-⟦⟧ : (C : Circuit n) (x z : Assign n) →
         amp ⟦ C ⟧ x z ≐ Σᴮ (λ (y : Assign (paths C)) → pathAmp C x z (str y))
amp-⟦⟧ C x z = Σᴮ-cong (λ y → if-cong
  (trans (hits-same ⟦ C ⟧ x y z)
         (same-≗ {x = outBit ⟦ C ⟧ x y}
                 {x′ = proj₂ (trace C (str y) (start x))} {z = z} {z′ = z}
                 (outBit-⟦⟧ C x y) (λ _ → refl)))
  (zpow-≡ (eval-⟦⟧ C x y)))

-- The summand reads the stream only through its values.

pathAmp-≗ : (C : Circuit n) (x z : Assign n) {s s′ : Stream} →
            (∀ i → s i ≡ s′ i) → pathAmp C x z s ≐ pathAmp C x z s′
pathAmp-≗ C x z {s} {s′} s≗ = if-cong
  (same-≗ {x = proj₂ (trace C s (start x))}
          {x′ = proj₂ (trace C s′ (start x))} {z = z} {z′ = z}
          (≈v t≈) (λ _ → refl))
  (zpow-≡ (≈φ t≈))
  where
  t≈ = trace-cong C s≗ (≈ᶜ-refl {a = start x})

-- A sum over the paths of one length, read through the stream, is the
-- same sum at any equal length.

Σᴮ-str : ∀ {K K′} → K ≡ K′ → (G : Stream → Amp) →
         Σᴮ {K} (λ y → G (str y)) ≐ Σᴮ {K′} (λ y → G (str y))
Σᴮ-str refl G _ = refl


------------------------------------------------------------------------
-- Concatenation

norm-++ : (C D : Circuit n) → norm (C ++ D) ≡ norm C ℕ+ norm D
norm-++ []                D = refl
norm-++ (H _ ∷ C)         D = cong suc (norm-++ C D)
norm-++ (CNOT _ _ _ ∷ C)  D = norm-++ C D
norm-++ (R _ _ ∷ C)       D = norm-++ C D
norm-++ (R† _ _ ∷ C)      D = norm-++ C D

-- The stream past its first d bits.

shift : ℕ → Stream → Stream
shift d s i = s (i ℕ+ d)

-- C's Hadamards come before D's, so they own the bits after D's.

trace-++ : (C D : Circuit n) (s : Stream) (a : Conf n) →
           trace (C ++ D) s a ≈ᶜ trace D s (trace C (shift (norm D) s) a)
trace-++ []      D s a = ≈ᶜ-refl
trace-++ (g ∷ C) D s a = ≈ᶜ-trans
  (trace-++ C D s (gateᶜ g (s (norm (C ++ D))) a))
  (trace-cong D (λ _ → refl) (trace-cong C (λ _ → refl)
    (gateᶜ-cong g (cong s (norm-++ C D)) (≈ᶜ-refl {a = a}))))


------------------------------------------------------------------------
-- Relabelling wires

Injective : (Fin n → Fin n′) → Set
Injective ρ = ∀ {a b} → ρ a ≡ ρ b → a ≡ b

-- A gate, and a circuit, moved along an injection of wires.

mapG : (ρ : Fin n → Fin n′) → Injective ρ → Gate n → Gate n′
mapG ρ inj (H w)          = H (ρ w)
mapG ρ inj (CNOT c t c≢t) = CNOT (ρ c) (ρ t) (λ eq → c≢t (inj eq))
mapG ρ inj (R k w)        = R k (ρ w)
mapG ρ inj (R† k w)       = R† k (ρ w)

mapC : (ρ : Fin n → Fin n′) → Injective ρ → Circuit n → Circuit n′
mapC ρ inj = map (mapG ρ inj)

norm-map : (ρ : Fin n → Fin n′) (inj : Injective ρ) (C : Circuit n) →
           norm (mapC ρ inj C) ≡ norm C
norm-map ρ inj []                = refl
norm-map ρ inj (H _ ∷ C)         = cong suc (norm-map ρ inj C)
norm-map ρ inj (CNOT _ _ _ ∷ C)  = norm-map ρ inj C
norm-map ρ inj (R _ _ ∷ C)       = norm-map ρ inj C
norm-map ρ inj (R† _ _ ∷ C)      = norm-map ρ inj C

-- A configuration read through ρ.

pull : (Fin n → Fin n′) → Conf n′ → Conf n
pull ρ (φ , v) = φ , (λ w → v (ρ w))

private
  -- Writing at ρ w and reading at ρ u is writing at w and reading at u.

  ≔-map : (ρ : Fin n → Fin n′) → Injective ρ → (v : Assign n′) (w : Fin n)
          (b : Bool) (u : Fin n) →
          (v [ ρ w ≔ b ]) (ρ u) ≡ ((λ i → v (ρ i)) [ w ≔ b ]) u
  ≔-map ρ inj v w b u with u Fin.≟ w
  ... | yes refl = ≔-here v (ρ u) b
  ... | no  u≢w  = ≔-there v b (λ eq → u≢w (inj eq))

  gate-map : (ρ : Fin n → Fin n′) (inj : Injective ρ) (g : Gate n)
             (b : Bool) (a : Conf n′) →
             pull ρ (gateᶜ (mapG ρ inj g) b a) ≈ᶜ gateᶜ g b (pull ρ a)
  gate-map ρ inj (H w)        b (φ , v) = conf≈ refl (≔-map ρ inj v w b)
  gate-map ρ inj (CNOT c t _) b (φ , v) =
    conf≈ refl (≔-map ρ inj v t (v (ρ t) xor v (ρ c)))
  gate-map ρ inj (R k w)      b (φ , v) = ≈ᶜ-refl
  gate-map ρ inj (R† k w)     b (φ , v) = ≈ᶜ-refl

  gate-off : (ρ : Fin n → Fin n′) (inj : Injective ρ) (g : Gate n)
             (b : Bool) (a : Conf n′) (u : Fin n′) → (∀ w → ρ w ≢ u) →
             proj₂ (gateᶜ (mapG ρ inj g) b a) u ≡ proj₂ a u
  gate-off ρ inj (H w)        b (φ , v) u off =
    ≔-there v b (λ eq → off w (sym eq))
  gate-off ρ inj (CNOT c t _) b (φ , v) u off =
    ≔-there v (v (ρ t) xor v (ρ c)) (λ eq → off t (sym eq))
  gate-off ρ inj (R k w)      b (φ , v) u off = refl
  gate-off ρ inj (R† k w)     b (φ , v) u off = refl

pull-cong : (ρ : Fin n → Fin n′) {a a′ : Conf n′} → a ≈ᶜ a′ →
            pull ρ a ≈ᶜ pull ρ a′
pull-cong ρ {φ , v} {φ′ , v′} (conf≈ p q) = conf≈ p (λ w → q (ρ w))

-- On the wires in the image, the relabelled circuit runs as the
-- original; the phase is the original's.

trace-map : (ρ : Fin n → Fin n′) (inj : Injective ρ) (C : Circuit n)
            (s : Stream) (a : Conf n′) →
            pull ρ (trace (mapC ρ inj C) s a) ≈ᶜ trace C s (pull ρ a)
trace-map ρ inj []      s a = ≈ᶜ-refl
trace-map ρ inj (g ∷ C) s a = ≈ᶜ-trans
  (trace-map ρ inj C s (gateᶜ (mapG ρ inj g) (s (norm (mapC ρ inj C))) a))
  (trace-cong C (λ _ → refl) (≈ᶜ-trans
    (gate-map ρ inj g (s (norm (mapC ρ inj C))) a)
    (gateᶜ-cong g (cong s (norm-map ρ inj C)) (≈ᶜ-refl {a = pull ρ a}))))

-- Off the image, nothing happens.

trace-map-off : (ρ : Fin n → Fin n′) (inj : Injective ρ) (C : Circuit n)
                (s : Stream) (a : Conf n′) (u : Fin n′) →
                (∀ w → ρ w ≢ u) →
                proj₂ (trace (mapC ρ inj C) s a) u ≡ proj₂ a u
trace-map-off ρ inj []      s a u off = refl
trace-map-off ρ inj (g ∷ C) s a u off = trans
  (trace-map-off ρ inj C s (gateᶜ (mapG ρ inj g) (s (norm (mapC ρ inj C))) a)
                 u off)
  (gate-off ρ inj g (s (norm (mapC ρ inj C))) a u off)


------------------------------------------------------------------------
-- Reading the path variables in reverse

-- Σᴮ splits off the head variable; read in reverse, the head is the
-- last variable, which Σᴮ-insert splits off at the far end.

private
  insertᵃ-≗ : ∀ {k} (j : Fin (suc k)) (c : Bool) {g g′ : Assign k} →
              (∀ l → g l ≡ g′ l) → ∀ i → insertᵃ j c g i ≡ insertᵃ j c g′ i
  insertᵃ-≗         zero     c g≗ zero    = refl
  insertᵃ-≗         zero     c g≗ (suc i) = g≗ i
  insertᵃ-≗ {zero}  (suc ()) c g≗ i
  insertᵃ-≗ {suc k} (suc j)  c g≗ zero    = g≗ zero
  insertᵃ-≗ {suc k} (suc j)  c g≗ (suc i) =
    insertᵃ-≗ j c (λ l → g≗ (suc l)) i

  -- Inserting at the last position leaves the others where they were.

  insertᵃ-last : ∀ {k} (c : Bool) (h : Assign k) (i : Fin k) →
                 insertᵃ (fromℕ k) c h (inject₁ i) ≡ h i
  insertᵃ-last {suc k} c h zero    = refl
  insertᵃ-last {suc k} c h (suc i) = insertᵃ-last c (λ l → h (suc l)) i

  -- An assignment extended at the head, read in reverse, is the
  -- reversed assignment extended at the far end.

  rev-extend′ : ∀ {k} (b : Bool) (g : Assign k) (j : Fin (suc k)) →
                extend b g j ≡
                insertᵃ (fromℕ k) b (λ l → g (opposite l)) (opposite j)
  rev-extend′ {k} b g zero    = sym (insertᵃ-here (fromℕ k) b _)
  rev-extend′ {k} b g (suc j) = sym (trans
    (insertᵃ-last b (λ l → g (opposite l)) (opposite j))
    (cong g (Fin.opposite-involutive j)))

  rev-extend : ∀ {k} (b : Bool) (g : Assign k) (i : Fin (suc k)) →
               extend b g (opposite i) ≡
               insertᵃ (fromℕ k) b (λ l → g (opposite l)) i
  rev-extend {k} b g i = trans (rev-extend′ b g (opposite i))
    (cong (insertᵃ (fromℕ k) b (λ l → g (opposite l)))
          (Fin.opposite-involutive i))

Σᴮ-opposite : (F : Assign K → Amp) → Respects F →
              Σᴮ (λ y → F (λ i → y (opposite i))) ≐ Σᴮ F
Σᴮ-opposite {zero}  F resp = resp _ _ (λ ())
Σᴮ-opposite {suc k} F resp w = trans
  (cong₂ _+_ (half true) (half false))
  (sym (Σᴮ-insert (fromℕ k) F resp w))
  where
  Fb : Bool → Assign k → Amp
  Fb b g = F (insertᵃ (fromℕ k) b g)

  resp-b : ∀ b → Respects (Fb b)
  resp-b b g g′ g≗ = resp (insertᵃ (fromℕ k) b g) (insertᵃ (fromℕ k) b g′)
                          (insertᵃ-≗ (fromℕ k) b g≗)

  half : ∀ b → Σᴮ (λ g → F (λ i → extend b g (opposite i))) w ≡
               Σᴮ (Fb b) w
  half b = trans
    (Σᴮ-cong (λ g → resp (λ i → extend b g (opposite i))
                          (insertᵃ (fromℕ k) b (λ l → g (opposite l)))
                          (rev-extend b g)) w)
    (Σᴮ-opposite (Fb b) (resp-b b) w)
