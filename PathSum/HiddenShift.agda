------------------------------------------------------------------------
-- Presentations of groups
--
-- The quantum hidden shift algorithm (Amy, QPL 2018, section 5.2)
--
-- Section 5.2 verifies the hidden shift algorithm for the
-- Maiorana-McFarland bent functions on n = 2m bits,
--
--    f(x, y) = (-1)^{g(x) + x·y},   dual  f̃(x, y) = (-1)^{g(y) + x·y},
--
-- g any Boolean function on m bits: given the oracles O_f′ of the
-- shifted function f′ = f(· ⊕ s) and O_f̃ of the dual, the circuit
-- H^{⊗n} O_f̃ H^{⊗n} O_f′ H^{⊗n} "is known to implement the mapping
-- |0⟩ ↦ |s⟩".  This module proves that at the level of path-sums, for
-- every m, every g and every shift s (hidden-shift): the column of the
-- composite at the input 0 is √2^K |s⟩, K = 3n being its
-- normalisation, so that the normalised amplitude from |0⟩ to |z⟩ is
-- 1 at z = s and 0 elsewhere.  Equivalently, on that column it agrees
-- with the path-sum |x⟩ ↦ |s⟩ (hidden-shift-spec).
--
-- The path-sums.  The Hadamard layer Hᴾ is |x⟩ ↦ 1/√2^n Σ_y (-1)^{x·y}
-- |y⟩, with phase ½ Σ_i x_i y_i.  An oracle Oᴾ E is diagonal with
-- phase ½ E, for E any integer polynomial in the inputs: its sign
-- (-1)^{E(x)} depends only on E modulo 2, so E may be the lift of a
-- Boolean exponent (lemma 2.5) or any other integer polynomial with
-- the same parities.  The exponent of f is mmᴾ g = g(x) + Σ_i x_i y_i
-- (g read on the first half of the inputs, by renaming), that of f̃ is
-- dualᴾ g = g(y) + Σ_i x_i y_i, and shiftᴾ s substitutes x_i ⊕ s_i --
-- 1 - x_i where s_i is set -- for every input.  The circuit is their
-- composite by definition 2.6 (PathSum.Compose._∘ᴾ_), five path-sums
-- with 3n path variables between them.  g is any polynomial on m bits,
-- read modulo 2 (boolᴾ): Boolean-valued polynomials, the paper's case,
-- are among them, and so every Boolean function is.
--
-- The proof never looks inside the composite.  Proposition 2.7 in
-- operator form (prop-2-7ᶜ) says the column of ξ′ ∘ ξ at 0 is U_ξ′
-- applied to the column of ξ at 0, so the column of the circuit is
-- computed layer by layer, and every intermediate column is an
-- integer multiple of ζ^0 at each entry (PathSum.HiddenShift.Sign):
--
--    1  ↦  (-1)^{f′(u)}  ↦  2^m (-1)^{f̃(v) + s·v}  ↦  2^m (-1)^{s·v}
--       ↦  2^m 2^n [z = s],
--
-- the Hadamard layer acting as Σ_w (-1)^{w·z} (applyᴾ-Hᴾ) and an oracle
-- as the sign of its exponent (applyᴾ-Oᴾ).  The two sums over 2^n
-- terms are the Walsh transform of the bent function, 2^m times its
-- dual (walsh-mm-shift), and the orthogonality of characters
-- (character-shift), both in PathSum.HiddenShift.Walsh.  2^m 2^n is
-- 2^(3m) = √2^(6m), the normalisation of the composite.
--
-- Departures from the paper.
--
-- * The paper's displayed formula for the shifted function,
--   "f′(x, y) = f((x, y) + s) = (-1)^{g(x)+xy}", drops the shift in
--   its last member; it is f's formula, and f′ = f(· ⊕ s) is used
--   here.  (g is the paper's "random n/2 bit Boolean function": m
--   bits here, n = 2m.)
-- * The oracles are path-sums, not circuits, and the shift is a
--   substitution rather than figure 3(a)'s X gates: the circuits of
--   figure 3, and the paper's oracles built from Z, CZ and CCZ gates,
--   are not formalised in this module.
-- * There are no constant inputs in this development, so the
--   specification |0⟩ ↦ |s⟩ is the column of the composite at the
--   input 0, stated for every output z.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-comm; xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _-_; _*_)
open import Data.Integer.Properties using
  (*-identityʳ; *-identityˡ; *-zeroʳ; *-zeroˡ; *-assoc; *-comm; pos-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc)
  renaming (_+_ to _ℕ+_; _^_ to _ℕ^_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ
import Data.Nat.Solver as ℕSolver

open import PathSum.Assign using ([_]ᶻ; same; same-≗)
open import PathSum.AssignSum using (Σᶻ; Σᶻ-cong; Σᶻ-*; RespectsZ)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties M₀ using
  (applyᴾ; applyᴾ-cong; prop-2-7ᶜ; hits-same)
open import PathSum.Compose.Sum M₀ using
  (Σᴮ-δ; if-cong; zpow-≡; scale-exp)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _·ᴬ_; _≐_; Σᴮ; Σᴮ-cong; zpow; rot; rot-exp; scale;
   scale-map; √2·-map; √2·-twice; √2·-0ᴬ; Respects)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; outBit-μ)
open import PathSum.HiddenShift.Sign M₀ using
  (odd-[]; odd-+; odd-∧; 1ᴬ; zpow-½; rot-½; ⌈_⌉; Σᴮ-ᶻ)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; lhalf; rhalf; RespectsB; dot; dot-cong; dot-0ˡ; sgn-xor;
   sgn-absorb; character-shift; mm; dual; mm-resp; dual-resp;
   walsh-mm-shift)
open import PathSum.Polynomial using
  (Poly; Var; x[_]; y[_]; 0ᴾ; _+ᴾ_; _-ᴾ_; _·ᴾ_; κ; μ; eval; sgn)
open import PathSum.Polynomial.Bind using
  (bind; rename; eval-bind; eval-rename; odd)
open import PathSum.Polynomial.Product using
  (_*ᴾ_; eval-*ᴾ; eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using
  (valᵛ; eval-+ᴾ; eval-·ᴾ; eval-κ; eval-−ᴾ; eval-cong)

open +-*-Solver using (solve; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Reduction M using (½)

private
  variable
    n m k j : ℕ


------------------------------------------------------------------------
-- Inner products as polynomials

-- Σ_i u_i v_i for two lists of variables, as the head term followed by
-- the rest, in the order of PathSum.HiddenShift.Walsh's dot.

dotᴾ : (Fin j → Var n m) → (Fin j → Var n m) → Poly n m
dotᴾ {j = zero}  u v = 0ᴾ
dotᴾ {j = suc j} u v =
  (μ (u zero) *ᴾ μ (v zero)) +ᴾ dotᴾ (λ i → u (suc i)) (λ i → v (suc i))

-- Its parity is the inner product over Z₂ of the variables' values.

odd-dotᴾ : (u v : Fin j → Var n m) (x : Assign n) (y : Assign m) →
           odd (eval (dotᴾ u v) x y) ≡
           dot (λ i → valᵛ (u i) x y) (λ i → valᵛ (v i) x y)
odd-dotᴾ {j = zero}  u v x y = trans (cong odd (eval-0ᴾ x y)) (odd-[] false)
odd-dotᴾ {j = suc j} u v x y = trans (cong odd (eval-+ᴾ A B x y))
  (trans (odd-+ (eval A x y) (eval B x y))
         (cong₂ _xor_ first (odd-dotᴾ (λ i → u (suc i)) (λ i → v (suc i)) x y)))
  where
  A B : Poly _ _
  A = μ (u zero) *ᴾ μ (v zero)
  B = dotᴾ (λ i → u (suc i)) (λ i → v (suc i))

  first : odd (eval A x y) ≡ valᵛ (u zero) x y ∧ valᵛ (v zero) x y
  first = trans
    (cong odd (trans (eval-*ᴾ (μ (u zero)) (μ (v zero)) x y)
                     (cong₂ _*_ (eval-μᴾ (u zero) x y) (eval-μᴾ (v zero) x y))))
    (odd-∧ (valᵛ (u zero) x y) (valᵛ (v zero) x y))


------------------------------------------------------------------------
-- The path-sums

-- The Hadamard layer H^{⊗n}: |x⟩ ↦ 1/√2^n Σ_y (-1)^{x·y} |y⟩.

hdotᴾ : Poly n n
hdotᴾ = dotᴾ (λ i → x[ i ]) (λ i → y[ i ])

Hᴾ : PathSum n n n
Hᴾ = ⟨ ½ ·ᴾ hdotᴾ , (λ i → μ y[ i ]) ⟩

-- The oracle of the exponent E: |x⟩ ↦ (-1)^{E(x)} |x⟩.

Oᴾ : Poly n 0 → PathSum n 0 0
Oᴾ E = ⟨ ½ ·ᴾ E , (λ i → μ x[ i ]) ⟩

-- The specification |x⟩ ↦ |s⟩.

specᴾ : Assign n → PathSum n 0 0
specᴾ s = ⟨ 0ᴾ , (λ i → κ [ s i ]ᶻ) ⟩

-- The Boolean function a polynomial in the inputs denotes, read modulo
-- 2 as outputs are; none is the assignment to no path variables.

none : Assign 0
none ()

boolᴾ : Poly n 0 → Assign n → Bool
boolᴾ P x = odd (eval P x none)


------------------------------------------------------------------------
-- The Maiorana-McFarland exponents

-- The two halves of the inputs, and g read on either.

leftᵛ rightᵛ : Fin m → Var (m ℕ+ m) 0
leftᵛ  {m} i = x[ i ↑ˡ m ]
rightᵛ {m} i = x[ m ↑ʳ i ]

onˡ onʳ : Var m 0 → Var (m ℕ+ m) 0
onˡ x[ i ]  = leftᵛ i
onˡ y[ () ]
onʳ x[ i ]  = rightᵛ i
onʳ y[ () ]

-- g(x) + x·y and g(y) + x·y.

mmᴾ dualᴾ : Poly m 0 → Poly (m ℕ+ m) 0
mmᴾ   {m} g = rename onˡ g +ᴾ dotᴾ (leftᵛ {m}) (rightᵛ {m})
dualᴾ {m} g = rename onʳ g +ᴾ dotᴾ (leftᵛ {m}) (rightᵛ {m})

-- The lift of v ⊕ b, and the substitution of x_i ⊕ s_i for every
-- input x_i.

xorᴾ : Bool → Var n m → Poly n m
xorᴾ false v = μ v
xorᴾ true  v = κ 1ℤ -ᴾ μ v

shiftᵛ : Assign n → Var n 0 → Poly n 0
shiftᵛ s x[ i ]  = xorᴾ (s i) x[ i ]
shiftᵛ s y[ () ]

shiftᴾ : Assign n → Poly n 0 → Poly n 0
shiftᴾ s P = bind P (shiftᵛ s)


------------------------------------------------------------------------
-- The exponents' values

-- Assignments to no variables are all alike.

eval-none : (P : Poly n 0) (x : Assign n) (y : Assign 0) →
            eval P x y ≡ eval P x none
eval-none P x y = eval-cong P {x} {x} {y} {none} (λ _ → refl) (λ ())

boolᴾ-resp : (P : Poly n 0) → RespectsB (boolᴾ P)
boolᴾ-resp P u v h = cong odd (eval-cong P {u} {v} {none} {none} h (λ ()))

-- The exponents are the paper's, modulo 2.

bool-mmᴾ : (g : Poly m 0) (u : Assign (m ℕ+ m)) →
           boolᴾ (mmᴾ g) u ≡ mm (boolᴾ g) u
bool-mmᴾ {m} g u = trans (cong odd (eval-+ᴾ A B u none))
  (trans (odd-+ (eval A u none) (eval B u none))
         (cong₂ _xor_ first (odd-dotᴾ (leftᵛ {m}) (rightᵛ {m}) u none)))
  where
  A B : Poly (m ℕ+ m) 0
  A = rename onˡ g
  B = dotᴾ (leftᵛ {m}) (rightᵛ {m})

  first : odd (eval A u none) ≡ boolᴾ g (lhalf {m} u)
  first = cong odd (trans (eval-rename onˡ g u none)
    (eval-cong g {λ i → valᵛ (onˡ x[ i ]) u none} {lhalf {m} u}
                 {λ j → valᵛ (onˡ {m} y[ j ]) u none} {none}
                 (λ _ → refl) (λ ())))

bool-dualᴾ : (g : Poly m 0) (u : Assign (m ℕ+ m)) →
             boolᴾ (dualᴾ g) u ≡ dual (boolᴾ g) u
bool-dualᴾ {m} g u = trans (cong odd (eval-+ᴾ A B u none))
  (trans (odd-+ (eval A u none) (eval B u none))
         (cong₂ _xor_ first (odd-dotᴾ (leftᵛ {m}) (rightᵛ {m}) u none)))
  where
  A B : Poly (m ℕ+ m) 0
  A = rename onʳ g
  B = dotᴾ (leftᵛ {m}) (rightᵛ {m})

  first : odd (eval A u none) ≡ boolᴾ g (rhalf {m} u)
  first = cong odd (trans (eval-rename onʳ g u none)
    (eval-cong g {λ i → valᵛ (onʳ x[ i ]) u none} {rhalf {m} u}
                 {λ j → valᵛ (onʳ {m} y[ j ]) u none} {none}
                 (λ _ → refl) (λ ())))

-- The lift of v ⊕ b takes the value of v ⊕ b, so the shifted
-- polynomial is the polynomial of the shifted argument.

eval-xorᴾ : (b : Bool) (v : Var n m) (x : Assign n) (y : Assign m) →
            eval (xorᴾ b v) x y ≡ [ valᵛ v x y xor b ]ᶻ
eval-xorᴾ false v x y =
  trans (eval-μᴾ v x y) (cong [_]ᶻ (sym (xor-identityʳ (valᵛ v x y))))
eval-xorᴾ true  v x y = trans (eval-−ᴾ (κ 1ℤ) (μ v) x y)
  (trans (cong₂ _-_ (eval-κ 1ℤ x y) (eval-μᴾ v x y)) (flip (valᵛ v x y)))
  where
  flip : ∀ a → 1ℤ - [ a ]ᶻ ≡ [ a xor true ]ᶻ
  flip false = refl
  flip true  = refl

eval-shiftᴾ : (s : Assign n) (P : Poly n 0) (u : Assign n) →
              eval (shiftᴾ s P) u none ≡ eval P (u ⊕ᵃ s) none
eval-shiftᴾ s P u = eval-bind P (shiftᵛ s) u none (u ⊕ᵃ s) none value
  where
  value : ∀ v → eval (shiftᵛ s v) u none ≡ [ valᵛ v (u ⊕ᵃ s) none ]ᶻ
  value x[ i ]  = eval-xorᴾ (s i) x[ i ] u none
  value y[ () ]

bool-shiftᴾ : (s : Assign n) (P : Poly n 0) (u : Assign n) →
              boolᴾ (shiftᴾ s P) u ≡ boolᴾ P (u ⊕ᵃ s)
bool-shiftᴾ s P u = cong odd (eval-shiftᴾ s P u)


------------------------------------------------------------------------
-- The layers on columns

-- Comparing assignments is symmetric.

same-comm : (x z : Assign k) → same x z ≡ same z x
same-comm {zero}  x z = refl
same-comm {suc k} x z = cong₂ _∧_ (cong not (xor-comm (x zero) (z zero)))
  (same-comm (λ i → x (suc i)) (λ i → z (suc i)))

-- A sum over no path variables has a single term.

Σᴮ-none : (f : Assign 0 → Amp) {a : Amp} → (∀ y → f y ≐ a) → Σᴮ f ≐ a
Σᴮ-none f h = h _

-- The paths of the Hadamard layer hit their own assignment, those of
-- an oracle its input.

hits-Hᴾ : (x y z : Assign n) → hits (Hᴾ {n}) x y z ≡ same z y
hits-Hᴾ {n} x y z = trans (hits-same (Hᴾ {n}) x y z)
  (trans (same-≗ {x = outBit (Hᴾ {n}) x y} {x′ = y} {z = z} {z′ = z}
                 (λ w → outBit-μ (Hᴾ {n}) x y w y[ w ] refl) (λ _ → refl))
         (same-comm y z))

hits-Oᴾ : (E : Poly n 0) (w : Assign n) (y : Assign 0) (z : Assign n) →
          hits (Oᴾ E) w y z ≡ same w z
hits-Oᴾ E w y z = trans (hits-same (Oᴾ E) w y z)
  (same-≗ {x = outBit (Oᴾ E) w y} {x′ = w} {z = z} {z′ = z}
          (λ v → outBit-μ (Oᴾ E) w y v x[ v ] refl) (λ _ → refl))

-- The matrix of the Hadamard layer: (-1)^{x·z}, unnormalised.

amp-Hᴾ : (x z : Assign n) → amp (Hᴾ {n}) x z ≐ sgn (dot x z) ·ᴬ 1ᴬ
amp-Hᴾ {n} x z i = trans
  (Σᴮ-cong {f = λ y → if hits (Hᴾ {n}) x y z then F y else 0ᴬ}
           {g = λ y → if same z y then F y else 0ᴬ}
           (λ y → if-cong (hits-Hᴾ x y z) (λ _ → refl)) i)
  (trans (Σᴮ-δ z F F-resp i) value)
  where
  F : Assign n → Amp
  F y = zpow (eval (phase (Hᴾ {n})) x y)

  F-resp : Respects F
  F-resp g h g≗h = zpow-≡ (eval-cong (phase (Hᴾ {n})) {x} {x} {g} {h}
                                     (λ _ → refl) g≗h)

  value : F z i ≡ sgn (dot x z) * zpow 0ℤ i
  value = trans (zpow-≡ (eval-·ᴾ ½ hdotᴾ x z) i)
    (trans (zpow-½ (eval hdotᴾ x z) i)
           (cong (λ b → sgn b * zpow 0ℤ i)
                 (odd-dotᴾ (λ w → x[ w ]) (λ w → y[ w ]) x z)))

-- On a column of integers the layer is the Walsh-Hadamard transform:
-- the entry at z is Σ_w (-1)^{w·z} c(w).

applyᴾ-Hᴾ : (c : Assign n → ℤ) → RespectsZ c → (z : Assign n) →
            applyᴾ (Hᴾ {n}) ⌈ c ⌉ z ≐ Σᶻ (λ w → sgn (dot w z) * c w) ·ᴬ 1ᴬ
applyᴾ-Hᴾ {n} c resp z i = trans
  (Σᴮ-cong {f = λ w → Σᴮ (λ y → if hits (Hᴾ {n}) w y z then G w y else 0ᴬ)}
           {g = λ w → (sgn (dot w z) * c w) ·ᴬ 1ᴬ} inner i)
  (Σᴮ-ᶻ (λ w → sgn (dot w z) * c w) resp′ 1ᴬ i)
  where
  G : Assign n → Assign n → Amp
  G w y = rot (eval (phase (Hᴾ {n})) w y) (⌈ c ⌉ w)

  G-resp : ∀ w → Respects (G w)
  G-resp w g h g≗h = rot-exp {eval (phase (Hᴾ {n})) w g}
    {eval (phase (Hᴾ {n})) w h} (⌈ c ⌉ w)
    (eval-cong (phase (Hᴾ {n})) {w} {w} {g} {h} (λ _ → refl) g≗h)

  inner : ∀ w → Σᴮ (λ y → if hits (Hᴾ {n}) w y z then G w y else 0ᴬ) ≐
                (sgn (dot w z) * c w) ·ᴬ 1ᴬ
  inner w l = trans
    (Σᴮ-cong {f = λ y → if hits (Hᴾ {n}) w y z then G w y else 0ᴬ}
             {g = λ y → if same z y then G w y else 0ᴬ}
             (λ y → if-cong (hits-Hᴾ w y z) (λ _ → refl)) l)
    (trans (Σᴮ-δ z (G w) (G-resp w) l)
      (trans (rot-exp {eval (phase (Hᴾ {n})) w z} {½ * eval hdotᴾ w z}
                      (⌈ c ⌉ w) (eval-·ᴾ ½ hdotᴾ w z) l)
        (trans (rot-½ (eval hdotᴾ w z) (c w) l)
               (cong (λ b → (sgn b * c w) * zpow 0ℤ l)
                     (odd-dotᴾ (λ v → x[ v ]) (λ v → y[ v ]) w z)))))

  resp′ : RespectsZ (λ w → sgn (dot w z) * c w)
  resp′ g h g≗h = cong₂ (λ a b → sgn a * b)
    (dot-cong {u = g} {u′ = h} {v = z} {v′ = z} g≗h (λ _ → refl))
    (resp g h g≗h)

-- The matrix of an oracle: diagonal, with the sign of its exponent.

amp-Oᴾ : (E : Poly n 0) (x z : Assign n) →
         amp (Oᴾ E) x z ≐ (if same x z then sgn (boolᴾ E x) ·ᴬ 1ᴬ else 0ᴬ)
amp-Oᴾ E x z = Σᴮ-none
  (λ y → if hits (Oᴾ E) x y z then zpow (eval (phase (Oᴾ E)) x y) else 0ᴬ)
  (λ y → if-cong (hits-Oᴾ E x y z) (value y))
  where
  value : ∀ y → zpow (eval (phase (Oᴾ E)) x y) ≐ sgn (boolᴾ E x) ·ᴬ 1ᴬ
  value y i = trans
    (zpow-≡ (trans (eval-·ᴾ ½ E x y) (cong (½ *_) (eval-none E x y))) i)
    (zpow-½ (eval E x none) i)

-- On a column of integers an oracle multiplies each entry by its sign.

applyᴾ-Oᴾ : (E : Poly n 0) (c : Assign n → ℤ) → RespectsZ c →
            (z : Assign n) →
            applyᴾ (Oᴾ E) ⌈ c ⌉ z ≐ (sgn (boolᴾ E z) * c z) ·ᴬ 1ᴬ
applyᴾ-Oᴾ {n} E c resp z i = trans
  (Σᴮ-cong {f = λ w → Σᴮ (λ y → T w y)}
           {g = λ w → if same z w then F w else 0ᴬ}
           (λ w → Σᴮ-none (T w) (per w)) i)
  (Σᴮ-δ z F F-resp i)
  where
  T : Assign n → Assign 0 → Amp
  T w y = if hits (Oᴾ E) w y z
          then rot (eval (phase (Oᴾ E)) w y) (⌈ c ⌉ w) else 0ᴬ

  F : Assign n → Amp
  F w = (sgn (boolᴾ E w) * c w) ·ᴬ 1ᴬ

  per : ∀ w y → T w y ≐ (if same z w then F w else 0ᴬ)
  per w y = if-cong (trans (hits-Oᴾ E w y z) (same-comm w z)) (λ l → trans
    (rot-exp {eval (phase (Oᴾ E)) w y} {½ * eval E w none} (⌈ c ⌉ w)
             (trans (eval-·ᴾ ½ E w y) (cong (½ *_) (eval-none E w y))) l)
    (rot-½ (eval E w none) (c w) l))

  F-resp : Respects F
  F-resp g h g≗h l = cong (λ t → t * zpow 0ℤ l) (cong₂ (λ a b → sgn a * b)
    (boolᴾ-resp E g h g≗h) (resp g h g≗h))

-- The specification's column at any input is |s⟩.

amp-specᴾ : (s x z : Assign n) →
            amp (specᴾ s) x z ≐ (if same s z then 1ᴬ else 0ᴬ)
amp-specᴾ s x z = Σᴮ-none
  (λ y → if hits (specᴾ s) x y z then zpow (eval (phase (specᴾ s)) x y)
         else 0ᴬ)
  (λ y → if-cong (guard y) (zpow-≡ (eval-0ᴾ x y)))
  where
  guard : ∀ y → hits (specᴾ s) x y z ≡ same s z
  guard y = trans (hits-same (specᴾ s) x y z)
    (same-≗ {x = outBit (specᴾ s) x y} {x′ = s} {z = z} {z′ = z}
            (λ w → trans (cong odd (eval-κ [ s w ]ᶻ x y)) (odd-[] (s w)))
            (λ _ → refl))


------------------------------------------------------------------------
-- The hidden shift circuit

-- H^{⊗n} O_f̃ H^{⊗n} O_f′ H^{⊗n}, read right to left: first a Hadamard
-- layer, last a Hadamard layer.  Its normalisation is 3n.

hs-norm : ℕ → ℕ
hs-norm n = (((n ℕ+ 0) ℕ+ n) ℕ+ 0) ℕ+ n

HS : Poly m 0 → Assign (m ℕ+ m) →
     PathSum (m ℕ+ m) (hs-norm (m ℕ+ m)) (hs-norm (m ℕ+ m))
HS g s = Hᴾ ∘ᴾ Oᴾ (dualᴾ g) ∘ᴾ Hᴾ ∘ᴾ Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ

-- √2^(2j) = 2^j.

scale-twice : ∀ j (a : Amp) → scale (j ℕ+ j) a ≐ (+ (2 ℕ^ j)) ·ᴬ a
scale-twice zero    a i = sym (*-identityˡ (a i))
scale-twice (suc j) a i = trans (√2·-map (scale-exp a (ℕ.+-suc j j)) i)
  (trans (√2·-twice (scale (j ℕ+ j) a) i)
    (trans (cong (+ 2 *_) (scale-twice j a i))
      (trans (sym (*-assoc (+ 2) (+ (2 ℕ^ j)) (a i)))
             (cong (_* a i) (sym (pos-* 2 (2 ℕ^ j)))))))

scale-0ᴬ : ∀ j → scale j 0ᴬ ≐ 0ᴬ
scale-0ᴬ zero    i = refl
scale-0ᴬ (suc j) i = trans (√2·-map (scale-0ᴬ j) i) (√2·-0ᴬ i)


------------------------------------------------------------------------
-- The column at 0

module _ {m : ℕ} (g : Poly m 0) (s : Assign (m ℕ+ m)) where

  private
    gᵇ : Assign m → Bool
    gᵇ = boolᴾ g

    gᵇ-resp : RespectsB gᵇ
    gᵇ-resp = boolᴾ-resp g

    P : ℤ
    P = + (2 ℕ^ m)

    swap : ∀ a p t → a * (p * t) ≡ p * (a * t)
    swap = solve 3 (λ a p t → a :* (p :* t) := p :* (a :* t)) refl

    -- The column after each layer.

    c₁ c₂ c₃ c₄ c₅ : Assign (m ℕ+ m) → ℤ
    c₁ _ = 1ℤ
    c₂ u = sgn (mm gᵇ (u ⊕ᵃ s))
    c₃ v = P * sgn (dual gᵇ v xor dot s v)
    c₄ v = P * sgn (dot s v)
    c₅ z = P * (if same s z then + (2 ℕ^ (m ℕ+ m)) else 0ℤ)

    c₂-resp : RespectsZ c₂
    c₂-resp a b h = cong sgn (mm-resp gᵇ gᵇ-resp (a ⊕ᵃ s) (b ⊕ᵃ s)
                                      (λ i → cong (_xor s i) (h i)))

    c₃-resp : RespectsZ c₃
    c₃-resp a b h = cong (λ t → P * sgn t) (cong₂ _xor_
      (dual-resp gᵇ gᵇ-resp a b h)
      (dot-cong {u = s} {u′ = s} {v = a} {v′ = b} (λ _ → refl) h))

    c₄-resp : RespectsZ c₄
    c₄-resp a b h = cong (λ t → P * sgn t)
      (dot-cong {u = s} {u′ = s} {v = a} {v′ = b} (λ _ → refl) h)

    -- The oracle of f′ = f(· ⊕ s) signs the uniform column.

    st₁ : ∀ u → amp (Hᴾ {m ℕ+ m}) 0ᵃ u ≐ ⌈ c₁ ⌉ u
    st₁ u i = trans (amp-Hᴾ 0ᵃ u i)
                    (cong (λ b → sgn b * zpow 0ℤ i) (dot-0ˡ u))

    st₂ : ∀ u → amp (Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ) 0ᵃ u ≐ ⌈ c₂ ⌉ u
    st₂ u i = trans (prop-2-7ᶜ (Oᴾ (shiftᴾ s (mmᴾ g))) Hᴾ 0ᵃ u i)
      (trans (applyᴾ-cong (Oᴾ (shiftᴾ s (mmᴾ g))) {amp Hᴾ 0ᵃ} {⌈ c₁ ⌉}
                          st₁ u i)
        (trans (applyᴾ-Oᴾ (shiftᴾ s (mmᴾ g)) c₁ (λ _ _ _ → refl) u i)
               (cong (λ t → t * zpow 0ℤ i) sign)))
      where
      sign : sgn (boolᴾ (shiftᴾ s (mmᴾ g)) u) * 1ℤ ≡ c₂ u
      sign = trans (*-identityʳ _)
        (cong sgn (trans (bool-shiftᴾ s (mmᴾ g) u) (bool-mmᴾ g (u ⊕ᵃ s))))

    -- The Walsh transform of f′: 2^m f̃ times the character of s.

    st₃ : ∀ v → amp (Hᴾ ∘ᴾ Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ) 0ᵃ v ≐ ⌈ c₃ ⌉ v
    st₃ v i = trans (prop-2-7ᶜ Hᴾ (Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ) 0ᵃ v i)
      (trans (applyᴾ-cong Hᴾ {amp (Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ) 0ᵃ} {⌈ c₂ ⌉}
                          st₂ v i)
        (trans (applyᴾ-Hᴾ c₂ c₂-resp v i)
               (cong (λ t → t * zpow 0ℤ i) walsh)))
      where
      walsh : Σᶻ (λ u → sgn (dot u v) * c₂ u) ≡ c₃ v
      walsh = trans
        (Σᶻ-cong (λ u → trans (*-comm (sgn (dot u v)) (c₂ u))
                              (sym (sgn-xor (mm gᵇ (u ⊕ᵃ s)) (dot u v)))))
        (walsh-mm-shift gᵇ gᵇ-resp s v)

    -- The oracle of the dual cancels f̃, leaving the character of s.

    st₄ : ∀ v → amp (Oᴾ (dualᴾ g) ∘ᴾ Hᴾ ∘ᴾ Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ) 0ᵃ v ≐
                ⌈ c₄ ⌉ v
    st₄ v i = trans
      (prop-2-7ᶜ (Oᴾ (dualᴾ g)) (Hᴾ ∘ᴾ Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ) 0ᵃ v i)
      (trans (applyᴾ-cong (Oᴾ (dualᴾ g))
                          {amp (Hᴾ ∘ᴾ Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ) 0ᵃ}
                          {⌈ c₃ ⌉} st₃ v i)
        (trans (applyᴾ-Oᴾ (dualᴾ g) c₃ c₃-resp v i)
               (cong (λ t → t * zpow 0ℤ i) sign)))
      where
      sign : sgn (boolᴾ (dualᴾ g) v) * c₃ v ≡ c₄ v
      sign = trans (cong (λ b → sgn b * c₃ v) (bool-dualᴾ g v))
        (trans (swap (sgn (dual gᵇ v)) P (sgn (dual gᵇ v xor dot s v)))
               (cong (P *_) (sgn-absorb (dual gᵇ v) (dot s v))))

    -- The last layer interferes the character of s into |s⟩.

    st₅ : ∀ z → amp (HS g s) 0ᵃ z ≐ ⌈ c₅ ⌉ z
    st₅ z i = trans
      (prop-2-7ᶜ Hᴾ (Oᴾ (dualᴾ g) ∘ᴾ Hᴾ ∘ᴾ Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ)
                 0ᵃ z i)
      (trans (applyᴾ-cong Hᴾ
               {amp (Oᴾ (dualᴾ g) ∘ᴾ Hᴾ ∘ᴾ Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ) 0ᵃ}
               {⌈ c₄ ⌉} st₄ z i)
        (trans (applyᴾ-Hᴾ c₄ c₄-resp z i)
               (cong (λ t → t * zpow 0ℤ i) orth)))
      where
      orth : Σᶻ (λ v → sgn (dot v z) * c₄ v) ≡ c₅ z
      orth = trans
        (Σᶻ-cong (λ v → trans (swap (sgn (dot v z)) P (sgn (dot s v)))
          (cong (P *_) (sym (sgn-xor (dot v z) (dot s v))))))
        (trans (Σᶻ-* P (λ v → sgn (dot v z xor dot s v)))
               (cong (P *_) (character-shift s z)))

    -- 2^m 2^n is √2^(3n).

    norm≡ : hs-norm (m ℕ+ m) ≡ (m ℕ+ (m ℕ+ m)) ℕ+ (m ℕ+ (m ℕ+ m))
    norm≡ = ℕSolver.+-*-Solver.solve 1 (λ a →
      ((((a ℕSolver.+-*-Solver.:+ a) ℕSolver.+-*-Solver.:+
         ℕSolver.+-*-Solver.con 0) ℕSolver.+-*-Solver.:+
        (a ℕSolver.+-*-Solver.:+ a)) ℕSolver.+-*-Solver.:+
        ℕSolver.+-*-Solver.con 0) ℕSolver.+-*-Solver.:+
        (a ℕSolver.+-*-Solver.:+ a)
      ℕSolver.+-*-Solver.:=
      (a ℕSolver.+-*-Solver.:+ (a ℕSolver.+-*-Solver.:+ a))
        ℕSolver.+-*-Solver.:+
      (a ℕSolver.+-*-Solver.:+ (a ℕSolver.+-*-Solver.:+ a))) refl m

    final : ∀ b l → (P * (if b then + (2 ℕ^ (m ℕ+ m)) else 0ℤ)) * zpow 0ℤ l ≡
                    (if b then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ) else 0ᴬ) l
    final true  l = sym (trans (scale-exp (zpow 0ℤ) norm≡ l)
      (trans (scale-twice (m ℕ+ (m ℕ+ m)) (zpow 0ℤ) l)
             (cong (_* zpow 0ℤ l)
                   (trans (cong +_ (ℕ.^-distribˡ-+-* 2 m (m ℕ+ m)))
                          (pos-* (2 ℕ^ m) (2 ℕ^ (m ℕ+ m)))))))
    final false l =
      trans (cong (_* zpow 0ℤ l) (*-zeroʳ P)) (*-zeroˡ (zpow 0ℤ l))

  -- The hidden shift algorithm: from |0⟩ the circuit reaches |s⟩, with
  -- amplitude √2^K before the normalisation 1/√2^K, and nothing else.

  hidden-shift : (z : Assign (m ℕ+ m)) →
                 amp (HS g s) 0ᵃ z ≐
                 (if same s z then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ) else 0ᴬ)
  hidden-shift z i = trans (st₅ z i) (final (same s z) i)

  -- The same against the specification |x⟩ ↦ |s⟩, whose column is |s⟩
  -- at every input x: the column of HS g s at 0 is that column,
  -- normalised alike.

  hidden-shift-spec : (x z : Assign (m ℕ+ m)) →
                      amp (HS g s) 0ᵃ z ≐
                      scale (hs-norm (m ℕ+ m)) (amp (specᴾ s) x z)
  hidden-shift-spec x z i = trans (hidden-shift z i)
    (sym (trans (scale-map (hs-norm (m ℕ+ m)) (amp-specᴾ s x z) i)
                (pick (same s z) i)))
    where
    pick : ∀ b → scale (hs-norm (m ℕ+ m)) (if b then 1ᴬ else 0ᴬ) ≐
                 (if b then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ) else 0ᴬ)
    pick true  l = refl
    pick false l = scale-0ᴬ (hs-norm (m ℕ+ m)) l
