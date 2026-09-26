------------------------------------------------------------------------
-- Presentations of groups
--
-- The hidden shift circuit of figure 3(a), over {H, CNOT, R_k, R_k†}
-- (Amy, QPL 2018, section 5.2)
--
-- The oracles.  g is given as the paper builds its random instances:
-- a list of Z, CZ and CCZ gates on m wires, i.e. a list of monomials
-- of degree at most 3 (PathSum.HiddenShift.Gates's Term), g(x) being
-- their sum over Z₂.  The oracle of the Maiorana-McFarland function
-- f(x, y) = g(x) + x·y is g's monomials on the x wires followed by
-- the x·y part, a CZ between x_i and y_i for every i (oracleᶠ); that
-- of the dual f̃(x, y) = g(y) + x·y is the CZs followed by g's
-- monomials on the y wires (oracleᵈ).  Each is the diagonal (-1)^f,
-- respectively (-1)^{f̃} (oracleᶠ-amp, oracleᵈ-amp), for every m and
-- every list of monomials, and is equivalent to PathSum.HiddenShift's
-- oracle path-sum Oᴾ of the exponent mmᴾ or dualᴾ of the polynomial
-- sumᴾ gs of the monomials (oracleᶠ-≋, oracleᵈ-≋).
--
-- The circuit (HSᶜ) is figure 3(a) read left to right:
--
--    H^{⊗n};  X^s;  O_f;  X^s;  H^{⊗n};  O_f̃;  H^{⊗n},
--
-- n = 2m.  Each layer simulates a layer of PathSum.HiddenShift's
-- composite HS (PathSum.HiddenShift.Layers): H^{⊗n} is Hᴾ, and
-- X^s O_f X^s is the oracle of the shifted exponent, the O_f′ of the
-- paper.  Simulations compose, so the circuit simulates HS; by
-- proposition 2.10 its amplitudes are HS's at every input, scaled by
-- the four Hadamards of each X gate (hidden-shift-circuit-sim), and
-- ⟦ HSᶜ gs s ⟧ ≋ HS (sumᴾ gs) s in the sense of definition 2.3
-- (hidden-shift-circuit-≋).  PathSum.HiddenShift's theorem then gives
-- the paper's specification: from |0⟩ the circuit reaches |s⟩ with
-- normalised amplitude 1, and nothing else (hidden-shift-circuit); the
-- circuit's path-sum on |0⟩ is equivalent to |x⟩ ↦ |s⟩
-- (hidden-shift-circuit-at0); and whenever a reduction of it by the
-- rules of figure 2 eliminates all path variables, it ends at |s⟩
-- syntactically (circuit-reduces, circuit-derives) -- the paper
-- reports its tool finds |s⟩ "even without providing the
-- specification"; that such a reduction exists is not proved here
-- (only for one instance of the path-sum composite, in
-- PathSum.HiddenShift.Example).
-- All of it for every m, every list of monomials and every s.
--
-- Departures from the paper.  X is not in the gate set of definition
-- 2.9; here it is H R₁ H, so each X adds two Hadamards and two path
-- variables, which the paper's X, a primitive of its tool, does not:
-- the circuit's path-sum has 3n + 4|s| path variables rather than 3n
-- (table 2), and the same amplitudes once normalised.  The symbolic
-- shift of figure 3(b), which needs no X, is
-- PathSum.HiddenShift.Symbolic.  Monomials have no constant term.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Circuit (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-comm)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _*_)
open import Data.Integer.Properties using (*-zeroʳ)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Nat.Base using (zero; suc; _<_) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ
import Data.Nat.Solver as ℕSolver

open import PathSum.AmpLinear M₀ using (scale-+; scale-exp)
open import PathSum.Ancilla.Register M₀ using
  (Prepared; set0ᶜ; amp-input; _≋⟨_⟩₀_; ≋⟨⟩₀-set0ᶜ)
open import PathSum.Assign using ([_]ᶻ; same; same-true)
open import PathSum.Base using (PathSum; out; phase)
open import PathSum.CircuitSemantics M₀ using (Column; δ; δ-resp)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; _·ᴬ_; zpow; scale; scale-map)
open import PathSum.Denotation M₀ using
  (Assign; amp; _≋_; ≋-sym; ≋-trans)
open import PathSum.HiddenShift M₀ using
  (Hᴾ; Oᴾ; mmᴾ; dualᴾ; shiftᴾ; boolᴾ; bool-mmᴾ; bool-dualᴾ; none; HS;
   hs-norm; specᴾ; amp-specᴾ; hidden-shift; scale-0ᴬ)
open import PathSum.HiddenShift.Gates M₀ using
  (Term; Z; CZ; CCZ; mono; sumᵇ; sumᵇ-resp; sumᵇ-++; sumᵇ-map; mapTerm;
   oracle; norm-oracle; Signs; signed; Signs-oracle)
open import PathSum.HiddenShift.Layers M₀ using
  (hadamards; norm-hadamards; flips; Sim; Sim-++; Sim-exp; Sim-circuit;
   Sim-≋; Sim-hadamards; Sim-signs; Sim-shifted; oracle-≋)
open import PathSum.HiddenShift.Sign M₀ using (1ᴬ; odd-+; odd-[])
open import PathSum.HiddenShift.Simulation M₀ using
  (at0; amp-at0; spec-only-if)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; lhalf; rhalf; dot; mm; dual)
open import PathSum.Polynomial using
  (Poly; x[_]; 0ᴾ; _+ᴾ_; κ; μ; eval; sgn; _≈[_]_)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ; eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using (eval-+ᴾ)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Adjoint M using (norm-++)
open import PathSum.CRK.Circuit M using (Circuit; norm; ⟦_⟧)
open import PathSum.CRK.Semantics M₀ using (applyᴬ; prop-2-10)
open import PathSum.Full M using (_⟶ᶠ*_)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Order M using (pow)
open import PathSum.Reduction.Derivation M₀ using
  (Derivation; derivation-sound)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Monomials as polynomials

-- A list of monomials as an integer polynomial, for the path-sums of
-- PathSum.HiddenShift.

monoᴾ : Term n → Poly n 0
monoᴾ (Z a)             = μ x[ a ]
monoᴾ (CZ a b _)        = μ x[ a ] *ᴾ μ x[ b ]
monoᴾ (CCZ a b c _ _ _) = μ x[ a ] *ᴾ (μ x[ b ] *ᴾ μ x[ c ])

sumᴾ : List (Term n) → Poly n 0
sumᴾ []       = 0ᴾ
sumᴾ (t ∷ ts) = monoᴾ t +ᴾ sumᴾ ts

-- Read modulo 2, it is the sum of the monomials over Z₂.

private
  mul-bits : ∀ a b → [ a ]ᶻ * [ b ]ᶻ ≡ [ a ∧ b ]ᶻ
  mul-bits false false = refl
  mul-bits false true  = refl
  mul-bits true  false = refl
  mul-bits true  true  = refl

eval-monoᴾ : (t : Term n) (x : Assign n) (y : Assign 0) →
             eval (monoᴾ t) x y ≡ [ mono t x ]ᶻ
eval-monoᴾ (Z a)             x y = eval-μᴾ x[ a ] x y
eval-monoᴾ (CZ a b _)        x y = trans (eval-*ᴾ (μ x[ a ]) (μ x[ b ]) x y)
  (trans (cong₂ _*_ (eval-μᴾ x[ a ] x y) (eval-μᴾ x[ b ] x y))
         (mul-bits (x a) (x b)))
eval-monoᴾ (CCZ a b c _ _ _) x y =
  trans (eval-*ᴾ (μ x[ a ]) (μ x[ b ] *ᴾ μ x[ c ]) x y)
    (trans (cong₂ _*_ (eval-μᴾ x[ a ] x y)
             (trans (eval-*ᴾ (μ x[ b ]) (μ x[ c ]) x y)
               (trans (cong₂ _*_ (eval-μᴾ x[ b ] x y) (eval-μᴾ x[ c ] x y))
                      (mul-bits (x b) (x c)))))
           (mul-bits (x a) (x b ∧ x c)))

bool-sumᴾ : (ts : List (Term n)) (x : Assign n) → boolᴾ (sumᴾ ts) x ≡ sumᵇ ts x
bool-sumᴾ []       x = trans (cong odd (eval-0ᴾ x none)) (odd-[] false)
bool-sumᴾ (t ∷ ts) x = trans (cong odd (eval-+ᴾ (monoᴾ t) (sumᴾ ts) x none))
  (trans (odd-+ (eval (monoᴾ t) x none) (eval (sumᴾ ts) x none))
    (cong₂ _xor_ (trans (cong odd (eval-monoᴾ t x none)) (odd-[] (mono t x)))
                 (bool-sumᴾ ts x)))


------------------------------------------------------------------------
-- The oracle of a list of monomials

-- It is the diagonal (-1)^{g(x)}, g the sum of the monomials.

oracle-amp : (ts : List (Term n)) (x z : Assign n) →
             amp ⟦ oracle ts ⟧ x z ≐
             (if same x z then sgn (sumᵇ ts x) ·ᴬ 1ᴬ else 0ᴬ)
oracle-amp ts x z i = trans (prop-2-10 (oracle ts) x z i)
  (trans (signed (Signs-oracle ts) (δ x) (δ-resp x) z i)
         (pick (same x z) refl i))
  where
  pick : ∀ b → same x z ≡ b →
         sgn (sumᵇ ts z) ·ᴬ (if b then zpow 0ℤ else 0ᴬ) ≐
         (if b then sgn (sumᵇ ts x) ·ᴬ 1ᴬ else 0ᴬ)
  pick true  eq l = cong (λ t → sgn t * zpow 0ℤ l)
    (sumᵇ-resp ts z x (λ j → sym (same-true x z eq j)))
  pick false eq l = *-zeroʳ (sgn (sumᵇ ts z))

-- And the oracle path-sum of the polynomial of the monomials.

oracle-sumᴾ-≋ : (ts : List (Term n)) → ⟦ oracle ts ⟧ ≋ Oᴾ (sumᴾ ts)
oracle-sumᴾ-≋ ts = oracle-≋ ts (sumᴾ ts) (λ z → sym (bool-sumᴾ ts z))


------------------------------------------------------------------------
-- The Maiorana-McFarland oracles

-- x_i and y_i are different wires.

cross : ∀ m (i : Fin m) → i ↑ˡ m ≢ m ↑ʳ i
cross m i e = ℕ.<-irrefl same-ℕ lt
  where
  same-ℕ : toℕ i ≡ m ℕ+ toℕ i
  same-ℕ = trans (sym (Fin.toℕ-↑ˡ i m))
                 (trans (cong toℕ e) (Fin.toℕ-↑ʳ m i))

  lt : toℕ i < m ℕ+ toℕ i
  lt = ℕ.<-≤-trans (Fin.toℕ<n i) (ℕ.m≤m+n m (toℕ i))

-- A CZ between ℓ i and r i for every i, and its value, the inner
-- product of the two lists of bits.

pairs : (ℓ r : Fin k → Fin n) → (∀ i → ℓ i ≢ r i) → List (Term n)
pairs {zero}  ℓ r p = []
pairs {suc k} ℓ r p = CZ (ℓ zero) (r zero) (p zero) ∷
  pairs (λ i → ℓ (suc i)) (λ i → r (suc i)) (λ i → p (suc i))

sumᵇ-pairs : (ℓ r : Fin k → Fin n) (p : ∀ i → ℓ i ≢ r i) (z : Assign n) →
             sumᵇ (pairs ℓ r p) z ≡ dot (λ i → z (ℓ i)) (λ i → z (r i))
sumᵇ-pairs {zero}  ℓ r p z = refl
sumᵇ-pairs {suc k} ℓ r p z = cong ((z (ℓ zero) ∧ z (r zero)) xor_)
  (sumᵇ-pairs (λ i → ℓ (suc i)) (λ i → r (suc i)) (λ i → p (suc i)) z)

-- The monomials of x·y, and of g on either half.

xyTerms : ∀ m → List (Term (m ℕ+ m))
xyTerms m = pairs (λ i → i ↑ˡ m) (λ i → m ↑ʳ i) (cross m)

onLeft onRight : List (Term m) → List (Term (m ℕ+ m))
onLeft  {m} = map (mapTerm (λ i → i ↑ˡ m) (λ {a} {b} → Fin.↑ˡ-injective m a b))
onRight {m} = map (mapTerm (λ i → m ↑ʳ i) (λ {a} {b} → Fin.↑ʳ-injective m a b))

-- f = g(x) + x·y and f̃ = g(y) + x·y.

fTerms f̃Terms : List (Term m) → List (Term (m ℕ+ m))
fTerms  {m} gs = onLeft gs ++ xyTerms m
f̃Terms {m} gs = xyTerms m ++ onRight gs

oracleᶠ oracleᵈ : List (Term m) → Circuit (m ℕ+ m)
oracleᶠ gs = oracle (fTerms gs)
oracleᵈ gs = oracle (f̃Terms gs)

-- Their values are the paper's f and f̃ (PathSum.HiddenShift.Walsh's
-- mm and dual).

sum-f : (gs : List (Term m)) (u : Assign (m ℕ+ m)) →
        sumᵇ (fTerms gs) u ≡ mm (sumᵇ gs) u
sum-f {m} gs u = trans (sumᵇ-++ (onLeft gs) (xyTerms m) u)
  (cong₂ _xor_
    (sumᵇ-map (λ i → i ↑ˡ m) (λ {a} {b} → Fin.↑ˡ-injective m a b) gs u)
    (sumᵇ-pairs (λ i → i ↑ˡ m) (λ i → m ↑ʳ i) (cross m) u))

sum-f̃ : (gs : List (Term m)) (u : Assign (m ℕ+ m)) →
        sumᵇ (f̃Terms gs) u ≡ dual (sumᵇ gs) u
sum-f̃ {m} gs u = trans (sumᵇ-++ (xyTerms m) (onRight gs) u)
  (trans (cong₂ _xor_
           (sumᵇ-pairs (λ i → i ↑ˡ m) (λ i → m ↑ʳ i) (cross m) u)
           (sumᵇ-map (λ i → m ↑ʳ i) (λ {a} {b} → Fin.↑ʳ-injective m a b)
                     gs u))
         (xor-comm (dot (lhalf {m} u) (rhalf {m} u))
                   (sumᵇ gs (rhalf {m} u))))

-- They are the diagonals (-1)^f and (-1)^{f̃}.

oracleᶠ-amp : (gs : List (Term m)) (x z : Assign (m ℕ+ m)) →
              amp ⟦ oracleᶠ gs ⟧ x z ≐
              (if same x z then sgn (mm (sumᵇ gs) x) ·ᴬ 1ᴬ else 0ᴬ)
oracleᶠ-amp gs x z i = trans (oracle-amp (fTerms gs) x z i)
  (cong (λ t → (if same x z then sgn t ·ᴬ 1ᴬ else 0ᴬ) i) (sum-f gs x))

oracleᵈ-amp : (gs : List (Term m)) (x z : Assign (m ℕ+ m)) →
              amp ⟦ oracleᵈ gs ⟧ x z ≐
              (if same x z then sgn (dual (sumᵇ gs) x) ·ᴬ 1ᴬ else 0ᴬ)
oracleᵈ-amp gs x z i = trans (oracle-amp (f̃Terms gs) x z i)
  (cong (λ t → (if same x z then sgn t ·ᴬ 1ᴬ else 0ᴬ) i) (sum-f̃ gs x))

-- And PathSum.HiddenShift's oracles of the exponents mmᴾ and dualᴾ.

bool-f : (gs : List (Term m)) (u : Assign (m ℕ+ m)) →
         sumᵇ (fTerms gs) u ≡ boolᴾ (mmᴾ (sumᴾ gs)) u
bool-f {m} gs u = trans (sum-f gs u) (sym (trans (bool-mmᴾ (sumᴾ gs) u)
  (cong (_xor dot (lhalf {m} u) (rhalf {m} u)) (bool-sumᴾ gs (lhalf {m} u)))))

bool-f̃ : (gs : List (Term m)) (u : Assign (m ℕ+ m)) →
         sumᵇ (f̃Terms gs) u ≡ boolᴾ (dualᴾ (sumᴾ gs)) u
bool-f̃ {m} gs u = trans (sum-f̃ gs u) (sym (trans (bool-dualᴾ (sumᴾ gs) u)
  (cong (_xor dot (lhalf {m} u) (rhalf {m} u)) (bool-sumᴾ gs (rhalf {m} u)))))

oracleᶠ-≋ : (gs : List (Term m)) → ⟦ oracleᶠ gs ⟧ ≋ Oᴾ (mmᴾ (sumᴾ gs))
oracleᶠ-≋ gs = oracle-≋ (fTerms gs) (mmᴾ (sumᴾ gs)) (bool-f gs)

oracleᵈ-≋ : (gs : List (Term m)) → ⟦ oracleᵈ gs ⟧ ≋ Oᴾ (dualᴾ (sumᴾ gs))
oracleᵈ-≋ gs = oracle-≋ (f̃Terms gs) (dualᴾ (sumᴾ gs)) (bool-f̃ gs)


------------------------------------------------------------------------
-- Figure 3(a)

-- H^{⊗n}; X^s; O_f; X^s; H^{⊗n}; O_f̃; H^{⊗n}, bracketed so that the
-- simulations below compose into PathSum.HiddenShift's HS exactly.

HSᶜ : List (Term m) → Assign (m ℕ+ m) → Circuit (m ℕ+ m)
HSᶜ {m} gs s =
  (((hadamards (m ℕ+ m) ++ (flips s ++ (oracleᶠ gs ++ flips s))) ++
     hadamards (m ℕ+ m)) ++ oracleᵈ gs) ++ hadamards (m ℕ+ m)

-- The Hadamards of the X gates: two for each X, in each X layer.

xs-norm : Assign n → ℕ
xs-norm s = norm (flips s) ℕ+ norm (flips s)

-- The circuit simulates the composite.

Sim-HSᶜ : (gs : List (Term m)) (s : Assign (m ℕ+ m)) →
          Sim (applyᴬ (HSᶜ gs s)) (HS (sumᴾ gs) s) (xs-norm s ℕ+ 0)
Sim-HSᶜ {m} gs s =
  Sim-++ (((Hn ++ X) ++ Hn) ++ D) Hn
    (Sim-++ ((Hn ++ X) ++ Hn) D
      (Sim-++ (Hn ++ X) Hn
        (Sim-++ Hn X (Sim-hadamards (m ℕ+ m))
          (Sim-shifted s (Signs-oracle (fTerms gs)) (mmᴾ (sumᴾ gs))
                       (bool-f gs)))
        (Sim-hadamards (m ℕ+ m)))
      (Sim-signs (Signs-oracle (f̃Terms gs)) (dualᴾ (sumᴾ gs)) (bool-f̃ gs)))
    (Sim-hadamards (m ℕ+ m))
  where
  Hn X D : Circuit (m ℕ+ m)
  Hn = hadamards (m ℕ+ m)
  X  = flips s ++ (oracleᶠ gs ++ flips s)
  D  = oracleᵈ gs

-- Its normalisation: 3n and the X gates.

norm-HSᶜ : (gs : List (Term m)) (s : Assign (m ℕ+ m)) →
           norm (HSᶜ gs s) ≡ hs-norm (m ℕ+ m) ℕ+ (xs-norm s ℕ+ 0)
norm-HSᶜ {m} gs s = begin
  norm ((((Hn ++ X) ++ Hn) ++ D) ++ Hn)
    ≡⟨ norm-++ (((Hn ++ X) ++ Hn) ++ D) Hn ⟩
  norm (((Hn ++ X) ++ Hn) ++ D) ℕ+ norm Hn
    ≡⟨ cong₂ _ℕ+_ (trans (norm-++ ((Hn ++ X) ++ Hn) D)
         (cong₂ _ℕ+_ (trans (norm-++ (Hn ++ X) Hn)
           (cong₂ _ℕ+_ (trans (norm-++ Hn X) (cong₂ _ℕ+_ nH nX)) nH))
           (norm-oracle (f̃Terms gs))))
         nH ⟩
  (((w ℕ+ (Ns ℕ+ (0 ℕ+ Ns))) ℕ+ w) ℕ+ 0) ℕ+ w
    ≡⟨ arith w Ns ⟩
  hs-norm w ℕ+ ((Ns ℕ+ Ns) ℕ+ 0) ∎
  where
  open ≡-Reasoning
  open ℕSolver.+-*-Solver using (solve; con; _:+_; _:=_)

  w Ns : ℕ
  w  = m ℕ+ m
  Ns = norm (flips s)

  Hn X D : Circuit (m ℕ+ m)
  Hn = hadamards w
  X  = flips s ++ (oracleᶠ gs ++ flips s)
  D  = oracleᵈ gs

  nH : norm Hn ≡ w
  nH = norm-hadamards w

  nX : norm X ≡ Ns ℕ+ (0 ℕ+ Ns)
  nX = trans (norm-++ (flips s) (oracleᶠ gs ++ flips s))
    (cong (Ns ℕ+_) (trans (norm-++ (oracleᶠ gs) (flips s))
                          (cong (_ℕ+ Ns) (norm-oracle (fTerms gs)))))

  arith : ∀ a b → (((a ℕ+ (b ℕ+ (0 ℕ+ b))) ℕ+ a) ℕ+ 0) ℕ+ a ≡
                  ((((a ℕ+ 0) ℕ+ a) ℕ+ 0) ℕ+ a) ℕ+ ((b ℕ+ b) ℕ+ 0)
  arith = solve 2 (λ a b →
    (((a :+ (b :+ (con 0 :+ b))) :+ a) :+ con 0) :+ a :=
    ((((a :+ con 0) :+ a) :+ con 0) :+ a) :+ ((b :+ b) :+ con 0)) refl

-- On every input the circuit has the amplitudes of the composite, times
-- √2 to the Hadamards of its X gates.

hidden-shift-circuit-sim : (gs : List (Term m)) (s x z : Assign (m ℕ+ m)) →
                           amp ⟦ HSᶜ gs s ⟧ x z ≐
                           scale (xs-norm s ℕ+ 0) (amp (HS (sumᴾ gs) s) x z)
hidden-shift-circuit-sim gs s x z = Sim-circuit (HSᶜ gs s) (Sim-HSᶜ gs s) x z

-- So it is the composite, in the sense of definition 2.3.

hidden-shift-circuit-≋ : (gs : List (Term m)) (s : Assign (m ℕ+ m)) →
                         ⟦ HSᶜ gs s ⟧ ≋ HS (sumᴾ gs) s
hidden-shift-circuit-≋ gs s =
  Sim-≋ (HSᶜ gs s) (HS (sumᴾ gs) s) (Sim-HSᶜ gs s) (norm-HSᶜ gs s)

-- The hidden shift algorithm, as a circuit: from |0⟩ it reaches |s⟩,
-- with amplitude √2^K before the normalisation 1/√2^K, K = norm (HSᶜ
-- gs s), and nothing else.

hidden-shift-circuit : (gs : List (Term m)) (s z : Assign (m ℕ+ m)) →
                       amp ⟦ HSᶜ gs s ⟧ 0ᵃ z ≐
                       (if same s z then scale (norm (HSᶜ gs s)) (zpow 0ℤ)
                        else 0ᴬ)
hidden-shift-circuit {m} gs s z i =
  trans (hidden-shift-circuit-sim gs s 0ᵃ z i)
    (trans (scale-map E (hidden-shift (sumᴾ gs) s z) i) (pick (same s z) i))
  where
  E : ℕ
  E = xs-norm s ℕ+ 0

  pick : ∀ b → scale E (if b then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ) else 0ᴬ) ≐
               (if b then scale (norm (HSᶜ gs s)) (zpow 0ℤ) else 0ᴬ)
  pick true  l = trans (scale-+ E (hs-norm (m ℕ+ m)) (zpow 0ℤ) l)
    (scale-exp (zpow 0ℤ) (trans (ℕ.+-comm E (hs-norm (m ℕ+ m)))
                                (sym (norm-HSᶜ gs s))) l)
  pick false l = scale-0ᴬ E l

-- The same, as a statement named by its arguments.  A closed instance
-- of it is then recognised by its arguments, never by unfolding the
-- circuit into amplitudes (PathSum.HiddenShift.CircuitExample).

record HiddenShiftSpec (gs : List (Term m)) (s : Assign (m ℕ+ m)) : Set where
  constructor hidden-shift-spec-at
  field
    column-at-0 : ∀ z → amp ⟦ HSᶜ gs s ⟧ 0ᵃ z ≐
                        (if same s z then scale (norm (HSᶜ gs s)) (zpow 0ℤ)
                         else 0ᴬ)

hidden-shift-circuit-spec : (gs : List (Term m)) (s : Assign (m ℕ+ m)) →
                            HiddenShiftSpec gs s
hidden-shift-circuit-spec gs s =
  hidden-shift-spec-at (hidden-shift-circuit gs s)

-- The circuit's path-sum on |0⟩ is the specification |x⟩ ↦ |s⟩.

hidden-shift-circuit-at0 : (gs : List (Term m)) (s : Assign (m ℕ+ m)) →
                           at0 ⟦ HSᶜ gs s ⟧ ≋ specᴾ s
hidden-shift-circuit-at0 gs s x z i = trans (amp-at0 ⟦ HSᶜ gs s ⟧ x z i)
  (trans (hidden-shift-circuit gs s z i)
    (sym (trans (scale-map (norm (HSᶜ gs s)) (amp-specᴾ s x z) i)
                (pick (same s z) i))))
  where
  pick : ∀ b → scale (norm (HSᶜ gs s)) (if b then 1ᴬ else 0ᴬ) ≐
               (if b then scale (norm (HSᶜ gs s)) (zpow 0ℤ) else 0ᴬ)
  pick true  l = refl
  pick false l = scale-0ᴬ (norm (HSᶜ gs s)) l

-- The same with every qubit an ancilla prepared in |0⟩
-- (PathSum.Ancilla.Register): on the prepared input the circuit is the
-- specification, and so is its path-sum with every input read as 0.

allMask : ∀ n → Fin n → Bool
allMask n _ = true

hidden-shift-circuit-register : (gs : List (Term m)) (s : Assign (m ℕ+ m)) →
                                ⟦ HSᶜ gs s ⟧ ≋⟨ allMask (m ℕ+ m) ⟩₀ specᴾ s
hidden-shift-circuit-register gs s x z p i =
  trans (amp-input ⟦ HSᶜ gs s ⟧ (λ j → p j refl) z i)
        (trans (sym (amp-at0 ⟦ HSᶜ gs s ⟧ x z i))
               (hidden-shift-circuit-at0 gs s x z i))

hidden-shift-circuit-set0 : (gs : List (Term m)) (s : Assign (m ℕ+ m)) →
                            set0ᶜ (allMask (m ℕ+ m)) ⟦ HSᶜ gs s ⟧ ≋ specᴾ s
hidden-shift-circuit-set0 {m} gs s =
  ≋⟨⟩₀-set0ᶜ (allMask (m ℕ+ m)) ⟦ HSᶜ gs s ⟧ (specᴾ s)
    (hidden-shift-circuit-register gs s)
    (λ x z l → trans (amp-specᴾ s _ z l) (sym (amp-specᴾ s x z l)))

-- Every complete reduction of it by figure 2's rules, at any path
-- variables, ends at |x⟩ ↦ |s⟩ syntactically: normalisation 0,
-- outputs s modulo 2, phase 0 modulo 1.

circuit-reduces : (gs : List (Term m)) (s : Assign (m ℕ+ m)) {k′ : ℕ}
                  {ζ : PathSum (m ℕ+ m) k′ 0} →
                  at0 ⟦ HSᶜ gs s ⟧ ⟶ᶠ* ζ →
                  (k′ ≡ 0) ×
                  (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
                  (phase ζ ≈[ pow M ] 0ᴾ)
circuit-reduces gs s {k′} {ζ} steps = spec-only-if s ζ
  (≋-trans {ξ = ζ} {ζ = at0 ⟦ HSᶜ gs s ⟧} {χ = specᴾ s}
    (≋-sym {ξ = at0 ⟦ HSᶜ gs s ⟧} {ζ = ζ} (⟶ᶠ*-sound steps))
    (hidden-shift-circuit-at0 gs s))

-- The same for a derivation in the paper's style.

circuit-derives : (gs : List (Term m)) (s : Assign (m ℕ+ m)) {k′ : ℕ}
                  {ζ : PathSum (m ℕ+ m) k′ 0} →
                  Derivation (at0 ⟦ HSᶜ gs s ⟧) ζ →
                  (k′ ≡ 0) ×
                  (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
                  (phase ζ ≈[ pow M ] 0ᴾ)
circuit-derives gs s {k′} {ζ} d = spec-only-if s ζ
  (≋-trans {ξ = ζ} {ζ = at0 ⟦ HSᶜ gs s ⟧} {χ = specᴾ s}
    (≋-sym {ξ = at0 ⟦ HSᶜ gs s ⟧} {ζ = ζ} (derivation-sound d))
    (hidden-shift-circuit-at0 gs s))
