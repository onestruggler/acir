------------------------------------------------------------------------
-- Presentations of groups
--
-- The quantum Fourier transform, verified for every number of qubits
-- (Amy, QPL 2018, section 5.2)
--
-- Section 5.2 of the paper verifies "an implementation of the quantum
-- Fourier transform", a circuit from Nielsen and Chuang "together with
-- a final qubit permutation correction", against the path-sum
--
--    QFT_n : |x⟩ ↦ 1/√2^n Σ_{y ∈ Z₂^n} e^{2πi [x·y]/2^n} |y⟩,
--
-- and reports verifying it with its reduction algorithm up to 31
-- qubits (beyond that its dyadic arithmetic overflows).  Here the
-- equivalence is a theorem for every n at once: QFT-≋ proves
-- ⟦ QFTC n ⟧ ≋ QFTˢ n whenever n + 1 ≤ M, and QFTC-matrix reads off
-- the unnormalised entries e^{2πi [x][z]/2^n} of the circuit's
-- matrix.  The proof is by induction on n, through the values of the
-- phase polynomial along each path; no instance is computed.
--
-- The plan, module by module:
--
--  1. PathSum.CRK.Trace.  A circuit's path-sum ⟦ C ⟧ (definition 2.9,
--     PathSum.CRK.Circuit) read one path at a time: along a path the
--     phase is an integer and every wire a bit, and trace runs the
--     circuit on that configuration.  How H allocates path variables
--     in run: each Hadamard allocates y₀ and every later one pushes
--     it one further, so the gate g of g ∷ C owns the bit norm C of
--     the path.  run-trace proves the correspondence for every state,
--     hence eval-⟦⟧ and outBit-⟦⟧ (the phase and outputs of ⟦ C ⟧ at a
--     path are the trace's) and amp-⟦⟧ (the amplitudes as a sum over
--     paths).  trace-++ and trace-map make it compositional, over
--     concatenation and over relabelling of wires by an injection.
--  2. PathSum.CRK.Controlled.  The controlled rotation CR k c t as the
--     subcircuit R_(k+1) c ; R_(k+1) t ; CNOT c t ; R_(k+1)† t ;
--     CNOT c t, whose trace adds 2^(M-k) x_c x_t and restores every
--     wire (trace-CR), and whose path-sum is the diagonal
--     |x⟩ ↦ e^{2πi x_c x_t/2^k} |x⟩ for any wires c ≠ t and any k
--     with k + 1 ≤ M (CR-≋).
--  3. PathSum.QFT.Spec.  QFTˢ n, the paper's specification built as
--     it says, [x] · [y] with [x] = x₁ + 2x₂ + … a polynomial
--     (numᴾ); its phase at a path is 2^(M-n) [x][y] (eval-QFTˢ) and
--     its matrix the Fourier matrix (QFTˢ-matrix).
--  4. PathSum.QFT.Circuit.  The circuit QFTC n: Hadamards and
--     controlled rotations (QFT₀ n), then the reversal of the wires
--     by SWAPs of three CNOTs each.  By induction on n its trace from
--     an input x along a path s has phase
--
--        Φ n x s = Σ_{j<n} s_j · 2^(M-j-1) · [x_0 … x_j]
--
--     and wire w holding s_(n-1-w) (trace-QFTC): the Hadamard of wire
--     j owns path bit j.  So the phase polynomial of ⟦ QFTC n ⟧ takes
--     the value Φ n x y at the path y, and output w reads y_(n-1-w)
--     (eval-QFTC, outBit-QFTC, here).
--  5. Here.  Modulo 2^M, Φ n x s is 2^(M-n) [x] [y] with y the path
--     read backwards, y_j = s_(n-1-j) (spec-Φ, by induction on n: the
--     terms x_i y_j with i + j ≥ n are integers and vanish).  So along
--     each path the circuit's path-sum and the specification agree
--     after reversing the order of the path variables -- the circuit's
--     first Hadamard owns the last variable -- and a sum over all
--     paths does not see that order (Σᴮ-opposite).  The number of path
--     variables of ⟦ QFTC n ⟧ is n only propositionally
--     (paths≡norm, norm-QFTC), which Σᴮ-str absorbs.
--
-- PathSum.Examples.QFT lists the gates of QFTC 3 (figure 5.1 of
-- Nielsen and Chuang, then the reversal) and instantiates the theorem
-- at the paper's two sizes, 16 and 31 qubits.  Around the theorem:
-- PathSum.QFT.Unitary shows the circuit and the specification unitary
-- (the latter exactly when n ≤ M); PathSum.QFT.Relabel reads the final
-- permutation as a relabelling of the outputs instead of SWAP gates,
-- and shows it cannot be left out; PathSum.QFT.Count counts path
-- variables and Clifford gates against the paper's table.
--
-- Departures from the paper.  The precision M (numerators over 2^M,
-- M = 3 + M₀) is fixed, where the paper's implementation uses dyadic
-- arithmetic; the circuit's gates go up to R_(n+1), so the theorem
-- asks n + 1 ≤ M.  The paper does not say how its controlled
-- rotations are built from its gate set {H, CNOT, R_k, R_k†}; here
-- they are the standard five-gate subcircuit.  Wire i carries the bit
-- of weight 2^i, the paper's x_(i+1).  And the equivalence is proved
-- through the amplitudes (definition 2.3), not by the rewriting of
-- figure 2 that the paper's tool runs: this is the statement the
-- tool checks, not a run of the tool.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.QFT (M₀ : ℕ) where

open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; inject₁; opposite)
open import Data.Integer.Base using (0ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣-refl; ∣m∣n⇒∣m+n; ∣m⇒∣m*n)
open import Data.Integer.Properties using (+-identityʳ; *-zeroʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _∸_; _≤_)
open import Data.Product.Base using (proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using ([_]ᶻ; same; same-≗)
open import PathSum.Base using (phase)
open import PathSum.Compose.Gates M₀ using (≋-amp)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.CRK.Circuit M using (paths; paths≡norm; ⟦_⟧; Rk-order)
open import PathSum.CRK.Controlled M₀ using (pow-half)
open import PathSum.CRK.Trace M₀ using
  (Stream; ≈φ; ≈v; trace; start; str; pathOf-str; pathAmp; eval-⟦⟧;
   outBit-⟦⟧; amp-⟦⟧; Σᴮ-str; Σᴮ-opposite)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; Σᴮ-cong; Respects; zpow; zpow-cong)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.Properties using (i∣0)
open import PathSum.QFT.Circuit M₀ using (QFTC; Φ; norm-QFTC; trace-QFTC)
open import PathSum.QFT.Spec M₀ using
  (bin; bin-≗; bin-top; QFTˢ; amp-QFTˢ; QFTˢ-matrix)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- The path-sum of the circuit, path by path

-- At the path y the phase polynomial of ⟦ QFTC n ⟧ takes the value
-- Φ n x y = Σ_{j<n} y_j · 2^(M-j-1) · [x_0 … x_j], and output w reads
-- y_(n-1-w) (read through the stream str y, since ⟦ QFTC n ⟧ has
-- paths (QFTC n) path variables, n only propositionally).

eval-QFTC : ∀ n → suc n ≤ M → (x : Assign n) (y : Assign (paths (QFTC n))) →
            eval (phase ⟦ QFTC n ⟧) x y ≡ Φ n x (str y)
eval-QFTC n le x y = trans (eval-⟦⟧ (QFTC n) x y)
                           (≈φ (trace-QFTC n le (str y) x))

outBit-QFTC : ∀ n → suc n ≤ M → (x : Assign n)
              (y : Assign (paths (QFTC n))) (w : Fin n) →
              outBit ⟦ QFTC n ⟧ x y w ≡ str y (toℕ (opposite w))
outBit-QFTC n le x y w = trans (outBit-⟦⟧ (QFTC n) x y w)
                               (≈v (trace-QFTC n le (str y) x) w)


------------------------------------------------------------------------
-- The phase modulo 2^M

-- A path read backwards: bit j is s_(n-1-j).

rev : Stream → Assign n
rev s j = s (toℕ (opposite j))

-- Peeling the top wire: the reversed path of n + 1 bits is s_n
-- followed by the reversed path of n bits.

private
  bin-rev : ∀ n (s : Stream) →
            bin (rev {suc n} s) ≡ [ s n ]ᶻ + (+ 2) * bin (rev {n} s)
  bin-rev n s = cong₂ (λ b e → [ b ]ᶻ + (+ 2) * e)
    (cong s (Fin.toℕ-fromℕ n))
    (bin-≗ {n = n} (λ i → cong s (Fin.toℕ-inject₁ (opposite i))))

-- Φ n x s ≡ 2^(M-n) [x] [rev s] modulo 2^M: the two differ by the
-- terms x_i y_j with i + j ≥ n, multiples of 2^M.

spec-Φ : ∀ n → n ≤ M → (x : Assign n) (s : Stream) →
         pow M ∣ (pow (M ∸ n) * (bin x * bin (rev {n} s)) - Φ n x s)
spec-Φ zero    le x s = Eq.subst (pow M ∣_)
  (sym (trans (+-identityʳ (pow M * 0ℤ)) (*-zeroʳ (pow M)))) i∣0
spec-Φ (suc n) le x s = Eq.subst (pow M ∣_) (sym split)
  (∣m∣n⇒∣m+n ih (Eq.subst (_∣ (((p * (+ 2)) * q) * (a * Y′))) whole
                          (∣m⇒∣m*n (a * Y′) (∣-refl {(p * (+ 2)) * q}))))
  where
  le′ = ℕ.<⇒≤ le
  p  = pow (M ∸ suc n)
  q  = pow n
  X′ = bin (λ i → x (inject₁ i))
  a  = [ x (fromℕ n) ]ᶻ
  b  = [ s n ]ᶻ
  Y′ = bin (rev {n} s)
  Φ′ = Φ n (λ i → x (inject₁ i)) s

  -- 2^(M-n) = 2 · 2^(M-n-1), and 2^(M-n) · 2^n = 2^M.

  half  = pow-half n le
  whole : (p * (+ 2)) * q ≡ pow M
  whole = trans (cong (_* q) (sym half)) (Rk-order le′)

  ih : pow M ∣ ((p * (+ 2)) * (X′ * Y′) - Φ′)
  ih = Eq.subst (λ c → pow M ∣ (c * (X′ * Y′) - Φ′)) half
                (spec-Φ n le′ (λ i → x (inject₁ i)) s)

  split : p * (bin x * bin (rev {suc n} s)) - Φ (suc n) x s ≡
          ((p * (+ 2)) * (X′ * Y′) - Φ′) + ((p * (+ 2)) * q) * (a * Y′)
  split = trans
    (cong₂ (λ u v → p * (u * v) - (b * (p * u) + Φ′))
           (bin-top x) (bin-rev n s))
    (solve 7 (λ p q X a b Y F →
       p :* ((X :+ q :* a) :* (b :+ con (+ 2) :* Y)) :-
       (b :* (p :* (X :+ q :* a)) :+ F) :=
       ((p :* con (+ 2)) :* (X :* Y) :- F) :+
       ((p :* con (+ 2)) :* q) :* (a :* Y))
     refl p q X′ a b Y′ Φ′)


------------------------------------------------------------------------
-- The circuit computes the specification

-- Path by path, after reading the path backwards; then summed.

amp-QFTC : ∀ n → suc n ≤ M → (x z : Assign n) →
           amp ⟦ QFTC n ⟧ x z ≐ amp (QFTˢ n) x z
amp-QFTC n le x z =
  amp-⟦⟧ (QFTC n) x z
  ∙ Σᴮ-str (trans (paths≡norm (QFTC n)) (norm-QFTC n)) (pathAmp (QFTC n) x z)
  ∙ Σᴮ-cong per-path
  ∙ Σᴮ-opposite F resp
  ∙ ≐-sym (amp-QFTˢ x z)
  where
  F : Assign n → Amp
  F y = if same y z then zpow (pow (M ∸ n) * (bin x * bin y)) else 0ᴬ

  resp : Respects F
  resp g h g≗h = if-cong
    (same-≗ {x = g} {x′ = h} {z = z} {z′ = z} g≗h (λ _ → refl))
    (zpow-≡ (cong (λ c → pow (M ∸ n) * (bin x * c)) (bin-≗ g≗h)))

  per-path : (y : Assign n) →
             pathAmp (QFTC n) x z (str y) ≐ F (λ i → y (opposite i))
  per-path y = if-cong
    (same-≗ {x = proj₂ (trace (QFTC n) (str y) (start x))}
            {x′ = λ i → y (opposite i)} {z = z} {z′ = z}
            (λ w → trans (≈v t w) (pathOf-str y (opposite w)))
            (λ _ → refl))
    (λ i → trans (zpow-≡ (≈φ t) i)
                 (sym (zpow-cong {e} {Φ n x (str y)} congr i)))
    where
    t = trace-QFTC n le (str y) x
    e = pow (M ∸ n) * (bin x * bin (λ i → y (opposite i)))

    congr : pow M ∣ (e - Φ n x (str y))
    congr = Eq.subst
      (λ c → pow M ∣ (pow (M ∸ n) * (bin x * c) - Φ n x (str y)))
      (bin-≗ {n = n} (λ i → pathOf-str y (opposite i)))
      (spec-Φ n (ℕ.<⇒≤ le) x (str y))

-- Section 5.2: the circuit is equivalent to the specification.

QFT-≋ : ∀ n → suc n ≤ M → ⟦ QFTC n ⟧ ≋ QFTˢ n
QFT-≋ n le = ≋-amp ⟦ QFTC n ⟧ (QFTˢ n) (norm-QFTC n) (amp-QFTC n le)

-- Its matrix, unnormalised: e^{2πi [x][z]/2^n} from x to z.

QFTC-matrix : ∀ n → suc n ≤ M → (x z : Assign n) →
              amp ⟦ QFTC n ⟧ x z ≐ zpow (pow (M ∸ n) * (bin x * bin z))
QFTC-matrix n le x z = amp-QFTC n le x z ∙ QFTˢ-matrix x z
