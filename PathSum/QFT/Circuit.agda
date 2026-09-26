------------------------------------------------------------------------
-- Presentations of groups
--
-- The circuit for the quantum Fourier transform (Amy, QPL 2018,
-- section 5.2), and its trace along a path
--
-- Section 5.2 verifies "a circuit from [20]" -- Nielsen and Chuang,
-- figure 5.1 -- "together with a final qubit permutation correction".
-- On n wires, wire i holding the bit of weight 2^i, that circuit is:
--
--    for each wire j, from the top wire n-1 down to wire 0: a
--    Hadamard on j, then the controlled rotations CR_2, ..., CR_(j+1)
--    onto j from the wires j-1, ..., 0 below it; then the wires
--    reversed, by SWAPs of wires i and n-1-i.
--
-- Here: rotations n puts the rotations onto the top wire n of n + 1
-- wires, nearest control first (CR_2 from wire n-1, ..., CR_(n+1) from
-- wire 0), each a PathSum.CRK.Controlled.CR subcircuit; QFT₀ n is the
-- circuit without the reversal, recursively a Hadamard and the
-- rotations on the top wire followed by QFT₀ (n-1) on the wires below
-- (mapC inject₁); reversal n swaps the outer pair and recurses inside,
-- which is the SWAPs (0, n-1), (1, n-2), ... in that order, each
-- SWAP three CNOTs; and QFTC n = QFT₀ n ++ reversal n.  The gates are
-- R_(k+1) for k up to n, so the circuit needs precision n + 1 ≤ M.
--
-- The trace (PathSum.CRK.Trace) of each piece, along any path:
--
--  * trace-SWAP: SWAP a b exchanges the bits on a and b.
--  * trace-reversal: reversal n reads wire w off wire n-1-w.
--  * trace-rotations: onto the top wire t the rotations add
--    v_t · 2^(M-n-1) · [v_0 … v_(n-1)] to the phase (the bits below t
--    read as an integer), and change no wire.
--  * trace-QFT₀: the Hadamard of wire j owns the path bit s_j (its
--    variable is y_j of ⟦ QFT₀ n ⟧: the top wire's Hadamard comes
--    first, so its variable is pushed furthest), leaves s_j on the
--    wire, and with the rotations adds s_j · 2^(M-j-1) · [v_0 … v_j],
--    so the phase is
--
--        Φ n v s = Σ_{j<n} s_j · 2^(M-j-1) · [v_0 … v_j]
--
--    and wire j ends holding s_j.
--  * trace-QFTC: the same phase, and wire w ends holding s_(n-1-w).
--
-- So the path-sum ⟦ QFTC n ⟧ has phase Φ n x y at every path y
-- (PathSum.CRK.Trace.eval-⟦⟧) and outputs y_(n-1-w): the order of its
-- path variables is the reverse of the specification's, which
-- PathSum.QFT deals with by renumbering the sum (Σᴮ-opposite).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.QFT.Circuit (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Fin.Base using
  (Fin; zero; suc; toℕ; fromℕ; inject₁; opposite)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _+_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-zeroʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (zero; suc; _∸_; _≤_; s≤s; z≤n)
  renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-cong; ≔-comm; ≔-≔)
open import PathSum.CRK.Circuit M using
  (Circuit; H; CNOT; norm; Rk-primitive)
open import PathSum.CRK.Controlled M₀ using (CR; trace-CR; pow-half; bit-*)
open import PathSum.CRK.Trace M₀ using
  (Stream; _≈ᶜ_; conf≈; ≈φ; ≈v; ≈ᶜ-refl; ≈ᶜ-trans; ≔-cong₂; trace;
   trace-cong; start; norm-++; shift; trace-++; Injective; mapC;
   norm-map; pull; pull-cong; trace-map; trace-map-off)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Order M using (pow)
open import PathSum.QFT.Spec M₀ using (bin; bin-≗; bin-top)
open import PathSum.Reduction M using (½)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The circuit

-- SWAP as three CNOTs.

SWAP : (a b : Fin n) → a ≢ b → Circuit n
SWAP a b a≢b = CNOT a b a≢b ∷ CNOT b a (λ eq → a≢b (sym eq)) ∷ CNOT a b a≢b ∷ []

-- The controlled rotations onto the top wire n of n + 1 wires: CR_2
-- from wire n-1 first, CR_(n+1) from wire 0 last.

rotations : (n : ℕ) → Circuit (suc n)
rotations zero    = []
rotations (suc n) =
  mapC suc Fin.suc-injective (rotations n) ++
  CR (suc (suc n)) zero (fromℕ (suc n)) (λ ())

-- The transform with its output in reverse order: the top wire's
-- Hadamard and rotations, then the same on the wires below.

QFT₀ : (n : ℕ) → Circuit n
QFT₀ zero    = []
QFT₀ (suc n) =
  H (fromℕ n) ∷ rotations n ++ mapC inject₁ Fin.inject₁-injective (QFT₀ n)

-- The wires below the top and above the bottom.

inner : Fin n → Fin (suc (suc n))
inner i = suc (inject₁ i)

inner-injective : Injective (inner {n})
inner-injective eq = Fin.inject₁-injective (Fin.suc-injective eq)

-- The reversal of the wires: swap the outer pair, reverse the inside.

reversal : (n : ℕ) → Circuit n
reversal zero          = []
reversal (suc zero)    = []
reversal (suc (suc n)) =
  SWAP zero (fromℕ (suc n)) (λ ()) ++
  mapC inner inner-injective (reversal n)

-- The circuit of section 5.2.

QFTC : (n : ℕ) → Circuit n
QFTC n = QFT₀ n ++ reversal n


------------------------------------------------------------------------
-- Hadamards

-- One Hadamard for each wire, none in the rotations or the reversal.

norm-rotations : ∀ n → norm (rotations n) ≡ 0
norm-rotations zero    = refl
norm-rotations (suc n) = trans
  (norm-++ (mapC suc Fin.suc-injective (rotations n))
           (CR (suc (suc n)) zero (fromℕ (suc n)) (λ ())))
  (trans (ℕ.+-identityʳ _)
    (trans (norm-map suc Fin.suc-injective (rotations n))
           (norm-rotations n)))

norm-QFT₀ : ∀ n → norm (QFT₀ n) ≡ n
norm-QFT₀ zero    = refl
norm-QFT₀ (suc n) = cong suc (trans
  (norm-++ (rotations n) (mapC inject₁ Fin.inject₁-injective (QFT₀ n)))
  (cong₂ _ℕ+_ (norm-rotations n)
    (trans (norm-map inject₁ Fin.inject₁-injective (QFT₀ n))
           (norm-QFT₀ n))))

norm-reversal : ∀ n → norm (reversal n) ≡ 0
norm-reversal zero          = refl
norm-reversal (suc zero)    = refl
norm-reversal (suc (suc n)) =
  trans (norm-map inner inner-injective (reversal n)) (norm-reversal n)

norm-QFTC : ∀ n → norm (QFTC n) ≡ n
norm-QFTC n = trans (norm-++ (QFT₀ n) (reversal n))
  (trans (cong₂ _ℕ+_ (norm-QFT₀ n) (norm-reversal n)) (ℕ.+-identityʳ n))


------------------------------------------------------------------------
-- Fin: the top and the rest

-- Every wire of n + 1 is the top one or one of the n below.

data Top : ∀ {n} → Fin (suc n) → Set where
  top : ∀ {n} → Top (fromℕ n)
  low : ∀ {n} (w : Fin n) → Top (inject₁ w)

top? : ∀ {n} (u : Fin (suc n)) → Top u
top? {zero}  zero    = top
top? {suc n} zero    = low zero
top? {suc n} (suc u) = up (top? u)
  where
  up : ∀ {u} → Top {n} u → Top (suc u)
  up top     = top
  up (low w) = low (suc w)

inject₁≢fromℕ : (w : Fin n) → inject₁ w ≢ fromℕ n
inject₁≢fromℕ w eq = Fin.fromℕ≢inject₁ (sym eq)

-- Reversing the wires: the bottom goes to the top, one below the top
-- goes one above the bottom.

opposite-fromℕ : ∀ n → opposite (fromℕ n) ≡ zero
opposite-fromℕ zero    = refl
opposite-fromℕ (suc n) = cong inject₁ (opposite-fromℕ n)

opposite-inject₁ : (i : Fin n) → opposite (inject₁ i) ≡ suc (opposite i)
opposite-inject₁ {suc n} zero    = refl
opposite-inject₁ {suc n} (suc i) = cong inject₁ (opposite-inject₁ i)


------------------------------------------------------------------------
-- The trace of a SWAP

private
  xor-back : ∀ p q → p xor (q xor p) ≡ q
  xor-back false false = refl
  xor-back false true  = refl
  xor-back true  false = refl
  xor-back true  true  = refl

  xor-back′ : ∀ p q → (q xor p) xor (p xor (q xor p)) ≡ p
  xor-back′ false false = refl
  xor-back′ false true  = refl
  xor-back′ true  false = refl
  xor-back′ true  true  = refl

trace-SWAP : (a b : Fin n) (a≢b : a ≢ b) (s : Stream) (φ : ℤ)
             (v : Assign n) →
             trace (SWAP a b a≢b) s (φ , v) ≈ᶜ
             (φ , (v [ a ≔ v b ]) [ b ≔ v a ])
trace-SWAP a b a≢b s φ v = conf≈ refl (λ u → trans
  (≔-cong₂ {z = v₂} {z′ = v₁ [ a ≔ v b ]} b e₃
    (≔-cong₂ {z = v₁} {z′ = v₁} a e₂ (λ _ → refl)) u)
  (trans (≔-cong {z = v₁ [ a ≔ v b ]} {z′ = (v [ a ≔ v b ]) [ b ≔ e₁ ]}
                 b (v a) (≔-comm v e₁ (v b) b≢a) u)
         (≔-≔ (v [ a ≔ v b ]) b e₁ (v a) u)))
  where
  b≢a : b ≢ a
  b≢a eq = a≢b (sym eq)

  e₁ = v b xor v a
  v₁ = v [ b ≔ e₁ ]
  v₂ = v₁ [ a ≔ v₁ a xor v₁ b ]

  e₂ : v₁ a xor v₁ b ≡ v b
  e₂ = trans (cong₂ _xor_ (≔-there v e₁ a≢b) (≔-here v b e₁))
             (xor-back (v a) (v b))

  e₃ : v₂ b xor v₂ a ≡ v a
  e₃ = trans (cong₂ _xor_ (trans (≔-there v₁ (v₁ a xor v₁ b) b≢a)
                                 (≔-here v b e₁))
                          (trans (≔-here v₁ a (v₁ a xor v₁ b))
                                 (cong₂ _xor_ (≔-there v e₁ a≢b)
                                              (≔-here v b e₁))))
             (xor-back′ (v a) (v b))


------------------------------------------------------------------------
-- The trace of the reversal

trace-reversal : ∀ n (s : Stream) (φ : ℤ) (v : Assign n) →
                 trace (reversal n) s (φ , v) ≈ᶜ (φ , (λ w → v (opposite w)))
trace-reversal zero          s φ v = conf≈ refl (λ ())
trace-reversal (suc zero)    s φ v = conf≈ refl (λ { zero → refl })
trace-reversal (suc (suc n)) s φ v =
  ≈ᶜ-trans (trace-++ sw D s (φ , v)) (conf≈ (≈φ inner≈) wire)
  where
  t  = fromℕ (suc n)
  sw = SWAP zero t (λ ())
  D  = mapC inner inner-injective (reversal n)
  a₁ = trace sw (shift (norm D) s) (φ , v)
  v′ = (v [ zero ≔ v t ]) [ t ≔ v zero ]

  a₁≈ : a₁ ≈ᶜ (φ , v′)
  a₁≈ = trace-SWAP zero t (λ ()) (shift (norm D) s) φ v

  -- The inside, through the relabelling.

  inner≈ : pull inner (trace D s a₁) ≈ᶜ (φ , (λ w → v′ (inner (opposite w))))
  inner≈ = ≈ᶜ-trans (trace-map inner inner-injective (reversal n) s a₁)
    (≈ᶜ-trans (trace-cong (reversal n) (λ _ → refl) (pull-cong inner a₁≈))
              (trace-reversal n s φ (λ w → v′ (inner w))))

  -- The swap is not undone by the inside.

  v′-inner : ∀ w → v′ (inner w) ≡ v (inner w)
  v′-inner w = trans (≔-there (v [ zero ≔ v t ]) (v zero)
                        (λ eq → inject₁≢fromℕ w (Fin.suc-injective eq)))
                     (≔-there v {zero} {inner w} (v t) (λ ()))

  off : ∀ u → (∀ w → inner w ≢ u) →
        proj₂ (trace D s a₁) u ≡ v′ u
  off u o = trans (trace-map-off inner inner-injective (reversal n) s a₁ u o)
                  (≈v a₁≈ u)

  wire-suc : ∀ u → Top u → proj₂ (trace D s a₁) (suc u) ≡ v (opposite (suc u))
  wire-suc _ top     = trans
    (off t (λ w eq → inject₁≢fromℕ w (Fin.suc-injective eq)))
    (trans (≔-here (v [ zero ≔ v t ]) t (v zero))
           (cong (λ i → v (inject₁ i)) (sym (opposite-fromℕ n))))
  wire-suc _ (low w) = trans (≈v inner≈ w)
    (trans (v′-inner (opposite w))
           (cong (λ i → v (inject₁ i)) (sym (opposite-inject₁ w))))

  wire : ∀ u → proj₂ (trace D s a₁) u ≡ v (opposite u)
  wire zero    = trans (off zero (λ w ()))
    (trans (≔-there (v [ zero ≔ v t ]) {t} {zero} (v zero) (λ ()))
           (≔-here v zero (v t)))
  wire (suc u) = wire-suc u (top? u)


------------------------------------------------------------------------
-- The trace of the rotations

-- Onto the top wire t they add v_t · 2^(M-n-1) · [v_0 … v_(n-1)].

trace-rotations : ∀ n → suc (suc n) ≤ M → (s : Stream) (φ : ℤ)
                  (v : Assign (suc n)) →
                  trace (rotations n) s (φ , v) ≈ᶜ
                  (φ + [ v (fromℕ n) ]ᶻ *
                         (pow (M ∸ suc n) * bin (λ i → v (inject₁ i)))
                  , v)
trace-rotations zero    le s φ v = conf≈
  (sym (trans (cong (λ e → φ + e)
                    (trans (cong ([ v zero ]ᶻ *_) (*-zeroʳ (pow (M ∸ 1))))
                           (*-zeroʳ [ v zero ]ᶻ)))
              (+-identityʳ φ)))
  (λ _ → refl)
trace-rotations (suc n) le s φ v =
  ≈ᶜ-trans (trace-++ Rn cr s (φ , v))
    (≈ᶜ-trans (trace-cong cr {s} {s} (λ _ → refl) a₁≈)
      (≈ᶜ-trans (trace-CR (suc (suc n)) le zero t (λ ()) s φ₁ v)
                (conf≈ arith (λ _ → refl))))
  where
  t  = fromℕ (suc n)
  Rn = mapC suc Fin.suc-injective (rotations n)
  cr = CR (suc (suc n)) zero t (λ ())
  s′ = shift 0 s
  le′ = ℕ.<⇒≤ le

  B  = bin (λ i → v (suc (inject₁ i)))
  p′ = pow (M ∸ suc (suc n))
  φ₁ = φ + [ v t ]ᶻ * (pow (M ∸ suc n) * B)

  ih = trace-rotations n le′ s′ φ (λ i → v (suc i))
  mp = trace-map suc Fin.suc-injective (rotations n) s′ (φ , v)

  a₁≈ : trace Rn s′ (φ , v) ≈ᶜ (φ₁ , v)
  a₁≈ = conf≈ (trans (≈φ mp) (≈φ ih)) wire
    where
    wire : ∀ u → proj₂ (trace Rn s′ (φ , v)) u ≡ v u
    wire zero    = trace-map-off suc Fin.suc-injective (rotations n) s′
                                 (φ , v) zero (λ w ())
    wire (suc u) = trans (≈v mp u) (≈v ih u)

  arith : φ₁ + p′ * [ v zero ∧ v t ]ᶻ ≡
          φ + [ v t ]ᶻ * (p′ * bin (λ i → v (inject₁ i)))
  arith = trans
    (cong₂ (λ q r → (φ + [ v t ]ᶻ * (q * B)) + p′ * r)
           (pow-half (suc n) le′) (sym (bit-* (v zero) (v t))))
    (solve 5 (λ φ c p a b →
       (φ :+ c :* ((p :* con (+ 2)) :* b)) :+ p :* (a :* c) :=
       φ :+ c :* (p :* (a :+ con (+ 2) :* b)))
     refl φ [ v t ]ᶻ p′ [ v zero ]ᶻ B)


------------------------------------------------------------------------
-- The trace of the transform without its reversal

-- The phase along the path s, from wire values v.

Φ : (n : ℕ) → Assign n → Stream → ℤ
Φ zero    v s = 0ℤ
Φ (suc n) v s =
  [ s n ]ᶻ * (pow (M ∸ suc n) * bin v) + Φ n (λ i → v (inject₁ i)) s

trace-QFT₀ : ∀ n → suc n ≤ M → (s : Stream) (φ : ℤ) (v : Assign n) →
             trace (QFT₀ n) s (φ , v) ≈ᶜ (φ + Φ n v s , (λ w → s (toℕ w)))
trace-QFT₀ zero    le s φ v = conf≈ (sym (+-identityʳ φ)) (λ ())
trace-QFT₀ (suc n) le s φ v =
  ≈ᶜ-trans (trace-++ (H t ∷ rotations n) D s (φ , v))
           (conf≈ (trans (≈φ lowᶜ) arith) wire)
  where
  t  = fromℕ n
  D  = mapC inject₁ Fin.inject₁-injective (QFT₀ n)
  s′ = shift (norm D) s
  le′ = ℕ.<⇒≤ le

  -- The top wire's Hadamard reads the path bit s_n.

  b  = s′ (norm (rotations n))

  b≡ : b ≡ s n
  b≡ = cong s (cong₂ _ℕ+_ (norm-rotations n)
    (trans (norm-map inject₁ Fin.inject₁-injective (QFT₀ n)) (norm-QFT₀ n)))

  vb = v [ t ≔ b ]
  B  = bin (λ i → v (inject₁ i))
  p  = pow (M ∸ suc n)
  φ₁ = (φ + ½ * [ v t ∧ b ]ᶻ) + [ b ]ᶻ * (p * B)

  a₁ = trace (H t ∷ rotations n) s′ (φ , v)

  below : ∀ i → vb (inject₁ i) ≡ v (inject₁ i)
  below i = ≔-there v b (inject₁≢fromℕ i)

  a₁≈ : a₁ ≈ᶜ (φ₁ , vb)
  a₁≈ = ≈ᶜ-trans (trace-rotations n le s′ (φ + ½ * [ v t ∧ b ]ᶻ) vb)
    (conf≈ (cong₂ (λ c d → (φ + ½ * [ v t ∧ b ]ᶻ) + [ c ]ᶻ * (p * d))
                  (≔-here v t b) (bin-≗ below))
           (λ _ → refl))

  -- The wires below run QFT₀ n.

  lowᶜ : pull inject₁ (trace D s a₁) ≈ᶜ
         (φ₁ + Φ n (λ i → v (inject₁ i)) s , (λ w → s (toℕ w)))
  lowᶜ = ≈ᶜ-trans (trace-map inject₁ Fin.inject₁-injective (QFT₀ n) s a₁)
    (≈ᶜ-trans (trace-cong (QFT₀ n) (λ _ → refl)
                (≈ᶜ-trans (pull-cong inject₁ a₁≈) (conf≈ refl below)))
              (trace-QFT₀ n le′ s φ₁ (λ i → v (inject₁ i))))

  -- ½ is 2^(M-n-1) · 2^n, and [v] is [v_0 … v_(n-1)] + 2^n v_n.

  arith : φ₁ + Φ n (λ i → v (inject₁ i)) s ≡ φ + Φ (suc n) v s
  arith = trans
    (cong₂ (λ h e → ((φ + h * e) + [ b ]ᶻ * (p * B)) +
                    Φ n (λ i → v (inject₁ i)) s)
           (sym (Rk-primitive (s≤s z≤n) le′))
           (sym (bit-* (v t) b)))
    (trans (solve 7 (λ φ p q a c B Φ′ →
              ((φ :+ (p :* q) :* (a :* c)) :+ c :* (p :* B)) :+ Φ′ :=
              φ :+ (c :* (p :* (B :+ q :* a)) :+ Φ′))
            refl φ p (pow n) [ v t ]ᶻ [ b ]ᶻ B
                 (Φ n (λ i → v (inject₁ i)) s))
      (cong₂ (λ c e → φ + ([ c ]ᶻ * (p * e) + Φ n (λ i → v (inject₁ i)) s))
             b≡ (sym (bin-top v))))

  wire : ∀ u → proj₂ (trace D s a₁) u ≡ s (toℕ u)
  wire u = go u (top? u)
    where
    go : ∀ u → Top u → proj₂ (trace D s a₁) u ≡ s (toℕ u)
    go _ top     = trans
      (trace-map-off inject₁ Fin.inject₁-injective (QFT₀ n) s a₁ t
                     (λ w eq → inject₁≢fromℕ w eq))
      (trans (≈v a₁≈ t)
        (trans (≔-here v t b) (trans b≡ (cong s (sym (Fin.toℕ-fromℕ n))))))
    go _ (low w) = trans (≈v lowᶜ w) (cong s (sym (Fin.toℕ-inject₁ w)))


------------------------------------------------------------------------
-- The trace of the whole circuit

-- From the input x: the phase Φ n x s, and wire w holding s_(n-1-w).

trace-QFTC : ∀ n → suc n ≤ M → (s : Stream) (x : Assign n) →
             trace (QFTC n) s (start x) ≈ᶜ
             (Φ n x s , (λ w → s (toℕ (opposite w))))
trace-QFTC n le s x =
  ≈ᶜ-trans (trace-++ (QFT₀ n) (reversal n) s (start x))
    (≈ᶜ-trans (trace-cong (reversal n) (λ _ → refl)
                (≈ᶜ-trans (trace-cong (QFT₀ n) shift≗ (≈ᶜ-refl {a = start x}))
                          (trace-QFT₀ n le s 0ℤ x)))
      (≈ᶜ-trans (trace-reversal n s (0ℤ + Φ n x s) (λ w → s (toℕ w)))
                (conf≈ (+-identityˡ (Φ n x s)) (λ _ → refl))))
  where
  shift≗ : ∀ i → shift (norm (reversal n)) s i ≡ s i
  shift≗ i = cong s (trans (cong (i ℕ+_) (norm-reversal n)) (ℕ.+-identityʳ i))
