------------------------------------------------------------------------
-- Presentations of groups
--
-- Character sums over Z₂^k, and the Walsh transform of a
-- Maiorana-McFarland bent function
--
-- Section 5.2 of Amy's "Towards Large-scale Functional Verification of
-- Universal Quantum Circuits" (QPL 2018) verifies the quantum hidden
-- shift algorithm for the Maiorana-McFarland bent functions on 2m bits,
--
--    f(x, y) = (-1)^{g(x) + x·y},   dual  f̃(x, y) = (-1)^{g(y) + x·y},
--
-- g any Boolean function on m bits.  Why the algorithm works is two
-- facts about sums of signs over Z₂^k, and this module proves them
-- over the integers, with no path-sum in sight; PathSum.HiddenShift
-- carries them to the amplitudes of the circuit.
--
-- * Orthogonality of characters (character): Σ_v (-1)^{v·c} is 2^k
--   when c = 0 and 0 otherwise.  By induction on k: the head bit of c
--   either doubles the sum over the tail or, being 1, pairs every v
--   with its negation.  In Z[ζ] this is where ζ^H = -1 makes the
--   destructive interference.
--
-- * The Walsh transform of f is 2^m f̃ (walsh-mm): for every c,
--
--      Σ_u (-1)^{f(u) + u·c} = 2^m (-1)^{f̃(c)}.
--
--   This is the duality the paper takes from its references, checked
--   here rather than assumed.  Write u = (a, b) and c = (c₁, c₂); the
--   exponent is g(a) + a·c₁ + b·(a + c₂), so the sum over b is 2^m when
--   a = c₂ and 0 otherwise, which leaves 2^m (-1)^{g(c₂) + c₂·c₁}.
--   Shifting the argument by s multiplies the transform by the
--   character of s (walsh-mm-shift), the sum being invariant under
--   translation (Σᶻ-shift).
--
-- Sums are PathSum.AssignSum's Σᶻ.  Assignments are plain functions,
-- equal only pointwise; the concatenation a ⧺ b is built bit by bit
-- exactly as Σᶻ builds its assignments, so that splitting a sum over
-- 2m bits into a double sum over m and m (Σᶻ-⧺) needs no hypothesis,
-- while g, an arbitrary function, is asked to read its argument only
-- through its values (RespectsB).  Signs are PathSum.Polynomial.sgn,
-- sgn true = -1.
--
-- The package.  This module is the combinatorics over the integers.
-- PathSum.HiddenShift.Sign turns the powers ζ^(½ v) of the circuit into
-- signs, so that a column of integers stands for a column of
-- amplitudes; PathSum.HiddenShift defines the path-sums -- Hadamard
-- layer, oracles, the composite -- and computes the composite's column
-- at 0 layer by layer, by proposition 2.7, with the two sums here;
-- PathSum.HiddenShift.Simulation reads the result as a statement about
-- the rewrite rules of figure 2, which cannot reduce the circuit on
-- |0⟩ to anything but |x⟩ ↦ |s⟩; and PathSum.HiddenShift.Example
-- carries out one such reduction.  Everything is parametric in m, g
-- and s except the example.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.HiddenShift.Walsh where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using
  (xor-assoc; xor-comm; ∧-comm; ∧-distribˡ-xor)
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _*_)
open import Data.Integer.Properties using
  (*-comm; *-assoc; *-zeroʳ; +-comm; +-identityʳ)
open import Data.Nat.Base using (ℕ; zero; suc)
  renaming (_+_ to _ℕ+_; _^_ to _ℕ^_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

import Data.Nat.Properties as ℕ

open import PathSum.Assign using (same; same-refl; same-≗)
open import PathSum.AssignSum using
  (Σᶻ; Σᶻ-zero; Σᶻ-suc; Σᶻ-cong; Σᶻ-+; Σᶻ-*; Σᶻ-0; Σᶻ-point; RespectsZ;
   _∷ᵃ_)
open import PathSum.Polynomial using (sgn)

private
  variable
    k l : ℕ


------------------------------------------------------------------------
-- Assignments

-- The all-false assignment and the pointwise sum.

0ᵃ : Fin k → Bool
0ᵃ _ = false

infixl 6 _⊕ᵃ_

_⊕ᵃ_ : (Fin k → Bool) → (Fin k → Bool) → (Fin k → Bool)
(u ⊕ᵃ v) i = u i xor v i

-- Concatenation, bit by bit with AssignSum's _∷ᵃ_.

infixr 5 _⧺_

_⧺_ : (Fin k → Bool) → (Fin l → Bool) → (Fin (k ℕ+ l) → Bool)
_⧺_ {zero}  a b = b
_⧺_ {suc k} a b = a zero ∷ᵃ ((λ i → a (suc i)) ⧺ b)

-- Reading either block back, and every assignment as its two blocks.

⧺-↑ˡ : (a : Fin k → Bool) (b : Fin l → Bool) (i : Fin k) →
       (a ⧺ b) (i ↑ˡ l) ≡ a i
⧺-↑ˡ a b zero    = refl
⧺-↑ˡ a b (suc i) = ⧺-↑ˡ (λ j → a (suc j)) b i

⧺-↑ʳ : (a : Fin k → Bool) (b : Fin l → Bool) (i : Fin l) →
       (a ⧺ b) (k ↑ʳ i) ≡ b i
⧺-↑ʳ {zero}  a b i = refl
⧺-↑ʳ {suc k} a b i = ⧺-↑ʳ (λ j → a (suc j)) b i

⧺-split : ∀ k l (x : Fin (k ℕ+ l) → Bool) (j : Fin (k ℕ+ l)) →
          ((λ i → x (i ↑ˡ l)) ⧺ (λ i → x (k ↑ʳ i))) j ≡ x j
⧺-split zero    l x j       = refl
⧺-split (suc k) l x zero    = refl
⧺-split (suc k) l x (suc j) = ⧺-split k l (λ i → x (suc i)) j

-- The two halves of an assignment to 2m bits.

lhalf rhalf : ∀ {m} → (Fin (m ℕ+ m) → Bool) → (Fin m → Bool)
lhalf {m} u i = u (i ↑ˡ m)
rhalf {m} u i = u (m ↑ʳ i)

-- A Boolean function of an assignment that reads only its values.

RespectsB : ((Fin k → Bool) → Bool) → Set
RespectsB f = ∀ u v → (∀ i → u i ≡ v i) → f u ≡ f v


------------------------------------------------------------------------
-- The inner product over Z₂

dot : (Fin k → Bool) → (Fin k → Bool) → Bool
dot {zero}  u v = false
dot {suc k} u v =
  (u zero ∧ v zero) xor dot (λ i → u (suc i)) (λ i → v (suc i))

dot-cong : {u u′ v v′ : Fin k → Bool} → (∀ i → u i ≡ u′ i) →
           (∀ i → v i ≡ v′ i) → dot u v ≡ dot u′ v′
dot-cong {zero}  hu hv = refl
dot-cong {suc k} hu hv = cong₂ _xor_ (cong₂ _∧_ (hu zero) (hv zero))
  (dot-cong (λ i → hu (suc i)) (λ i → hv (suc i)))

dot-comm : (u v : Fin k → Bool) → dot u v ≡ dot v u
dot-comm {zero}  u v = refl
dot-comm {suc k} u v = cong₂ _xor_ (∧-comm (u zero) (v zero))
  (dot-comm (λ i → u (suc i)) (λ i → v (suc i)))

dot-0ˡ : (v : Fin k → Bool) → dot 0ᵃ v ≡ false
dot-0ˡ {zero}  v = refl
dot-0ˡ {suc k} v = dot-0ˡ (λ i → v (suc i))

-- Four bits added in two orders.

xor-medial : ∀ p q r t → (p xor q) xor (r xor t) ≡ (p xor r) xor (q xor t)
xor-medial false false false false = refl
xor-medial false false false true  = refl
xor-medial false false true  false = refl
xor-medial false false true  true  = refl
xor-medial false true  false false = refl
xor-medial false true  false true  = refl
xor-medial false true  true  false = refl
xor-medial false true  true  true  = refl
xor-medial true  false false false = refl
xor-medial true  false false true  = refl
xor-medial true  false true  false = refl
xor-medial true  false true  true  = refl
xor-medial true  true  false false = refl
xor-medial true  true  false true  = refl
xor-medial true  true  true  false = refl
xor-medial true  true  true  true  = refl

-- The inner product is bilinear, and splits over concatenations.

dot-⊕ʳ : (u v w : Fin k → Bool) → dot u (v ⊕ᵃ w) ≡ dot u v xor dot u w
dot-⊕ʳ {zero}  u v w = refl
dot-⊕ʳ {suc k} u v w = trans
  (cong₂ _xor_ (∧-distribˡ-xor (u zero) (v zero) (w zero))
               (dot-⊕ʳ (λ i → u (suc i)) (λ i → v (suc i)) (λ i → w (suc i))))
  (xor-medial (u zero ∧ v zero) (u zero ∧ w zero)
    (dot (λ i → u (suc i)) (λ i → v (suc i)))
    (dot (λ i → u (suc i)) (λ i → w (suc i))))

dot-⊕ˡ : (u v w : Fin k → Bool) → dot (u ⊕ᵃ v) w ≡ dot u w xor dot v w
dot-⊕ˡ u v w = trans (dot-comm (u ⊕ᵃ v) w)
  (trans (dot-⊕ʳ w u v) (cong₂ _xor_ (dot-comm w u) (dot-comm w v)))

dot-⧺ : (a c : Fin k → Bool) (b d : Fin l → Bool) →
        dot (a ⧺ b) (c ⧺ d) ≡ dot a c xor dot b d
dot-⧺ {zero}  a c b d = refl
dot-⧺ {suc k} a c b d = trans
  (cong ((a zero ∧ c zero) xor_)
        (dot-⧺ (λ i → a (suc i)) (λ i → c (suc i)) b d))
  (sym (xor-assoc (a zero ∧ c zero)
                  (dot (λ i → a (suc i)) (λ i → c (suc i))) (dot b d)))


------------------------------------------------------------------------
-- Signs

sgn-xor : ∀ a b → sgn (a xor b) ≡ sgn a * sgn b
sgn-xor false false = refl
sgn-xor false true  = refl
sgn-xor true  false = refl
sgn-xor true  true  = refl

sgn-cancel : ∀ b → sgn b + sgn (not b) ≡ 0ℤ
sgn-cancel false = refl
sgn-cancel true  = refl

sgn-sq : ∀ b → sgn b * sgn b ≡ 1ℤ
sgn-sq false = refl
sgn-sq true  = refl

-- sgn a · sgn (a + b) = sgn b.

sgn-absorb : ∀ a b → sgn a * sgn (a xor b) ≡ sgn b
sgn-absorb false false = refl
sgn-absorb false true  = refl
sgn-absorb true  false = refl
sgn-absorb true  true  = refl


------------------------------------------------------------------------
-- Sums over assignments

-- A sum over k + l bits is a double sum, with no hypothesis on the
-- summand: the assignments on both sides are built the same way.

Σᶻ-⧺ : ∀ k l (f : (Fin (k ℕ+ l) → Bool) → ℤ) →
       Σᶻ f ≡ Σᶻ {k} (λ a → Σᶻ {l} (λ b → f (a ⧺ b)))
Σᶻ-⧺ zero    l f = sym (Σᶻ-zero (λ a → Σᶻ (λ b → f (a ⧺ b))))
Σᶻ-⧺ (suc k) l f = trans (Σᶻ-suc f)
  (trans (cong₂ _+_ (Σᶻ-⧺ k l (λ g → f (false ∷ᵃ g)))
                    (Σᶻ-⧺ k l (λ g → f (true ∷ᵃ g))))
         (sym (Σᶻ-suc (λ a → Σᶻ (λ b → f (a ⧺ b))))))

-- A delta collapses a sum.

Σᶻ-δ : (u : Fin k → Bool) (F : (Fin k → Bool) → ℤ) → RespectsZ F →
       Σᶻ (λ v → if same u v then F v else 0ℤ) ≡ F u
Σᶻ-δ u F resp = begin
  Σᶻ f
    ≡⟨ Σᶻ-point f resp′ u ⟩
  f u + Σᶻ (λ z → if same u z then 0ℤ else f z)
    ≡⟨ cong₂ _+_ here (trans (Σᶻ-cong (λ z → rest (same u z) (F z))) Σᶻ-0) ⟩
  F u + 0ℤ
    ≡⟨ +-identityʳ (F u) ⟩
  F u
    ∎
  where
  open ≡-Reasoning

  f : (Fin _ → Bool) → ℤ
  f v = if same u v then F v else 0ℤ

  resp′ : RespectsZ f
  resp′ g h g≗h = cong₂ (λ b w → if b then w else 0ℤ)
    (same-≗ (λ _ → refl) g≗h) (resp g h g≗h)

  here : f u ≡ F u
  here = cong (λ b → if b then F u else 0ℤ) (same-refl u)

  rest : ∀ b w → (if b then 0ℤ else (if b then w else 0ℤ)) ≡ 0ℤ
  rest true  w = refl
  rest false w = refl

-- A sum is invariant under translation of its variable.  The head bit
-- of the shift either keeps the two halves of the sum or swaps them.

Σᶻ-shift : (s : Fin k → Bool) (f : (Fin k → Bool) → ℤ) → RespectsZ f →
           Σᶻ (λ v → f (v ⊕ᵃ s)) ≡ Σᶻ f
Σᶻ-shift {zero}  s f resp = trans (Σᶻ-zero (λ v → f (v ⊕ᵃ s)))
  (trans (resp _ _ (λ ())) (sym (Σᶻ-zero f)))
Σᶻ-shift {suc k} s f resp = trans (Σᶻ-suc (λ v → f (v ⊕ᵃ s)))
  (trans (cong₂ _+_ (half false) (half true)) (fin (s zero)))
  where
  s′ : Fin k → Bool
  s′ i = s (suc i)

  -- The summand with its head bit fixed.
  fixed : Bool → (Fin k → Bool) → ℤ
  fixed b g = f (b ∷ᵃ g)

  fixed-resp : ∀ b → RespectsZ (fixed b)
  fixed-resp b g h g≗h = resp (b ∷ᵃ g) (b ∷ᵃ h) pt
    where
    pt : ∀ j → (b ∷ᵃ g) j ≡ (b ∷ᵃ h) j
    pt zero    = refl
    pt (suc j) = g≗h j

  half : ∀ b → Σᶻ (λ g → f ((b ∷ᵃ g) ⊕ᵃ s)) ≡ Σᶻ (fixed (b xor s zero))
  half b = trans
    (Σᶻ-cong (λ g → resp ((b ∷ᵃ g) ⊕ᵃ s) ((b xor s zero) ∷ᵃ (g ⊕ᵃ s′)) (pt g)))
    (Σᶻ-shift s′ (fixed (b xor s zero)) (fixed-resp (b xor s zero)))
    where
    pt : ∀ g j → ((b ∷ᵃ g) ⊕ᵃ s) j ≡ ((b xor s zero) ∷ᵃ (g ⊕ᵃ s′)) j
    pt g zero    = refl
    pt g (suc j) = refl

  fin : ∀ t → Σᶻ (fixed t) + Σᶻ (fixed (not t)) ≡ Σᶻ f
  fin false = sym (Σᶻ-suc f)
  fin true  = trans (+-comm (Σᶻ (fixed true)) (Σᶻ (fixed false)))
                    (sym (Σᶻ-suc f))


------------------------------------------------------------------------
-- Orthogonality of characters

-- Σ_v (-1)^{v·c} is 2^k at c = 0 and vanishes elsewhere.

character : (c : Fin k → Bool) →
            Σᶻ (λ v → sgn (dot v c)) ≡ (if same 0ᵃ c then + (2 ℕ^ k) else 0ℤ)
character {zero}  c = Σᶻ-zero (λ v → sgn (dot v c))
character {suc k} c = trans (Σᶻ-suc (λ v → sgn (dot v c))) (step (c zero))
  where
  c′ : Fin k → Bool
  c′ i = c (suc i)

  double : ∀ b →
           (if b then + (2 ℕ^ k) else 0ℤ) + (if b then + (2 ℕ^ k) else 0ℤ) ≡
           (if b then + (2 ℕ^ suc k) else 0ℤ)
  double true  = cong (λ w → + ((2 ℕ^ k) ℕ+ w)) (sym (ℕ.+-identityʳ (2 ℕ^ k)))
  double false = refl

  step : ∀ t →
         Σᶻ (λ g → sgn (dot g c′)) + Σᶻ (λ g → sgn (t xor dot g c′)) ≡
         (if not t ∧ same 0ᵃ c′ then + (2 ℕ^ suc k) else 0ℤ)
  step false = trans (cong₂ _+_ (character c′) (character c′))
                     (double (same 0ᵃ c′))
  step true  = trans (sym (Σᶻ-+ (λ g → sgn (dot g c′))
                                (λ g → sgn (not (dot g c′)))))
    (trans (Σᶻ-cong (λ g → sgn-cancel (dot g c′))) Σᶻ-0)

-- The zero test of a sum is a comparison.

same-0⊕ : (u v : Fin k → Bool) → same 0ᵃ (u ⊕ᵃ v) ≡ same v u
same-0⊕ {zero}  u v = refl
same-0⊕ {suc k} u v = cong₂ _∧_ (cong not (xor-comm (u zero) (v zero)))
  (same-0⊕ (λ i → u (suc i)) (λ i → v (suc i)))

-- Σ_z (-1)^{z·u + s·z} is 2^k when u = s and 0 otherwise.

character-shift : (s u : Fin k → Bool) →
                  Σᶻ (λ z → sgn (dot z u xor dot s z)) ≡
                  (if same s u then + (2 ℕ^ k) else 0ℤ)
character-shift {k = k} s u = trans
  (Σᶻ-cong (λ z → cong sgn
    (trans (cong (dot z u xor_) (dot-comm s z)) (sym (dot-⊕ʳ z u s)))))
  (trans (character (u ⊕ᵃ s)) (cong pick (same-0⊕ u s)))
  where
  pick : Bool → ℤ
  pick b = if b then + (2 ℕ^ k) else 0ℤ


------------------------------------------------------------------------
-- Maiorana-McFarland bent functions

-- f(x, y) = g(x) + x·y and its dual f̃(x, y) = g(y) + x·y, as the
-- exponents of their signs, on the two halves of an assignment.

mm dual : ∀ {m} → ((Fin m → Bool) → Bool) → (Fin (m ℕ+ m) → Bool) → Bool
mm   {m} g u = g (lhalf {m} u) xor dot (lhalf {m} u) (rhalf {m} u)
dual {m} g u = g (rhalf {m} u) xor dot (lhalf {m} u) (rhalf {m} u)

mm-resp : ∀ {m} (g : (Fin m → Bool) → Bool) → RespectsB g → RespectsB (mm g)
mm-resp {m} g g-resp u v h = cong₂ _xor_
  (g-resp (lhalf {m} u) (lhalf {m} v) (λ i → h (i ↑ˡ m)))
  (dot-cong (λ i → h (i ↑ˡ m)) (λ i → h (m ↑ʳ i)))

dual-resp : ∀ {m} (g : (Fin m → Bool) → Bool) → RespectsB g →
            RespectsB (dual g)
dual-resp {m} g g-resp u v h = cong₂ _xor_
  (g-resp (rhalf {m} u) (rhalf {m} v) (λ i → h (m ↑ʳ i)))
  (dot-cong (λ i → h (i ↑ˡ m)) (λ i → h (m ↑ʳ i)))

-- The Walsh transform of f is 2^m f̃.

walsh-mm : ∀ {m} (g : (Fin m → Bool) → Bool) → RespectsB g →
           (c : Fin (m ℕ+ m) → Bool) →
           Σᶻ (λ u → sgn (mm g u xor dot u c)) ≡ + (2 ℕ^ m) * sgn (dual g c)
walsh-mm {m} g g-resp c = begin
  Σᶻ (λ u → sgn (mm g u xor dot u c))
    ≡⟨ Σᶻ-⧺ m m (λ u → sgn (mm g u xor dot u c)) ⟩
  Σᶻ (λ a → Σᶻ (λ b → sgn (mm g (a ⧺ b) xor dot (a ⧺ b) c)))
    ≡⟨ Σᶻ-cong (λ a → Σᶻ-cong (λ b → point a b)) ⟩
  Σᶻ (λ a → Σᶻ (λ b → sgn (g a xor dot a c₁) * sgn (dot b (a ⊕ᵃ c₂))))
    ≡⟨ Σᶻ-cong (λ a → trans (Σᶻ-* (sgn (g a xor dot a c₁))
                                  (λ b → sgn (dot b (a ⊕ᵃ c₂))))
                            (cong (sgn (g a xor dot a c₁) *_)
                                  (character (a ⊕ᵃ c₂)))) ⟩
  Σᶻ (λ a → sgn (g a xor dot a c₁) *
            (if same 0ᵃ (a ⊕ᵃ c₂) then P else 0ℤ))
    ≡⟨ Σᶻ-cong (λ a → trans
         (cong (λ t → sgn (g a xor dot a c₁) * (if t then P else 0ℤ))
               (same-0⊕ a c₂))
         (guard (same c₂ a) (sgn (g a xor dot a c₁)))) ⟩
  Σᶻ (λ a → if same c₂ a then P * sgn (g a xor dot a c₁) else 0ℤ)
    ≡⟨ Σᶻ-δ c₂ (λ a → P * sgn (g a xor dot a c₁)) resp ⟩
  P * sgn (g c₂ xor dot c₂ c₁)
    ≡⟨ cong (λ t → P * sgn (g c₂ xor t)) (dot-comm c₂ c₁) ⟩
  P * sgn (dual g c)
    ∎
  where
  open ≡-Reasoning

  P : ℤ
  P = + (2 ℕ^ m)

  c₁ c₂ : Fin m → Bool
  c₁ = lhalf {m} c
  c₂ = rhalf {m} c

  -- The exponent at (a, b), regrouped as g(a) + a·c₁ + b·(a + c₂).
  point : ∀ a b → sgn (mm g (a ⧺ b) xor dot (a ⧺ b) c) ≡
                  sgn (g a xor dot a c₁) * sgn (dot b (a ⊕ᵃ c₂))
  point a b = trans (cong sgn exponent)
    (sgn-xor (g a xor dot a c₁) (dot b (a ⊕ᵃ c₂)))
    where
    mm-ab : mm g (a ⧺ b) ≡ g a xor dot a b
    mm-ab = cong₂ _xor_ (g-resp _ a (⧺-↑ˡ a b))
                        (dot-cong (⧺-↑ˡ a b) (⧺-↑ʳ a b))

    dot-ab : dot (a ⧺ b) c ≡ dot a c₁ xor dot b c₂
    dot-ab = trans (dot-cong (λ _ → refl) (λ j → sym (⧺-split m m c j)))
                   (dot-⧺ a c₁ b c₂)

    exponent : mm g (a ⧺ b) xor dot (a ⧺ b) c ≡
               (g a xor dot a c₁) xor dot b (a ⊕ᵃ c₂)
    exponent = trans (cong₂ _xor_ mm-ab dot-ab)
      (trans (xor-medial (g a) (dot a b) (dot a c₁) (dot b c₂))
        (cong ((g a xor dot a c₁) xor_)
          (trans (cong (_xor dot b c₂) (dot-comm a b))
                 (sym (dot-⊕ʳ b a c₂)))))

  guard : ∀ t (σ : ℤ) → σ * (if t then P else 0ℤ) ≡ (if t then P * σ else 0ℤ)
  guard true  σ = *-comm σ P
  guard false σ = *-zeroʳ σ

  resp : RespectsZ (λ a → P * sgn (g a xor dot a c₁))
  resp u v h = cong (λ t → P * sgn t)
    (cong₂ _xor_ (g-resp u v h) (dot-cong h (λ _ → refl)))

-- Shifting f by s multiplies its transform by the character of s.

walsh-mm-shift : ∀ {m} (g : (Fin m → Bool) → Bool) → RespectsB g →
                 (s c : Fin (m ℕ+ m) → Bool) →
                 Σᶻ (λ u → sgn (mm g (u ⊕ᵃ s) xor dot u c)) ≡
                 + (2 ℕ^ m) * sgn (dual g c xor dot s c)
walsh-mm-shift {m} g g-resp s c = begin
  Σᶻ F
    ≡⟨ sym (Σᶻ-shift s F F-resp) ⟩
  Σᶻ (λ v → F (v ⊕ᵃ s))
    ≡⟨ Σᶻ-cong point ⟩
  Σᶻ (λ v → sgn (dot s c) * sgn (mm g v xor dot v c))
    ≡⟨ Σᶻ-* (sgn (dot s c)) (λ v → sgn (mm g v xor dot v c)) ⟩
  sgn (dot s c) * Σᶻ (λ v → sgn (mm g v xor dot v c))
    ≡⟨ cong (sgn (dot s c) *_) (walsh-mm g g-resp c) ⟩
  sgn (dot s c) * (P * sgn (dual g c))
    ≡⟨ regroup (sgn (dot s c)) P (sgn (dual g c)) ⟩
  P * (sgn (dual g c) * sgn (dot s c))
    ≡⟨ cong (P *_) (sym (sgn-xor (dual g c) (dot s c))) ⟩
  P * sgn (dual g c xor dot s c)
    ∎
  where
  open ≡-Reasoning

  P : ℤ
  P = + (2 ℕ^ m)

  F : (Fin (m ℕ+ m) → Bool) → ℤ
  F u = sgn (mm g (u ⊕ᵃ s) xor dot u c)

  F-resp : RespectsZ F
  F-resp u v h = cong sgn (cong₂ _xor_
    (mm-resp g g-resp (u ⊕ᵃ s) (v ⊕ᵃ s) (λ i → cong (_xor s i) (h i)))
    (dot-cong h (λ _ → refl)))

  cancel : ∀ v i → ((v ⊕ᵃ s) ⊕ᵃ s) i ≡ v i
  cancel v i = trans (xor-assoc (v i) (s i) (s i)) (again (v i) (s i))
    where
    again : ∀ a b → a xor (b xor b) ≡ a
    again false false = refl
    again false true  = refl
    again true  false = refl
    again true  true  = refl

  point : ∀ v → F (v ⊕ᵃ s) ≡ sgn (dot s c) * sgn (mm g v xor dot v c)
  point v = trans
    (cong sgn (trans
      (cong₂ _xor_ (mm-resp g g-resp ((v ⊕ᵃ s) ⊕ᵃ s) v (cancel v))
                   (dot-⊕ˡ v s c))
      (sym (xor-assoc (mm g v) (dot v c) (dot s c)))))
    (trans (sgn-xor (mm g v xor dot v c) (dot s c))
           (*-comm (sgn (mm g v xor dot v c)) (sgn (dot s c))))

  regroup : ∀ a b d → a * (b * d) ≡ b * (d * a)
  regroup a b d = trans (sym (*-assoc a b d))
    (trans (cong (_* d) (*-comm a b))
      (trans (*-assoc b a d) (cong (b *_) (*-comm a d))))
