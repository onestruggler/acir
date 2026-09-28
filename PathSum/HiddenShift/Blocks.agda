------------------------------------------------------------------------
-- Presentations of groups
--
-- The phase of the hidden shift circuit, block by block
--
-- The hidden shift circuit H^{⊗n} O_f̃ H^{⊗n} O_f′ H^{⊗n} of section 5.2
-- of Amy's "Towards Large-scale Functional Verification of Universal
-- Quantum Circuits" (QPL 2018) has 3n path variables, n = 2m, one for
-- each qubit at each Hadamard layer.  They come in six blocks of m: the
-- first layer's two halves a and b, the second's c and d, the third's
-- e and h, in that order (PathSum.HiddenShift.Example names them so at
-- m = 1).  On the input |0⟩ the phase along a path is ½ times the
-- parity (PathSum.HiddenShift.Simulation.hs-parity)
--
--   g(a ⊕ s_L) + (a ⊕ s_L)·(b ⊕ s_R) + a·c + b·d + g(d) + c·d + c·e + d·h,
--
-- s = (s_L, s_R) being the shift and g any Boolean function on m bits:
-- the first two terms are f′ on the first layer's path, the next two
-- the inner product of the first two layers, then f̃ on the second
-- layer, and the inner product of the last two.  This module is about
-- that Boolean function of the six blocks, Fblk, with g arbitrary:
-- nothing here mentions path-sums.
--
-- PathSum.HiddenShift.Exists reduces the circuit on |0⟩ with figure 2's
-- [HH] and [Elim] in three passes over the coordinates i < m -- [HH] at
-- b_i with d_i ← a_i ⊕ s_L,i, then at c_i with e_i ← s_L,i, then at
-- a_i with h_i ← s_R,i, each followed by [Elim] of the substituted
-- variable -- and each [HH] asks for one fact proved here.  [HH] at a
-- variable applies when the phase is ½ times the variable times
-- (y_i + Q), Q free of y_i, plus terms free of the variable; for a
-- phase ½F that is a statement about the derivative of F, F with the
-- variable set xor F with it clear, which must be y_i ⊕ Q.  Here Q is
-- a_i ⊕ s_L,i or a constant.  The three derivatives, ∂-b, ∂-c and
-- ∂-a below, are computed term by term (Fblk-∂): an inner product
-- changes by the other side's bit when one side flips at i (dot-∂ˡ,
-- dot-∂ʳ), and a term not reading the flipped block does not change.
-- In the third pass the two g-terms change, but together: every d has
-- by then been replaced by a ⊕ s_L, so g(a ⊕ s_L) and g(d) are the
-- same function of a, and that is the only place where g, which is
-- arbitrary, cancels.
--
-- The labels.  A path variable of the circuit is named by its block
-- and coordinate (Lbl), a path by the value of each label (LAssign).
-- Each [HH] with its [Elim] removes two labels, and a removed label
-- keeps a value determined by the others (dflt): [HH] sets its
-- variable to 0 and its substitution fixes the other one, so a, b and
-- c become 0, d_k becomes a_k ⊕ s_L,k (and follows a_k when that is
-- removed in turn), e_k becomes s_L,k and h_k becomes s_R,k.  Ret₁,
-- Ret₂ and Ret₃ say which labels are still path variables during each
-- pass, given the coordinates the pass has done.  The outputs of the
-- circuit are the third layer's path, the e and h blocks (Gblk).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.HiddenShift.Blocks where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_)
open import Data.Bool.Properties using
  (xor-same; xor-comm; xor-identityʳ; ∧-identityʳ; ∧-zeroʳ)
open import Data.Fin.Base using (Fin; zero; suc; splitAt)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Product.Properties using (≡-dec)
open import Data.Sum.Base using ([_,_]′; inj₁; inj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (map′)

import Data.Fin.Properties as Fin

open import PathSum.HiddenShift.Walsh using
  (_⊕ᵃ_; RespectsB; dot; dot-cong; dot-comm; dot-⊕ʳ; xor-medial)

private
  variable
    k m : ℕ


------------------------------------------------------------------------
-- Derivatives of inner products

-- A vector that vanishes has inner product 0 with anything; one that
-- vanishes off i reads the other side at i.

dot-null : (u w : Fin k → Bool) → (∀ j → w j ≡ false) → dot u w ≡ false
dot-null {zero}  u w h = refl
dot-null {suc k} u w h =
  cong₂ _xor_ (trans (cong (u zero ∧_) (h zero)) (∧-zeroʳ (u zero)))
              (dot-null (λ j → u (suc j)) (λ j → w (suc j)) (λ j → h (suc j)))

dot-point : (u w : Fin k → Bool) (i : Fin k) →
            (∀ j → j ≢ i → w j ≡ false) → dot u w ≡ u i ∧ w i
dot-point u w zero h = trans
  (cong ((u zero ∧ w zero) xor_)
        (dot-null (λ j → u (suc j)) (λ j → w (suc j))
                  (λ j → h (suc j) (λ ()))))
  (xor-identityʳ (u zero ∧ w zero))
dot-point u w (suc i) h = trans
  (cong (_xor dot (λ j → u (suc j)) (λ j → w (suc j)))
        (trans (cong (u zero ∧_) (h zero (λ ()))) (∧-zeroʳ (u zero))))
  (dot-point (λ j → u (suc j)) (λ j → w (suc j)) i
             (λ j j≢i → h (suc j) (λ eq → j≢i (suc-injective eq))))

-- The derivative of an inner product, written u·v xor u′·v′ for two
-- pairs of vectors: 0 when neither side changes, and the other side's
-- bit at i when one side flips at i alone.

dot-∂⁰ : {u u′ v v′ : Fin k → Bool} →
         (∀ j → u j ≡ u′ j) → (∀ j → v j ≡ v′ j) →
         dot u v xor dot u′ v′ ≡ false
dot-∂⁰ {u′ = u′} {v′ = v′} hu hv =
  trans (cong (_xor dot u′ v′) (dot-cong hu hv)) (xor-same (dot u′ v′))

dot-∂ʳ : {u u′ v v′ : Fin k → Bool} (i : Fin k) →
         (∀ j → u j ≡ u′ j) → (∀ j → j ≢ i → v j ≡ v′ j) →
         v i xor v′ i ≡ true → dot u v xor dot u′ v′ ≡ u′ i
dot-∂ʳ {u = u} {u′} {v} {v′} i hu hv hi = trans
  (cong (_xor dot u′ v′) (dot-cong hu (λ _ → refl)))
  (trans (sym (dot-⊕ʳ u′ v v′))
    (trans (dot-point u′ (v ⊕ᵃ v′) i off)
      (trans (cong (u′ i ∧_) hi) (∧-identityʳ (u′ i)))))
  where
  off : ∀ j → j ≢ i → (v ⊕ᵃ v′) j ≡ false
  off j j≢i = trans (cong (_xor v′ j) (hv j j≢i)) (xor-same (v′ j))

dot-∂ˡ : {u u′ v v′ : Fin k → Bool} (i : Fin k) →
         (∀ j → j ≢ i → u j ≡ u′ j) → u i xor u′ i ≡ true →
         (∀ j → v j ≡ v′ j) → dot u v xor dot u′ v′ ≡ v′ i
dot-∂ˡ {u = u} {u′} {v} {v′} i hu hi hv = trans
  (cong₂ _xor_ (dot-comm u v) (dot-comm u′ v′))
  (dot-∂ʳ i hv hu hi)

-- Adding the same bit to both sides of a derivative leaves it alone.

xor-cancelʳ : ∀ a b c → (a xor c) xor (b xor c) ≡ a xor b
xor-cancelʳ a b c = trans (xor-medial a c b c)
  (trans (cong ((a xor b) xor_) (xor-same c)) (xor-identityʳ (a xor b)))


------------------------------------------------------------------------
-- Labels

-- The six blocks: the first Hadamard layer's two halves, the second's,
-- the third's.

data Blk : Set where
  A₁ B₁ C₂ D₂ E₃ H₃ : Blk

private
  toFin : Blk → Fin 6
  toFin A₁ = zero
  toFin B₁ = suc zero
  toFin C₂ = suc (suc zero)
  toFin D₂ = suc (suc (suc zero))
  toFin E₃ = suc (suc (suc (suc zero)))
  toFin H₃ = suc (suc (suc (suc (suc zero))))

  fromFin : Fin 6 → Blk
  fromFin zero                                   = A₁
  fromFin (suc zero)                             = B₁
  fromFin (suc (suc zero))                       = C₂
  fromFin (suc (suc (suc zero)))                 = D₂
  fromFin (suc (suc (suc (suc zero))))           = E₃
  fromFin (suc (suc (suc (suc (suc zero)))))     = H₃

  from-to : ∀ b → fromFin (toFin b) ≡ b
  from-to A₁ = refl
  from-to B₁ = refl
  from-to C₂ = refl
  from-to D₂ = refl
  from-to E₃ = refl
  from-to H₃ = refl

_≟ᵇ_ : DecidableEquality Blk
b ≟ᵇ b′ = map′
  (λ e → trans (sym (from-to b)) (trans (cong fromFin e) (from-to b′)))
  (cong toFin) (toFin b Fin.≟ toFin b′)

-- A path variable is named by its block and its coordinate.

Lbl : ℕ → Set
Lbl m = Blk × Fin m

_≟ˡ_ : DecidableEquality (Lbl m)
_≟ˡ_ = ≡-dec _≟ᵇ_ Fin._≟_

-- A path, read by label, and one block of it.

LAssign : ℕ → Set
LAssign m = Lbl m → Bool

infixl 10 _‹_›

_‹_› : LAssign m → Blk → Fin m → Bool
(Z ‹ b ›) i = Z (b , i)

-- The labels still path variables at each stage, d being the
-- coordinates the current pass has done: pass 1 removes b and d, pass
-- 2 c and e, pass 3 a and h.

Ret₁ Ret₂ Ret₃ : (Fin m → Bool) → Lbl m → Bool
Ret₁ d (A₁ , i) = true
Ret₁ d (B₁ , i) = not (d i)
Ret₁ d (C₂ , i) = true
Ret₁ d (D₂ , i) = not (d i)
Ret₁ d (E₃ , i) = true
Ret₁ d (H₃ , i) = true
Ret₂ d (A₁ , i) = true
Ret₂ d (B₁ , i) = false
Ret₂ d (C₂ , i) = not (d i)
Ret₂ d (D₂ , i) = false
Ret₂ d (E₃ , i) = not (d i)
Ret₂ d (H₃ , i) = true
Ret₃ d (A₁ , i) = not (d i)
Ret₃ d (B₁ , i) = false
Ret₃ d (C₂ , i) = false
Ret₃ d (D₂ , i) = false
Ret₃ d (E₃ , i) = false
Ret₃ d (H₃ , i) = not (d i)

-- A pass that has done every coordinate is the next pass before any.

Ret₁₂ : ∀ (ℓ : Lbl m) → Ret₁ (λ _ → true) ℓ ≡ Ret₂ (λ _ → false) ℓ
Ret₁₂ (A₁ , i) = refl
Ret₁₂ (B₁ , i) = refl
Ret₁₂ (C₂ , i) = refl
Ret₁₂ (D₂ , i) = refl
Ret₁₂ (E₃ , i) = refl
Ret₁₂ (H₃ , i) = refl

Ret₂₃ : ∀ (ℓ : Lbl m) → Ret₂ (λ _ → true) ℓ ≡ Ret₃ (λ _ → false) ℓ
Ret₂₃ (A₁ , i) = refl
Ret₂₃ (B₁ , i) = refl
Ret₂₃ (C₂ , i) = refl
Ret₂₃ (D₂ , i) = refl
Ret₂₃ (E₃ , i) = refl
Ret₂₃ (H₃ , i) = refl

-- Before the first pass every label is a path variable, after the last
-- none is.

Ret₁-all : ∀ (ℓ : Lbl m) → Ret₁ (λ _ → false) ℓ ≡ true
Ret₁-all (A₁ , i) = refl
Ret₁-all (B₁ , i) = refl
Ret₁-all (C₂ , i) = refl
Ret₁-all (D₂ , i) = refl
Ret₁-all (E₃ , i) = refl
Ret₁-all (H₃ , i) = refl

Ret₃-none : ∀ (ℓ : Lbl m) → Ret₃ (λ _ → true) ℓ ≡ false
Ret₃-none (A₁ , i) = refl
Ret₃-none (B₁ , i) = refl
Ret₃-none (C₂ , i) = refl
Ret₃-none (D₂ , i) = refl
Ret₃-none (E₃ , i) = refl
Ret₃-none (H₃ , i) = refl

-- Which coordinates are done is read pointwise.

Ret₁-resp : {d d′ : Fin m → Bool} → (∀ i → d i ≡ d′ i) →
            ∀ (ℓ : Lbl m) → Ret₁ d ℓ ≡ Ret₁ d′ ℓ
Ret₁-resp h (A₁ , i) = refl
Ret₁-resp h (B₁ , i) = cong not (h i)
Ret₁-resp h (C₂ , i) = refl
Ret₁-resp h (D₂ , i) = cong not (h i)
Ret₁-resp h (E₃ , i) = refl
Ret₁-resp h (H₃ , i) = refl

Ret₂-resp : {d d′ : Fin m → Bool} → (∀ i → d i ≡ d′ i) →
            ∀ (ℓ : Lbl m) → Ret₂ d ℓ ≡ Ret₂ d′ ℓ
Ret₂-resp h (A₁ , i) = refl
Ret₂-resp h (B₁ , i) = refl
Ret₂-resp h (C₂ , i) = cong not (h i)
Ret₂-resp h (D₂ , i) = refl
Ret₂-resp h (E₃ , i) = cong not (h i)
Ret₂-resp h (H₃ , i) = refl

Ret₃-resp : {d d′ : Fin m → Bool} → (∀ i → d i ≡ d′ i) →
            ∀ (ℓ : Lbl m) → Ret₃ d ℓ ≡ Ret₃ d′ ℓ
Ret₃-resp h (A₁ , i) = cong not (h i)
Ret₃-resp h (B₁ , i) = refl
Ret₃-resp h (C₂ , i) = refl
Ret₃-resp h (D₂ , i) = refl
Ret₃-resp h (E₃ , i) = refl
Ret₃-resp h (H₃ , i) = cong not (h i)


------------------------------------------------------------------------
-- The outputs

-- The circuit's outputs are the third layer's path: e, then h.

Gblk : Fin (m ℕ+ m) → LAssign m → Bool
Gblk {m} w Z = [ Z ‹ E₃ › , Z ‹ H₃ › ]′ (splitAt m w)

Gblk-cong : {Z Z′ : LAssign m} →
            (∀ i → Z (E₃ , i) ≡ Z′ (E₃ , i)) →
            (∀ i → Z (H₃ , i) ≡ Z′ (H₃ , i)) →
            ∀ w → Gblk w Z ≡ Gblk w Z′
Gblk-cong {m} {Z} {Z′} e h w = go (splitAt m w)
  where
  go : ∀ t → [ Z ‹ E₃ › , Z ‹ H₃ › ]′ t ≡ [ Z′ ‹ E₃ › , Z′ ‹ H₃ › ]′ t
  go (inj₁ i) = e i
  go (inj₂ i) = h i


------------------------------------------------------------------------
-- The parity

private
  -- The three Boolean identities the derivatives end with.

  close-b : ∀ x y →
            (((false xor x) xor (false xor y)) xor (false xor false)) xor
            (false xor false) ≡ x xor y
  close-b x y =
    trans (xor-identityʳ ((x xor y) xor false)) (xor-identityʳ (x xor y))

  close-c : ∀ x y z →
            (((false xor false) xor (x xor false)) xor (false xor y)) xor
            (z xor false) ≡ (x xor y) xor z
  close-c x y z =
    cong₂ (λ p q → (p xor y) xor q) (xor-identityʳ x) (xor-identityʳ z)

  close-a : ∀ γ b r c h →
            (((γ xor (b xor r)) xor (c xor b)) xor (γ xor c)) xor
            (false xor h) ≡ r xor h
  close-a false false false false h = refl
  close-a false false false true  h = refl
  close-a false false true  false h = refl
  close-a false false true  true  h = refl
  close-a false true  false false h = refl
  close-a false true  false true  h = refl
  close-a false true  true  false h = refl
  close-a false true  true  true  h = refl
  close-a true  false false false h = refl
  close-a true  false false true  h = refl
  close-a true  false true  false h = refl
  close-a true  false true  true  h = refl
  close-a true  true  false false h = refl
  close-a true  true  false true  h = refl
  close-a true  true  true  false h = refl
  close-a true  true  true  true  h = refl

-- The parity, for a Boolean function g on m bits and a shift
-- (s_L, s_R).

module Phase {m : ℕ} (gᵇ : (Fin m → Bool) → Bool) (gᵇ-resp : RespectsB gᵇ)
             (sL sR : Fin m → Bool) where

  -- Its eight terms: f′ on the first layer's path (T₁, T₂), the inner
  -- product of the first two layers (T₃, T₄), f̃ on the second layer's
  -- (T₅, T₆), and the inner product of the last two (T₇, T₈).

  T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ : LAssign m → Bool
  T₁ Z = gᵇ (Z ‹ A₁ › ⊕ᵃ sL)
  T₂ Z = dot (Z ‹ A₁ › ⊕ᵃ sL) (Z ‹ B₁ › ⊕ᵃ sR)
  T₃ Z = dot (Z ‹ A₁ ›) (Z ‹ C₂ ›)
  T₄ Z = dot (Z ‹ B₁ ›) (Z ‹ D₂ ›)
  T₅ Z = gᵇ (Z ‹ D₂ ›)
  T₆ Z = dot (Z ‹ C₂ ›) (Z ‹ D₂ ›)
  T₇ Z = dot (Z ‹ C₂ ›) (Z ‹ E₃ ›)
  T₈ Z = dot (Z ‹ D₂ ›) (Z ‹ H₃ ›)

  -- Grouped as hs-parity groups them.

  Fblk : LAssign m → Bool
  Fblk Z = (((T₁ Z xor T₂ Z) xor (T₃ Z xor T₄ Z)) xor (T₅ Z xor T₆ Z)) xor
           (T₇ Z xor T₈ Z)

  -- The value a removed label keeps: [HH] clears its own variable and
  -- fixes the one it substitutes for.

  dflt : Lbl m → LAssign m → Bool
  dflt (A₁ , i) Z = false
  dflt (B₁ , i) Z = false
  dflt (C₂ , i) Z = false
  dflt (D₂ , i) Z = Z (A₁ , i) xor sL i
  dflt (E₃ , i) Z = sL i
  dflt (H₃ , i) Z = sR i

  -- The derivative of the sum is the sum of the derivatives.

  Fblk-∂ : ∀ Z Z′ → Fblk Z xor Fblk Z′ ≡
    ((((T₁ Z xor T₁ Z′) xor (T₂ Z xor T₂ Z′)) xor
      ((T₃ Z xor T₃ Z′) xor (T₄ Z xor T₄ Z′))) xor
     ((T₅ Z xor T₅ Z′) xor (T₆ Z xor T₆ Z′))) xor
    ((T₇ Z xor T₇ Z′) xor (T₈ Z xor T₈ Z′))
  Fblk-∂ Z Z′ = trans (xor-medial X Y X′ Y′) (cong₂ _xor_
    (trans (xor-medial U V U′ V′) (cong₂ _xor_
      (trans (xor-medial P R P′ R′) (cong₂ _xor_
        (xor-medial (T₁ Z) (T₂ Z) (T₁ Z′) (T₂ Z′))
        (xor-medial (T₃ Z) (T₄ Z) (T₃ Z′) (T₄ Z′))))
      (xor-medial (T₅ Z) (T₆ Z) (T₅ Z′) (T₆ Z′))))
    (xor-medial (T₇ Z) (T₈ Z) (T₇ Z′) (T₈ Z′)))
    where
    P P′ R R′ U U′ V V′ X X′ Y Y′ : Bool
    P  = T₁ Z xor T₂ Z
    P′ = T₁ Z′ xor T₂ Z′
    R  = T₃ Z xor T₄ Z
    R′ = T₃ Z′ xor T₄ Z′
    U  = P xor R
    U′ = P′ xor R′
    V  = T₅ Z xor T₆ Z
    V′ = T₅ Z′ xor T₆ Z′
    X  = U xor V
    X′ = U′ xor V′
    Y  = T₇ Z xor T₈ Z
    Y′ = T₇ Z′ xor T₈ Z′

  private
    g-∂⁰ : {u u′ : Fin m → Bool} → (∀ j → u j ≡ u′ j) →
           gᵇ u xor gᵇ u′ ≡ false
    g-∂⁰ {u} {u′} h =
      trans (cong (_xor gᵇ u′) (gᵇ-resp u u′ h)) (xor-same (gᵇ u′))

  -- Pass 1: b flips at i and nothing else changes.  The parity changes
  -- by (a_i ⊕ s_L,i) ⊕ d_i.

  ∂-b : ∀ (Z Z′ : LAssign m) (i : Fin m) →
        (∀ j → Z (A₁ , j) ≡ Z′ (A₁ , j)) →
        (∀ j → j ≢ i → Z (B₁ , j) ≡ Z′ (B₁ , j)) →
        Z (B₁ , i) xor Z′ (B₁ , i) ≡ true →
        (∀ j → Z (C₂ , j) ≡ Z′ (C₂ , j)) →
        (∀ j → Z (D₂ , j) ≡ Z′ (D₂ , j)) →
        (∀ j → Z (E₃ , j) ≡ Z′ (E₃ , j)) →
        (∀ j → Z (H₃ , j) ≡ Z′ (H₃ , j)) →
        Fblk Z xor Fblk Z′ ≡ (Z′ (A₁ , i) xor sL i) xor Z′ (D₂ , i)
  ∂-b Z Z′ i a b bi c d e h = trans (Fblk-∂ Z Z′)
    (trans (cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_
              (cong₂ _xor_ (g-∂⁰ aL) ∂₂)
              (cong₂ _xor_ (dot-∂⁰ a c) ∂₄))
              (cong₂ _xor_ (g-∂⁰ d) (dot-∂⁰ c d)))
              (cong₂ _xor_ (dot-∂⁰ c e) (dot-∂⁰ d h)))
      (close-b (Z′ (A₁ , i) xor sL i) (Z′ (D₂ , i))))
    where
    aL : ∀ j → (Z ‹ A₁ › ⊕ᵃ sL) j ≡ (Z′ ‹ A₁ › ⊕ᵃ sL) j
    aL j = cong (_xor sL j) (a j)

    ∂₂ : T₂ Z xor T₂ Z′ ≡ Z′ (A₁ , i) xor sL i
    ∂₂ = dot-∂ʳ i aL (λ j j≢i → cong (_xor sR j) (b j j≢i))
                (trans (xor-cancelʳ (Z (B₁ , i)) (Z′ (B₁ , i)) (sR i)) bi)

    ∂₄ : T₄ Z xor T₄ Z′ ≡ Z′ (D₂ , i)
    ∂₄ = dot-∂ˡ i b bi d

  -- Pass 2: c flips at i.  The parity changes by a_i ⊕ d_i ⊕ e_i.

  ∂-c : ∀ (Z Z′ : LAssign m) (i : Fin m) →
        (∀ j → Z (A₁ , j) ≡ Z′ (A₁ , j)) →
        (∀ j → Z (B₁ , j) ≡ Z′ (B₁ , j)) →
        (∀ j → j ≢ i → Z (C₂ , j) ≡ Z′ (C₂ , j)) →
        Z (C₂ , i) xor Z′ (C₂ , i) ≡ true →
        (∀ j → Z (D₂ , j) ≡ Z′ (D₂ , j)) →
        (∀ j → Z (E₃ , j) ≡ Z′ (E₃ , j)) →
        (∀ j → Z (H₃ , j) ≡ Z′ (H₃ , j)) →
        Fblk Z xor Fblk Z′ ≡ (Z′ (A₁ , i) xor Z′ (D₂ , i)) xor Z′ (E₃ , i)
  ∂-c Z Z′ i a b c ci d e h = trans (Fblk-∂ Z Z′)
    (trans (cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_
              (cong₂ _xor_ (g-∂⁰ aL) (dot-∂⁰ aL bR))
              (cong₂ _xor_ (dot-∂ʳ i a c ci) (dot-∂⁰ b d)))
              (cong₂ _xor_ (g-∂⁰ d) (dot-∂ˡ i c ci d)))
              (cong₂ _xor_ (dot-∂ˡ i c ci e) (dot-∂⁰ d h)))
      (close-c (Z′ (A₁ , i)) (Z′ (D₂ , i)) (Z′ (E₃ , i))))
    where
    aL : ∀ j → (Z ‹ A₁ › ⊕ᵃ sL) j ≡ (Z′ ‹ A₁ › ⊕ᵃ sL) j
    aL j = cong (_xor sL j) (a j)

    bR : ∀ j → (Z ‹ B₁ › ⊕ᵃ sR) j ≡ (Z′ ‹ B₁ › ⊕ᵃ sR) j
    bR j = cong (_xor sR j) (b j)

  -- Pass 3: a flips at i, and d with it, d being a ⊕ s_L throughout.
  -- The two g-terms change alike, and the parity changes by
  -- s_R,i ⊕ h_i.

  ∂-a : ∀ (Z Z′ : LAssign m) (i : Fin m) →
        (∀ j → j ≢ i → Z (A₁ , j) ≡ Z′ (A₁ , j)) →
        Z (A₁ , i) xor Z′ (A₁ , i) ≡ true →
        (∀ j → Z (B₁ , j) ≡ Z′ (B₁ , j)) →
        (∀ j → Z (C₂ , j) ≡ Z′ (C₂ , j)) →
        (∀ j → Z (D₂ , j) ≡ Z (A₁ , j) xor sL j) →
        (∀ j → Z′ (D₂ , j) ≡ Z′ (A₁ , j) xor sL j) →
        (∀ j → Z (E₃ , j) ≡ Z′ (E₃ , j)) →
        (∀ j → Z (H₃ , j) ≡ Z′ (H₃ , j)) →
        Fblk Z xor Fblk Z′ ≡ sR i xor Z′ (H₃ , i)
  ∂-a Z Z′ i a ai b c dZ dZ′ e h = trans (Fblk-∂ Z Z′)
    (trans (cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_
              (cong ((T₁ Z xor T₁ Z′) xor_) (dot-∂ˡ i aL aLi bR))
              (cong₂ _xor_ (dot-∂ˡ i a ai c) (dot-∂ʳ i b dD dDi)))
              (cong₂ _xor_ ∂₅ (dot-∂ʳ i c dD dDi)))
              (cong₂ _xor_ (dot-∂⁰ c e) (dot-∂ˡ i dD dDi h)))
      (close-a (T₁ Z xor T₁ Z′) (Z′ (B₁ , i)) (sR i) (Z′ (C₂ , i))
               (Z′ (H₃ , i))))
    where
    aL : ∀ j → j ≢ i → (Z ‹ A₁ › ⊕ᵃ sL) j ≡ (Z′ ‹ A₁ › ⊕ᵃ sL) j
    aL j j≢i = cong (_xor sL j) (a j j≢i)

    aLi : (Z (A₁ , i) xor sL i) xor (Z′ (A₁ , i) xor sL i) ≡ true
    aLi = trans (xor-cancelʳ (Z (A₁ , i)) (Z′ (A₁ , i)) (sL i)) ai

    bR : ∀ j → (Z ‹ B₁ › ⊕ᵃ sR) j ≡ (Z′ ‹ B₁ › ⊕ᵃ sR) j
    bR j = cong (_xor sR j) (b j)

    dD : ∀ j → j ≢ i → Z (D₂ , j) ≡ Z′ (D₂ , j)
    dD j j≢i = trans (dZ j) (trans (aL j j≢i) (sym (dZ′ j)))

    dDi : Z (D₂ , i) xor Z′ (D₂ , i) ≡ true
    dDi = trans (cong₂ _xor_ (dZ i) (dZ′ i)) aLi

    ∂₅ : T₅ Z xor T₅ Z′ ≡ T₁ Z xor T₁ Z′
    ∂₅ = cong₂ _xor_ (gᵇ-resp (Z ‹ D₂ ›) (Z ‹ A₁ › ⊕ᵃ sL) dZ)
                     (gᵇ-resp (Z′ ‹ D₂ ›) (Z′ ‹ A₁ › ⊕ᵃ sL) dZ′)
