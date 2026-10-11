------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix of a Hadamard pair
--
-- Lemma A.6 asks which signed permutations commute with a Hadamard
-- pair H_[p,q] H_[r,s], and to answer that one has to know the pair's
-- matrix entry by entry.  This module works it out, for any two
-- *disjoint* index pairs rather than only the paper's 0, 1, 3, 2,
-- since the general form is what Equation (65) needs anyway.
--
-- Everything rests on writing a row of a two-level Hadamard as a
-- combination of two deltas,
--
--     H_[i,j] at i  =  δᵢ + δⱼ,    H_[i,j] at j  =  δᵢ − δⱼ,
--
-- and as √2·δ at every other index.  `Σ-add` and `Σ-δˡ` then collapse
-- the matrix product row by row, and the answer is that the pair is √2
-- times a two-level Hadamard on each of its two pairs and twice the
-- identity everywhere else.
--
-- Signs are written `-1# *` rather than with negation, so that a row
-- is always `c * δᵢ + d * δⱼ` and one lemma covers every case.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.HadamardPair (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Vec using ([] ; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB ; hadOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
  using (eqB-refl ; eqB-sound ; eqB-complete ; eqB-false)

private
  n : ℕ
  n = ₃₊ m

------------------------------------------------------------------------
-- Deltas

δ≢ : ∀ {k : ℕ} (x y : Bits k) → x ≢ y → δb x y ≡ 0#
δ≢ []           []           ne = ⊥-elim (ne Eq.refl)
δ≢ (true  ∷ xs) (true  ∷ ys) ne = δ≢ xs ys (λ e → ne (Eq.cong (true ∷_) e))
δ≢ (false ∷ xs) (false ∷ ys) ne = δ≢ xs ys (λ e → ne (Eq.cong (false ∷_) e))
δ≢ (true  ∷ xs) (false ∷ ys) ne = Eq.refl
δ≢ (false ∷ xs) (true  ∷ ys) ne = Eq.refl

eqB-≢ : ∀ (x y : Bits n) → eqB x y ≡ false → x ≢ y
eqB-≢ x y ef e = tf (Eq.trans (Eq.sym (eqB-complete x y e)) ef)
  where
  tf : true ≡ false → _
  tf ()

------------------------------------------------------------------------
-- The rows of a two-level Hadamard

-- At the first index of its pair.
had-i : ∀ (i j : Bits n) → i ≢ j → ∀ (y : Bits n) →
        hadOp i j i y ≡ 1# * δb i y + 1# * δb j y
had-i i j ne y rewrite eqB-refl i = go (eqB y i) (eqB y j) Eq.refl Eq.refl
  where
  go : ∀ (u v : Bool) → eqB y i ≡ u → eqB y j ≡ v →
       (if eqB y i then 1# else if eqB y j then 1# else 0#)
       ≡ 1# * δb i y + 1# * δb j y
  go true v eu ev rewrite eu =
    Eq.sym (Eq.trans (Eq.cong₂ _+_ (Eq.trans (*-identityˡ (δb i y)) di)
                                   (Eq.trans (*-identityˡ (δb j y)) dj))
                     (+-identityʳ 1#))
    where
    y≡i = eqB-sound y i eu
    di : δb i y ≡ 1#
    di = Eq.trans (Eq.cong (δb i) y≡i) (δb-refl i)
    dj : δb j y ≡ 0#
    dj = δ≢ j y (λ e → ne (Eq.sym (Eq.trans e y≡i)))
  go false true eu ev rewrite eu | ev =
    Eq.sym (Eq.trans (Eq.cong₂ _+_ (Eq.trans (*-identityˡ (δb i y)) di)
                                   (Eq.trans (*-identityˡ (δb j y)) dj))
                     (+-identityˡ 1#))
    where
    y≡j = eqB-sound y j ev
    di : δb i y ≡ 0#
    di = δ≢ i y (λ e → ne (Eq.trans e y≡j))
    dj : δb j y ≡ 1#
    dj = Eq.trans (Eq.cong (δb j) y≡j) (δb-refl j)
  go false false eu ev rewrite eu | ev =
    Eq.sym (Eq.trans (Eq.cong₂ _+_ (Eq.trans (*-identityˡ (δb i y)) di)
                                   (Eq.trans (*-identityˡ (δb j y)) dj))
                     (+-identityʳ 0#))
    where
    di : δb i y ≡ 0#
    di = δ≢ i y (λ e → eqB-≢ y i eu (Eq.sym e))
    dj : δb j y ≡ 0#
    dj = δ≢ j y (λ e → eqB-≢ y j ev (Eq.sym e))

-- At the second.
had-j : ∀ (i j : Bits n) → i ≢ j → ∀ (y : Bits n) →
        hadOp i j j y ≡ 1# * δb i y + -1# * δb j y
had-j i j ne y
  rewrite eqB-false j i (λ e → ne (Eq.sym e)) | eqB-refl j =
  go (eqB y i) (eqB y j) Eq.refl Eq.refl
  where
  go : ∀ (u v : Bool) → eqB y i ≡ u → eqB y j ≡ v →
       (if eqB y i then 1# else if eqB y j then -1# else 0#)
       ≡ 1# * δb i y + -1# * δb j y
  go true v eu ev rewrite eu =
    Eq.sym (Eq.trans (Eq.cong₂ _+_ (Eq.trans (*-identityˡ (δb i y)) di)
                                   (Eq.trans (Eq.cong (-1# *_) dj) (*-zeroʳ -1#)))
                     (+-identityʳ 1#))
    where
    y≡i = eqB-sound y i eu
    di : δb i y ≡ 1#
    di = Eq.trans (Eq.cong (δb i) y≡i) (δb-refl i)
    dj : δb j y ≡ 0#
    dj = δ≢ j y (λ e → ne (Eq.sym (Eq.trans e y≡i)))
  go false true eu ev rewrite eu | ev =
    Eq.sym (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (1# *_) di) (*-zeroʳ 1#))
                                   (Eq.trans (Eq.cong (-1# *_) dj) (*-identityʳ -1#)))
                     (+-identityˡ -1#))
    where
    y≡j = eqB-sound y j ev
    di : δb i y ≡ 0#
    di = δ≢ i y (λ e → ne (Eq.trans e y≡j))
    dj : δb j y ≡ 1#
    dj = Eq.trans (Eq.cong (δb j) y≡j) (δb-refl j)
  go false false eu ev rewrite eu | ev =
    Eq.sym (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (1# *_) di) (*-zeroʳ 1#))
                                   (Eq.trans (Eq.cong (-1# *_) dj) (*-zeroʳ -1#)))
                     (+-identityʳ 0#))
    where
    di : δb i y ≡ 0#
    di = δ≢ i y (λ e → eqB-≢ y i eu (Eq.sym e))
    dj : δb j y ≡ 0#
    dj = δ≢ j y (λ e → eqB-≢ y j ev (Eq.sym e))

-- And anywhere else.
had-o : ∀ (i j x : Bits n) → x ≢ i → x ≢ j → ∀ (y : Bits n) →
        hadOp i j x y ≡ √2 * δb x y
had-o i j x nx ny y rewrite eqB-false x i nx | eqB-false x j ny = Eq.refl

------------------------------------------------------------------------
-- A row of a product
--
-- If the left factor's row at x is a combination of two deltas then
-- the product's row at x is the same combination of the right
-- factor's two rows; `Σ-add` splits the sum and `Σ-δˡ` collapses each
-- half.

prod-row : ∀ (c d : 𝔽) (i j : Bits n) (H : Op n) (x : Bits n) →
           (∀ y → hadOp i j x y ≡ c * δb i y + d * δb j y) →
           ∀ (y : Bits n) → (hadOp i j ⊙ H) x y ≡ c * H i y + d * H j y
prod-row c d i j H x e y =
  Eq.trans (Σ-cong {f = λ z → hadOp i j x z * H z y}
                    {g = λ z → c * (δb i z * H z y) + d * (δb j z * H z y)} step)
    (Eq.trans (Σ-add (λ z → c * (δb i z * H z y)) (λ z → d * (δb j z * H z y)))
              (Eq.cong₂ _+_
                (Eq.trans (Σ-scaleˡ c (λ z → δb i z * H z y))
                          (Eq.cong (c *_) (Σ-δˡ i (λ z → H z y))))
                (Eq.trans (Σ-scaleˡ d (λ z → δb j z * H z y))
                          (Eq.cong (d *_) (Σ-δˡ j (λ z → H z y))))))
  where
  step : ∀ (z : Bits n) →
         hadOp i j x z * H z y ≡ c * (δb i z * H z y) + d * (δb j z * H z y)
  step z = Eq.trans (Eq.cong (_* H z y) (e z))
             (Eq.trans (*-distribʳ-+ (H z y) (c * δb i z) (d * δb j z))
                       (Eq.cong₂ _+_ (*-assoc c (δb i z) (H z y))
                                     (*-assoc d (δb j z) (H z y))))

prod-row-o : ∀ (i j : Bits n) (H : Op n) (x : Bits n) → x ≢ i → x ≢ j →
             ∀ (y : Bits n) → (hadOp i j ⊙ H) x y ≡ √2 * H x y
prod-row-o i j H x nx ny y =
  Eq.trans (Σ-cong {f = λ z → hadOp i j x z * H z y}
                    {g = λ z → √2 * (δb x z * H z y)}
                    (λ z → Eq.trans (Eq.cong (_* H z y) (had-o i j x nx ny z))
                                    (*-assoc √2 (δb x z) (H z y))))
           (Eq.trans (Σ-scaleˡ √2 (λ z → δb x z * H z y))
                     (Eq.cong (√2 *_) (Σ-δˡ x (λ z → H z y))))

------------------------------------------------------------------------
-- The pair itself
--
-- On each of its two pairs it is √2 times a two-level Hadamard, and
-- everywhere else it is twice the identity.

HH2 : Bits n → Bits n → Bits n → Bits n → Op n
HH2 p q r s = hadOp p q ⊙ hadOp r s

module Entries (p q r s : Bits n)
               (pq : p ≢ q) (rs : r ≢ s)
               (pr : p ≢ r) (ps : p ≢ s) (qr : q ≢ r) (qs : q ≢ s)
  where

  HH2-p : ∀ (y : Bits n) → HH2 p q r s p y ≡ √2 * δb p y + √2 * δb q y
  HH2-p y =
    Eq.trans (prod-row 1# 1# p q (hadOp r s) p (had-i p q pq) y)
             (Eq.cong₂ _+_ (Eq.trans (*-identityˡ (hadOp r s p y))
                                     (had-o r s p pr ps y))
                           (Eq.trans (*-identityˡ (hadOp r s q y))
                                     (had-o r s q qr qs y)))

  HH2-q : ∀ (y : Bits n) → HH2 p q r s q y ≡ √2 * δb p y + -1# * (√2 * δb q y)
  HH2-q y =
    Eq.trans (prod-row 1# -1# p q (hadOp r s) q (had-j p q pq) y)
             (Eq.cong₂ _+_ (Eq.trans (*-identityˡ (hadOp r s p y))
                                     (had-o r s p pr ps y))
                           (Eq.cong (-1# *_) (had-o r s q qr qs y)))

  HH2-r : ∀ (y : Bits n) → HH2 p q r s r y ≡ √2 * (1# * δb r y + 1# * δb s y)
  HH2-r y =
    Eq.trans (prod-row-o p q (hadOp r s) r (λ e → pr (Eq.sym e)) (λ e → qr (Eq.sym e)) y)
             (Eq.cong (√2 *_) (had-i r s rs y))

  HH2-s : ∀ (y : Bits n) → HH2 p q r s s y ≡ √2 * (1# * δb r y + -1# * δb s y)
  HH2-s y =
    Eq.trans (prod-row-o p q (hadOp r s) s (λ e → ps (Eq.sym e)) (λ e → qs (Eq.sym e)) y)
             (Eq.cong (√2 *_) (had-j r s rs y))

  HH2-o : ∀ (x : Bits n) → x ≢ p → x ≢ q → x ≢ r → x ≢ s →
          ∀ (y : Bits n) → HH2 p q r s x y ≡ √2 * (√2 * δb x y)
  HH2-o x xp xq xr xs y =
    Eq.trans (prod-row-o p q (hadOp r s) x xp xq y)
             (Eq.cong (√2 *_) (had-o r s x xr xs y))

------------------------------------------------------------------------
-- The four values a diagonal entry can take
--
-- On its own pairs the pair's diagonal is ±√2 and elsewhere it is 2,
-- and those are three different elements of ℤ[√2] — which is what
-- tells a signed permutation commuting with the pair where it may
-- send each index.  ±1 is a unit, so it cancels.

√2≢0 : √2 ≢ 0#
√2≢0 ()

√2≢2 : √2 ≢ √2 * √2
√2≢2 ()

-√2≢2 : -1# * √2 ≢ √2 * √2
-√2≢2 ()

√2≢-√2 : √2 ≢ -1# * √2
√2≢-√2 ()

-- √2 times a sign is never zero, …
√2·≢0 : ∀ (b : Bool) → √2 * (if b then -1# else 1#) ≢ 0#
√2·≢0 true  ()
√2·≢0 false ()

-- … and it determines the sign.
sign-from : ∀ (b c : Bool) →
            (if b then -1# else 1#) * √2 ≡ √2 * (if c then -1# else 1#) → b ≡ c
sign-from false false _  = Eq.refl
sign-from true  true  _  = Eq.refl
sign-from false true  ()
sign-from true  false ()

-- Multiplication by a sign is injective.
sign-cancel : ∀ (b : Bool) (u v : 𝔽) →
              (if b then -1# else 1#) * u ≡ (if b then -1# else 1#) * v → u ≡ v
sign-cancel false u v e = Eq.trans (Eq.sym (*-identityˡ u)) (Eq.trans e (*-identityˡ v))
sign-cancel true  u v e =
  Eq.trans (Eq.sym (neg-neg u)) (Eq.trans (Eq.cong (-1# *_) e) (neg-neg v))
  where
  neg-neg : ∀ (x : 𝔽) → -1# * (-1# * x) ≡ x
  neg-neg x = Eq.trans (Eq.sym (*-assoc -1# -1# x)) (*-identityˡ x)

------------------------------------------------------------------------
-- The same two row lemmas, for an arbitrary left factor
--
-- `prod-row` above is the case where the left factor is a two-level
-- Hadamard; the commuting condition needs it with the *pair* on the
-- left, so here it is once more with the row assumed rather than
-- computed.

row-two : ∀ (c d : 𝔽) (i j : Bits n) (G H : Op n) (x : Bits n) →
          (∀ y → G x y ≡ c * δb i y + d * δb j y) →
          ∀ (y : Bits n) → (G ⊙ H) x y ≡ c * H i y + d * H j y
row-two c d i j G H x e y =
  Eq.trans (Σ-cong {f = λ z → G x z * H z y}
                    {g = λ z → c * (δb i z * H z y) + d * (δb j z * H z y)} step)
    (Eq.trans (Σ-add (λ z → c * (δb i z * H z y)) (λ z → d * (δb j z * H z y)))
              (Eq.cong₂ _+_
                (Eq.trans (Σ-scaleˡ c (λ z → δb i z * H z y))
                          (Eq.cong (c *_) (Σ-δˡ i (λ z → H z y))))
                (Eq.trans (Σ-scaleˡ d (λ z → δb j z * H z y))
                          (Eq.cong (d *_) (Σ-δˡ j (λ z → H z y))))))
  where
  step : ∀ (z : Bits n) →
         G x z * H z y ≡ c * (δb i z * H z y) + d * (δb j z * H z y)
  step z = Eq.trans (Eq.cong (_* H z y) (e z))
             (Eq.trans (*-distribʳ-+ (H z y) (c * δb i z) (d * δb j z))
                       (Eq.cong₂ _+_ (*-assoc c (δb i z) (H z y))
                                     (*-assoc d (δb j z) (H z y))))

row-one : ∀ (c : 𝔽) (i : Bits n) (G H : Op n) (x : Bits n) →
          (∀ y → G x y ≡ c * δb i y) →
          ∀ (y : Bits n) → (G ⊙ H) x y ≡ c * H i y
row-one c i G H x e y =
  Eq.trans (Σ-cong {f = λ z → G x z * H z y} {g = λ z → c * (δb i z * H z y)}
                   (λ z → Eq.trans (Eq.cong (_* H z y) (e z))
                                   (*-assoc c (δb i z) (H z y))))
           (Eq.trans (Σ-scaleˡ c (λ z → δb i z * H z y))
                     (Eq.cong (c *_) (Σ-δˡ i (λ z → H z y))))

------------------------------------------------------------------------
-- The diagonal of a Hadamard pair
--
-- +√2 on the first index of each of its pairs, −√2 on the second, and
-- 2 everywhere else.  Since those are three different elements, the
-- diagonal says where an index is — which is how Lemma A.6 pins down
-- a signed permutation that commutes with the pair.

module Diagonal (p q r s : Bits n)
                (pq : p ≢ q) (rs : r ≢ s)
                (pr : p ≢ r) (ps : p ≢ s) (qr : q ≢ r) (qs : q ≢ s)
  where

  open Entries p q r s pq rs pr ps qr qs

  diag-p : HH2 p q r s p p ≡ √2
  diag-p = Eq.trans (HH2-p p)
             (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (√2 *_) (δb-refl p))
                                               (*-identityʳ √2))
                                     (Eq.trans (Eq.cong (√2 *_)
                                                        (δ≢ q p (λ e → pq (Eq.sym e))))
                                               (*-zeroʳ √2)))
                      (+-identityʳ √2))

  diag-q : HH2 p q r s q q ≡ -1# * √2
  diag-q = Eq.trans (HH2-q q)
             (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (√2 *_) (δ≢ p q pq))
                                               (*-zeroʳ √2))
                                     (Eq.cong (-1# *_)
                                       (Eq.trans (Eq.cong (√2 *_) (δb-refl q))
                                                 (*-identityʳ √2))))
                      (+-identityˡ (-1# * √2)))

  diag-r : HH2 p q r s r r ≡ √2
  diag-r = Eq.trans (HH2-r r)
             (Eq.trans (Eq.cong (√2 *_)
                         (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (1# *_) (δb-refl r))
                                                           (*-identityʳ 1#))
                                                 (Eq.trans (Eq.cong (1# *_)
                                                             (δ≢ s r (λ e → rs (Eq.sym e))))
                                                           (*-zeroʳ 1#)))
                                   (+-identityʳ 1#)))
                      (*-identityʳ √2))

  diag-s : HH2 p q r s s s ≡ -1# * √2
  diag-s = Eq.trans (HH2-s s)
             (Eq.trans (Eq.cong (√2 *_)
                         (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (1# *_) (δ≢ r s rs))
                                                           (*-zeroʳ 1#))
                                                 (Eq.trans (Eq.cong (-1# *_) (δb-refl s))
                                                           (*-identityʳ -1#)))
                                   (+-identityˡ -1#)))
                      (*-comm √2 -1#))

  diag-o : ∀ (x : Bits n) → x ≢ p → x ≢ q → x ≢ r → x ≢ s →
           HH2 p q r s x x ≡ √2 * √2
  diag-o x xp xq xr xs =
    Eq.trans (HH2-o x xp xq xr xs x)
             (Eq.cong (√2 *_) (Eq.trans (Eq.cong (√2 *_) (δb-refl x))
                                        (*-identityʳ √2)))

  -- So a +√2 on the diagonal means the first index of one of the two
  -- pairs, and a −√2 the second.
  diag-is-√2 : ∀ (x : Bits n) → HH2 p q r s x x ≡ √2 → x ≡ p ⊎ x ≡ r
  diag-is-√2 x e = go (eqB x p) (eqB x q) (eqB x r) (eqB x s)
                      Eq.refl Eq.refl Eq.refl Eq.refl
    where
    go : ∀ (u v w t : Bool) → eqB x p ≡ u → eqB x q ≡ v → eqB x r ≡ w → eqB x s ≡ t →
         x ≡ p ⊎ x ≡ r
    go true _ _ _ eu _ _ _ = inj₁ (eqB-sound x p eu)
    go false true _ _ eu ev _ _ =
      ⊥-elim (√2≢-√2 (Eq.trans (Eq.sym e)
                               (Eq.trans (Eq.cong (λ z → HH2 p q r s z z)
                                                  (eqB-sound x q ev))
                                         diag-q)))
    go false false true _ eu ev ew _ = inj₂ (eqB-sound x r ew)
    go false false false true eu ev ew et =
      ⊥-elim (√2≢-√2 (Eq.trans (Eq.sym e)
                               (Eq.trans (Eq.cong (λ z → HH2 p q r s z z)
                                                  (eqB-sound x s et))
                                         diag-s)))
    go false false false false eu ev ew et =
      ⊥-elim (√2≢2 (Eq.trans (Eq.sym e)
                             (diag-o x (eqB-≢ x p eu) (eqB-≢ x q ev)
                                       (eqB-≢ x r ew) (eqB-≢ x s et))))

  diag-is--√2 : ∀ (x : Bits n) → HH2 p q r s x x ≡ -1# * √2 → x ≡ q ⊎ x ≡ s
  diag-is--√2 x e = go (eqB x p) (eqB x q) (eqB x r) (eqB x s)
                       Eq.refl Eq.refl Eq.refl Eq.refl
    where
    go : ∀ (u v w t : Bool) → eqB x p ≡ u → eqB x q ≡ v → eqB x r ≡ w → eqB x s ≡ t →
         x ≡ q ⊎ x ≡ s
    go true _ _ _ eu _ _ _ =
      ⊥-elim (√2≢-√2 (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ z → HH2 p q r s z z)
                                                          (eqB-sound x p eu))
                                                 diag-p))
                               e))
    go false true _ _ _ ev _ _ = inj₁ (eqB-sound x q ev)
    go false false true _ _ _ ew _ =
      ⊥-elim (√2≢-√2 (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ z → HH2 p q r s z z)
                                                          (eqB-sound x r ew))
                                                 diag-r))
                               e))
    go false false false true _ _ _ et = inj₂ (eqB-sound x s et)
    go false false false false eu ev ew et =
      ⊥-elim (-√2≢2 (Eq.trans (Eq.sym e)
                              (diag-o x (eqB-≢ x p eu) (eqB-≢ x q ev)
                                        (eqB-≢ x r ew) (eqB-≢ x s et))))

  -- An index away from both pairs, and the diagonal entry that says so.
  Outside : Bits n → Set
  Outside x = (x ≢ p) × (x ≢ q) × (x ≢ r) × (x ≢ s)

  diag-is-2 : ∀ (x : Bits n) → HH2 p q r s x x ≡ √2 * √2 → Outside x
  diag-is-2 x e = go (eqB x p) (eqB x q) (eqB x r) (eqB x s)
                     Eq.refl Eq.refl Eq.refl Eq.refl
    where
    go : ∀ (u v w t : Bool) → eqB x p ≡ u → eqB x q ≡ v → eqB x r ≡ w → eqB x s ≡ t →
         Outside x
    go true _ _ _ eu _ _ _ =
      ⊥-elim (√2≢2 (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ z → HH2 p q r s z z)
                                                        (eqB-sound x p eu))
                                               diag-p))
                             e))
    go false true _ _ _ ev _ _ =
      ⊥-elim (-√2≢2 (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ z → HH2 p q r s z z)
                                                         (eqB-sound x q ev))
                                                diag-q))
                              e))
    go false false true _ _ _ ew _ =
      ⊥-elim (√2≢2 (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ z → HH2 p q r s z z)
                                                        (eqB-sound x r ew))
                                               diag-r))
                             e))
    go false false false true _ _ _ et =
      ⊥-elim (-√2≢2 (Eq.trans (Eq.sym (Eq.trans (Eq.cong (λ z → HH2 p q r s z z)
                                                         (eqB-sound x s et))
                                                diag-s))
                              e))
    go false false false false eu ev ew et =
      eqB-≢ x p eu , eqB-≢ x q ev , eqB-≢ x r ew , eqB-≢ x s et
