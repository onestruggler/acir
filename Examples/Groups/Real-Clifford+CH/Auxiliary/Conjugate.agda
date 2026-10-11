------------------------------------------------------------------------
-- Presentations of groups
--
-- Conjugating a matrix by a signed permutation
--
-- Equation (65) says that H_[a,b] H_[c,d] is the standard pair with a
-- Hadamard-free word on each side; Corollary A.7 reduces it to the two
-- words being inverse and to (65) being *sound*, which is this
-- computation: conjugating any matrix by a signed permutation and its
-- inverse pulls the matrix back along the permutation and conjugates
-- it by the signs,
--
--     (F M G) x y  =  σ x · M (π x) (π y) · σ y ,
--
-- there being one non-zero entry per row on each side.  For a
-- two-level Hadamard the pull-back is again one, on the indices the
-- permutation came from (`had-pull`), so a sign-free permutation
-- carries the standard pair to the pair on the images.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Conjugate (m : ℕ) where

open import Data.Nat renaming (_^_ to _^ℕ_) using ()
open import Data.Bool using (Bool ; true ; false ; _xor_ ; if_then_else_)
open import Data.Bool.Properties renaming (_≟_ to _≟ᵇ_) using ()
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Vec using ([] ; _∷_)
open import Data.Vec.Properties using (≡-dec)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
  using (eqB-sound ; eqB-complete ; eqB-false)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (code ; index ; code-index ; index-code ; code-injective)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB ; hadOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sgn ; prm ; sgn≡ ; prm≡ ; idSP ; Inj ; ⊙-inverse)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix m
  using (spOp ; sgnOf ; spOp-⊙ ; spOp-cong ; spOp-id)

private
  n : ℕ
  n = ₃₊ m

  -- Bitstrings have decidable equality.
  _≟ᵇˢ_ : ∀ {k} (x y : Bits k) → Dec (x ≡ y)
  _≟ᵇˢ_ = ≡-dec _≟ᵇ_

------------------------------------------------------------------------
-- A delta at a bitstring

private
  δ≡ : ∀ {k} (x y : Bits k) → x ≡ y → δb x y ≡ 1#
  δ≡ x y Eq.refl = δb-refl x

  δ≢′ : ∀ {k} (x y : Bits k) → x ≢ y → δb x y ≡ 0#
  δ≢′ []           []           ne = ⊥-elim (ne Eq.refl)
  δ≢′ (true  ∷ xs) (true  ∷ ys) ne = δ≢′ xs ys (λ e → ne (Eq.cong (true ∷_) e))
  δ≢′ (false ∷ xs) (false ∷ ys) ne = δ≢′ xs ys (λ e → ne (Eq.cong (false ∷_) e))
  δ≢′ (true  ∷ xs) (false ∷ ys) ne = Eq.refl
  δ≢′ (false ∷ xs) (true  ∷ ys) ne = Eq.refl

  -- Two deltas that are true together are equal.
  δ-iff : ∀ {k} (u v x y : Bits k) → (u ≡ v → x ≡ y) → (x ≡ y → u ≡ v) →
          δb u v ≡ δb x y
  δ-iff u v x y f g = go (u ≟ᵇˢ v)
    where
    go : Dec (u ≡ v) → δb u v ≡ δb x y
    go (yes e) = Eq.trans (δ≡ u v e) (Eq.sym (δ≡ x y (f e)))
    go (no ne) = Eq.trans (δ≢′ u v ne) (Eq.sym (δ≢′ x y (λ e → ne (g e))))

------------------------------------------------------------------------
-- The conjugation
--
-- `f` acts first, so `spOp f` is the left factor; `g` is its inverse.

module Conj (f g : SP) (gi : Inj g) (inv : f ⊛ g ≗ idSP) where

  π : Bits n → Bits n
  π x = code n (prm f (index n x))

  σ : Bits n → Bool
  σ x = sgn f (index n x)

  private
    -- `g` undoes `f` on indices, both ways round, and carries the same
    -- sign at the transported index.
    undo : ∀ (i : Fin (2 ^ℕ n)) → prm g (prm f i) ≡ i
    undo i = prm≡ inv i

    undo′ : ∀ (i : Fin (2 ^ℕ n)) → prm f (prm g i) ≡ i
    undo′ i = prm≡ (⊙-inverse f g gi inv) i

    sgn-g : ∀ (i : Fin (2 ^ℕ n)) → sgn g (prm f i) ≡ sgn f i
    sgn-g i = go (sgn f i) (sgn g (prm f i)) (sgn≡ inv i)
      where
      go : ∀ (u v : Bool) → u xor v ≡ false → v ≡ u
      go false false _ = Eq.refl
      go true  true  _ = Eq.refl

    -- The index of `π y` is where `f` sent `y`.
    ix-π : ∀ (y : Bits n) → index n (π y) ≡ prm f (index n y)
    ix-π y = index-code n (prm f (index n y))

    -- `g`'s delta at `w` fires exactly at `w ≡ π y`.
    right-δ : ∀ (w y : Bits n) → δb (code n (prm g (index n w))) y ≡ δb w (π y)
    right-δ w y = δ-iff (code n (prm g (index n w))) y w (π y) there back
      where
      there : code n (prm g (index n w)) ≡ y → w ≡ π y
      there e = Eq.trans (Eq.sym (code-index n w)) (Eq.cong (code n) step)
        where
        h : prm g (index n w) ≡ index n y
        h = Eq.trans (Eq.sym (index-code n (prm g (index n w))))
                     (Eq.cong (index n) e)

        step : index n w ≡ prm f (index n y)
        step = Eq.trans (Eq.sym (undo′ (index n w))) (Eq.cong (prm f) h)

      back : w ≡ π y → code n (prm g (index n w)) ≡ y
      back e =
        Eq.trans (Eq.cong (λ z → code n (prm g (index n z))) e)
          (Eq.trans (Eq.cong (λ z → code n (prm g z)) (ix-π y))
            (Eq.trans (Eq.cong (code n) (undo (index n y))) (code-index n y)))

    -- One half of the product: the right factor collapses its sum.
    half : ∀ (M : Op n) (z y : Bits n) →
           (M ⊙ spOp g) z y ≡ M z (π y) * sgnOf (σ y)
    half M z y =
      Eq.trans
        (Σ-cong {f = λ w → M z w * spOp g w y}
                {g = λ w → (M z w * sgnOf (sgn g (index n w))) * δb w (π y)}
                (λ w → Eq.trans
                  (Eq.cong (M z w *_)
                    (Eq.cong (sgnOf (sgn g (index n w)) *_) (right-δ w y)))
                  (Eq.sym (*-assoc (M z w) (sgnOf (sgn g (index n w))) (δb w (π y))))))
        (Eq.trans (Σ-δʳ (π y) (λ w → M z w * sgnOf (sgn g (index n w))))
                  (Eq.cong (λ b → M z (π y) * sgnOf b)
                    (Eq.trans (Eq.cong (sgn g) (ix-π y)) (sgn-g (index n y)))))

  -- Conjugating pulls back along the permutation and conjugates by
  -- the signs.
  conj : ∀ (M : Op n) (x y : Bits n) →
         (spOp f ⊙ (M ⊙ spOp g)) x y
         ≡ sgnOf (σ x) * (M (π x) (π y) * sgnOf (σ y))
  conj M x y =
    Eq.trans
      (Σ-cong {f = λ z → spOp f x z * (M ⊙ spOp g) z y}
              {g = λ z → sgnOf (σ x) * (δb (π x) z * (M ⊙ spOp g) z y)}
              (λ z → *-assoc (sgnOf (σ x)) (δb (π x) z) ((M ⊙ spOp g) z y)))
      (Eq.trans (Σ-scaleˡ (sgnOf (σ x)) (λ z → δb (π x) z * (M ⊙ spOp g) z y))
        (Eq.cong (sgnOf (σ x) *_)
          (Eq.trans (Σ-δˡ (π x) (λ z → (M ⊙ spOp g) z y)) (half M (π x) y))))

------------------------------------------------------------------------
-- A two-level Hadamard pulled back
--
-- If the permutation carries a and b to p and q then the pair's rows
-- at the images are the pair's own rows on a and b.

module _ (π : Bits n → Bits n)
         (π-inj : ∀ {x y : Bits n} → π x ≡ π y → x ≡ y)
  where

  private
    δ-π : ∀ (x y : Bits n) → δb (π x) (π y) ≡ δb x y
    δ-π x y = δ-iff (π x) (π y) x y π-inj (Eq.cong π)

    -- `eqB (π x) (π a)` decides `x ≡ a` just as `eqB x a` does.
    eq-π : ∀ (x a : Bits n) → eqB (π x) (π a) ≡ eqB x a
    eq-π x a = go (x ≟ᵇˢ a)
      where
      go : Dec (x ≡ a) → eqB (π x) (π a) ≡ eqB x a
      go (yes Eq.refl) = Eq.trans (eqB-complete (π x) (π a) Eq.refl)
                                  (Eq.sym (eqB-complete x a Eq.refl))
      go (no ne) = Eq.trans (eqB-false (π x) (π a) (λ e → ne (π-inj e)))
                            (Eq.sym (eqB-false x a ne))

  had-pull : ∀ (a b : Bits n) (x y : Bits n) →
             hadOp (π a) (π b) (π x) (π y) ≡ hadOp a b x y
  had-pull a b x y
    rewrite eq-π x a | eq-π x b | eq-π y a | eq-π y b | δ-π x y = Eq.refl

------------------------------------------------------------------------
-- Signs a two-level Hadamard does not see
--
-- Conjugating by a diagonal of ±1 multiplies the entry at (x , y) by
-- the signs at x and at y.  A two-level Hadamard's non-zero entries
-- are on its own pair and on the diagonal, so the product of the two
-- signs is 1 at every one of them as soon as the two signs of the pair
-- agree — which is all Definition E.1's word gives, its letters each
-- carrying a sign of their own.

private
  sgnOf-sq : ∀ (b : Bool) → sgnOf b * sgnOf b ≡ 1#
  sgnOf-sq true  = Eq.refl
  sgnOf-sq false = Eq.refl

had-sign : ∀ (σ : Bits n → Bool) (a b x y : Bits n) → σ a ≡ σ b →
           sgnOf (σ x) * (hadOp a b x y * sgnOf (σ y)) ≡ hadOp a b x y
had-sign σ a b x y sab = goA (x ≟ᵇˢ a)
  where
  h : 𝔽
  h = hadOp a b x y

  -- When the two signs agree they cancel.
  keep : σ x ≡ σ y → sgnOf (σ x) * (h * sgnOf (σ y)) ≡ h
  keep e =
    Eq.trans (Eq.cong (λ t → sgnOf (σ x) * (h * sgnOf t)) (Eq.sym e))
      (Eq.trans (Eq.cong (sgnOf (σ x) *_) (*-comm h (sgnOf (σ x))))
        (Eq.trans (Eq.sym (*-assoc (sgnOf (σ x)) (sgnOf (σ x)) h))
          (Eq.trans (Eq.cong (_* h) (sgnOf-sq (σ x))) (*-identityˡ h))))

  -- And where they do not, the entry is zero.
  kill : h ≡ 0# → sgnOf (σ x) * (h * sgnOf (σ y)) ≡ h
  kill e =
    Eq.trans (Eq.cong (λ z → sgnOf (σ x) * (z * sgnOf (σ y))) e)
      (Eq.trans (Eq.cong (sgnOf (σ x) *_) (*-zeroˡ (sgnOf (σ y))))
        (Eq.trans (*-zeroʳ (sgnOf (σ x))) (Eq.sym e)))

  -- The three shapes of a row.
  row-a : x ≡ a → eqB y a ≡ false → eqB y b ≡ false → h ≡ 0#
  row-a Eq.refl ea eb rewrite eqB-complete x x Eq.refl | ea | eb = Eq.refl

  row-b : x ≡ b → eqB x a ≡ false → eqB y a ≡ false → eqB y b ≡ false → h ≡ 0#
  row-b Eq.refl xa ea eb rewrite xa | eqB-complete x x Eq.refl | ea | eb = Eq.refl

  row-o : eqB x a ≡ false → eqB x b ≡ false → δb x y ≡ 0# → h ≡ 0#
  row-o xa xb d rewrite xa | xb | d = *-zeroʳ √2

  goA : Dec (x ≡ a) → sgnOf (σ x) * (h * sgnOf (σ y)) ≡ h
  goA (yes Eq.refl) = go (y ≟ᵇˢ x) (y ≟ᵇˢ b)
    where
    go : Dec (y ≡ x) → Dec (y ≡ b) → sgnOf (σ x) * (h * sgnOf (σ y)) ≡ h
    go (yes Eq.refl) _             = keep Eq.refl
    go (no _)        (yes Eq.refl) = keep sab
    go (no ny)       (no nb)       =
      kill (row-a Eq.refl (eqB-false y x ny) (eqB-false y b nb))
  goA (no na) = goB (x ≟ᵇˢ b)
    where
    goB : Dec (x ≡ b) → sgnOf (σ x) * (h * sgnOf (σ y)) ≡ h
    goB (yes Eq.refl) = go (y ≟ᵇˢ a) (y ≟ᵇˢ x)
      where
      go : Dec (y ≡ a) → Dec (y ≡ x) → sgnOf (σ x) * (h * sgnOf (σ y)) ≡ h
      go (yes Eq.refl) _             = keep (Eq.sym sab)
      go (no _)        (yes Eq.refl) = keep Eq.refl
      go (no ny)       (no nx)       =
        kill (row-b Eq.refl (eqB-false x a na) (eqB-false y a ny)
                            (eqB-false y x nx))
    goB (no nb) = go (x ≟ᵇˢ y)
      where
      go : Dec (x ≡ y) → sgnOf (σ x) * (h * sgnOf (σ y)) ≡ h
      go (yes Eq.refl) = keep Eq.refl
      go (no ny) =
        kill (row-o (eqB-false x a na) (eqB-false x b nb) (δ≢′ x y ny))

------------------------------------------------------------------------
-- Conjugation is multiplicative
--
-- Over abstract operators: with the matrices in place the conversion
-- checker expands every `⊙` into its sum over bitstrings.

conj-mult : ∀ (F G A B : Op n) → (G ⊙ F) ≐ Idₒ →
            (F ⊙ ((A ⊙ B) ⊙ G)) ≐ ((F ⊙ (A ⊙ G)) ⊙ (F ⊙ (B ⊙ G)))
conj-mult F G A B e =
  ≐-trans (⊙-cong (≐-refl F) (⊙-assoc A B G))
  (≐-trans (⊙-cong (≐-refl F)
             (⊙-cong (≐-refl A)
               (≐-trans (≐-sym (⊙-identityˡ (B ⊙ G)))
                        (⊙-cong (≐-sym e) (≐-refl (B ⊙ G))))))
  (≐-trans (⊙-cong (≐-refl F)
             (≐-trans (⊙-cong (≐-refl A) (⊙-assoc G F (B ⊙ G)))
                      (≐-sym (⊙-assoc A G (F ⊙ (B ⊙ G))))))
           (≐-sym (⊙-assoc F (A ⊙ G) (F ⊙ (B ⊙ G))))))

------------------------------------------------------------------------
-- A sign-free permutation carries the standard pair to the pair on
-- the indices it came from

module Pull (f g : SP) (gi : Inj g) (inv : f ⊛ g ≗ idSP) where

  open Conj f g gi inv using (π ; σ ; conj)

  private
    -- `prm f` is injective: `prm g` is a left inverse for it.
    f-inj : ∀ {i j : Fin (2 ^ℕ n)} → prm f i ≡ prm f j → i ≡ j
    f-inj {i} {j} e =
      Eq.trans (Eq.sym (prm≡ inv i))
               (Eq.trans (Eq.cong (prm g) e) (prm≡ inv j))

    π-inj : ∀ {x y : Bits n} → π x ≡ π y → x ≡ y
    π-inj {x} {y} e =
      Eq.trans (Eq.sym (code-index n x))
        (Eq.trans (Eq.cong (code n) (f-inj (code-injective n e)))
                  (code-index n y))

    -- The inverse pair of matrices.
    GF : (spOp g ⊙ spOp f) ≐ Idₒ
    GF = ≐-trans (≐-sym (spOp-⊙ g f))
                 (≐-trans (spOp-cong (⊙-inverse f g gi inv)) spOp-id)

  -- One two-level Hadamard: the permutation moves its pair, and the
  -- signs cancel as soon as they agree along the pair.
  conj-had : ∀ (a b : Bits n) → σ a ≡ σ b →
             (spOp f ⊙ (hadOp (π a) (π b) ⊙ spOp g)) ≐ hadOp a b
  conj-had a b sab x y =
    Eq.trans (conj (hadOp (π a) (π b)) x y)
      (Eq.trans (Eq.cong (λ z → sgnOf (σ x) * (z * sgnOf (σ y)))
                         (had-pull π π-inj a b x y))
                (had-sign σ a b x y sab))

  -- And the pair.
  conj-pair : ∀ (a b c d : Bits n) → σ a ≡ σ b → σ c ≡ σ d →
              (spOp f ⊙ ((hadOp (π a) (π b) ⊙ hadOp (π c) (π d)) ⊙ spOp g))
              ≐ (hadOp a b ⊙ hadOp c d)
  conj-pair a b c d sab scd =
    ≐-trans (conj-mult (spOp f) (spOp g) (hadOp (π a) (π b)) (hadOp (π c) (π d)) GF)
            (⊙-cong (conj-had a b sab) (conj-had c d scd))
