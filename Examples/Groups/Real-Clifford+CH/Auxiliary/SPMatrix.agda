------------------------------------------------------------------------
-- Presentations of groups
--
-- A signed permutation as a matrix
--
-- `SignedPerm` reads a Hadamard-free word over P as a permutation of
-- the 2ⁿ basis indices together with a sign on each, and that is all
-- Corollary A.5 needs.  What comes after it does not: Lemma A.6 asks
-- which such words *commute with a Hadamard pair*, which is a question
-- about matrices.  This module says that the two readings agree — the
-- matrix of a Hadamard-free word is the matrix of its signed
-- permutation — so that the one can be used to answer questions about
-- the other.
--
-- The composition of `SignedPerm` has the left factor acting first,
-- and `(M ⊙ N) x y` sums `M x z * N z y`, so the two agree on the
-- nose; `Σ-δˡ` collapses the sum, every signed permutation matrix
-- having exactly one non-zero entry in each row.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ) renaming (_^_ to _^ℕ_ ; _+_ to _+ℕ_)

module Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_ ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Data.Vec using ([] ; _∷_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (code ; index ; code-index ; index-code ; code-injective)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices
  using (eqB ; negOp ; swapOp ; ⟦_⟧ᴳ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
  using (eqB-sound ; eqB-complete ; eqB-false)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP ; ⟦_⟧ᴾ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFree ; hf-zz ; hf-zx ; hf-xx ; HFreeʷ ; gen ; nil ; cat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sgn ; prm ; sgn≡ ; prm≡ ; idSP ; NEG ; SWP ; δ ; δ-here ; δ-≢
       ; swapF ; swapF-a ; swapF-b ; swapF-o ; sp ; spg)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; eqv to eqv′)

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

  W : Set
  W = Word (GenP n)

------------------------------------------------------------------------
-- The matrix of a signed permutation

sgnOf : Bool → 𝔽
sgnOf true  = -1#
sgnOf false = 1#

sgnOf-if : ∀ (b : Bool) → sgnOf b ≡ (if b then -1# else 1#)
sgnOf-if true  = Eq.refl
sgnOf-if false = Eq.refl

sgnOf-xor : ∀ (a b : Bool) → sgnOf (a xor b) ≡ sgnOf a * sgnOf b
sgnOf-xor false false = Eq.refl
sgnOf-xor false true  = Eq.refl
sgnOf-xor true  false = Eq.refl
sgnOf-xor true  true  = Eq.refl

spOp : SP → Op n
spOp f x y = sgnOf (sgn f (index n x)) * δb (code n (prm f (index n x))) y

spOp-cong : ∀ {f g : SP} → f ≗ g → spOp f ≐ spOp g
spOp-cong e x y =
  Eq.cong₂ _*_ (Eq.cong sgnOf (sgn≡ e (index n x)))
               (Eq.cong (λ z → δb (code n z) y) (prm≡ e (index n x)))

spOp-id : spOp idSP ≐ Idₒ
spOp-id x y =
  Eq.trans (*-identityˡ (δb (code n (index n x)) y))
           (Eq.cong (λ z → δb z y) (code-index n x))

-- The reading is multiplicative: one non-zero entry per row, so the
-- sum of the matrix product has one surviving term.
spOp-⊙ : ∀ (f g : SP) → spOp (f ⊛ g) ≐ (spOp f ⊙ spOp g)
spOp-⊙ f g x y = Eq.trans lhs (Eq.sym rhs)
  where
  i = index n x
  j = prm f i

  lhs : spOp (f ⊛ g) x y
      ≡ sgnOf (sgn f i) * (sgnOf (sgn g j) * δb (code n (prm g j)) y)
  lhs = Eq.trans (Eq.cong (_* δb (code n (prm g j)) y) (sgnOf-xor (sgn f i) (sgn g j)))
                 (*-assoc (sgnOf (sgn f i)) (sgnOf (sgn g j))
                          (δb (code n (prm g j)) y))

  rhs : (spOp f ⊙ spOp g) x y
      ≡ sgnOf (sgn f i) * (sgnOf (sgn g j) * δb (code n (prm g j)) y)
  rhs = Eq.trans
          (Eq.trans (Σ-cong {f = λ z → spOp f x z * spOp g z y}
                             {g = λ z → sgnOf (sgn f i) * (δb (code n j) z * spOp g z y)}
                             (λ z → *-assoc (sgnOf (sgn f i)) (δb (code n j) z)
                                            (spOp g z y)))
                    (Σ-scaleˡ (sgnOf (sgn f i)) (λ z → δb (code n j) z * spOp g z y)))
          (Eq.cong (sgnOf (sgn f i) *_)
                   (Eq.trans (Σ-δˡ (code n j) (λ z → spOp g z y)) step))
    where
    step : spOp g (code n j) y ≡ sgnOf (sgn g j) * δb (code n (prm g j)) y
    step = Eq.cong₂ _*_ (Eq.cong (λ z → sgnOf (sgn g z)) (index-code n j))
                        (Eq.cong (λ z → δb (code n (prm g z)) y) (index-code n j))

------------------------------------------------------------------------
-- The atoms are the one- and two-level matrices

private
  -- An index is the one carrying the sign exactly when the bitstrings
  -- agree, the Gray code being a bijection.  Both case splits below
  -- decide in a helper: a `with` would rewrite the goal into the shape
  -- of `δ`'s and `swapF`'s own splits, and their characterisations
  -- would no longer apply.
  code≡ : ∀ (a : Fin N) (x : Bits n) → index n x ≡ a → x ≡ code n a
  code≡ a x q = Eq.trans (Eq.sym (code-index n x)) (Eq.cong (code n) q)

  index≢ : ∀ (a : Fin N) (x : Bits n) → index n x ≢ a → x ≢ code n a
  index≢ a x ¬p e = ¬p (Eq.trans (Eq.cong (index n) e) (index-code n a))

  δ-eqB : ∀ (a : Fin N) (x : Bits n) → δ a (index n x) ≡ eqB x (code n a)
  δ-eqB a x = go (index n x ≟ᶠ a)
    where
    go : Dec (index n x ≡ a) → δ a (index n x) ≡ eqB x (code n a)
    go (yes p) =
      Eq.trans (Eq.subst (λ z → δ z (index n x) ≡ true) p (δ-here (index n x)))
               (Eq.sym (eqB-complete x (code n a) (code≡ a x p)))
    go (no ¬p) =
      Eq.trans (δ-≢ a (index n x) ¬p)
               (Eq.sym (eqB-false x (code n a) (index≢ a x ¬p)))

spOp-NEG : ∀ (a : Fin N) → spOp (NEG a) ≐ negOp (code n a)
spOp-NEG a x y =
  Eq.cong₂ _*_ (Eq.trans (sgnOf-if (δ a (index n x)))
                         (Eq.cong (λ t → if t then -1# else 1#) (δ-eqB a x)))
               (Eq.cong (λ z → δb z y) (code-index n x))

spOp-SWP : ∀ (a b : Fin N) → spOp (SWP a b) ≐ swapOp (code n a) (code n b)
spOp-SWP a b x y =
  Eq.trans (*-identityˡ (δb (code n (swapF a b (index n x))) y))
           (Eq.cong (λ z → δb z y) (target (index n x ≟ᶠ a) (index n x ≟ᶠ b)))
  where
  i = index n x

  target : Dec (i ≡ a) → Dec (i ≡ b) →
           code n (swapF a b i)
           ≡ (if eqB x (code n a) then code n b
              else if eqB x (code n b) then code n a else x)
  target (yes p) _ =
    Eq.trans (Eq.cong (λ z → code n (swapF a b z)) p)
      (Eq.trans (Eq.cong (code n) (swapF-a a b))
                (Eq.sym (Eq.cong (λ t → if t then code n b
                                        else if eqB x (code n b) then code n a else x)
                                 (eqB-complete x (code n a) (code≡ a x p)))))
  target (no ¬p) (yes q) =
    Eq.trans (Eq.cong (λ z → code n (swapF a b z)) q)
      (Eq.trans (Eq.cong (code n) (swapF-b a b))
                (Eq.sym (Eq.trans
                  (Eq.cong (λ t → if t then code n b
                                  else if eqB x (code n b) then code n a else x)
                           (eqB-false x (code n a) (index≢ a x ¬p)))
                  (Eq.cong (λ t → if t then code n a else x)
                           (eqB-complete x (code n b) (code≡ b x q))))))
  target (no ¬p) (no ¬q) =
    Eq.trans (Eq.cong (code n) (swapF-o a b i ¬p ¬q))
      (Eq.trans (code-index n x)
                (Eq.sym (Eq.trans
                  (Eq.cong (λ t → if t then code n b
                                  else if eqB x (code n b) then code n a else x)
                           (eqB-false x (code n a) (index≢ a x ¬p)))
                  (Eq.cong (λ t → if t then code n a else x)
                           (eqB-false x (code n b) (index≢ b x ¬q))))))

------------------------------------------------------------------------
-- A Hadamard-free word and its signed permutation have one matrix

gen-sem : ∀ {g : GenP n} → HFree g → proj₂ ⟦ g ⟧ᴾ ≐ spOp (spg g)
gen-sem (hf-zz a b) =
  ≐-sym (≐-trans (spOp-⊙ (NEG a) (NEG b))
                 (⊙-cong (spOp-NEG a) (spOp-NEG b)))
gen-sem (hf-zx c a b ni) =
  ≐-sym (≐-trans (spOp-⊙ (NEG c) (SWP a b))
                 (⊙-cong (spOp-NEG c) (spOp-SWP a b)))
gen-sem (hf-xx a b c d ni ni′) =
  ≐-sym (≐-trans (spOp-⊙ (SWP a b) (SWP c d))
                 (⊙-cong (spOp-SWP a b) (spOp-SWP c d)))

-- The reading of a word, letter by letter.
⟦_⟧ʷ : W → Scaled n
⟦ [ g ]ʷ ⟧ʷ = ⟦ g ⟧ᴾ
⟦ ε ⟧ʷ      = ε∙
⟦ u • v ⟧ʷ  = ⟦ u ⟧ʷ ∙ ⟦ v ⟧ʷ

-- A Hadamard-free word carries no power of 1/√2 …
word-scale : ∀ {w : W} → HFreeʷ w → proj₁ ⟦ w ⟧ʷ ≡ 0
word-scale (gen (hf-zz a b))          = Eq.refl
word-scale (gen (hf-zx c a b ni))     = Eq.refl
word-scale (gen (hf-xx a b c d ni n′)) = Eq.refl
word-scale nil                        = Eq.refl
word-scale (cat p q) = Eq.cong₂ _+ℕ_ (word-scale p) (word-scale q)

-- … and its matrix is that of its signed permutation.
word-op : ∀ {w : W} → HFreeʷ w → proj₂ ⟦ w ⟧ʷ ≐ spOp (sp w)
word-op (gen h)   = gen-sem h
word-op nil       = ≐-sym spOp-id
word-op {u • v} (cat p q) =
  ≐-trans (⊙-cong (word-op p) (word-op q)) (≐-sym (spOp-⊙ (sp u) (sp v)))

------------------------------------------------------------------------
-- The reading is faithful
--
-- A signed permutation matrix has one non-zero entry in each row, and
-- that entry is ±1, so the matrix determines both halves.  With that,
-- the hypothesis of Corollary A.5 can be given as an equality of
-- matrices — which is how the paper states it.

private
  δb-≢ : ∀ {k : ℕ} (x y : Bits k) → x ≢ y → δb x y ≡ 0#
  δb-≢ []           []           ne = ⊥-elim (ne Eq.refl)
  δb-≢ (true  ∷ xs) (true  ∷ ys) ne = δb-≢ xs ys (λ e → ne (Eq.cong (true ∷_) e))
  δb-≢ (false ∷ xs) (false ∷ ys) ne = δb-≢ xs ys (λ e → ne (Eq.cong (false ∷_) e))
  δb-≢ (true  ∷ xs) (false ∷ ys) ne = Eq.refl
  δb-≢ (false ∷ xs) (true  ∷ ys) ne = Eq.refl

  sgnOf≢0 : ∀ (b : Bool) → sgnOf b ≢ 0#
  sgnOf≢0 true  ()
  sgnOf≢0 false ()

  sgnOf-inj : ∀ (a b : Bool) → sgnOf a ≡ sgnOf b → a ≡ b
  sgnOf-inj true  true  _  = Eq.refl
  sgnOf-inj false false _  = Eq.refl
  sgnOf-inj true  false ()
  sgnOf-inj false true  ()

spOp-inj : ∀ {f g : SP} → spOp f ≐ spOp g → f ≗ g
spOp-inj {f} {g} e = eqv′ (λ i → sgnEq i (prmEq i)) prmEq
  where
  -- The row at an index, read at the column where f is non-zero.
  row : ∀ (i : Fin N) →
        sgnOf (sgn f i) * δb (code n (prm f i)) (code n (prm f i))
        ≡ sgnOf (sgn g i) * δb (code n (prm g i)) (code n (prm f i))
  row i = Eq.subst
            (λ j → sgnOf (sgn f j) * δb (code n (prm f j)) (code n (prm f i))
                 ≡ sgnOf (sgn g j) * δb (code n (prm g j)) (code n (prm f i)))
            (index-code n i)
            (e (code n i) (code n (prm f i)))

  lhs : ∀ (i : Fin N) →
        sgnOf (sgn f i) * δb (code n (prm f i)) (code n (prm f i)) ≡ sgnOf (sgn f i)
  lhs i = Eq.trans (Eq.cong (sgnOf (sgn f i) *_) (δb-refl (code n (prm f i))))
                   (*-identityʳ (sgnOf (sgn f i)))

  prmEq : ∀ (i : Fin N) → prm f i ≡ prm g i
  prmEq i = go (prm f i ≟ᶠ prm g i)
    where
    go : Dec (prm f i ≡ prm g i) → prm f i ≡ prm g i
    go (yes p) = p
    go (no ¬p) = ⊥-elim (sgnOf≢0 (sgn f i)
      (Eq.trans (Eq.sym (lhs i))
                (Eq.trans (row i)
                          (Eq.trans (Eq.cong (sgnOf (sgn g i) *_)
                                             (δb-≢ (code n (prm g i)) (code n (prm f i))
                                                   (λ c → ¬p (Eq.sym (code-injective n c)))))
                                    (*-zeroʳ (sgnOf (sgn g i)))))))

  sgnEq : ∀ (i : Fin N) → prm f i ≡ prm g i → sgn f i ≡ sgn g i
  sgnEq i p = sgnOf-inj (sgn f i) (sgn g i)
    (Eq.trans (Eq.sym (lhs i))
              (Eq.trans (row i)
                        (Eq.trans (Eq.cong (λ z → sgnOf (sgn g i) * δb (code n z)
                                                                      (code n (prm f i)))
                                           (Eq.sym p))
                                  (lhs′ i))))
    where
    lhs′ : ∀ (i : Fin N) →
           sgnOf (sgn g i) * δb (code n (prm f i)) (code n (prm f i)) ≡ sgnOf (sgn g i)
    lhs′ i = Eq.trans (Eq.cong (sgnOf (sgn g i) *_) (δb-refl (code n (prm f i))))
                      (*-identityʳ (sgnOf (sgn g i)))

------------------------------------------------------------------------
-- Corollary A.5, as the paper states it

private
  ~⇒≐ : ∀ {s t : Scaled n} → proj₁ s ≡ 0 → proj₁ t ≡ 0 → s ~ t → proj₂ s ≐ proj₂ t
  ~⇒≐ {s} {t} e₁ e₂ h x y =
    Eq.trans (Eq.sym (*-identityˡ (proj₂ s x y)))
      (Eq.trans (Eq.cong (λ l → √2^ l * proj₂ s x y) (Eq.sym e₂))
        (Eq.trans (h x y)
          (Eq.trans (Eq.cong (λ l → √2^ l * proj₂ t x y) e₁)
                    (*-identityˡ (proj₂ t x y)))))

-- Two Hadamard-free words with the same matrix are equivalent.
A5-mat : ∀ {u v : W} → HFreeʷ u → HFreeʷ v → ⟦ u ⟧ʷ ~ ⟦ v ⟧ʷ →
         PB._≈_ (m P,_===_) u v
A5-mat hu hv h =
  A5-full hu hv
    (spOp-inj (≐-trans (≐-sym (word-op hu))
                       (≐-trans (~⇒≐ (word-scale hu) (word-scale hv) h) (word-op hv))))
