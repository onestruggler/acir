------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma A.6
--
-- `Commutant` says what a signed permutation commuting with a Hadamard
-- pair does to the pair's four indices, and `Passes` says that every
-- word doing that to them crosses the pair inside a derivation.  This
-- module joins the two: it reads a Hadamard-free word's matrix as the
-- signed permutation it is (`SPMatrix`), takes the pair's four indices
-- to be the paper's 0, 1, 3 and 2 in the Gray code, and turns the
-- bitstring-level conclusion back into a statement about `sp w`.
--
-- The result is Lemma A.6 in the form Corollary A.7 consumes it: not
-- the shape of a commuting word, but that it passes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.A6 (m : ℕ) where

open import Data.Bool using (Bool ; false)
open import Data.Nat renaming (_^_ to _^ℕ_ ; _+_ to _+ℕ_) using ()
open import Data.Fin using (Fin)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (code ; index ; code-index ; index-code ; code-injective)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.HadamardPair m using (HH2)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (hadOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m using (HFreeʷ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sp ; sgn ; prm ; sp-inj ; Inj ; idSP)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix m
  using (spOp ; sgnOf ; sgnOf-if ; word-op ; word-scale ; ⟦_⟧ʷ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; Λw ; hh0132≡
       ; i₀≢i₁ ; i₀≢i₂ ; i₀≢i₃ ; i₁≢i₂ ; i₁≢i₃ ; i₂≢i₃ ; i₃≢i₂)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m
  using (Passes ; passes-A6 ; Λ)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Conjugate m
  using (module Pull ; module Conj)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Commutant m as CM

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

  W : Set
  W = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- The pair's four indices, as basis vectors

P₀ P₁ P₂ P₃ : Bits n
P₀ = code n i₀
P₁ = code n i₁
P₂ = code n i₂
P₃ = code n i₃

private
  dif : ∀ {a b : Fin (2 ^ℕ n)} → a ≢ b → code n a ≢ code n b
  dif ne e = ne (code-injective n e)

  d₀₁ : P₀ ≢ P₁
  d₀₁ = dif i₀≢i₁

  d₃₂ : P₃ ≢ P₂
  d₃₂ = dif i₃≢i₂

  d₀₃ : P₀ ≢ P₃
  d₀₃ = dif i₀≢i₃

  d₀₂ : P₀ ≢ P₂
  d₀₂ = dif i₀≢i₂

  d₁₃ : P₁ ≢ P₃
  d₁₃ = dif i₁≢i₃

  d₁₂ : P₁ ≢ P₂
  d₁₂ = dif i₁≢i₂

-- The pair's matrix, which is what `Λ` denotes.
Mpair : Op n
Mpair = HH2 P₀ P₁ P₃ P₂

------------------------------------------------------------------------
-- A word's signed permutation, read on bitstrings

module _ {w : W} (h : HFreeʷ w) where

  private
    sgw : Bits n → Bool
    sgw x = sgn (sp w) (index n x)

    pmw : Bits n → Bits n
    pmw x = code n (prm (sp w) (index n x))

    pm-inj : ∀ {x y : Bits n} → pmw x ≡ pmw y → x ≡ y
    pm-inj {x} {y} e =
      Eq.trans (Eq.sym (code-index n x))
        (Eq.trans (Eq.cong (code n) (sp-inj w (code-injective n e)))
                  (code-index n y))

  open CM.Pair P₀ P₁ P₃ P₂ d₀₁ d₃₂ d₀₃ d₀₂ d₁₃ d₁₂ sgw pmw pm-inj
    using (P ; M ; module Commuting)

  private
    -- The two readings agree: `Commutant`'s `P` spells the sign with
    -- an `if`, `SPMatrix`'s `spOp` with `sgnOf`.
    P≐ : P ≐ spOp (sp w)
    P≐ x y = Eq.cong (_* δb (pmw x) y) (Eq.sym (sgnOf-if (sgw x)))

    -- An equation between codes is one between indices.
    rd : ∀ {a b : Fin (2 ^ℕ n)} → pmw (code n a) ≡ code n b → prm (sp w) a ≡ b
    rd {a} {b} e =
      code-injective n
        (Eq.trans (Eq.sym (Eq.cong (λ z → code n (prm (sp w) z)) (index-code n a)))
                  e)

    rs : ∀ {a b : Fin (2 ^ℕ n)} →
         sgw (code n a) ≡ sgw (code n b) → sgn (sp w) a ≡ sgn (sp w) b
    rs {a} {b} e =
      Eq.trans (Eq.sym (Eq.cong (sgn (sp w)) (index-code n a)))
               (Eq.trans e (Eq.cong (sgn (sp w)) (index-code n b)))

  -- Lemma A.6: a Hadamard-free word whose matrix commutes with the
  -- pair's passes the pair.
  A6 : (spOp (sp w) ⊙ Mpair) ≐ (Mpair ⊙ spOp (sp w)) → Passes w
  A6 c = passes-A6 h (perm (Commuting.places comm))
                     (rs (proj₁ (Commuting.signs comm)))
                     (rs (proj₂ (Commuting.signs comm)))
    where
    comm : (P ⊙ M) ≐ (M ⊙ P)
    comm = ≐-trans (⊙-cong P≐ (≐-refl M))
                   (≐-trans c (⊙-cong (≐-refl M) (≐-sym P≐)))

    perm : (pmw P₀ ≡ P₀ × pmw P₁ ≡ P₁ × pmw P₃ ≡ P₃ × pmw P₂ ≡ P₂)
         ⊎ (pmw P₀ ≡ P₃ × pmw P₁ ≡ P₂ × pmw P₃ ≡ P₀ × pmw P₂ ≡ P₁) →
           (prm (sp w) i₀ ≡ i₀ × prm (sp w) i₁ ≡ i₁
            × prm (sp w) i₂ ≡ i₂ × prm (sp w) i₃ ≡ i₃)
         ⊎ (prm (sp w) i₀ ≡ i₃ × prm (sp w) i₁ ≡ i₂
            × prm (sp w) i₂ ≡ i₁ × prm (sp w) i₃ ≡ i₀)
    perm (inj₁ (a , b , c′ , d)) = inj₁ (rd a , rd b , rd d , rd c′)
    perm (inj₂ (a , b , c′ , d)) = inj₂ (rd a , rd b , rd d , rd c′)

------------------------------------------------------------------------
-- Conjugating the standard pair onto four indices
--
-- Any signed permutation that sends four indices to 0, 1, 3 and 2
-- without signing them carries the standard pair to the pair on those
-- four.  Definition E.1's Σ is one such, and so is the six-index word
-- of `SixWord` and the composites built from them, so this is the
-- shape every appeal to Corollary A.7 in Figure 10 goes through.

conj-at : ∀ (X X′ : W) → Inj (sp X′) → sp X ⊛ sp X′ ≗ idSP →
          ∀ (p q r s : Fin N) →
          prm (sp X) p ≡ i₀ → prm (sp X) q ≡ i₁ →
          prm (sp X) r ≡ i₃ → prm (sp X) s ≡ i₂ →
          sgn (sp X) p ≡ false → sgn (sp X) q ≡ false →
          sgn (sp X) r ≡ false → sgn (sp X) s ≡ false →
          (spOp (sp X) ⊙ (Mpair ⊙ spOp (sp X′)))
          ≐ (hadOp (code n p) (code n q) ⊙ hadOp (code n r) (code n s))
conj-at X X′ inj inv p q r s ep eq er es tp tq tr ts =
  Eq.subst (λ M → (spOp (sp X) ⊙ (M ⊙ spOp (sp X′)))
                  ≐ (hadOp (code n p) (code n q) ⊙ hadOp (code n r) (code n s)))
           frame
           (conj-pair (code n p) (code n q) (code n r) (code n s)
                      (Eq.trans (sg p tp) (Eq.sym (sg q tq)))
                      (Eq.trans (sg r tr) (Eq.sym (sg s ts))))
  where
  open Conj (sp X) (sp X′) inj inv using (π ; σ)
  open Pull (sp X) (sp X′) inj inv using (conj-pair)

  imgOf : ∀ (x k : Fin N) → prm (sp X) x ≡ k → π (code n x) ≡ code n k
  imgOf x k h = Eq.cong (code n) (Eq.trans (Eq.cong (prm (sp X)) (index-code n x)) h)

  sg : ∀ (x : Fin N) → sgn (sp X) x ≡ false → σ (code n x) ≡ false
  sg x h = Eq.trans (Eq.cong (sgn (sp X)) (index-code n x)) h

  frame : (hadOp (π (code n p)) (π (code n q))
           ⊙ hadOp (π (code n r)) (π (code n s))) ≡ Mpair
  frame =
    Eq.trans (Eq.cong₂ (λ u v → hadOp u v ⊙ hadOp (π (code n r)) (π (code n s)))
                       (imgOf p i₀ ep) (imgOf q i₁ eq))
             (Eq.cong₂ (λ u v → hadOp P₀ P₁ ⊙ hadOp u v) (imgOf r i₃ er) (imgOf s i₂ es))

------------------------------------------------------------------------
-- The same, with the hypothesis on the words
--
-- Both readings carry the pair's two powers of 1/√2 and nothing else,
-- so the localisation relation between them is an equality of matrices
-- once that power is cancelled.

private
  Λ≡ : ⟦ Λ ⟧ʷ ≡ ⟦ Λw ⟧ʷ
  Λ≡ = Eq.cong ⟦_⟧ʷ hh0132≡

-- And `Λw` is one letter, whose reading is the pair's matrix.
Λ-op : proj₂ ⟦ Λ ⟧ʷ ≐ Mpair
Λ-op = Eq.subst (λ s → proj₂ s ≐ Mpair) (Eq.sym Λ≡) (≐-refl Mpair)

Λ-scale : proj₁ ⟦ Λ ⟧ʷ ≡ 2
Λ-scale = Eq.cong proj₁ Λ≡

-- Scales that agree cancel: the localisation relation is then an
-- equality of matrices.
~≡ : ∀ (l : ℕ) {s t : Scaled n} → proj₁ s ≡ l → proj₁ t ≡ l → s ~ t →
     proj₂ s ≐ proj₂ t
~≡ l {s} {t} e₁ e₂ h x y = √2^-cancel l _ _
  (Eq.trans (Eq.cong (λ k → √2^ k * proj₂ s x y) (Eq.sym e₂))
            (Eq.trans (h x y) (Eq.cong (λ k → √2^ k * proj₂ t x y) e₁)))

A6-word : ∀ {w : W} → HFreeʷ w → ⟦ w • Λ ⟧ʷ ~ ⟦ Λ • w ⟧ʷ → Passes w
A6-word {w} h hyp = A6 h comm
  where
  Mw : Op n
  Mw = proj₂ ⟦ w ⟧ʷ

  e₁ : proj₁ ⟦ w • Λ ⟧ʷ ≡ 2
  e₁ = Eq.cong₂ _+ℕ_ (word-scale h) Λ-scale

  e₂ : proj₁ ⟦ Λ • w ⟧ʷ ≡ 2
  e₂ = Eq.cong₂ _+ℕ_ Λ-scale (word-scale h)

  -- The two products, with the pair's matrix put in.
  lhs : proj₂ ⟦ w • Λ ⟧ʷ ≐ (spOp (sp w) ⊙ Mpair)
  lhs = ⊙-cong (word-op h) Λ-op

  rhs : proj₂ ⟦ Λ • w ⟧ʷ ≐ (Mpair ⊙ spOp (sp w))
  rhs = ⊙-cong Λ-op (word-op h)

  comm : (spOp (sp w) ⊙ Mpair) ≐ (Mpair ⊙ spOp (sp w))
  comm = ≐-trans (≐-sym lhs) (≐-trans (~≡ 2 e₁ e₂ hyp) rhs)
