------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation (65) is sound, and what is left of it
--
-- Figure 10's first equation says that H_[a,b] H_[c,d], for any two
-- disjoint pairs, is the standard pair H_[0,1] H_[3,2] with Definition
-- E.1's word on each side — Equation (35) without the restriction on
-- the codes.  The paper proves it from Corollary A.7 given that it is
-- *sound* for all a, b, c, d.
--
-- That soundness is proved here.  `SigmaPerm` says what Definition
-- E.1's word is — a signed permutation carrying a, b, c, d to 0, 1, 3,
-- 2, signing none of them, with its companion for an inverse — and
-- `Conjugate` says that conjugating by such a thing carries the
-- standard pair to the pair on the pre-images.  Together they give
-- both readings of (65) the same matrix, and `A7` then reduces the
-- equation itself to writing H_[a,b] H_[c,d] as *some* pair of
-- inverse Hadamard-free words around the standard pair — which is what
-- Equations (35), (36) and (37) do.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65 (m : ℕ) where

open import Data.Nat renaming (_^_ to _^ℕ_ ; _+_ to _+ℕ_) using ()
open import Data.Bool using (false ; true)
open import Data.Maybe using (nothing)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (code ; index ; code-index ; index-code)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.HadamardPair m using (HH2)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (hadOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP ; HH)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
  using (_P,_===_ ; r35)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; hpat ; distinct4)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; gen ; nil ; cat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; sgn ; prm ; sp-inj ; ⊙-inverse ; idSP)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix m
  using (spOp ; word-op ; word-scale ; ⟦_⟧ʷ ; spOp-⊙ ; spOp-id ; spOp-cong
       ; A5-mat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Conjugate m
  using (module Pull ; module Conj)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃ ; gen-hh)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m using (Λ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A6 m
  using (P₀ ; P₁ ; P₂ ; P₃ ; Mpair ; Λ-op ; Λ-scale ; ~≡)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A7 m using (A7)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m
  as SP using ()

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

  W : Set
  W = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- The pair on four arbitrary indices

Pair : Fin N → Fin N → Fin N → Fin N → Op n
Pair a b c d = HH2 (code n a) (code n b) (code n c) (code n d)

-- Which is what the letter denotes.
hh-scale : ∀ (a b c d : Fin N) → a ≢ b → c ≢ d → proj₁ ⟦ hh {₃₊ m} a b c d ⟧ʷ ≡ 2
hh-scale a b c d ab cd = Eq.cong (λ w → proj₁ ⟦ w ⟧ʷ) (Eq.sym (gen-hh a b c d ab cd))

hh-op : ∀ (a b c d : Fin N) → a ≢ b → c ≢ d →
        proj₂ ⟦ hh {₃₊ m} a b c d ⟧ʷ ≐ Pair a b c d
hh-op a b c d ab cd =
  Eq.subst (λ w → proj₂ ⟦ w ⟧ʷ ≐ Pair a b c d) (gen-hh a b c d ab cd)
           (≐-refl (Pair a b c d))

------------------------------------------------------------------------
-- The conjugate of the standard pair, over variable words
--
-- Stated at Definition E.1's words themselves, as `Tuple.Σ-conj` was,
-- every comparison the conversion checker cannot settle syntactically
-- evaluates their signed permutations (12 s); over variables `sp X` is
-- stuck.

private
  module Std (X X′ : W) (inv : sp X ⊛ sp X′ ≗ idSP) (a b c d : Fin N)
             (pa : toℕ (prm (sp X) a) ≡ 0) (pb : toℕ (prm (sp X) b) ≡ 1)
             (pc : toℕ (prm (sp X) c) ≡ 3) (pd : toℕ (prm (sp X) d) ≡ 2)
             (sa : sgn (sp X) a ≡ false) (sb : sgn (sp X) b ≡ false)
             (sc : sgn (sp X) c ≡ false) (sd : sgn (sp X) d ≡ false)
    where

    open Conj (sp X) (sp X′) (sp-inj X′) inv using (π ; σ)
    open Pull (sp X) (sp X′) (sp-inj X′) inv using (conj-pair)

    -- Where the conjugation sends the pair's four indices.
    img : ∀ (x : Fin N) (k : Fin N) → toℕ (prm (sp X) x) ≡ toℕ k →
          π (code n x) ≡ code n k
    img x k e =
      Eq.cong (code n)
        (Eq.trans (Eq.cong (prm (sp X)) (index-code n x)) (toℕ-injective e))

    π-a : π (code n a) ≡ P₀
    π-a = img a i₀ (Eq.trans pa (Eq.sym toℕ-i₀))

    π-b : π (code n b) ≡ P₁
    π-b = img b i₁ (Eq.trans pb (Eq.sym toℕ-i₁))

    π-c : π (code n c) ≡ P₃
    π-c = img c i₃ (Eq.trans pc (Eq.sym toℕ-i₃))

    π-d : π (code n d) ≡ P₂
    π-d = img d i₂ (Eq.trans pd (Eq.sym toℕ-i₂))

    -- And that it signs none of them.
    sg : ∀ (x : Fin N) → sgn (sp X) x ≡ false → σ (code n x) ≡ false
    sg x e = Eq.trans (Eq.cong (sgn (sp X)) (index-code n x)) e

    frame : (hadOp (π (code n a)) (π (code n b))
             ⊙ hadOp (π (code n c)) (π (code n d))) ≡ Mpair
    frame =
      Eq.trans (Eq.cong₂ (λ u v → hadOp u v ⊙ hadOp (π (code n c)) (π (code n d)))
                         π-a π-b)
               (Eq.cong₂ (λ u v → hadOp P₀ P₁ ⊙ hadOp u v) π-c π-d)

    conj : (spOp (sp X) ⊙ (Mpair ⊙ spOp (sp X′))) ≐ Pair a b c d
    conj =
      Eq.subst (λ M → (spOp (sp X) ⊙ (M ⊙ spOp (sp X′))) ≐ Pair a b c d)
               frame
               (conj-pair (code n a) (code n b) (code n c) (code n d)
                          (Eq.trans (sg a sa) (Eq.sym (sg b sb)))
                          (Eq.trans (sg c sc) (Eq.sym (sg d sd))))

------------------------------------------------------------------------
-- Equation (65) is sound

module Tuple (a b c d : Fin N)
             (ab : a ≢ b) (ac : a ≢ c) (ad : a ≢ d)
             (bc : b ≢ c) (bd : b ≢ d) (cd : c ≢ d)
  where

  open SP.Sig a b c d ab ac ad bc bd cd public
    using (Σw ; Σ′w ; Σ-inv ; hfree-Σ ; hfree-Σ′
         ; prm-Σ-a ; prm-Σ-b ; prm-Σ-c ; prm-Σ-d
         ; sgn-Σ-a ; sgn-Σ-b ; sgn-Σ-c ; sgn-Σ-d)

  -- The conjugate of the standard pair is the pair on a, b, c and d.
  Σ-conj : (spOp (sp Σw) ⊙ (Mpair ⊙ spOp (sp Σ′w))) ≐ Pair a b c d
  Σ-conj = Std.conj Σw Σ′w Σ-inv a b c d prm-Σ-a prm-Σ-b prm-Σ-c prm-Σ-d
                    sgn-Σ-a sgn-Σ-b sgn-Σ-c sgn-Σ-d

  -- The scale and the matrix of the right-hand side of (65), on their
  -- own: composing those is much cheaper than composing two `_~_`s,
  -- whose types the conversion checker would expand into sums over
  -- bitstrings, once per letter.
  conj-scale : proj₁ ⟦ Σw • (Λ • Σ′w) ⟧ʷ ≡ 2
  conj-scale = Eq.cong₂ _+ℕ_ (word-scale hfree-Σ)
                             (Eq.cong₂ _+ℕ_ Λ-scale (word-scale hfree-Σ′))

  conj-op : proj₂ ⟦ Σw • (Λ • Σ′w) ⟧ʷ ≐ Pair a b c d
  conj-op = ≐-trans (⊙-cong (word-op hfree-Σ) (⊙-cong Λ-op (word-op hfree-Σ′)))
                    Σ-conj

  -- So both readings of (65) have the same matrix, at the same scale.
  sound-65 : ⟦ Σw • (Λ • Σ′w) ⟧ʷ ~ ⟦ hh {₃₊ m} a b c d ⟧ʷ
  sound-65 = ~-reflexive scale matEq
    where
    scale : proj₁ ⟦ Σw • (Λ • Σ′w) ⟧ʷ ≡ proj₁ ⟦ hh {₃₊ m} a b c d ⟧ʷ
    scale = Eq.trans conj-scale (Eq.sym (hh-scale a b c d ab cd))

    matEq : proj₂ ⟦ Σw • (Λ • Σ′w) ⟧ʷ ≐ proj₂ ⟦ hh {₃₊ m} a b c d ⟧ʷ
    matEq = ≐-trans conj-op (≐-sym (hh-op a b c d ab cd))

  ----------------------------------------------------------------------
  -- Equation (65), given any writing of the letter around the pair
  --
  -- What is left is the syntactic half: Equations (35), (36) and (37)
  -- write H_[a,b] H_[c,d] as A (H_[0,1] H_[3,2]) A′ for Hadamard-free
  -- A, A′ — (35) with Definition E.1's own words, (36) and (37) with a
  -- swap network — and this turns any such writing into (65).

  private
    sp-id : (spOp (sp Σw) ⊙ spOp (sp Σ′w)) ≐ Idₒ
    sp-id = ≐-trans (≐-sym (spOp-⊙ (sp Σw) (sp Σ′w)))
                    (≐-trans (spOp-cong Σ-inv) spOp-id)

  -- Definition E.1's two words are inverse.
  ΣΣ′ : ⟦ Σw • Σ′w ⟧ʷ ~ ⟦ ε ⟧ʷ
  ΣΣ′ = ~-reflexive
          (Eq.cong₂ _+ℕ_ (word-scale hfree-Σ) (word-scale hfree-Σ′))
          (≐-trans (⊙-cong (word-op hfree-Σ) (word-op hfree-Σ′)) sp-id)

  private
    sp-id′ : (spOp (sp Σ′w) ⊙ spOp (sp Σw)) ≐ Idₒ
    sp-id′ = ≐-trans (≐-sym (spOp-⊙ (sp Σ′w) (sp Σw)))
                     (≐-trans (spOp-cong (⊙-inverse (sp Σw) (sp Σ′w)
                                                    (sp-inj Σ′w) Σ-inv))
                              spOp-id)

  -- In the other order too: a one-sided inverse of a signed
  -- permutation is two-sided.
  Σ′Σ : ⟦ Σ′w • Σw ⟧ʷ ~ ⟦ ε ⟧ʷ
  Σ′Σ = ~-reflexive
          (Eq.cong₂ _+ℕ_ (word-scale hfree-Σ′) (word-scale hfree-Σ))
          (≐-trans (⊙-cong (word-op hfree-Σ′) (word-op hfree-Σ)) sp-id′)

  -- And so, by Corollary A.5, they cancel in the theory, both ways.
  ΣΣ′-≈ : PB._≈_ (m P,_===_) (Σw • Σ′w) ε
  ΣΣ′-≈ = A5-mat (cat hfree-Σ hfree-Σ′) nil ΣΣ′

  Σ′Σ-≈ : PB._≈_ (m P,_===_) (Σ′w • Σw) ε
  Σ′Σ-≈ = A5-mat (cat hfree-Σ′ hfree-Σ) nil Σ′Σ

  -- A writing of the letter around the standard pair: what Equations
  -- (35), (36) and (37) produce, with the two facts about it that
  -- Corollary A.7 consumes.
  record Writing : Set where
    field
      A A′ : W
      hA   : HFreeʷ A
      hA′  : HFreeʷ A′
      inv  : ⟦ A • A′ ⟧ʷ ~ ⟦ ε ⟧ʷ
      sem  : ⟦ A • (Λ • A′) ⟧ʷ ~ ⟦ hh {₃₊ m} a b c d ⟧ʷ
      syn  : PB._≈_ (m P,_===_) (hh {₃₊ m} a b c d) (A • (Λ • A′))

  eq65 : ∀ {A A′ : W} → HFreeʷ A → HFreeʷ A′ →
         ⟦ A • A′ ⟧ʷ ~ ⟦ ε ⟧ʷ →
         ⟦ A • (Λ • A′) ⟧ʷ ~ ⟦ hh {₃₊ m} a b c d ⟧ʷ →
         PB._≈_ (m P,_===_) (A • (Λ • A′)) (Σw • (Λ • Σ′w))
  eq65 {A} {A′} hA hA′ eAA′ eq =
    A7 hA hA′ hfree-Σ hfree-Σ′ eAA′ ΣΣ′
       (~-trans {s = ⟦ A • (Λ • A′) ⟧ʷ} {t = ⟦ hh {₃₊ m} a b c d ⟧ʷ}
                {u = ⟦ Σw • (Λ • Σ′w) ⟧ʷ}
                eq (~-sym {s = ⟦ Σw • (Λ • Σ′w) ⟧ʷ}
                          {t = ⟦ hh {₃₊ m} a b c d ⟧ʷ} sound-65))

  -- Equation (65) itself, from any such writing.
  eq65-from : Writing → PB._≈_ (m P,_===_) (hh {₃₊ m} a b c d) (Σw • (Λ • Σ′w))
  eq65-from w = PB.trans (Writing.syn w)
                  (eq65 (Writing.hA w) (Writing.hA′ w)
                        (Writing.inv w) (Writing.sem w))

  -- And Equation (35) is one, so (65) holds outright wherever (35)
  -- applies: there the writing is by Definition E.1's own words.
  writing-35 : PB._≈_ (m P,_===_) (hh {₃₊ m} a b c d) (Σw • (Λ • Σ′w)) → Writing
  writing-35 r = record
    { A = Σw ; A′ = Σ′w ; hA = hfree-Σ ; hA′ = hfree-Σ′
    ; inv = ΣΣ′ ; sem = sound-65 ; syn = r }

  -- Where the codes have no H-pattern, Equation (35) *is* (65).
  eq65-35 : distinct4 (toℕ a) (toℕ b) (toℕ c) (toℕ d) ≡ true →
            hpat (code n a) (code n b) (code n c) (code n d) ≡ nothing →
            PB._≈_ (m P,_===_) (hh {₃₊ m} a b c d) (Σw • (Λ • Σ′w))
  eq65-35 d4 hp = PB.axiom (r35 a b c d d4 hp)
