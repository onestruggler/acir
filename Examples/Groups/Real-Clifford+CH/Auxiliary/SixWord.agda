------------------------------------------------------------------------
-- Presentations of groups
--
-- The six-index analogue of Definition E.1's word
--
-- Figure 10's (71) needs a Hadamard-free word carrying six given
-- indices a, b, c, d, e, f to the numerals 0, 1, 3, 2, 4, 5 — the
-- paper's `T_{a,b,c,d,e,f}`, which footnote 13 says is "constructed in
-- a similar way to Σ".  It is not a letter of Figure 8 and appears
-- only inside proofs, so its spelling is ours to choose: here it is
-- `TeleWord`'s word for the obvious plan, with 6 for the spare index
-- that carries the signs.
--
-- What comes out is exactly what `Conjugate` asks of it: the
-- permutation sends each of the six indices to its numeral, no sign
-- sits on any of them, and the companion word is an inverse.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.SixWord (m : ℕ) where

open import Data.Bool using (false)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties
  using (toℕ-injective ; toℕ<n ; toℕ-inject≤)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (_<_) renaming (_^_ to _^ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (fin8 ; code ; index ; index-code)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (hadOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m using (HFreeʷ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; sgn ; prm ; idSP ; sp-inj)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix m using (spOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Conjugate m
  using (module Conj ; module Pull)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A6 m
  using (P₀ ; P₁ ; P₂ ; P₃ ; Mpair)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Telescope
open import Examples.Groups.Real-Clifford+CH.Auxiliary.TeleWord m
  using (Wrd ; Wrd′ ; Hfree ; Hfree′ ; Prm-wrd ; Sgn-wrd ; Inv)

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

  -- The numerals below 8 are indices.
  lit< : ∀ (k : Fin 8) → toℕ k < N
  lit< k = Eq.subst (_< N) (toℕ-inject≤ k _) (toℕ<n (fin8 {m} k))

------------------------------------------------------------------------
-- The plan

module Six (a b c d e f : Fin N)
           (ab : a ≢ b) (ac : a ≢ c) (ad : a ≢ d) (ae : a ≢ e) (af : a ≢ f)
           (bc : b ≢ c) (bd′ : b ≢ d) (be : b ≢ e) (bf : b ≢ f)
           (cd : c ≢ d) (ce : c ≢ e) (cf : c ≢ f)
           (de : d ≢ e) (df : d ≢ f)
           (ef : e ≢ f)
  where

  pl : Plan
  pl = (toℕ a , 0) ∷ (toℕ b , 1) ∷ (toℕ c , 3) ∷ (toℕ d , 2)
     ∷ (toℕ e , 4) ∷ (toℕ f , 5) ∷ []

  private
    ≢ℕ : ∀ {x y : Fin N} → x ≢ y → toℕ x ≢ toℕ y
    ≢ℕ ne q = ne (toℕ-injective q)

  ok : Ok pl
  ok = cons h₀ (cons h₁ (cons h₂ (cons h₃ (cons h₄ (cons h₅ nil)))))
    where
    h₅ : ∀ {y j : ℕ} → (y , j) ∈ [] → (toℕ f ≢ y) × (5 ≢ j)
    h₅ ()

    h₄ : ∀ {y j : ℕ} → (y , j) ∈ ((toℕ f , 5) ∷ []) → (toℕ e ≢ y) × (4 ≢ j)
    h₄ here = ≢ℕ ef , λ ()

    h₃ : ∀ {y j : ℕ} → (y , j) ∈ ((toℕ e , 4) ∷ (toℕ f , 5) ∷ []) →
         (toℕ d ≢ y) × (2 ≢ j)
    h₃ here         = ≢ℕ de , λ ()
    h₃ (there here) = ≢ℕ df , λ ()

    h₂ : ∀ {y j : ℕ} →
         (y , j) ∈ ((toℕ d , 2) ∷ (toℕ e , 4) ∷ (toℕ f , 5) ∷ []) →
         (toℕ c ≢ y) × (3 ≢ j)
    h₂ here                 = ≢ℕ cd , λ ()
    h₂ (there here)         = ≢ℕ ce , λ ()
    h₂ (there (there here)) = ≢ℕ cf , λ ()

    h₁ : ∀ {y j : ℕ} →
         (y , j) ∈ ((toℕ c , 3) ∷ (toℕ d , 2) ∷ (toℕ e , 4) ∷ (toℕ f , 5) ∷ []) →
         (toℕ b ≢ y) × (1 ≢ j)
    h₁ here                         = ≢ℕ bc , λ ()
    h₁ (there here)                 = ≢ℕ bd′ , λ ()
    h₁ (there (there here))         = ≢ℕ be , λ ()
    h₁ (there (there (there here))) = ≢ℕ bf , λ ()

    h₀ : ∀ {y j : ℕ} →
         (y , j) ∈ ((toℕ b , 1) ∷ (toℕ c , 3) ∷ (toℕ d , 2) ∷ (toℕ e , 4)
                    ∷ (toℕ f , 5) ∷ []) →
         (toℕ a ≢ y) × (0 ≢ j)
    h₀ here                                 = ≢ℕ ab , λ ()
    h₀ (there here)                         = ≢ℕ ac , λ ()
    h₀ (there (there here))                 = ≢ℕ ad , λ ()
    h₀ (there (there (there here)))         = ≢ℕ ae , λ ()
    h₀ (there (there (there (there here)))) = ≢ℕ af , λ ()

  bnd : Bounded N pl
  bnd here                                         = toℕ<n a , lit< ₀
  bnd (there here)                                 = toℕ<n b , lit< ₁
  bnd (there (there here))                         = toℕ<n c , lit< ₃
  bnd (there (there (there here)))                 = toℕ<n d , lit< ₂
  bnd (there (there (there (there here))))         = toℕ<n e , lit< ₄
  bnd (there (there (there (there (there here))))) = toℕ<n f , lit< ₅

  ----------------------------------------------------------------------
  -- The word, and what it does

  Tw T′w : W
  Tw  = Wrd  6 pl
  T′w = Wrd′ 6 pl

  hfree-T : HFreeʷ Tw
  hfree-T = Hfree 6 (lit< ₆) pl bnd

  hfree-T′ : HFreeʷ T′w
  hfree-T′ = Hfree′ 6 (lit< ₆) pl bnd

  T-inv : sp Tw ⊛ sp T′w ≗ idSP
  T-inv = Inv 6 (lit< ₆) pl bnd

  private
    -- The six memberships, once.
    ma : (toℕ a , 0) ∈ pl
    ma = here

    mb : (toℕ b , 1) ∈ pl
    mb = there here

    mc : (toℕ c , 3) ∈ pl
    mc = there (there here)

    md : (toℕ d , 2) ∈ pl
    md = there (there (there here))

    me : (toℕ e , 4) ∈ pl
    me = there (there (there (there here)))

    mf : (toℕ f , 5) ∈ pl
    mf = there (there (there (there (there here))))

    at : ∀ {x k : ℕ} → (x , k) ∈ pl → ∀ (v : Fin N) → toℕ v ≡ x →
         toℕ (prm (sp Tw) v) ≡ k
    at mem v ev =
      Eq.trans (Prm-wrd 6 (lit< ₆) pl bnd v)
               (Eq.trans (Eq.cong (P pl) ev) (P-img ok mem))

    sg : ∀ {x k : ℕ} → (x , k) ∈ pl → k ≢ 6 → ∀ (v : Fin N) → toℕ v ≡ x →
         sgn (sp Tw) v ≡ false
    sg {x} {k} mem k6 v ev =
      Sgn-wrd 6 (lit< ₆) pl bnd k k6 v (Eq.trans ev (Eq.sym (ρ-img ok mem)))

  -- Where it sends the six indices …
  T-a : toℕ (prm (sp Tw) a) ≡ 0
  T-a = at ma a Eq.refl

  T-b : toℕ (prm (sp Tw) b) ≡ 1
  T-b = at mb b Eq.refl

  T-c : toℕ (prm (sp Tw) c) ≡ 3
  T-c = at mc c Eq.refl

  T-d : toℕ (prm (sp Tw) d) ≡ 2
  T-d = at md d Eq.refl

  T-e : toℕ (prm (sp Tw) e) ≡ 4
  T-e = at me e Eq.refl

  T-f : toℕ (prm (sp Tw) f) ≡ 5
  T-f = at mf f Eq.refl

  -- … and that it signs none of them.
  T-sa : sgn (sp Tw) a ≡ false
  T-sa = sg ma (λ ()) a Eq.refl

  T-sb : sgn (sp Tw) b ≡ false
  T-sb = sg mb (λ ()) b Eq.refl

  T-sc : sgn (sp Tw) c ≡ false
  T-sc = sg mc (λ ()) c Eq.refl

  T-sd : sgn (sp Tw) d ≡ false
  T-sd = sg md (λ ()) d Eq.refl

  T-se : sgn (sp Tw) e ≡ false
  T-se = sg me (λ ()) e Eq.refl

  T-sf : sgn (sp Tw) f ≡ false
  T-sf = sg mf (λ ()) f Eq.refl

  ----------------------------------------------------------------------
  -- So it conjugates the standard pair onto a, b, c, d
  --
  -- The same computation `Eq65` makes for Σ, and what the first of
  -- (71)'s three appeals to Corollary A.7 consumes.

  open Conj (sp Tw) (sp T′w) (sp-inj T′w) T-inv using (π ; σ)
  open Pull (sp Tw) (sp T′w) (sp-inj T′w) T-inv using (conj-pair)

  private
    img : ∀ (x : Fin N) (k : Fin N) → toℕ (prm (sp Tw) x) ≡ toℕ k →
          π (code n x) ≡ code n k
    img x k q =
      Eq.cong (code n)
        (Eq.trans (Eq.cong (prm (sp Tw)) (index-code n x)) (toℕ-injective q))

    sgo : ∀ (x : Fin N) → sgn (sp Tw) x ≡ false → σ (code n x) ≡ false
    sgo x q = Eq.trans (Eq.cong (sgn (sp Tw)) (index-code n x)) q

    frame : (hadOp (π (code n a)) (π (code n b))
             ⊙ hadOp (π (code n c)) (π (code n d))) ≡ Mpair
    frame =
      Eq.trans (Eq.cong₂ (λ u v → hadOp u v ⊙ hadOp (π (code n c)) (π (code n d)))
                         (img a i₀ (Eq.trans T-a (Eq.sym toℕ-i₀)))
                         (img b i₁ (Eq.trans T-b (Eq.sym toℕ-i₁))))
               (Eq.cong₂ (λ u v → hadOp P₀ P₁ ⊙ hadOp u v)
                         (img c i₃ (Eq.trans T-c (Eq.sym toℕ-i₃)))
                         (img d i₂ (Eq.trans T-d (Eq.sym toℕ-i₂))))

  T-conj : (spOp (sp Tw) ⊙ (Mpair ⊙ spOp (sp T′w)))
           ≐ (hadOp (code n a) (code n b) ⊙ hadOp (code n c) (code n d))
  T-conj =
    Eq.subst (λ M → (spOp (sp Tw) ⊙ (M ⊙ spOp (sp T′w)))
                    ≐ (hadOp (code n a) (code n b) ⊙ hadOp (code n c) (code n d)))
             frame
             (conj-pair (code n a) (code n b) (code n c) (code n d)
                        (Eq.trans (sgo a T-sa) (Eq.sym (sgo b T-sb)))
                        (Eq.trans (sgo c T-sc) (Eq.sym (sgo d T-sd))))
