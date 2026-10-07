------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma A.1: (a1), (b1), (b4) and (b6) at every index (Clément,
-- Appendix A.2)
--
-- Figure 7 states (a1*), (b1*), (b4*) and (b6*) at the indices 0 … 3.
-- (a1) at another index is conjugation by X_[0,a], as in the paper; the
-- other three are moved to any tuple of distinct indices by a product
-- of exchanges (LemmaA1.Rename.move), "renaming the indices up to
-- conjugating by some X generators".  That needs the width to hold the
-- literals: k distinct indices of Fin N make N at least k (`fits`, by
-- the injectivity of the lookup), and the view `Wide k N` turns that
-- into N = k + m, where the literal rule lives.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Moves where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Properties using (injective⇒≤)
open import Data.List using ([] ; _∷_)
open import Data.Nat using (ℕ ; _≤_ ; z≤n ; s≤s ; _+_)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup)
open import Data.Vec.Relation.Unary.All using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics
  using (Gen ; −1 ; X ; H ; _G,_===_ ; −1ᵖ ; Xᵖ ; Hᵖ)
open _G,_===_
import Examples.Groups.Real-Clifford+CH.Auxiliary.SegChain as SegChain
import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1.Rename as Rename

infix 4 _⊢ᴳ_≈_
_⊢ᴳ_≈_ : (N : ℕ) → Word (Gen N) → Word (Gen N) → Set
N ⊢ᴳ u ≈ v = PB._≈_ (N G,_===_) u v

------------------------------------------------------------------------
-- Enough room for k distinct indices

data Wide (k : ℕ) : ℕ → Set where
  wide : ∀ m → Wide k (k + m)

≤⇒wide : ∀ {k n} → k ≤ n → Wide k n
≤⇒wide {n = n} z≤n = wide n
≤⇒wide (s≤s p) with ≤⇒wide p
... | wide m = wide m

module _ {N : ℕ} where
  open Rename N using (Distinct ; lookup-inj)

  fits : ∀ {k} (v : Vec (Fin N) k) → Distinct v → Wide k N
  fits v d = ≤⇒wide (injective⇒≤ {f = lookup v} (lookup-inj d))

private
  subst₂ : ∀ {A : Set} (P : A → A → Set) {a b a′ b′} →
           a ≡ a′ → b ≡ b′ → P a b → P a′ b′
  subst₂ P Eq.refl Eq.refl p = p

  subst₃ : ∀ {A : Set} (P : A → A → A → Set) {a b c a′ b′ c′} →
           a ≡ a′ → b ≡ b′ → c ≡ c′ → P a b c → P a′ b′ c′
  subst₃ P Eq.refl Eq.refl Eq.refl p = p

  subst₄ : ∀ {A : Set} (P : A → A → A → A → Set) {a b c d a′ b′ c′ d′} →
           a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → P a b c d → P a′ b′ c′ d′
  subst₄ P Eq.refl Eq.refl Eq.refl Eq.refl p = p

------------------------------------------------------------------------
-- (a1)

a1 : ∀ {N} (a : Fin N) → N ⊢ᴳ −1 a • −1 a ≈ ε
a1 zero    = PB.axiom a1*
a1 {N} (suc a) =
  run {−1 s ∷ −1 s ∷ []} {[]}
    ( at 0 0 (X ₀ s ∷ X ₀ s ∷ []) (PB.sym (PB.axiom (a2 z≢s))) ▸
      at 1 2 (−1 ₀ ∷ X ₀ s ∷ []) (PB.sym (PB.axiom (c1 z≢s))) ▸
      at 2 2 (−1 ₀ ∷ X ₀ s ∷ []) (PB.sym (PB.axiom (c1 z≢s))) ▸
      at 1 2 [] (PB.axiom a1*) ▸
      at 0 2 [] (PB.axiom (a2 z≢s)) ▸
      done)
  where
  open SegChain (N G,_===_) using (at ; _▸_ ; done ; run)
  s : Fin N
  s = suc a
  z≢s : ₀ ≢ s
  z≢s ()

------------------------------------------------------------------------
-- (b1), (b4), (b6)

private
  b1′ : ∀ {N} → Wide 2 N → (a b : Fin N) → a ≢ b → N ⊢ᴳ −1 a • −1 b ≈ −1 b • −1 a
  b1′ (wide m) a b ab =
    subst₂ (λ p q → ₂₊ m ⊢ᴳ −1 p • −1 q ≈ −1 q • −1 p) (ok ₀) (ok ₁)
      (move ts (−1ᵖ , −1ᵖ) (−1ᵖ , −1ᵖ) (PB.axiom b1*))
    where
    open Rename (₂₊ m)
    ls is : Vec (Fin (₂₊ m)) 2
    ls = ₀ ∷ ₁ ∷ []
    is = a ∷ b ∷ []
    ts = build ls is
    ok : ∀ j → σ ts (lookup ls j) ≡ lookup is j
    ok = build-ok ls is (((λ ()) ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ)) ((ab ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ))

  b4′ : ∀ {N} → Wide 3 N → (a b c : Fin N) → a ≢ b → a ≢ c → b ≢ c →
        N ⊢ᴳ −1 a • H b c ≈ H b c • −1 a
  b4′ (wide m) a b c ab ac bc =
    subst₃ (λ p q r → ₃₊ m ⊢ᴳ −1 p • H q r ≈ H q r • −1 p) (ok ₀) (ok ₁) (ok ₂)
      (move ts (−1ᵖ , Hᵖ (λ ())) (Hᵖ (λ ()) , −1ᵖ) (PB.axiom b4*))
    where
    open Rename (₃₊ m)
    ls is : Vec (Fin (₃₊ m)) 3
    ls = ₁ ∷ ₀ ∷ ₂ ∷ []
    is = a ∷ b ∷ c ∷ []
    ts = build ls is
    ok : ∀ j → σ ts (lookup ls j) ≡ lookup is j
    ok = build-ok ls is
           (((λ ()) ∷ (λ ()) ∷ []) ∷ᵈ (((λ ()) ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ)))
           ((ab ∷ ac ∷ []) ∷ᵈ ((bc ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ)))

  b6′ : ∀ {N} → Wide 4 N → (a b c d : Fin N) →
        a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
        N ⊢ᴳ H a b • H c d ≈ H c d • H a b
  b6′ (wide m) a b c d ab ac ad bc bd cd =
    subst₄ (λ p q r s → ₄₊ m ⊢ᴳ H p q • H r s ≈ H r s • H p q) (ok ₀) (ok ₁) (ok ₂) (ok ₃)
      (move ts (Hᵖ (λ ()) , Hᵖ (λ ())) (Hᵖ (λ ()) , Hᵖ (λ ())) (PB.axiom b6*))
    where
    open Rename (₄₊ m)
    ls is : Vec (Fin (₄₊ m)) 4
    ls = ₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ []
    is = a ∷ b ∷ c ∷ d ∷ []
    ts = build ls is
    ok : ∀ j → σ ts (lookup ls j) ≡ lookup is j
    ok = build-ok ls is
           (((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ᵈ (((λ ()) ∷ (λ ()) ∷ []) ∷ᵈ
             (((λ ()) ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ))))
           ((ab ∷ ac ∷ ad ∷ []) ∷ᵈ ((bc ∷ bd ∷ []) ∷ᵈ ((cd ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ))))

b1 : ∀ {N} {a b : Fin N} → a ≢ b → N ⊢ᴳ −1 a • −1 b ≈ −1 b • −1 a
b1 {N} {a} {b} ab = b1′ (fits (a ∷ b ∷ []) ((ab ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ))) a b ab
  where open Rename N using (_∷ᵈ_ ; []ᵈ)

b4 : ∀ {N} {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c → N ⊢ᴳ −1 a • H b c ≈ H b c • −1 a
b4 {N} {a} {b} {c} ab ac bc =
  b4′ (fits (a ∷ b ∷ c ∷ []) ((ab ∷ ac ∷ []) ∷ᵈ ((bc ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ)))) a b c ab ac bc
  where open Rename N using (_∷ᵈ_ ; []ᵈ)

b6 : ∀ {N} {a b c d : Fin N} → a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
     N ⊢ᴳ H a b • H c d ≈ H c d • H a b
b6 {N} {a} {b} {c} {d} ab ac ad bc bd cd =
  b6′ (fits (a ∷ b ∷ c ∷ d ∷ [])
            ((ab ∷ ac ∷ ad ∷ []) ∷ᵈ ((bc ∷ bd ∷ []) ∷ᵈ ((cd ∷ []) ∷ᵈ ([] ∷ᵈ []ᵈ)))))
      a b c d ab ac ad bc bd cd
  where open Rename N using (_∷ᵈ_ ; []ᵈ)
