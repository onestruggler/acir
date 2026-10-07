------------------------------------------------------------------------
-- Presentations of groups
--
-- Monomials in commuting diagonal gates
--
-- Fix a list Gs of diagonal circuits of order p.  A vector of labels e
-- gives the product Π gᵢ^eᵢ (eval).  Diagonal circuits commute, so
-- these products multiply by adding the vectors (eval-add) and take
-- iterates by scaling them (eval-^ᶠ), and a single gᵢ^c is the vector
-- with c at i (eval-unit).  An equation between products of the gates
-- is then an equation between label vectors (term-eval): a ring
-- identity for each entry.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Mono
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith ; map ; replicate ; lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_ ; _^_)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; p ; 0F ; 1F ; _+_ ; _*_ ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Diag p-2 p-prime lv h gt3

private
  variable
    m k : ℕ

-- A diagonal circuit of order p.
record Gen₃ (m : ℕ) : Set where
  constructor gen
  field
    the : Circuit m
    dia : Diag₃ m the
    ord : m ⊢ the ^ p ≈ ε

open Gen₃ public

eval : Vec (Gen₃ m) k → Vec F k → Circuit m
eval []       []       = ε
eval (G ∷ Gs) (e ∷ es) = the G ^ᶠ e • eval Gs es

module _ {m : ℕ} where

  open Width m

  Diag₃-eval : (Gs : Vec (Gen₃ m) k) (es : Vec F k) → Diag₃ m (eval Gs es)
  Diag₃-eval []       []       = Diag₃-ε
  Diag₃-eval (G ∷ Gs) (e ∷ es) = Diag₃-• (Diag₃-^ᶠ (dia G) e) (Diag₃-eval Gs es)

  eval-add : (Gs : Vec (Gen₃ m) k) (es es' : Vec F k) → m ⊢ eval Gs es • eval Gs es' ≈ eval Gs (zipWith _+_ es es')
  eval-add []       []       []         = left-unit
  eval-add (G ∷ Gs) (e ∷ es) (e' ∷ es') = begin
    (the G ^ᶠ e • eval Gs es) • the G ^ᶠ e' • eval Gs es'
      ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    the G ^ᶠ e • (eval Gs es • the G ^ᶠ e') • eval Gs es'
      ≈⟨ back _ (front _ (diag₃∥ (Diag₃-eval Gs es) (Diag₃-^ᶠ (dia G) e'))) ⟩
    the G ^ᶠ e • (the G ^ᶠ e' • eval Gs es) • eval Gs es'
      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (the G ^ᶠ e • the G ^ᶠ e') • eval Gs es • eval Gs es'
      ≈⟨ cong (Pow.Order.^ᶠ-+ m (ord G) e e') (eval-add Gs es es') ⟩
    the G ^ᶠ (e + e') • eval Gs (zipWith _+_ es es') ∎

  eval-0 : (Gs : Vec (Gen₃ m) k) → m ⊢ eval Gs (replicate _ 0F) ≈ ε
  eval-0 []       = refl
  eval-0 (G ∷ Gs) = trans left-unit (eval-0 Gs)

  eval-^ᶠ : (Gs : Vec (Gen₃ m) k) (es : Vec F k) (c : F) → m ⊢ eval Gs es ^ᶠ c ≈ eval Gs (map (_* c) es)
  eval-^ᶠ []       []       c = Pow.pow-ε m (toℕ c)
  eval-^ᶠ (G ∷ Gs) (e ∷ es) c = begin
    (the G ^ᶠ e • eval Gs es) ^ᶠ c
      ≈⟨ Pow.pow-• m (toℕ c) (diag₃∥ (Diag₃-^ᶠ (dia G) e) (Diag₃-eval Gs es)) ⟩
    (the G ^ᶠ e) ^ᶠ c • eval Gs es ^ᶠ c
      ≈⟨ cong (Pow.Order.^ᶠ-* m (ord G) e c) (eval-^ᶠ Gs es c) ⟩
    the G ^ᶠ (e * c) • eval Gs (map (_* c) es) ∎

  -- The vector with c at i.
  unitᵛ : Fin k → F → Vec F k
  unitᵛ {suc k} zero    c = c ∷ replicate k 0F
  unitᵛ {suc k} (suc i) c = 0F ∷ unitᵛ i c

  eval-unit : (Gs : Vec (Gen₃ m) k) (i : Fin k) (c : F) → m ⊢ the (lookup Gs i) ^ᶠ c ≈ eval Gs (unitᵛ i c)
  eval-unit (G ∷ Gs) zero    c = sym (trans (back _ (eval-0 Gs)) right-unit)
  eval-unit (G ∷ Gs) (suc i) c = trans (eval-unit Gs i c) (sym left-unit)

  -- A product of iterates of the gates, as a list of (gate, label).
  term : Vec (Gen₃ m) k → List (Fin k × F) → Circuit m
  term Gs []             = ε
  term Gs ((i , c) ∷ ts) = the (lookup Gs i) ^ᶠ c • term Gs ts

  -- Its label vector.
  vec : List (Fin k × F) → Vec F k
  vec []             = replicate _ 0F
  vec ((i , c) ∷ ts) = zipWith _+_ (unitᵛ i c) (vec ts)

  term-eval : (Gs : Vec (Gen₃ m) k) (ts : List (Fin k × F)) → m ⊢ term Gs ts ≈ eval Gs (vec ts)
  term-eval Gs []             = sym (eval-0 Gs)
  term-eval Gs ((i , c) ∷ ts) = trans (cong (eval-unit Gs i c) (term-eval Gs ts)) (eval-add Gs _ _)

  -- Two products with the same label vector are equal.
  by-labels : (Gs : Vec (Gen₃ m) k) (ts us : List (Fin k × F)) → vec ts ≡ vec us → m ⊢ term Gs ts ≈ term Gs us
  by-labels Gs ts us e = trans (term-eval Gs ts) (trans (refl' (Eq.cong (eval Gs) e)) (sym (term-eval Gs us)))
