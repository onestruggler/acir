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
open import Data.List.Base as List using (List ; [] ; _∷_ ; _++_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith ; map ; replicate ; lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; p ; 0F ; 1F ; 2F ; _+_ ; _-_ ; _*_ ; -_ ; half ; sixth ; binom2 ; binom3 ; big⇒odd ; module FR ; module Odd ; module Big
        ; solve ; _:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con )
import Data.Integer.Base as ℤ
open import Data.Vec.Base using (Vec)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv using (NZ ; r)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Diag p-2 p-prime lv h gt3

private
  variable
    m k : ℕ

------------------------------------------------------------------------
-- Diagonal circuits have order p

private
  -- A product of commuting words of order p has order p.
  •-order : {x y : Circuit m} → m ⊢ x ∥ y → m ⊢ x ^ p ≈ ε → m ⊢ y ^ p ≈ ε → m ⊢ (x • y) ^ p ≈ ε
  •-order {m} c ex ey = Width.trans (Pow.pow-• m p c) (Width.trans (Width.cong ex ey) Width.left-unit)

  ᶠ-order : {x : Circuit m} (k : F) → m ⊢ x ^ p ≈ ε → m ⊢ (x ^ᶠ k) ^ p ≈ ε
  ᶠ-order k e = pow-order e (toℕ k)

  Zc-order : (c : Vec F m) → m ⊢ Zc c ^ p ≈ ε
  Zc-order []       = Pow.pow-ε 0 p
  Zc-order {suc m} (c ∷ cs) =
    •-order (Zᶠ-up c (Zc cs)) (ᶠ-order c Z-order)
            (Width.trans (Width.refl' (₁₊ m) (Eq.sym (↑-pow (Zc cs) p))) (lift (Zc-order cs)))

  atom-ord : (ℓ : NZ m) → m ⊢ atom ℓ ^ p ≈ ε
  atom-ord = atom-order

  atomᵀ-ord : (ℓ : NZ m) → m ⊢ atomᵀ ℓ ^ p ≈ ε
  atomᵀ-ord {suc m} ℓ = Width.trans (AT.A-^ ℓ p) (Width.trans (Width.back (₁₊ m) _ (Width.trans (Width.front (₁₊ m) _ T-order) Width.left-unit)) (Inv.inverseˡ (₁₊ m)))

  atoms-order : (as : Atoms m) → m ⊢ atoms as ^ p ≈ ε
  atoms-order {m} []             = Pow.pow-ε m p
  atoms-order ((ℓ , k) ∷ as) =
    •-order (∥-sym (atoms∥ as λ ℓ' k' → ∥-^ᶠ² k' k (atom∥atom ℓ' ℓ))) (ᶠ-order k (atom-ord ℓ)) (atoms-order as)

  atomsᵀ-order : (ts : Atoms m) → m ⊢ atomsᵀ ts ^ p ≈ ε
  atomsᵀ-order {m} []             = Pow.pow-ε m p
  atomsᵀ-order ((ℓ , k) ∷ ts) =
    •-order (∥-sym (atomsᵀ∥ ts λ ℓ' k' → ∥-^ᶠ² k' k (atomᵀ∥atomᵀ ℓ' ℓ))) (ᶠ-order k (atomᵀ-ord ℓ)) (atomsᵀ-order ts)

Diag₃-order : {w : Circuit m} → Diag₃ m w → m ⊢ w ^ p ≈ ε
Diag₃-order {m} ((de s c as ∣ ts) , e) =
  Width.trans (Pow.pow-cong m p e)
    (•-order (de∥atomsᵀ (de s c as) ts)
             (•-order (ωᶠ-comm s _) (ᶠ-order s ω-order)
                      (•-order (Zc∥atoms c as) (Zc-order c) (atoms-order as)))
             (atomsᵀ-order ts))

-- A diagonal circuit of order p.
record Gen₃ (m : ℕ) : Set where
  constructor gen
  field
    the : Circuit m
    dia : Diag₃ m the
    ord : m ⊢ the ^ p ≈ ε

open Gen₃ public

-- Any diagonal circuit.
gen₃ : (w : Circuit m) → Diag₃ m w → Gen₃ m
gen₃ w D = gen w D (Diag₃-order D)

eval : Vec (Gen₃ m) k → Vec F k → Circuit m
eval []       []       = ε
eval (G ∷ Gs) (e ∷ es) = the G ^ᶠ e • eval Gs es

-- The vector with c at i.
unitᵛ : Fin k → F → Vec F k
unitᵛ {suc k} zero    c = c ∷ replicate k 0F
unitᵛ {suc k} (suc i) c = 0F ∷ unitᵛ i c

-- The label vector of a list of (gate, label).
vec : List (Fin k × F) → Vec F k
vec []             = replicate _ 0F
vec ((i , c) ∷ ts) = zipWith _+_ (unitᵛ i c) (vec ts)

-- Scaling every label.
scaleᵗ : F → List (Fin k × F) → List (Fin k × F)
scaleᵗ a []             = []
scaleᵗ a ((i , c) ∷ ts) = (i , c * a) ∷ scaleᵗ a ts

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

  eval-unit : (Gs : Vec (Gen₃ m) k) (i : Fin k) (c : F) → m ⊢ the (lookup Gs i) ^ᶠ c ≈ eval Gs (unitᵛ i c)
  eval-unit (G ∷ Gs) zero    c = sym (trans (back _ (eval-0 Gs)) right-unit)
  eval-unit (G ∷ Gs) (suc i) c = trans (eval-unit Gs i c) (sym left-unit)

  -- A product of iterates of the gates, as a list of (gate, label).
  term : Vec (Gen₃ m) k → List (Fin k × F) → Circuit m
  term Gs []             = ε
  term Gs ((i , c) ∷ ts) = the (lookup Gs i) ^ᶠ c • term Gs ts

  term-eval : (Gs : Vec (Gen₃ m) k) (ts : List (Fin k × F)) → m ⊢ term Gs ts ≈ eval Gs (vec ts)
  term-eval Gs []             = sym (eval-0 Gs)
  term-eval Gs ((i , c) ∷ ts) = trans (cong (eval-unit Gs i c) (term-eval Gs ts)) (eval-add Gs _ _)

  term-++ : (Gs : Vec (Gen₃ m) k) (ts us : List (Fin k × F)) → m ⊢ term Gs (ts ++ us) ≈ term Gs ts • term Gs us
  term-++ Gs []             us = sym left-unit
  term-++ Gs ((i , c) ∷ ts) us = trans (back _ (term-++ Gs ts us)) (sym assoc)

  Diag₃-term : (Gs : Vec (Gen₃ m) k) (ts : List (Fin k × F)) → Diag₃ m (term Gs ts)
  Diag₃-term Gs []             = Diag₃-ε
  Diag₃-term Gs ((i , c) ∷ ts) = Diag₃-• (Diag₃-^ᶠ (dia (lookup Gs i)) c) (Diag₃-term Gs ts)

  term-^ᶠ : (Gs : Vec (Gen₃ m) k) (ts : List (Fin k × F)) (a : F) → m ⊢ term Gs ts ^ᶠ a ≈ term Gs (scaleᵗ a ts)
  term-^ᶠ Gs []             a = Pow.pow-ε m (toℕ a)
  term-^ᶠ Gs ((i , c) ∷ ts) a = begin
    (the (lookup Gs i) ^ᶠ c • term Gs ts) ^ᶠ a
      ≈⟨ Pow.pow-• m (toℕ a) (diag₃∥ (Diag₃-^ᶠ (dia (lookup Gs i)) c) (Diag₃-term Gs ts)) ⟩
    (the (lookup Gs i) ^ᶠ c) ^ᶠ a • term Gs ts ^ᶠ a
      ≈⟨ cong (Pow.Order.^ᶠ-* m (ord (lookup Gs i)) c a) (term-^ᶠ Gs ts a) ⟩
    the (lookup Gs i) ^ᶠ (c * a) • term Gs (scaleᵗ a ts) ∎

  -- Two products with the same label vector are equal.
  by-labels : (Gs : Vec (Gen₃ m) k) (ts us : List (Fin k × F)) → vec ts ≡ vec us → m ⊢ term Gs ts ≈ term Gs us
  by-labels Gs ts us e = trans (term-eval Gs ts) (trans (refl' (Eq.cong (eval Gs) e)) (sym (term-eval Gs us)))

------------------------------------------------------------------------
-- The facts the label arithmetic uses

-- An entry equal to E up to multiples of 2·½ - 1, (−1 choose 2) - 1
-- and (−1 choose 3) + 1 is E.
fix : (E κ₁ κ₂ κ₃ : F) →
      E + (κ₁ * ((half + half) - 1F) + (κ₂ * (binom2 (- 1F) - 1F) + κ₃ * (binom3 (- 1F) + 1F))) ≡ E
fix E κ₁ κ₂ κ₃ = Eq.trans (Eq.cong (E +_) (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (κ₁ *_) hh) (FR.zeroʳ κ₁))
                                              (Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (κ₂ *_) b2) (FR.zeroʳ κ₂))
                                                                      (Eq.trans (Eq.cong (κ₃ *_) b3) (FR.zeroʳ κ₃)))
                                                        (FR.+-identityˡ 0F)))
                                   (FR.+-identityˡ 0F)))
                  (FR.+-identityʳ E)
  where
  odd = big⇒odd gt3
  b2-1 : binom2 1F ≡ 0F
  b2-1 = solve 1 (λ t → con (ℤ.+ 1) :* (con (ℤ.+ 1) :- con (ℤ.+ 1)) :* t := con (ℤ.+ 0)) Eq.refl half
  b3-1 : binom3 1F ≡ 0F
  b3-1 = solve 1 (λ t → con (ℤ.+ 1) :* (con (ℤ.+ 1) :- con (ℤ.+ 1)) :* (con (ℤ.+ 1) :- (con (ℤ.+ 1) :+ con (ℤ.+ 1))) :* t
                         := con (ℤ.+ 0)) Eq.refl sixth
  hh : (half + half) - 1F ≡ 0F
  hh = Eq.trans (Eq.cong (_- 1F) (Eq.trans (Eq.sym (Eq.trans (FR.distribʳ half 1F 1F)
                                                       (Eq.cong₂ _+_ (FR.*-identityˡ half) (FR.*-identityˡ half))))
                                            (Odd.2*half odd)))
                (FR.-‿inverseʳ 1F)
  b2 : binom2 (- 1F) - 1F ≡ 0F
  b2 = Eq.trans (Eq.cong (_- 1F) (Eq.trans (Odd.binom2-neg odd 1F) (Eq.trans (Eq.cong (_+ 1F) b2-1) (FR.+-identityˡ 1F))))
                (FR.-‿inverseʳ 1F)
  b3 : binom3 (- 1F) + 1F ≡ 0F
  b3 = Eq.trans (Eq.cong (_+ 1F) (Eq.trans (Big.binom3-neg gt3 1F) (Eq.cong₂ (λ s t → - s - 2F * t - 1F) b3-1 b2-1)))
         (solve 0 ((((:- con (ℤ.+ 0)) :- (con (ℤ.+ 1) :+ con (ℤ.+ 1)) :* con (ℤ.+ 0)) :- con (ℤ.+ 1)) :+ con (ℤ.+ 1)
                   := con (ℤ.+ 0)) Eq.refl)
