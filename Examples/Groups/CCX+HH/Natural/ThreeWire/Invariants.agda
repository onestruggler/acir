------------------------------------------------------------------------
-- Presentations of groups
--
-- The coset invariants of the three-wire tower.
--
-- Each level's cosets of the level below are told apart by an
-- invariant of signed permutations that the letters below leave
-- unchanged when acting on the left:
--   * AGL(3,2) over the translations: the images relative to the image
--     of level 0, with the signs (`ψA`);
--   * S8 over AGL(3,2): which 4-sets of levels are sent to affine
--     planes (`ψS`), since affine maps send planes to planes;
--   * W(D8) over S8: the signs (`ψD`), which permutations keep.
-- The letter lemmas (`ψA-letter`, `ψS-letter`, `ψD-letter`) reduce to
-- finite facts about the letters, decided by one boolean each.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Invariants where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _xor_ ; not)
import Data.Bool.Properties as BP
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.List.Base using (List ; [] ; _∷_)
import Data.List.Base as List
import Data.List.Properties as LP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; map)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Perm
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Gamma using (L ; x0 ; x1 ; x2 ; cx0 ; cx1 ; cxr0 ; cxr1 ; ccx0 ; z1 ; spL)

------------------------------------------------------------------------
-- The letters of each level

ιZ : Fin 3 → L
ιZ ₀ = x0
ιZ ₁ = x1
ιZ ₂ = x2

ιA : Fin 7 → L
ιA ₀ = x0
ιA ₁ = x1
ιA ₂ = x2
ιA ₃ = cx0
ιA ₄ = cx1
ιA ₅ = cxr0
ιA ₆ = cxr1

ιS : Fin 8 → L
ιS ₀ = x0
ιS ₁ = x1
ιS ₂ = x2
ιS ₃ = cx0
ιS ₄ = cx1
ιS ₅ = cxr0
ιS ₆ = cxr1
ιS ₇ = ccx0

ιD : Fin 9 → L
ιD ₀ = x0
ιD ₁ = x1
ιD ₂ = x2
ιD ₃ = cx0
ιD ₄ = cx1
ιD ₅ = cxr0
ιD ₆ = cxr1
ιD ₇ = ccx0
ιD (suc ₇) = z1

private
  img : SP → Fin 8 → Fin 8
  img g i = proj₁ (lookup g i)

  img-mul : ∀ a g i → img (mul a g) i ≡ proj₁ (lookup a (img g i))
  img-mul a g i = cong proj₁ (lookup-mul a g i)

  map-cong-vec : ∀ {A B : Set} {n} {f g : A → B} (v : Vec A n) → (∀ x → f x ≡ g x) → map f v ≡ map g v
  map-cong-vec v p = VP.map-cong p v

------------------------------------------------------------------------
-- AGL(3,2) over the translations

-- The translation of each letter of Z2^3.
tZ : Fin 3 → Fin 8
tZ ₀ = ₁
tZ ₁ = ₂
tZ ₂ = ₄

shift : Fin 8 → Fin 8 × Bool → Fin 8 × Bool
shift t (j , s) = j ⊕ t , s

ψA : SP → SP
ψA g = map (shift (img g ₀)) g

private
  translates : ∀ b j → lookup (spL (ιZ b)) j ≡ (j ⊕ tZ b , false)
  translates b j = check (allFin-sound 3 (λ b → allFin 8 (λ j → test b j)) refl b) j
    where
    test : Fin 3 → Fin 8 → Bool
    test b j = eqF (proj₁ (lookup (spL (ιZ b)) j)) (j ⊕ tZ b) ∧ not (proj₂ (lookup (spL (ιZ b)) j))
    pair : ∀ {p : Fin 8 × Bool} {k} → eqF (proj₁ p) k ∧ not (proj₂ p) ≡ true → p ≡ (k , false)
    pair {j′ , false} {k} h = cong (_, false) (eqF-sound j′ k (lemma h))
      where lemma : ∀ {x} → x ∧ true ≡ true → x ≡ true
            lemma {true} _ = refl
    pair {j′ , true} {k} h = ⊥-elim′ h
      where ⊥-elim′ : ∀ {x} {A : Set} → x ∧ false ≡ true → A
            ⊥-elim′ {true} ()
            ⊥-elim′ {false} ()
    check : allFin 8 (test b) ≡ true → ∀ j → lookup (spL (ιZ b)) j ≡ (j ⊕ tZ b , false)
    check h j = pair (allFin-sound 8 (test b) h j)

ψA-letter : ∀ b g → ψA (mul (spL (ιZ b)) g) ≡ ψA g
ψA-letter b g = vec-ext λ i → trans (VP.lookup-map i _ (mul (spL (ιZ b)) g))
  (trans (cong₂ shift (trans (img-mul (spL (ιZ b)) g ₀) (cong proj₁ (translates b (img g ₀))))
           (lookup-mul (spL (ιZ b)) g i))
  (trans (step (lookup g i)) (sym (VP.lookup-map i _ g))))
  where
  step : ∀ p → shift (img g ₀ ⊕ tZ b) (act (spL (ιZ b)) p) ≡ shift (img g ₀) p
  step (j , s) rewrite translates b j =
    cong₂ _,_ (xor-cancel j (img g ₀) (tZ b)) (BP.xor-identityʳ s)

------------------------------------------------------------------------
-- S8 over AGL(3,2)

quads : List (Fin 8 × Fin 8 × Fin 8 × Fin 8)
quads =
  (₀ , ₁ , ₂ , ₃) ∷
  (₀ , ₁ , ₂ , ₄) ∷
  (₀ , ₁ , ₂ , ₅) ∷
  (₀ , ₁ , ₂ , ₆) ∷
  (₀ , ₁ , ₂ , ₇) ∷
  (₀ , ₁ , ₃ , ₄) ∷
  (₀ , ₁ , ₃ , ₅) ∷
  (₀ , ₁ , ₃ , ₆) ∷
  (₀ , ₁ , ₃ , ₇) ∷
  (₀ , ₁ , ₄ , ₅) ∷
  (₀ , ₁ , ₄ , ₆) ∷
  (₀ , ₁ , ₄ , ₇) ∷
  (₀ , ₁ , ₅ , ₆) ∷
  (₀ , ₁ , ₅ , ₇) ∷
  (₀ , ₁ , ₆ , ₇) ∷
  (₀ , ₂ , ₃ , ₄) ∷
  (₀ , ₂ , ₃ , ₅) ∷
  (₀ , ₂ , ₃ , ₆) ∷
  (₀ , ₂ , ₃ , ₇) ∷
  (₀ , ₂ , ₄ , ₅) ∷
  (₀ , ₂ , ₄ , ₆) ∷
  (₀ , ₂ , ₄ , ₇) ∷
  (₀ , ₂ , ₅ , ₆) ∷
  (₀ , ₂ , ₅ , ₇) ∷
  (₀ , ₂ , ₆ , ₇) ∷
  (₀ , ₃ , ₄ , ₅) ∷
  (₀ , ₃ , ₄ , ₆) ∷
  (₀ , ₃ , ₄ , ₇) ∷
  (₀ , ₃ , ₅ , ₆) ∷
  (₀ , ₃ , ₅ , ₇) ∷
  (₀ , ₃ , ₆ , ₇) ∷
  (₀ , ₄ , ₅ , ₆) ∷
  (₀ , ₄ , ₅ , ₇) ∷
  (₀ , ₄ , ₆ , ₇) ∷
  (₀ , ₅ , ₆ , ₇) ∷
  (₁ , ₂ , ₃ , ₄) ∷
  (₁ , ₂ , ₃ , ₅) ∷
  (₁ , ₂ , ₃ , ₆) ∷
  (₁ , ₂ , ₃ , ₇) ∷
  (₁ , ₂ , ₄ , ₅) ∷
  (₁ , ₂ , ₄ , ₆) ∷
  (₁ , ₂ , ₄ , ₇) ∷
  (₁ , ₂ , ₅ , ₆) ∷
  (₁ , ₂ , ₅ , ₇) ∷
  (₁ , ₂ , ₆ , ₇) ∷
  (₁ , ₃ , ₄ , ₅) ∷
  (₁ , ₃ , ₄ , ₆) ∷
  (₁ , ₃ , ₄ , ₇) ∷
  (₁ , ₃ , ₅ , ₆) ∷
  (₁ , ₃ , ₅ , ₇) ∷
  (₁ , ₃ , ₆ , ₇) ∷
  (₁ , ₄ , ₅ , ₆) ∷
  (₁ , ₄ , ₅ , ₇) ∷
  (₁ , ₄ , ₆ , ₇) ∷
  (₁ , ₅ , ₆ , ₇) ∷
  (₂ , ₃ , ₄ , ₅) ∷
  (₂ , ₃ , ₄ , ₆) ∷
  (₂ , ₃ , ₄ , ₇) ∷
  (₂ , ₃ , ₅ , ₆) ∷
  (₂ , ₃ , ₅ , ₇) ∷
  (₂ , ₃ , ₆ , ₇) ∷
  (₂ , ₄ , ₅ , ₆) ∷
  (₂ , ₄ , ₅ , ₇) ∷
  (₂ , ₄ , ₆ , ₇) ∷
  (₂ , ₅ , ₆ , ₇) ∷
  (₃ , ₄ , ₅ , ₆) ∷
  (₃ , ₄ , ₅ , ₇) ∷
  (₃ , ₄ , ₆ , ₇) ∷
  (₃ , ₅ , ₆ , ₇) ∷
  (₄ , ₅ , ₆ , ₇) ∷
  []

plane : (Fin 8 → Fin 8) → Fin 8 × Fin 8 × Fin 8 × Fin 8 → Bool
plane f (a , b , c , d) = eqF (f a ⊕ f b ⊕ f c ⊕ f d) ₀

ψS : SP → List Bool
ψS g = List.map (plane (img g)) quads

private
  affine : ∀ b w x y z →
    eqF (proj₁ (lookup (spL (ιA b)) w) ⊕ proj₁ (lookup (spL (ιA b)) x) ⊕
         proj₁ (lookup (spL (ιA b)) y) ⊕ proj₁ (lookup (spL (ιA b)) z)) ₀
    ≡ eqF (w ⊕ x ⊕ y ⊕ z) ₀
  affine b w x y z = eqB (allFin-sound 8 (t₄ b w x y) (allFin-sound 8 (t₃ b w x)
    (allFin-sound 8 (t₂ b w) (allFin-sound 8 (t₁ b) (allFin-sound 7 t₀ refl b) w) x) y) z)
    where
    π : Fin 7 → Fin 8 → Fin 8
    π b j = proj₁ (lookup (spL (ιA b)) j)
    same : Bool → Bool → Bool
    same true  y = y
    same false y = not y
    eqB : ∀ {p q} → same p q ≡ true → p ≡ q
    eqB {true}  {true}  _ = refl
    eqB {false} {false} _ = refl
    t₄ : Fin 7 → Fin 8 → Fin 8 → Fin 8 → Fin 8 → Bool
    t₄ b w x y z = same (eqF (π b w ⊕ π b x ⊕ π b y ⊕ π b z) ₀) (eqF (w ⊕ x ⊕ y ⊕ z) ₀)
    t₃ : Fin 7 → Fin 8 → Fin 8 → Fin 8 → Bool
    t₃ b w x y = allFin 8 (t₄ b w x y)
    t₂ : Fin 7 → Fin 8 → Fin 8 → Bool
    t₂ b w x = allFin 8 (t₃ b w x)
    t₁ : Fin 7 → Fin 8 → Bool
    t₁ b w = allFin 8 (t₂ b w)
    t₀ : Fin 7 → Bool
    t₀ b = allFin 8 (t₁ b)

ψS-letter : ∀ b g → ψS (mul (spL (ιA b)) g) ≡ ψS g
ψS-letter b g = LP.map-cong step quads
  where
  step : ∀ q → plane (img (mul (spL (ιA b)) g)) q ≡ plane (img g) q
  step (a , b′ , c , d)
    rewrite img-mul (spL (ιA b)) g a | img-mul (spL (ιA b)) g b′
          | img-mul (spL (ιA b)) g c | img-mul (spL (ιA b)) g d =
    affine b (img g a) (img g b′) (img g c) (img g d)

------------------------------------------------------------------------
-- W(D8) over S8

ψD : SP → Vec Bool 8
ψD g = map proj₂ g

private
  unsigned : ∀ b j → proj₂ (lookup (spL (ιS b)) j) ≡ false
  unsigned b j = neg (allFin-sound 8 (test b) (allFin-sound 8 (λ b → allFin 8 (test b)) refl b) j)
    where
    test : Fin 8 → Fin 8 → Bool
    test b j = not (proj₂ (lookup (spL (ιS b)) j))
    neg : ∀ {x} → not x ≡ true → x ≡ false
    neg {false} _ = refl

ψD-letter : ∀ b g → ψD (mul (spL (ιS b)) g) ≡ ψD g
ψD-letter b g = trans (sym (VP.map-∘ proj₂ (act (spL (ιS b))) g)) (VP.map-cong step g)
  where
  step : ∀ p → proj₂ (act (spL (ιS b)) p) ≡ proj₂ p
  step (j , s) = trans (cong (s xor_) (unsigned b j)) (BP.xor-identityʳ s)

------------------------------------------------------------------------
-- Boolean equality of invariant values (for the coset lookup tables)

eqB : Bool → Bool → Bool
eqB true  true  = true
eqB false false = true
eqB _     _     = false

eqVec : ∀ {A : Set} {n} → (A → A → Bool) → Vec A n → Vec A n → Bool
eqVec eq []       []       = true
eqVec eq (x ∷ xs) (y ∷ ys) = eq x y ∧ eqVec eq xs ys

eqSP : SP → SP → Bool
eqSP = eqVec (λ p q → eqF (proj₁ p) (proj₁ q) ∧ eqB (proj₂ p) (proj₂ q))

eqVB : Vec Bool 8 → Vec Bool 8 → Bool
eqVB = eqVec eqB

eqLB : List Bool → List Bool → Bool
eqLB []       []       = true
eqLB (x ∷ xs) (y ∷ ys) = eqB x y ∧ eqLB xs ys
eqLB _        _        = false
