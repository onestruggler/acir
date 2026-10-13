------------------------------------------------------------------------
-- Presentations of groups
--
-- The number of normal forms (the count closing Section 3)
--
-- On n wires there are exactly 6 · ∏ₖ₌₁ⁿ 3 (9ᵏ − 1) 9ᵏ normal forms
-- (NF≅order): the factor for wire k is the number of Z-normal circuits
-- on k wires times the number of X-normal circuits, and the 6 is the
-- scalar (−ω)ᵗ.
--
-- Each type of NormalForm is put in bijection with a Fin, box by box
-- (_≅_).  A ladder on m + 1 wires is m B boxes and a C box, so there
-- are 3 · 9ᵐ; a Z-normal circuit on k wires is an A box and a ladder
-- on some wire, so there are Σₘ 8 · 3 · 9ᵐ = 3 (9ᵏ − 1) of them
-- (zc-closed); an X-normal circuit is an E box, an F box and k − 1 D
-- boxes, 9ᵏ of them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Count where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (+↔⊎ ; *↔× ; 1↔⊤)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_ ; _∸_)
import Data.Nat.Properties as ℕP
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Product.Function.NonDependent.Propositional using (_×-↔_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Sum.Function.Propositional using (_⊎-↔_)
open import Data.Unit.Base using (⊤ ; tt)
open import Function.Bundles using (_↔_ ; mk↔ₛ′)
open import Function.Properties.Inverse using (↔-sym ; ↔-trans)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Qutrit-Clifford.NormalForm

private
  variable
    k l m : ℕ
    A B : Set

------------------------------------------------------------------------
-- Finite types

infix 4 _≅_
_≅_ : Set → ℕ → Set
A ≅ k = A ↔ Fin k

⊎≅ : A ≅ k → B ≅ l → (A ⊎ B) ≅ k + l
⊎≅ f g = ↔-trans (f ⊎-↔ g) (↔-sym +↔⊎)

×≅ : A ≅ k → B ≅ l → (A × B) ≅ k * l
×≅ f g = ↔-trans (f ×-↔ g) (↔-sym *↔×)

------------------------------------------------------------------------
-- The boxes

private
  pattern 0F = zero
  pattern 1F = suc zero
  pattern 2F = suc (suc zero)
  pattern 3F = suc (suc (suc zero))
  pattern 4F = suc (suc (suc (suc zero)))
  pattern 5F = suc (suc (suc (suc (suc zero))))
  pattern 6F = suc (suc (suc (suc (suc (suc zero)))))
  pattern 7F = suc (suc (suc (suc (suc (suc (suc zero))))))
  pattern 8F = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))

AT≅ : AT ≅ 8
AT≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl ; 3F → refl ; 4F → refl ; 5F → refl ; 6F → refl ; 7F → refl })
                    (λ { A₀₁ → refl ; A₀₂ → refl ; A₁₀ → refl ; A₁₁ → refl ; A₁₂ → refl ; A₂₀ → refl ; A₂₁ → refl ; A₂₂ → refl })
  where
  to : AT → Fin 8
  to A₀₁ = 0F
  to A₀₂ = 1F
  to A₁₀ = 2F
  to A₁₁ = 3F
  to A₁₂ = 4F
  to A₂₀ = 5F
  to A₂₁ = 6F
  to A₂₂ = 7F
  from : Fin 8 → AT
  from 0F = A₀₁
  from 1F = A₀₂
  from 2F = A₁₀
  from 3F = A₁₁
  from 4F = A₁₂
  from 5F = A₂₀
  from 6F = A₂₁
  from 7F = A₂₂

BT≅ : BT ≅ 9
BT≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl ; 3F → refl ; 4F → refl ; 5F → refl ; 6F → refl ; 7F → refl ; 8F → refl })
                    (λ { B₀₀ → refl ; B₀₁ → refl ; B₀₂ → refl ; B₁₀ → refl ; B₁₁ → refl ; B₁₂ → refl ; B₂₀ → refl ; B₂₁ → refl ; B₂₂ → refl })
  where
  to : BT → Fin 9
  to B₀₀ = 0F
  to B₀₁ = 1F
  to B₀₂ = 2F
  to B₁₀ = 3F
  to B₁₁ = 4F
  to B₁₂ = 5F
  to B₂₀ = 6F
  to B₂₁ = 7F
  to B₂₂ = 8F
  from : Fin 9 → BT
  from 0F = B₀₀
  from 1F = B₀₁
  from 2F = B₀₂
  from 3F = B₁₀
  from 4F = B₁₁
  from 5F = B₁₂
  from 6F = B₂₀
  from 7F = B₂₁
  from 8F = B₂₂

CT≅ : CT ≅ 3
CT≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl })
                    (λ { C₀ → refl ; C₁ → refl ; C₂ → refl })
  where
  to : CT → Fin 3
  to C₀ = 0F
  to C₁ = 1F
  to C₂ = 2F
  from : Fin 3 → CT
  from 0F = C₀
  from 1F = C₁
  from 2F = C₂

DT≅ : DT ≅ 9
DT≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl ; 3F → refl ; 4F → refl ; 5F → refl ; 6F → refl ; 7F → refl ; 8F → refl })
                    (λ { D₀₀ → refl ; D₀₁ → refl ; D₀₂ → refl ; D₁₀ → refl ; D₁₁ → refl ; D₁₂ → refl ; D₂₀ → refl ; D₂₁ → refl ; D₂₂ → refl })
  where
  to : DT → Fin 9
  to D₀₀ = 0F
  to D₀₁ = 1F
  to D₀₂ = 2F
  to D₁₀ = 3F
  to D₁₁ = 4F
  to D₁₂ = 5F
  to D₂₀ = 6F
  to D₂₁ = 7F
  to D₂₂ = 8F
  from : Fin 9 → DT
  from 0F = D₀₀
  from 1F = D₀₁
  from 2F = D₀₂
  from 3F = D₁₀
  from 4F = D₁₁
  from 5F = D₁₂
  from 6F = D₂₀
  from 7F = D₂₁
  from 8F = D₂₂

ET≅ : ET ≅ 3
ET≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl })
                    (λ { E₀ → refl ; E₁ → refl ; E₂ → refl })
  where
  to : ET → Fin 3
  to E₀ = 0F
  to E₁ = 1F
  to E₂ = 2F
  from : Fin 3 → ET
  from 0F = E₀
  from 1F = E₁
  from 2F = E₂

FT≅ : FT ≅ 3
FT≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl })
                    (λ { F₀ → refl ; F₁ → refl ; F₂ → refl })
  where
  to : FT → Fin 3
  to F₀ = 0F
  to F₁ = 1F
  to F₂ = 2F
  from : Fin 3 → FT
  from 0F = F₀
  from 1F = F₁
  from 2F = F₂

------------------------------------------------------------------------
-- Ladders and Z-normal circuits

-- Ladders on m + 1 wires.
lad : ℕ → ℕ
lad zero    = 3
lad (suc m) = 9 * lad m

private
  lad-top : Lad 1 ↔ CT
  lad-top = mk↔ₛ′ (λ { (top c) → c }) top (λ _ → refl) (λ { (top c) → refl })

  lad-split : Lad (₂₊ m) ↔ (BT × Lad (₁₊ m))
  lad-split = mk↔ₛ′ (λ { (b ∷ᴮ l) → b , l }) (λ { (b , l) → b ∷ᴮ l })
                    (λ { (b , l) → refl }) (λ { (b ∷ᴮ l) → refl })

Lad≅ : (m : ℕ) → Lad (₁₊ m) ≅ lad m
Lad≅ zero    = ↔-trans lad-top CT≅
Lad≅ (suc m) = ↔-trans lad-split (×≅ BT≅ (Lad≅ m))

-- Z-normal circuits on m + 1 wires: on the bottom wire, or one wire up.
zc : ℕ → ℕ
zc zero    = 8 * lad 0
zc (suc m) = zc m + 8 * lad (suc m)

private
  zc-bottom : Zc 1 ↔ (AT × Lad 1)
  zc-bottom = mk↔ₛ′ (λ { (at a l) → a , l }) (λ { (a , l) → at a l })
                    (λ { (a , l) → refl }) (λ { (at a l) → refl })

  zc-split : Zc (₂₊ m) ↔ (Zc (₁₊ m) ⊎ (AT × Lad (₂₊ m)))
  zc-split {m} = mk↔ₛ′ to from to-from from-to
    where
    to : Zc (₂₊ m) → Zc (₁₊ m) ⊎ (AT × Lad (₂₊ m))
    to (up L)   = inj₁ L
    to (at a l) = inj₂ (a , l)
    from : Zc (₁₊ m) ⊎ (AT × Lad (₂₊ m)) → Zc (₂₊ m)
    from (inj₁ L)       = up L
    from (inj₂ (a , l)) = at a l
    to-from : ∀ x → to (from x) ≡ x
    to-from (inj₁ _) = refl
    to-from (inj₂ _) = refl
    from-to : ∀ x → from (to x) ≡ x
    from-to (up L)   = refl
    from-to (at a l) = refl

Zc≅ : (m : ℕ) → Zc (₁₊ m) ≅ zc m
Zc≅ zero    = ↔-trans zc-bottom (×≅ AT≅ (Lad≅ 0))
Zc≅ (suc m) = ↔-trans zc-split (⊎≅ (Zc≅ m) (×≅ AT≅ (Lad≅ (suc m))))

------------------------------------------------------------------------
-- X-normal circuits and normal forms

private
  dl-bottom : DL 1 ↔ ⊤
  dl-bottom = mk↔ₛ′ (λ { []ᴰ → tt }) (λ { tt → []ᴰ }) (λ { tt → refl }) (λ { []ᴰ → refl })

  dl-split : DL (₂₊ m) ↔ (DT × DL (₁₊ m))
  dl-split = mk↔ₛ′ (λ { (d ∷ᴰ dl) → d , dl }) (λ { (d , dl) → d ∷ᴰ dl })
                   (λ { (d , dl) → refl }) (λ { (d ∷ᴰ dl) → refl })

  xc-split : Xc (₁₊ m) ↔ ((ET × FT) × DL (₁₊ m))
  xc-split = mk↔ₛ′ (λ { (xc e f dl) → (e , f) , dl }) (λ { ((e , f) , dl) → xc e f dl })
                   (λ { ((e , f) , dl) → refl }) (λ { (xc e f dl) → refl })

  nf-bottom : NF 0 ↔ Fin 6
  nf-bottom = mk↔ₛ′ (λ { (nf₀ t) → t }) nf₀ (λ _ → refl) (λ { (nf₀ t) → refl })

  nf-split : NF (₁₊ m) ↔ ((Zc (₁₊ m) × Xc (₁₊ m)) × NF m)
  nf-split = mk↔ₛ′ (λ { (nfₛ L M N) → (L , M) , N }) (λ { ((L , M) , N) → nfₛ L M N })
                   (λ { ((L , M) , N) → refl }) (λ { (nfₛ L M N) → refl })

DL≅ : (m : ℕ) → DL (₁₊ m) ≅ 9 ^ m
DL≅ zero    = ↔-trans dl-bottom (↔-sym 1↔⊤)
DL≅ (suc m) = ↔-trans dl-split (×≅ DT≅ (DL≅ m))

Xc≅ : (m : ℕ) → Xc (₁₊ m) ≅ 9 ^ suc m
Xc≅ m = ↔-trans xc-split (×≅ (×≅ ET≅ FT≅) (DL≅ m))

nf : ℕ → ℕ
nf zero    = 6
nf (suc m) = (zc m * 9 ^ suc m) * nf m

NF≅ : (n : ℕ) → NF n ≅ nf n
NF≅ zero    = nf-bottom
NF≅ (suc m) = ↔-trans nf-split (×≅ (×≅ (Zc≅ m) (Xc≅ m)) (NF≅ m))

------------------------------------------------------------------------
-- The count in closed form

-- The order of the Clifford group on n qutrits: 6 · ∏ₖ₌₁ⁿ 3 (9ᵏ − 1) 9ᵏ.
order : ℕ → ℕ
order zero    = 6
order (suc n) = order n * (3 * (9 ^ suc n ∸ 1) * 9 ^ suc n)

_ : order 1 ≡ 1296
_ = refl

_ : order 2 ≡ 25194240
_ = refl

private
  open +-*-Solver

  lad≡ : (m : ℕ) → lad m ≡ 3 * 9 ^ m
  lad≡ zero    = refl
  lad≡ (suc m) = begin
    9 * lad m           ≡⟨ Eq.cong (9 *_) (lad≡ m) ⟩
    9 * (3 * 9 ^ m)     ≡⟨ solve 1 (λ F → con 9 :* (con 3 :* F) := con 3 :* (con 9 :* F)) refl (9 ^ m) ⟩
    3 * (9 * 9 ^ m)     ∎
    where open Eq.≡-Reasoning

  zc-closed : (m : ℕ) → zc m + 3 ≡ 3 * 9 ^ suc m
  zc-closed zero    = refl
  zc-closed (suc m) = begin
    (zc m + 8 * lad (suc m)) + 3       ≡⟨ solve 2 (λ Z L → (Z :+ con 8 :* L) :+ con 3 := (Z :+ con 3) :+ con 8 :* L)
                                            refl (zc m) (lad (suc m)) ⟩
    (zc m + 3) + 8 * lad (suc m)       ≡⟨ Eq.cong₂ (λ x y → x + 8 * y) (zc-closed m) (lad≡ (suc m)) ⟩
    3 * F + 8 * (3 * F)                ≡⟨ solve 1 (λ F → con 3 :* F :+ con 8 :* (con 3 :* F) := con 3 :* (con 9 :* F))
                                            refl F ⟩
    3 * (9 * F)                        ∎
    where
    open Eq.≡-Reasoning
    F = 9 ^ suc m

-- There are 3 (9ᵏ − 1) Z-normal circuits on k wires.
zc≡ : (m : ℕ) → zc m ≡ 3 * (9 ^ suc m ∸ 1)
zc≡ m = Eq.trans (Eq.sym (ℕP.m+n∸n≡m (zc m) 3))
  (Eq.trans (Eq.cong (_∸ 3) (zc-closed m)) (Eq.sym (ℕP.*-distribˡ-∸ 3 (9 ^ suc m) 1)))

nf≡order : (n : ℕ) → nf n ≡ order n
nf≡order zero    = refl
nf≡order (suc m) = Eq.trans (ℕP.*-comm (zc m * 9 ^ suc m) (nf m))
  (Eq.cong₂ _*_ (nf≡order m) (Eq.cong (_* 9 ^ suc m) (zc≡ m)))

-- Counting normal forms.
NF≅order : (n : ℕ) → NF n ≅ order n
NF≅order n = Eq.subst (NF n ≅_) (nf≡order n) (NF≅ n)
