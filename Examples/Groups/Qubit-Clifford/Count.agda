------------------------------------------------------------------------
-- Presentations of groups
--
-- The number of normal forms (the count of Corollary 5.6)
--
-- On n wires there are exactly 8 · ∏ᵢ₌₁ⁿ 2 (4ⁱ − 1) 4ⁱ normal forms
-- (NF≅order): the factor for wire i is the number of Z-normal circuits
-- on i wires times the number of X-normal circuits, and the 8 is the
-- scalar ω^p.
--
-- Each type of NormalForm is put in bijection with a Fin, gate by gate
-- (_≅_).  A ladder on m + 1 wires is m B gates and a C gate, so there
-- are 2 · 4ᵐ; a Z-normal circuit on i wires is an A gate and a ladder
-- on some wire, so there are Σₘ 3 · 2 · 4ᵐ = 2 (4ⁱ − 1) of them
-- (zc-closed); an X-normal circuit is an E gate and i − 1 D gates, 4ⁱ
-- of them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Count where

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
open import Function.Properties.Inverse using (↔-sym ; ↔-trans ; ↔-refl)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Qubit-Clifford.NormalForm

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
-- The gates

private
  pattern 0F = zero
  pattern 1F = suc zero
  pattern 2F = suc (suc zero)
  pattern 3F = suc (suc (suc zero))

AT≅ : AT ≅ 3
AT≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl }) (λ { A₁ → refl ; A₂ → refl ; A₃ → refl })
  where
  to : AT → Fin 3
  to A₁ = 0F
  to A₂ = 1F
  to A₃ = 2F
  from : Fin 3 → AT
  from 0F = A₁
  from 1F = A₂
  from 2F = A₃

BT≅ : BT ≅ 4
BT≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl ; 3F → refl })
                    (λ { B₁ → refl ; B₂ → refl ; B₃ → refl ; B₄ → refl })
  where
  to : BT → Fin 4
  to B₁ = 0F
  to B₂ = 1F
  to B₃ = 2F
  to B₄ = 3F
  from : Fin 4 → BT
  from 0F = B₁
  from 1F = B₂
  from 2F = B₃
  from 3F = B₄

CT≅ : CT ≅ 2
CT≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl }) (λ { C₁ → refl ; C₂ → refl })
  where
  to : CT → Fin 2
  to C₁ = 0F
  to C₂ = 1F
  from : Fin 2 → CT
  from 0F = C₁
  from 1F = C₂

DT≅ : DT ≅ 4
DT≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl ; 3F → refl })
                    (λ { D₁ → refl ; D₂ → refl ; D₃ → refl ; D₄ → refl })
  where
  to : DT → Fin 4
  to D₁ = 0F
  to D₂ = 1F
  to D₃ = 2F
  to D₄ = 3F
  from : Fin 4 → DT
  from 0F = D₁
  from 1F = D₂
  from 2F = D₃
  from 3F = D₄

ET≅ : ET ≅ 4
ET≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl ; 3F → refl })
                    (λ { E₁ → refl ; E₂ → refl ; E₃ → refl ; E₄ → refl })
  where
  to : ET → Fin 4
  to E₁ = 0F
  to E₂ = 1F
  to E₃ = 2F
  to E₄ = 3F
  from : Fin 4 → ET
  from 0F = E₁
  from 1F = E₂
  from 2F = E₃
  from 3F = E₄

------------------------------------------------------------------------
-- Ladders and Z-normal circuits

-- Ladders on m + 1 wires.
lad : ℕ → ℕ
lad zero    = 2
lad (suc m) = 4 * lad m

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
zc zero    = 3 * lad 0
zc (suc m) = zc m + 3 * lad (suc m)

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

  xc-split : Xc (₁₊ m) ↔ (ET × DL (₁₊ m))
  xc-split = mk↔ₛ′ (λ { (e ,ˣ dl) → e , dl }) (λ { (e , dl) → e ,ˣ dl })
                   (λ { (e , dl) → refl }) (λ { (e ,ˣ dl) → refl })

  nf-bottom : NF 0 ↔ Fin 8
  nf-bottom = mk↔ₛ′ (λ { (nf₀ p) → p }) nf₀ (λ _ → refl) (λ { (nf₀ p) → refl })

  nf-split : NF (₁₊ m) ↔ ((Zc (₁₊ m) × Xc (₁₊ m)) × NF m)
  nf-split = mk↔ₛ′ (λ { (nfₛ L M N) → (L , M) , N }) (λ { ((L , M) , N) → nfₛ L M N })
                   (λ { ((L , M) , N) → refl }) (λ { (nfₛ L M N) → refl })

DL≅ : (m : ℕ) → DL (₁₊ m) ≅ 4 ^ m
DL≅ zero    = ↔-trans dl-bottom (↔-sym 1↔⊤)
DL≅ (suc m) = ↔-trans dl-split (×≅ DT≅ (DL≅ m))

Xc≅ : (m : ℕ) → Xc (₁₊ m) ≅ 4 ^ suc m
Xc≅ m = ↔-trans xc-split (×≅ ET≅ (DL≅ m))

nf : ℕ → ℕ
nf zero    = 8
nf (suc m) = (zc m * 4 ^ suc m) * nf m

NF≅ : (n : ℕ) → NF n ≅ nf n
NF≅ zero    = nf-bottom
NF≅ (suc m) = ↔-trans nf-split (×≅ (×≅ (Zc≅ m) (Xc≅ m)) (NF≅ m))

------------------------------------------------------------------------
-- The count in closed form

-- The order of the Clifford group on n qubits, as Corollary 5.6 has
-- it: 8 · ∏ᵢ₌₁ⁿ 2 (4ⁱ − 1) 4ⁱ.
order : ℕ → ℕ
order zero    = 8
order (suc n) = order n * (2 * (4 ^ suc n ∸ 1) * 4 ^ suc n)

_ : order 1 ≡ 192
_ = refl

_ : order 2 ≡ 92160
_ = refl

private
  open +-*-Solver

  lad≡ : (m : ℕ) → lad m ≡ 2 * 4 ^ m
  lad≡ zero    = refl
  lad≡ (suc m) = begin
    4 * lad m           ≡⟨ Eq.cong (4 *_) (lad≡ m) ⟩
    4 * (2 * 4 ^ m)     ≡⟨ solve 1 (λ F → con 4 :* (con 2 :* F) := con 2 :* (con 4 :* F)) refl (4 ^ m) ⟩
    2 * (4 * 4 ^ m)     ∎
    where open Eq.≡-Reasoning

  zc-closed : (m : ℕ) → zc m + 2 ≡ 2 * 4 ^ suc m
  zc-closed zero    = refl
  zc-closed (suc m) = begin
    (zc m + 3 * lad (suc m)) + 2       ≡⟨ solve 2 (λ Z L → (Z :+ con 3 :* L) :+ con 2 := (Z :+ con 2) :+ con 3 :* L)
                                            refl (zc m) (lad (suc m)) ⟩
    (zc m + 2) + 3 * lad (suc m)       ≡⟨ Eq.cong₂ (λ x y → x + 3 * y) (zc-closed m) (lad≡ (suc m)) ⟩
    2 * F + 3 * (2 * F)                ≡⟨ solve 1 (λ F → con 2 :* F :+ con 3 :* (con 2 :* F) := con 2 :* (con 4 :* F))
                                            refl F ⟩
    2 * (4 * F)                        ∎
    where
    open Eq.≡-Reasoning
    F = 4 ^ suc m

-- There are 2 (4ⁱ − 1) Z-normal circuits on i wires.
zc≡ : (m : ℕ) → zc m ≡ 2 * (4 ^ suc m ∸ 1)
zc≡ m = Eq.trans (Eq.sym (ℕP.m+n∸n≡m (zc m) 2))
  (Eq.trans (Eq.cong (_∸ 2) (zc-closed m)) (Eq.sym (ℕP.*-distribˡ-∸ 2 (4 ^ suc m) 1)))

nf≡order : (n : ℕ) → nf n ≡ order n
nf≡order zero    = refl
nf≡order (suc m) = Eq.trans (ℕP.*-comm (zc m * 4 ^ suc m) (nf m))
  (Eq.cong₂ _*_ (nf≡order m) (Eq.cong (_* 4 ^ suc m) (zc≡ m)))

-- Corollary 5.6, counting normal forms.
NF≅order : (n : ℕ) → NF n ≅ order n
NF≅order n = Eq.subst (NF n ≅_) (nf≡order n) (NF≅ n)
