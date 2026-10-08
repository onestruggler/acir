------------------------------------------------------------------------
-- Presentations of groups
--
-- The number of normal forms (the count of Corollary 4.16)
--
-- On n wires there are exactly 2 · ∏ᵢ₌₁ⁿ (4ⁱ + 2ⁱ − 2)(2 · 4ⁱ⁻¹) normal
-- forms (NF≅order): the factor for wire i is the number of Z-circuits
-- on i wires times the number of X-circuits, and the 2 is the sign.
--
-- Each type of NormalForm is put in bijection with a Fin, gate by gate
-- (_≅_): a ladder whose lower input has type t is a B gate with that
-- input, followed by a ladder whose lower input is the gate's upper
-- output, so with Lₜ(m) ladders on m + 1 wires,
--
--   L_sg(m + 1) = 3 L_sg(m) + L_db(m),   L_db(m + 1) = L_sg(m) + 3 L_db(m),
--
-- from L_sg(0) = 2 (the C gates) and L_db(0) = 0, which gives
-- L_sg(m) = 4ᵐ + 2ᵐ and L_db(m) = 4ᵐ − 2ᵐ (lad-sg, lad-db).  A Z-circuit
-- is an A gate (two of single type, one of double type) and a ladder,
-- on some wire, so there are 4ⁱ + 2ⁱ − 2 on i wires (zc-closed); an
-- X-circuit is an E gate and i − 1 D gates, 2 · 4ⁱ⁻¹ of them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Count where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (+↔⊎ ; *↔× ; 0↔⊥ ; 1↔⊤)
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

open import Examples.Groups.Real-Clifford.NormalForm

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

Bool≅ : Bool ≅ 2
Bool≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl }) (λ { false → refl ; true → refl })
  where
  to : Bool → Fin 2
  to false = 0F
  to true  = 1F
  from : Fin 2 → Bool
  from 0F = false
  from 1F = true

#A : Ty → ℕ
#A sg = 2
#A db = 1

AT≅ : (t : Ty) → AT t ≅ #A t
AT≅ sg = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl }) (λ { A₁ → refl ; A₂ → refl })
  where
  to : AT sg → Fin 2
  to A₁ = 0F
  to A₂ = 1F
  from : Fin 2 → AT sg
  from 0F = A₁
  from 1F = A₂
AT≅ db = mk↔ₛ′ (λ { A₃ → 0F }) (λ { 0F → A₃ }) (λ { 0F → refl }) (λ { A₃ → refl })

bt : Ty → Ty → ℕ
bt sg sg = 3
bt sg db = 1
bt db db = 3
bt db sg = 1

BT≅ : (t u : Ty) → BT t u ≅ bt t u
BT≅ sg sg = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl }) (λ { B₁ → refl ; B₂ → refl ; B₃ → refl })
  where
  to : BT sg sg → Fin 3
  to B₁ = 0F
  to B₂ = 1F
  to B₃ = 2F
  from : Fin 3 → BT sg sg
  from 0F = B₁
  from 1F = B₂
  from 2F = B₃
BT≅ sg db = mk↔ₛ′ (λ { B₄ → 0F }) (λ { 0F → B₄ }) (λ { 0F → refl }) (λ { B₄ → refl })
BT≅ db db = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl ; 2F → refl }) (λ { B₅ → refl ; B₆ → refl ; B₇ → refl })
  where
  to : BT db db → Fin 3
  to B₅ = 0F
  to B₆ = 1F
  to B₇ = 2F
  from : Fin 3 → BT db db
  from 0F = B₅
  from 1F = B₆
  from 2F = B₇
BT≅ db sg = mk↔ₛ′ (λ { B₈ → 0F }) (λ { 0F → B₈ }) (λ { 0F → refl }) (λ { B₈ → refl })

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

ET≅ : ET ≅ 2
ET≅ = mk↔ₛ′ to from (λ { 0F → refl ; 1F → refl }) (λ { E₁ → refl ; E₂ → refl })
  where
  to : ET → Fin 2
  to E₁ = 0F
  to E₂ = 1F
  from : Fin 2 → ET
  from 0F = E₁
  from 1F = E₂

------------------------------------------------------------------------
-- Ladders and Z-circuits

-- Ladders on m + 1 wires whose lower input has type t.
lad₀ : Ty → ℕ
lad₀ sg = 2
lad₀ db = 0

lad : Ty → ℕ → ℕ
lad t zero    = lad₀ t
lad t (suc m) = bt t sg * lad sg m + bt t db * lad db m

private
  lad-top : Lad sg 1 ↔ CT
  lad-top = mk↔ₛ′ (λ { (top c) → c }) top (λ _ → refl) (λ { (top c) → refl })

  lad-none : Lad db 1 ↔ ⊥
  lad-none = mk↔ₛ′ (λ ()) (λ ()) (λ ()) (λ ())

  lad-split : (t : Ty) → Lad t (₂₊ m) ↔ ((BT t sg × Lad sg (₁₊ m)) ⊎ (BT t db × Lad db (₁₊ m)))
  lad-split {m} t = mk↔ₛ′ to from to-from from-to
    where
    to : Lad t (₂₊ m) → (BT t sg × Lad sg (₁₊ m)) ⊎ (BT t db × Lad db (₁₊ m))
    to (_∷ᴮ_ {u = sg} b l) = inj₁ (b , l)
    to (_∷ᴮ_ {u = db} b l) = inj₂ (b , l)
    from : (BT t sg × Lad sg (₁₊ m)) ⊎ (BT t db × Lad db (₁₊ m)) → Lad t (₂₊ m)
    from (inj₁ (b , l)) = b ∷ᴮ l
    from (inj₂ (b , l)) = b ∷ᴮ l
    to-from : ∀ x → to (from x) ≡ x
    to-from (inj₁ _) = refl
    to-from (inj₂ _) = refl
    from-to : ∀ x → from (to x) ≡ x
    from-to (_∷ᴮ_ {u = sg} b l) = refl
    from-to (_∷ᴮ_ {u = db} b l) = refl

Lad≅ : (t : Ty) (m : ℕ) → Lad t (₁₊ m) ≅ lad t m
Lad≅ sg zero    = ↔-trans lad-top CT≅
Lad≅ db zero    = ↔-trans lad-none (↔-sym 0↔⊥)
Lad≅ t  (suc m) = ↔-trans (lad-split t) (⊎≅ (×≅ (BT≅ t sg) (Lad≅ sg m)) (×≅ (BT≅ t db) (Lad≅ db m)))

-- Z-circuits on m + 1 wires: on the bottom wire, or one wire up.
zc : ℕ → ℕ
zc zero    = #A sg * lad sg 0 + #A db * lad db 0
zc (suc m) = zc m + (#A sg * lad sg (suc m) + #A db * lad db (suc m))

private
  zc-bottom : Zc 1 ↔ ((AT sg × Lad sg 1) ⊎ (AT db × Lad db 1))
  zc-bottom = mk↔ₛ′ to from to-from from-to
    where
    to : Zc 1 → (AT sg × Lad sg 1) ⊎ (AT db × Lad db 1)
    to (at {t = sg} a l) = inj₁ (a , l)
    to (at {t = db} a l) = inj₂ (a , l)
    from : (AT sg × Lad sg 1) ⊎ (AT db × Lad db 1) → Zc 1
    from (inj₁ (a , l)) = at a l
    from (inj₂ (a , l)) = at a l
    to-from : ∀ x → to (from x) ≡ x
    to-from (inj₁ _) = refl
    to-from (inj₂ _) = refl
    from-to : ∀ x → from (to x) ≡ x
    from-to (at {t = sg} a l) = refl
    from-to (at {t = db} a l) = refl

  zc-split : Zc (₂₊ m) ↔ (Zc (₁₊ m) ⊎ ((AT sg × Lad sg (₂₊ m)) ⊎ (AT db × Lad db (₂₊ m))))
  zc-split {m} = mk↔ₛ′ to from to-from from-to
    where
    to : Zc (₂₊ m) → Zc (₁₊ m) ⊎ ((AT sg × Lad sg (₂₊ m)) ⊎ (AT db × Lad db (₂₊ m)))
    to (up L)            = inj₁ L
    to (at {t = sg} a l) = inj₂ (inj₁ (a , l))
    to (at {t = db} a l) = inj₂ (inj₂ (a , l))
    from : Zc (₁₊ m) ⊎ ((AT sg × Lad sg (₂₊ m)) ⊎ (AT db × Lad db (₂₊ m))) → Zc (₂₊ m)
    from (inj₁ L)                = up L
    from (inj₂ (inj₁ (a , l)))   = at a l
    from (inj₂ (inj₂ (a , l)))   = at a l
    to-from : ∀ x → to (from x) ≡ x
    to-from (inj₁ _)        = refl
    to-from (inj₂ (inj₁ _)) = refl
    to-from (inj₂ (inj₂ _)) = refl
    from-to : ∀ x → from (to x) ≡ x
    from-to (up L)            = refl
    from-to (at {t = sg} a l) = refl
    from-to (at {t = db} a l) = refl

Zc≅ : (m : ℕ) → Zc (₁₊ m) ≅ zc m
Zc≅ zero    = ↔-trans zc-bottom (⊎≅ (×≅ (AT≅ sg) (Lad≅ sg 0)) (×≅ (AT≅ db) (Lad≅ db 0)))
Zc≅ (suc m) = ↔-trans zc-split
  (⊎≅ (Zc≅ m) (⊎≅ (×≅ (AT≅ sg) (Lad≅ sg (suc m))) (×≅ (AT≅ db) (Lad≅ db (suc m)))))

------------------------------------------------------------------------
-- X-circuits and normal forms

private
  dl-bottom : DL 1 ↔ ⊤
  dl-bottom = mk↔ₛ′ (λ { []ᴰ → tt }) (λ { tt → []ᴰ }) (λ { tt → refl }) (λ { []ᴰ → refl })

  dl-split : DL (₂₊ m) ↔ (DT × DL (₁₊ m))
  dl-split = mk↔ₛ′ (λ { (d ∷ᴰ dl) → d , dl }) (λ { (d , dl) → d ∷ᴰ dl })
                   (λ { (d , dl) → refl }) (λ { (d ∷ᴰ dl) → refl })

  xc-split : Xc (₁₊ m) ↔ (ET × DL (₁₊ m))
  xc-split = mk↔ₛ′ (λ { (e ,ˣ dl) → e , dl }) (λ { (e , dl) → e ,ˣ dl })
                   (λ { (e , dl) → refl }) (λ { (e ,ˣ dl) → refl })

  nf-bottom : NF 0 ↔ Bool
  nf-bottom = mk↔ₛ′ (λ { (nf₀ s) → s }) nf₀ (λ _ → refl) (λ { (nf₀ s) → refl })

  nf-split : NF (₁₊ m) ↔ ((Zc (₁₊ m) × Xc (₁₊ m)) × NF m)
  nf-split = mk↔ₛ′ (λ { (nfₛ L M N) → (L , M) , N }) (λ { ((L , M) , N) → nfₛ L M N })
                   (λ { ((L , M) , N) → refl }) (λ { (nfₛ L M N) → refl })

DL≅ : (m : ℕ) → DL (₁₊ m) ≅ 4 ^ m
DL≅ zero    = ↔-trans dl-bottom (↔-sym 1↔⊤)
DL≅ (suc m) = ↔-trans dl-split (×≅ DT≅ (DL≅ m))

Xc≅ : (m : ℕ) → Xc (₁₊ m) ≅ 2 * 4 ^ m
Xc≅ m = ↔-trans xc-split (×≅ ET≅ (DL≅ m))

nf : ℕ → ℕ
nf zero    = 2
nf (suc m) = (zc m * (2 * 4 ^ m)) * nf m

NF≅ : (n : ℕ) → NF n ≅ nf n
NF≅ zero    = ↔-trans nf-bottom Bool≅
NF≅ (suc m) = ↔-trans nf-split (×≅ (×≅ (Zc≅ m) (Xc≅ m)) (NF≅ m))

------------------------------------------------------------------------
-- The count in closed form

-- The order of the real Clifford group on n qubits, as Corollary 4.16
-- has it: 2 · ∏ᵢ₌₁ⁿ (4ⁱ + 2ⁱ − 2)(2 · 4ⁱ⁻¹).
order : ℕ → ℕ
order zero    = 2
order (suc n) = order n * ((4 ^ suc n + 2 ^ suc n ∸ 2) * (2 * 4 ^ n))

_ : order 1 ≡ 16
_ = refl

_ : order 2 ≡ 2304
_ = refl

private
  open +-*-Solver

  lad-sg : (m : ℕ) → lad sg m ≡ 4 ^ m + 2 ^ m
  lad-db : (m : ℕ) → lad db m + 2 ^ m ≡ 4 ^ m

  lad-sg zero    = refl
  lad-sg (suc m) = begin
    3 * lad sg m + 1 * lad db m                    ≡⟨ Eq.cong (λ x → 3 * x + 1 * lad db m) (lad-sg m) ⟩
    3 * (F + T) + 1 * lad db m                     ≡⟨ solve 3 (λ F T L → con 3 :* (F :+ T) :+ con 1 :* L
                                                              := (con 3 :* F :+ con 2 :* T) :+ (L :+ T))
                                                        refl F T (lad db m) ⟩
    (3 * F + 2 * T) + (lad db m + T)               ≡⟨ Eq.cong ((3 * F + 2 * T) +_) (lad-db m) ⟩
    (3 * F + 2 * T) + F                            ≡⟨ solve 2 (λ F T → (con 3 :* F :+ con 2 :* T) :+ F
                                                              := con 4 :* F :+ con 2 :* T) refl F T ⟩
    4 * F + 2 * T                                  ∎
    where
    open Eq.≡-Reasoning
    F = 4 ^ m
    T = 2 ^ m

  lad-db zero    = refl
  lad-db (suc m) = begin
    (1 * lad sg m + 3 * lad db m) + 2 * T           ≡⟨ Eq.cong (λ x → (1 * x + 3 * lad db m) + 2 * T) (lad-sg m) ⟩
    (1 * (F + T) + 3 * lad db m) + 2 * T            ≡⟨ solve 3 (λ F T L → (con 1 :* (F :+ T) :+ con 3 :* L) :+ con 2 :* T
                                                               := F :+ con 3 :* (L :+ T))
                                                         refl F T (lad db m) ⟩
    F + 3 * (lad db m + T)                          ≡⟨ Eq.cong (λ x → F + 3 * x) (lad-db m) ⟩
    F + 3 * F                                       ≡⟨ solve 1 (λ F → F :+ con 3 :* F := con 4 :* F) refl F ⟩
    4 * F                                           ∎
    where
    open Eq.≡-Reasoning
    F = 4 ^ m
    T = 2 ^ m

  zc-closed : (m : ℕ) → zc m + 2 ≡ 4 ^ suc m + 2 ^ suc m
  zc-closed zero    = refl
  zc-closed (suc m) = begin
    (zc m + (2 * lad sg (suc m) + 1 * lad db (suc m))) + 2
      ≡⟨ solve 3 (λ Z S D → (Z :+ (con 2 :* S :+ con 1 :* D)) :+ con 2
                          := (Z :+ con 2) :+ (con 2 :* S :+ D)) refl (zc m) (lad sg (suc m)) (lad db (suc m)) ⟩
    (zc m + 2) + (2 * lad sg (suc m) + lad db (suc m))
      ≡⟨ Eq.cong₂ (λ x y → x + (2 * y + lad db (suc m))) (zc-closed m) (lad-sg (suc m)) ⟩
    (F + T) + (2 * (F + T) + lad db (suc m))
      ≡⟨ solve 3 (λ F T D → (F :+ T) :+ (con 2 :* (F :+ T) :+ D)
                          := (con 3 :* F :+ con 2 :* T) :+ (D :+ T)) refl F T (lad db (suc m)) ⟩
    (3 * F + 2 * T) + (lad db (suc m) + T)
      ≡⟨ Eq.cong ((3 * F + 2 * T) +_) (lad-db (suc m)) ⟩
    (3 * F + 2 * T) + F
      ≡⟨ solve 2 (λ F T → (con 3 :* F :+ con 2 :* T) :+ F := con 4 :* F :+ con 2 :* T) refl F T ⟩
    4 * F + 2 * T
      ∎
    where
    open Eq.≡-Reasoning
    F = 4 ^ suc m
    T = 2 ^ suc m

-- There are 4ⁱ + 2ⁱ − 2 Z-circuits on i wires.
zc≡ : (m : ℕ) → zc m ≡ 4 ^ suc m + 2 ^ suc m ∸ 2
zc≡ m = Eq.trans (Eq.sym (ℕP.m+n∸n≡m (zc m) 2)) (Eq.cong (_∸ 2) (zc-closed m))

nf≡order : (n : ℕ) → nf n ≡ order n
nf≡order zero    = refl
nf≡order (suc m) = Eq.trans (ℕP.*-comm (zc m * (2 * 4 ^ m)) (nf m))
  (Eq.cong₂ _*_ (nf≡order m) (Eq.cong (_* (2 * 4 ^ m)) (zc≡ m)))

-- Corollary 4.16, counting normal forms.
NF≅order : (n : ℕ) → NF n ≅ order n
NF≅order n = Eq.subst (NF n ≅_) (nf≡order n) (NF≅ n)
