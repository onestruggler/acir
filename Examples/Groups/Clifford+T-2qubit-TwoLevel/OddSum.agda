------------------------------------------------------------------------
-- Presentations of groups
--
-- In dimension at most 4, the four exponents a, b, c, d of the hard
-- subcase have an even sum.  After H_[j,α] and H_[β,ℓ′], the column is
-- δ times the numerator
--
--   (λω (g₃ + a + b), λω (a - b), λω (g₃ + c + d), λω (c - d))
--
-- of a unit vector at the exponent k - 1: in dimension 4 these are all
-- its entries.  For an odd sum, their residues modulo δ² are 0, 1, δ
-- and 1 + δ, so that three are nonzero and Σ Bₓ is odd.  But Σ Aₓ is
-- P_(k-1) ≤ 2 for k - 1 ≤ 1, and Q_(k-1) is even beyond.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.OddSum where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; _xor_ ; if_then_else_ ; T)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_] ; ∣_∣)
import Data.Integer.Properties as ℤP
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; ≢-sym)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import Quantum.Synthesis.Ring using (Omega)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale using (λωᶻ ; sc ; sc-δ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue
  using (P4 ; pa ; pb ; pc ; pd ; _⊕_ ; _⊗_ ; oddP ; par ; par-+ ; par-- ; par-* ; oddP-par ;
         allB ; allB-sound ; g3)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde using (_!_ ; scV ; scV-!)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Norm using (sq ; NA ; NB ; Σℕ ; Σℤ ; P ; Q ; unit-norm ; unit-normB)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics hiding (_!_ ; U)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.FourOdd as FourOdd

------------------------------------------------------------------------
-- Sums over four indices

private
  pick : ∀ {A : Set} {B : Set} → Dec B → A → A → A
  pick (yes _) z _ = z
  pick (no _) _ y = y

  pick-0 : ∀ {A B : Set} {z y : A} (d : Dec B) → (¬ B → y ≡ z) → pick d z y ≡ z
  pick-0 (yes _) _ = ≡.refl
  pick-0 (no ¬b) h = h ¬b

  pick-no : ∀ {A B : Set} {z y : A} (d : Dec B) → ¬ B → pick d z y ≡ y
  pick-no (yes b) ¬b = ⊥-elim (¬b b)
  pick-no (no _) _ = ≡.refl

module SumOver {A : Set} (_∙_ : A → A → A) (0# : A) (Σ : ∀ {m} → (Fin m → A) → A)
               (Σ-zero : (f : Fin 0 → A) → Σ f ≡ 0#)
               (Σ-suc : ∀ {m} (f : Fin (suc m) → A) → Σ f ≡ f zero ∙ Σ (f ∘ suc))
               (+-idˡ : ∀ x → 0# ∙ x ≡ x) (+-idʳ : ∀ x → x ∙ 0# ≡ x)
               (+-swap : ∀ x y z → x ∙ (y ∙ z) ≡ y ∙ (x ∙ z)) where

  Σ-cong : ∀ {m} {f g : Fin m → A} → (∀ x → f x ≡ g x) → Σ f ≡ Σ g
  Σ-cong {zero} {f} {g} _ = ≡.trans (Σ-zero f) (≡.sym (Σ-zero g))
  Σ-cong {suc m} {f} {g} eq =
    ≡.trans (Σ-suc f) (≡.trans (≡.cong₂ _∙_ (eq zero) (Σ-cong (eq ∘ suc))) (≡.sym (Σ-suc g)))

  Σ-0 : ∀ {m} (f : Fin m → A) → (∀ x → f x ≡ 0#) → Σ f ≡ 0#
  Σ-0 {zero} f _ = Σ-zero f
  Σ-0 {suc m} f z = ≡.trans (Σ-suc f) (≡.trans (≡.cong₂ _∙_ (z zero) (Σ-0 (f ∘ suc) (z ∘ suc))) (+-idˡ 0#))

  -- Σ f = f a ∙ Σ g, when g vanishes at a and agrees with f elsewhere.
  Σ-drop : ∀ {m} (f g : Fin m → A) (a : Fin m) → g a ≡ 0# → (∀ x → x ≢ a → f x ≡ g x) → Σ f ≡ f a ∙ Σ g
  Σ-drop {suc m} f g zero ga eq =
    ≡.trans (Σ-suc f)
      (≡.cong (f zero ∙_)
        (≡.trans (Σ-cong (λ x → eq (suc x) (λ ())))
          (≡.trans (≡.sym (+-idˡ _)) (≡.trans (≡.cong (_∙ Σ (g ∘ suc)) (≡.sym ga)) (≡.sym (Σ-suc g))))))
  Σ-drop {suc m} f g (suc a) ga eq =
    ≡.trans (Σ-suc f)
      (≡.trans (≡.cong (f zero ∙_) (Σ-drop (f ∘ suc) (g ∘ suc) a ga (λ x x≢a → eq (suc x) (x≢a ∘ FinP.suc-injective))))
        (≡.trans (+-swap (f zero) (f (suc a)) (Σ (g ∘ suc)))
          (≡.cong (f (suc a) ∙_) (≡.trans (≡.cong (_∙ Σ (g ∘ suc)) (eq zero (λ ()))) (≡.sym (Σ-suc g))))))

  private
    zeroAt : ∀ {m} → Fin m → (Fin m → A) → Fin m → A
    zeroAt a f x = pick (x FinP.≟ a) 0# (f x)

    drop : ∀ {m} (f : Fin m → A) (a : Fin m) → Σ f ≡ f a ∙ Σ (zeroAt a f)
    drop f a = Σ-drop f (zeroAt a f) a (pick-0 (a FinP.≟ a) (λ ¬e → ⊥-elim (¬e ≡.refl)))
                      (λ x x≢a → ≡.sym (pick-no (x FinP.≟ a) x≢a))

  -- A function vanishing beyond four distinct indices.
  Σ-four : ∀ {m} (f : Fin m → A) {a b c d : Fin m} → a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
           (∀ x → x ≢ a → x ≢ b → x ≢ c → x ≢ d → f x ≡ 0#) → Σ f ≡ f a ∙ (f b ∙ (f c ∙ f d))
  Σ-four f {a} {b} {c} {d} a≢b a≢c a≢d b≢c b≢d c≢d h =
    ≡.trans (drop f a)
      (≡.cong (f a ∙_) (≡.trans (drop f₁ b)
        (≡.cong₂ _∙_ (pick-no (b FinP.≟ a) (≢-sym a≢b)) (≡.trans (drop f₂ c)
          (≡.cong₂ _∙_ (≡.trans (pick-no (c FinP.≟ b) (≢-sym b≢c)) (pick-no (c FinP.≟ a) (≢-sym a≢c)))
            (≡.trans (drop f₃ d)
              (≡.trans (≡.cong (f₃ d ∙_) (Σ-0 f₄ z₄))
                (≡.trans (+-idʳ (f₃ d))
                  (≡.trans (pick-no (d FinP.≟ c) (≢-sym c≢d))
                    (≡.trans (pick-no (d FinP.≟ b) (≢-sym b≢d)) (pick-no (d FinP.≟ a) (≢-sym a≢d))))))))))))
    where
    f₁ = zeroAt a f
    f₂ = zeroAt b f₁
    f₃ = zeroAt c f₂
    f₄ = zeroAt d f₃
    z₄ : ∀ x → f₄ x ≡ 0#
    z₄ x = pick-0 (x FinP.≟ d) λ x≢d → pick-0 (x FinP.≟ c) λ x≢c → pick-0 (x FinP.≟ b) λ x≢b →
             pick-0 (x FinP.≟ a) λ x≢a → h x x≢a x≢b x≢c x≢d

private
  swapℕ : ∀ x y z → x ℕ.+ (y ℕ.+ z) ≡ y ℕ.+ (x ℕ.+ z)
  swapℕ x y z = ≡.trans (≡.sym (ℕP.+-assoc x y z)) (≡.trans (≡.cong (ℕ._+ z) (ℕP.+-comm x y)) (ℕP.+-assoc y x z))

  swapℤ : ∀ x y z → x ℤ.+ (y ℤ.+ z) ≡ y ℤ.+ (x ℤ.+ z)
  swapℤ x y z = ≡.trans (≡.sym (ℤP.+-assoc x y z)) (≡.trans (≡.cong (ℤ._+ z) (ℤP.+-comm x y)) (ℤP.+-assoc y x z))

module SN = SumOver ℕ._+_ 0 Σℕ (λ _ → ≡.refl) (λ _ → ≡.refl) (λ _ → ≡.refl) ℕP.+-identityʳ swapℕ
module SZ = SumOver ℤ._+_ (+ 0) Σℤ (λ _ → ≡.refl) (λ _ → ≡.refl) ℤP.+-identityˡ ℤP.+-identityʳ swapℤ

------------------------------------------------------------------------
-- Parities of the norm coordinates

ind : Bool → ℕ
ind b = if b then 1 else 0

-- Not ≡ 0 modulo 2, and the parity of B.
nz nbP : P4 → Bool
nz Y = pa Y ∨ pb Y ∨ pc Y ∨ pd Y
nbP Y = (pa Y xor pc Y) ∧ (pb Y xor pd Y)

private
  ind≤1 : ∀ b → ind b ℕ.≤ 1
  ind≤1 true = ℕP.≤-refl
  ind≤1 false = z≤n

  ind-odd : ∀ a → ind (oddℤ a) ℕ.≤ sq a
  ind-odd (+ zero) = z≤n
  ind-odd (+ suc m) = ℕP.≤-trans (ind≤1 _) (s≤s z≤n)
  ind-odd -[1+ m ] = ℕP.≤-trans (ind≤1 _) (s≤s z≤n)

  ind-∨ : ∀ p q → ind (p ∨ q) ℕ.≤ ind p ℕ.+ ind q
  ind-∨ true q = s≤s z≤n
  ind-∨ false q = ℕP.≤-refl

  nb-bool : ∀ a b c d → (((a ∧ b) xor (b ∧ c)) xor (c ∧ d)) xor (a ∧ d) ≡ (a xor c) ∧ (b xor d)
  nb-bool false false false false = ≡.refl
  nb-bool false false false true = ≡.refl
  nb-bool false false true false = ≡.refl
  nb-bool false false true true = ≡.refl
  nb-bool false true false false = ≡.refl
  nb-bool false true false true = ≡.refl
  nb-bool false true true false = ≡.refl
  nb-bool false true true true = ≡.refl
  nb-bool true false false false = ≡.refl
  nb-bool true false false true = ≡.refl
  nb-bool true false true false = ≡.refl
  nb-bool true false true true = ≡.refl
  nb-bool true true false false = ≡.refl
  nb-bool true true false true = ≡.refl
  nb-bool true true true false = ≡.refl
  nb-bool true true true true = ≡.refl

-- A ≥ 1 away from 0 modulo 2.
ind-NA : ∀ x → ind (nz (par x)) ℕ.≤ NA x
ind-NA (Omega a b c d) =
  ℕP.≤-trans (ind-∨ (oddℤ a) _)
    (ℕP.+-mono-≤ (ind-odd a)
      (ℕP.≤-trans (ind-∨ (oddℤ b) _)
        (ℕP.+-mono-≤ (ind-odd b)
          (ℕP.≤-trans (ind-∨ (oddℤ c) _)
            (ℕP.+-mono-≤ (ind-odd c) (ℕP.≤-trans (ind-odd d) (ℕP.m≤m+n _ 0)))))))

oddℤ-NB : ∀ x → oddℤ (NB x) ≡ nbP (par x)
oddℤ-NB (Omega a b c d) =
  ≡.trans (oddℤ-+ (a ℤ.* b ℤ.+ b ℤ.* c ℤ.+ c ℤ.* d) (ℤ.- (a ℤ.* d)))
    (≡.trans (≡.cong₂ _xor_
               (≡.trans (oddℤ-+ (a ℤ.* b ℤ.+ b ℤ.* c) (c ℤ.* d))
                 (≡.cong₂ _xor_ (≡.trans (oddℤ-+ (a ℤ.* b) (b ℤ.* c)) (≡.cong₂ _xor_ (oddℤ-* a b) (oddℤ-* b c)))
                                (oddℤ-* c d)))
               (≡.trans (oddℤ-neg (a ℤ.* d)) (oddℤ-* a d)))
      (nb-bool (oddℤ a) (oddℤ b) (oddℤ c) (oddℤ d)))

------------------------------------------------------------------------
-- The residues, by exhaustion

private
  imp : Bool → Bool → Bool
  imp p q = not p ∨ q

  imp-sound : ∀ {p q} → imp p q ≡ true → p ≡ true → q ≡ true
  imp-sound {true} h _ = h

  ∧-l : ∀ {p q} → p ∧ q ≡ true → p ≡ true
  ∧-l {true} _ = ≡.refl

  ∧-r : ∀ {p q} → p ∧ q ≡ true → q ≡ true
  ∧-r {true} h = h

  Λ G : P4
  Λ = par λωᶻ
  G = par g3

  -- The four entries, by the parities X of a - b and Y of c - d.
  three : P4 → P4 → Bool
  three X Y = 3 ℕ.≤ᵇ (ind (nz (Λ ⊗ (G ⊕ X))) ℕ.+ (ind (nz (Λ ⊗ X)) ℕ.+ (ind (nz (Λ ⊗ (G ⊕ Y))) ℕ.+ ind (nz (Λ ⊗ Y)))))

  nbodd : P4 → P4 → Bool
  nbodd X Y = nbP (Λ ⊗ (G ⊕ X)) xor (nbP (Λ ⊗ X) xor (nbP (Λ ⊗ (G ⊕ Y)) xor nbP (Λ ⊗ Y)))

  mkP : Bool → Bool → Bool → Bool → P4
  mkP a b c d = record { pa = a ; pb = b ; pc = c ; pd = d }

  test : Vec Bool 8 → Bool
  test (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ []) =
    imp (oddP (mkP x₁ x₂ x₃ x₄ ⊕ mkP y₁ y₂ y₃ y₄)) (three (mkP x₁ x₂ x₃ x₄) (mkP y₁ y₂ y₃ y₄) ∧ nbodd (mkP x₁ x₂ x₃ x₄) (mkP y₁ y₂ y₃ y₄))

  check : allB 8 test ≡ true
  check = ≡.refl

  residues : ∀ X Y → oddP (X ⊕ Y) ≡ true → three X Y ≡ true × nbodd X Y ≡ true
  residues X Y o = ∧-l h , ∧-r h
    where
    h = imp-sound (allB-sound 8 test check (pa X ∷ pb X ∷ pc X ∷ pd X ∷ pa Y ∷ pb Y ∷ pc Y ∷ pd Y ∷ [])) o

------------------------------------------------------------------------
-- The sum

private
  ¬5≤4 : ¬ (5 ℕ.≤ 4)
  ¬5≤4 (s≤s (s≤s (s≤s (s≤s ()))))

  -- Q_(k+2) is even.
  Q-even : ∀ k → oddℤ (Q (suc (suc k))) ≡ false
  Q-even k = ≡.trans (oddℤ-+ (P (suc k)) (+ 2 ℤ.* Q (suc k)))
               (≡.cong₂ _xor_ (oddℤ-* (+ 2) (P k ℤ.+ Q k)) (oddℤ-* (+ 2) (Q (suc k))))

  to-T : ∀ {b} → b ≡ true → T b
  to-T ≡.refl = tt

module _ {n : ℕ} (n≤4 : n ℕ.≤ 4) {j α β ℓ′ : Fin n} (jα : j < α) (αβ : α < β) (βℓ′ : β < ℓ′) (W : Vec Z n) where

  open FourOdd.Four {n} jα αβ βℓ′ W using (Nv ; Nv-j ; Nv-α ; Nv-β ; Nv-ℓ′ ; Nv-ext ; jβ ; αℓ′ ; jℓ′)
  open FourOdd {n} using (y₁ ; y₂)

  private
    -- No fifth index.
    five : ∀ {a b c d e : Fin n} → a < b → b < c → c < d → d < e → ⊥
    five {e = e} ab bc cd de = ¬5≤4 (ℕP.≤-trans (s≤s e4) (ℕP.≤-trans (FinP.toℕ<n e) n≤4))
      where
      step : ∀ {m} {x y : Fin n} → m ℕ.≤ toℕ x → x < y → suc m ℕ.≤ toℕ y
      step h xy = ℕP.≤-trans (s≤s h) xy
      e4 : 4 ℕ.≤ toℕ e
      e4 = step (step (step (step z≤n ab) bc) cd) de

    others : ∀ x → x ≢ j → x ≢ α → x ≢ β → x ≢ ℓ′ → ⊥
    others x x≢j x≢α x≢β x≢ℓ′ = c₁ (FinP.<-cmp x j)
      where
      c₄ : Tri (x < ℓ′) (x ≡ ℓ′) (ℓ′ < x) → β < x → ⊥
      c₄ (tri< xℓ′ _ _) βx = five jα αβ βx xℓ′
      c₄ (tri≈ _ e _) _ = x≢ℓ′ e
      c₄ (tri> _ _ ℓ′x) _ = five jα αβ βℓ′ ℓ′x
      c₃ : Tri (x < β) (x ≡ β) (β < x) → α < x → ⊥
      c₃ (tri< xβ _ _) αx = five jα αx xβ βℓ′
      c₃ (tri≈ _ e _) _ = x≢β e
      c₃ (tri> _ _ βx) _ = c₄ (FinP.<-cmp x ℓ′) βx
      c₂ : Tri (x < α) (x ≡ α) (α < x) → j < x → ⊥
      c₂ (tri< xα _ _) jx = five jx xα αβ βℓ′
      c₂ (tri≈ _ e _) _ = x≢α e
      c₂ (tri> _ _ αx) _ = c₃ (FinP.<-cmp x β) αx
      c₁ : Tri (x < j) (x ≡ j) (j < x) → ⊥
      c₁ (tri< xj _ _) = five xj jα αβ βℓ′
      c₁ (tri≈ _ e _) = x≢j e
      c₁ (tri> _ _ jx) = c₂ (FinP.<-cmp x α) jx

    j≢α = FinP.<⇒≢ jα
    j≢β = FinP.<⇒≢ jβ
    j≢ℓ′ = FinP.<⇒≢ jℓ′
    α≢β = FinP.<⇒≢ αβ
    α≢ℓ′ = FinP.<⇒≢ αℓ′
    β≢ℓ′ = FinP.<⇒≢ βℓ′

    scV-δmap : ∀ k (U : Vec Z n) → scV (suc k) (Vec.map (δᶻ ZR.*_) U) ≡ scV k U
    scV-δmap k U = vec-ext λ x →
      ≡.trans (scV-! (suc k) (Vec.map (δᶻ ZR.*_) U) x)
        (≡.trans (≡.cong (sc (suc k)) (VecP.lookup-map x (δᶻ ZR.*_) U))
          (≡.trans (sc-δ k (U ! x)) (≡.sym (scV-! k U x))))

  -- The state after H_[j,α] and H_[β,ℓ′] has a + b + c + d even.
  even-sum : ∀ K′ (a b c d : Z) (u : Vec D n) → ⟨ u , u ⟩ ≡ DR.1# →
             u ≡ scV (suc K′) (Nv (y₁ a b) (y₂ a b) (y₁ c d) (y₂ c d)) →
             oddᶻ ((a ZR.+ b) ZR.+ (c ZR.+ d)) ≡ false
  even-sum K′ a b c d u unit eq = by (oddᶻ ((a ZR.+ b) ZR.+ (c ZR.+ d))) ≡.refl
    where
    x₁ = λωᶻ ZR.* (g3 ZR.+ (a ZR.+ b))
    x₂ = λωᶻ ZR.* (a ZR.- b)
    x₃ = λωᶻ ZR.* (g3 ZR.+ (c ZR.+ d))
    x₄ = λωᶻ ZR.* (c ZR.- d)
    N = Nv x₁ x₂ x₃ x₄
    X = par a ⊕ par b
    Y = par c ⊕ par d

    δN : Vec.map (δᶻ ZR.*_) N ≡ Nv (δᶻ ZR.* x₁) (δᶻ ZR.* x₂) (δᶻ ZR.* x₃) (δᶻ ZR.* x₄)
    δN = Nv-ext (Vec.map (δᶻ ZR.*_) N)
      (≡.trans (VecP.lookup-map j (δᶻ ZR.*_) N) (≡.cong (δᶻ ZR.*_) (Nv-j x₁ x₂ x₃ x₄)))
      (≡.trans (VecP.lookup-map α (δᶻ ZR.*_) N) (≡.cong (δᶻ ZR.*_) (Nv-α x₁ x₂ x₃ x₄)))
      (≡.trans (VecP.lookup-map β (δᶻ ZR.*_) N) (≡.cong (δᶻ ZR.*_) (Nv-β x₁ x₂ x₃ x₄)))
      (≡.trans (VecP.lookup-map ℓ′ (δᶻ ZR.*_) N) (≡.cong (δᶻ ZR.*_) (Nv-ℓ′ x₁ x₂ x₃ x₄)))
      (λ x a′ b′ c′ d′ → ⊥-elim (others x a′ b′ c′ d′))

    u≡ : u ≡ scV K′ N
    u≡ = ≡.trans eq (≡.trans (≡.cong (scV (suc K′)) (≡.sym δN)) (scV-δmap K′ N))

    unit′ : ⟨ scV K′ N , scV K′ N ⟩ ≡ DR.1#
    unit′ = ≡.subst (λ w → ⟨ w , w ⟩ ≡ DR.1#) u≡ unit

    -- The sums over the four entries.
    ΣA : Σℕ (λ x → NA (N ! x)) ≡ NA x₁ ℕ.+ (NA x₂ ℕ.+ (NA x₃ ℕ.+ NA x₄))
    ΣA = ≡.trans (SN.Σ-four (λ x → NA (N ! x)) j≢α j≢β j≢ℓ′ α≢β α≢ℓ′ β≢ℓ′
                   (λ x a′ b′ c′ d′ → ⊥-elim (others x a′ b′ c′ d′)))
           (≡.cong₂ ℕ._+_ (≡.cong NA (Nv-j x₁ x₂ x₃ x₄))
             (≡.cong₂ ℕ._+_ (≡.cong NA (Nv-α x₁ x₂ x₃ x₄))
               (≡.cong₂ ℕ._+_ (≡.cong NA (Nv-β x₁ x₂ x₃ x₄)) (≡.cong NA (Nv-ℓ′ x₁ x₂ x₃ x₄)))))

    ΣB : Σℤ (λ x → NB (N ! x)) ≡ NB x₁ ℤ.+ (NB x₂ ℤ.+ (NB x₃ ℤ.+ NB x₄))
    ΣB = ≡.trans (SZ.Σ-four (λ x → NB (N ! x)) j≢α j≢β j≢ℓ′ α≢β α≢ℓ′ β≢ℓ′
                   (λ x a′ b′ c′ d′ → ⊥-elim (others x a′ b′ c′ d′)))
           (≡.cong₂ ℤ._+_ (≡.cong NB (Nv-j x₁ x₂ x₃ x₄))
             (≡.cong₂ ℤ._+_ (≡.cong NB (Nv-α x₁ x₂ x₃ x₄))
               (≡.cong₂ ℤ._+_ (≡.cong NB (Nv-β x₁ x₂ x₃ x₄)) (≡.cong NB (Nv-ℓ′ x₁ x₂ x₃ x₄)))))

    -- The parities of the entries.
    p₁ : par x₁ ≡ Λ ⊗ (G ⊕ X)
    p₁ = ≡.trans (par-* λωᶻ (g3 ZR.+ (a ZR.+ b))) (≡.cong (Λ ⊗_) (≡.trans (par-+ g3 (a ZR.+ b)) (≡.cong (G ⊕_) (par-+ a b))))
    p₂ : par x₂ ≡ Λ ⊗ X
    p₂ = ≡.trans (par-* λωᶻ (a ZR.- b)) (≡.cong (Λ ⊗_) (par-- a b))
    p₃ : par x₃ ≡ Λ ⊗ (G ⊕ Y)
    p₃ = ≡.trans (par-* λωᶻ (g3 ZR.+ (c ZR.+ d))) (≡.cong (Λ ⊗_) (≡.trans (par-+ g3 (c ZR.+ d)) (≡.cong (G ⊕_) (par-+ c d))))
    p₄ : par x₄ ≡ Λ ⊗ Y
    p₄ = ≡.trans (par-* λωᶻ (c ZR.- d)) (≡.cong (Λ ⊗_) (par-- c d))

    by : (b′ : Bool) → oddᶻ ((a ZR.+ b) ZR.+ (c ZR.+ d)) ≡ b′ → oddᶻ ((a ZR.+ b) ZR.+ (c ZR.+ d)) ≡ false
    by false e = e
    by true e = ⊥-elim (by-k K′ ≡.refl)
      where
      oXY : oddP (X ⊕ Y) ≡ true
      oXY = ≡.trans (≡.cong oddP (≡.sym (≡.trans (par-+ (a ZR.+ b) (c ZR.+ d)) (≡.cong₂ _⊕_ (par-+ a b) (par-+ c d)))))
                    (≡.trans (oddP-par ((a ZR.+ b) ZR.+ (c ZR.+ d))) e)
      res = residues X Y oXY
      -- Three entries are nonzero.
      three≤ : 3 ℕ.≤ NA x₁ ℕ.+ (NA x₂ ℕ.+ (NA x₃ ℕ.+ NA x₄))
      three≤ = ℕP.≤-trans (ℕP.≤ᵇ⇒≤ 3 S (to-T (≡.trans (≡.cong (3 ℕ.≤ᵇ_) sums) (proj₁′ res))))
                 (ℕP.+-mono-≤ (ind-NA x₁) (ℕP.+-mono-≤ (ind-NA x₂) (ℕP.+-mono-≤ (ind-NA x₃) (ind-NA x₄))))
        where
        proj₁′ : ∀ {A B : Set} → A × B → A
        proj₁′ (x , _) = x
        S = ind (nz (par x₁)) ℕ.+ (ind (nz (par x₂)) ℕ.+ (ind (nz (par x₃)) ℕ.+ ind (nz (par x₄))))
        sums : ind (nz (par x₁)) ℕ.+ (ind (nz (par x₂)) ℕ.+ (ind (nz (par x₃)) ℕ.+ ind (nz (par x₄)))) ≡
               ind (nz (Λ ⊗ (G ⊕ X))) ℕ.+ (ind (nz (Λ ⊗ X)) ℕ.+ (ind (nz (Λ ⊗ (G ⊕ Y))) ℕ.+ ind (nz (Λ ⊗ Y))))
        sums = ≡.cong₂ ℕ._+_ (≡.cong (ind ∘ nz) p₁)
                 (≡.cong₂ ℕ._+_ (≡.cong (ind ∘ nz) p₂) (≡.cong₂ ℕ._+_ (≡.cong (ind ∘ nz) p₃) (≡.cong (ind ∘ nz) p₄)))
      -- Σ B is odd.
      oddB : oddℤ (Σℤ (λ x → NB (N ! x))) ≡ true
      oddB = ≡.trans (≡.cong oddℤ ΣB)
               (≡.trans (oddℤ-+ (NB x₁) (NB x₂ ℤ.+ (NB x₃ ℤ.+ NB x₄)))
                 (≡.trans (≡.cong (oddℤ (NB x₁) xor_) (oddℤ-+ (NB x₂) (NB x₃ ℤ.+ NB x₄)))
                   (≡.trans (≡.cong (λ t → oddℤ (NB x₁) xor (oddℤ (NB x₂) xor t)) (oddℤ-+ (NB x₃) (NB x₄)))
                     (≡.trans (≡.cong₂ (λ s t → s xor t) (≡.trans (oddℤ-NB x₁) (≡.cong nbP p₁))
                                (≡.cong₂ _xor_ (≡.trans (oddℤ-NB x₂) (≡.cong nbP p₂))
                                  (≡.cong₂ _xor_ (≡.trans (oddℤ-NB x₃) (≡.cong nbP p₃))
                                                 (≡.trans (oddℤ-NB x₄) (≡.cong nbP p₄)))))
                              (proj₂′ res)))))
        where
        proj₂′ : ∀ {A B : Set} → A × B → B
        proj₂′ (_ , y) = y
      ΣA≡ : + (NA x₁ ℕ.+ (NA x₂ ℕ.+ (NA x₃ ℕ.+ NA x₄))) ≡ P K′
      ΣA≡ = ≡.trans (≡.cong +_ (≡.sym ΣA)) (unit-norm K′ N unit′)
      by-k : ∀ k → K′ ≡ k → ⊥
      by-k zero ≡.refl = ¬3≤1 (≡.subst (3 ℕ.≤_) (≡.cong ∣_∣ ΣA≡) three≤)
        where
        ¬3≤1 : ¬ (3 ℕ.≤ 1)
        ¬3≤1 (s≤s ())
      by-k (suc zero) ≡.refl = ¬3≤2 (≡.subst (3 ℕ.≤_) (≡.cong ∣_∣ ΣA≡) three≤)
        where
        ¬3≤2 : ¬ (3 ℕ.≤ 2)
        ¬3≤2 (s≤s (s≤s ()))
      by-k (suc (suc k)) ≡.refl = t≢f (≡.trans (≡.sym oddB) (≡.trans (≡.cong oddℤ (unit-normB K′ N unit′)) (Q-even k)))
        where
        t≢f : true ≢ false
        t≢f ()
