------------------------------------------------------------------------
-- Presentations of groups
--
-- Diagonal operators
--
-- DS w φ says that w keeps every basis state and multiplies |x⟩ by
-- ω^(φ x).  Diagonal operators compose by adding phases (DS-•), and
-- the phase of a shifted or swapped one is read off the wires it acts
-- on.  The phase gate P ℓ is diagonal with phase the parity ℓ·x
-- (DS-P): r ℓ writes the parity on wire 0, T reads it, and the
-- inverse of r ℓ undoes the state, linear circuits carrying no phase.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.Semantics where

open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _xor_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.CNOT+Dihedral.Semantics
open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Interpretation
open import Examples.Groups.CNOT+Dihedral.Soundness using (sound)
open import Examples.Groups.CNOT+Dihedral.Evaluation
open import Examples.Groups.CNOT+Dihedral.Linear.Local using (CX01)
open import Examples.Groups.CNOT+Dihedral.Linear.Base using (NZ ; e₀ ; cx ; sw ; r)
open import Examples.Groups.CNOT+Dihedral.Linear.Semantics using (dot ; r-head ; fn-CX01)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Phase using (P)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Calculus

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Diagonal operators

DS : Circuit n → (Bits n → ℤ₈) → Set
DS {n} w φ = (x : Bits n) → ⟦ w ⟧ x ≡ (x , φ x)

DS-≈ : ∀ {w v : Circuit n} {φ} → n ⊢ w ≈ v → DS v φ → DS w φ
DS-≈ e d x = Eq.trans (sound e x) (d x)

DS-ε : DS {n} ε (λ _ → 0₈)
DS-ε x = ⟦⟧-ε x

DS-• : ∀ {a b : Circuit n} {φ ψ} → DS a φ → DS b ψ → DS (a • b) (λ x → ψ x + φ x)
DS-• {a = a} {b} {φ} {ψ} da db x =
  Eq.trans (⟦⟧-• a b x)
    (Eq.trans (Eq.cong (λ p → proj₁ (⟦ a ⟧ (proj₁ p)) , proj₂ p + proj₂ (⟦ a ⟧ (proj₁ p))) (db x))
              (Eq.cong (λ p → proj₁ p , ψ x + proj₂ p) (da x)))

-- The phase of a power.
powφ : ℕ → (Bits n → ℤ₈) → Bits n → ℤ₈
powφ zero          φ x = 0₈
powφ (suc zero)    φ x = φ x
powφ (suc (suc k)) φ x = powφ (suc k) φ x + φ x

DS-^ : ∀ {a : Circuit n} {φ} → DS a φ → (k : ℕ) → DS (a ^ k) (powφ k φ)
DS-^ d zero          = DS-ε
DS-^ d (suc zero)    = d
DS-^ d (suc (suc k)) = DS-• d (DS-^ d (suc k))

DS-↑ : ∀ {a : Circuit n} {φ} → DS a φ → DS (a ↑) (λ v → φ (tail v))
DS-↑ {a = a} {φ} d (b ∷ x) =
  Eq.trans (up-word a (b ∷ x)) (Eq.cong (λ p → b ∷ proj₁ p , proj₂ p) (d x))

DS-ω : DS {n} ω (λ _ → 1₈)
DS-ω x = ⟦⟧-gen ω-gen x

DS-T : DS {₁₊ n} T (λ v → if head v then 1₈ else 0₈)
DS-T (b ∷ x) = ⟦⟧-gen T-gen (b ∷ x)

------------------------------------------------------------------------
-- Diagonal operators conjugated by swaps

DS-swap : ∀ {X : Circuit (₁₊ n)} {φ} → DS X φ →
          DS (SWAP • X ↑ • SWAP) (λ v → φ (head v ∷ tail (tail v)))
DS-swap {X = X} {φ} d (a ∷ b ∷ y) = Eq.cong₂ _,_ fn-eq ph-eq
  where
  st : ⟦ X ↑ ⟧ (b ∷ a ∷ y) ≡ (b ∷ a ∷ y , φ (a ∷ y))
  st = DS-↑ d (b ∷ a ∷ y)
  fn-eq : fn (SWAP • X ↑ • SWAP) (a ∷ b ∷ y) ≡ a ∷ b ∷ y
  fn-eq = Eq.trans (fn-• SWAP (X ↑ • SWAP) (a ∷ b ∷ y))
          (Eq.trans (Eq.cong (fn SWAP) (fn-• (X ↑) SWAP (a ∷ b ∷ y)))
          (Eq.trans (Eq.cong (λ v → fn SWAP (fn (X ↑) v)) (fn-SWAP a b y))
          (Eq.trans (Eq.cong (λ p → fn SWAP (proj₁ p)) st) (fn-SWAP b a y))))
  ph-eq : ph (SWAP • X ↑ • SWAP) (a ∷ b ∷ y) ≡ φ (a ∷ y)
  ph-eq = Eq.trans (ph-• SWAP (X ↑ • SWAP) (a ∷ b ∷ y))
          (Eq.trans (Eq.cong₂ _+_ (ph-• (X ↑) SWAP (a ∷ b ∷ y))
                       (Eq.cong (ph SWAP) (Eq.trans (fn-• (X ↑) SWAP (a ∷ b ∷ y))
                          (Eq.trans (Eq.cong (fn (X ↑)) (fn-SWAP a b y)) (Eq.cong proj₁ st)))))
          (Eq.trans (Eq.cong₂ _+_ (Eq.cong₂ _+_ (ph-SWAP a b y)
                       (Eq.trans (Eq.cong (ph (X ↑)) (fn-SWAP a b y)) (Eq.cong proj₂ st)))
                       (ph-SWAP b a y))
          (Eq.trans (+-identityʳ (0₈ + φ (a ∷ y))) (+-identityˡ (φ (a ∷ y))))))

------------------------------------------------------------------------
-- Phase gates

private
  ph-•↑ : (g : Circuit (₁₊ n)) (w : Circuit n) (a : Bool) (x : Bits n) →
          ph (g • w ↑) (a ∷ x) ≡ ph w x + ph g (a ∷ fn w x)
  ph-•↑ g w a x = Eq.trans (ph-• g (w ↑) (a ∷ x))
                    (Eq.cong₂ _+_ (ph-↑ w a x) (Eq.cong (ph g) (fn-↑ w a x)))

  ph-CNOT' : (a : Bool) (v : Bits (₁₊ n)) → ph CNOT (a ∷ v) ≡ 0₈
  ph-CNOT' a (c ∷ y) = ph-CNOT a c y

  ph-SWAP' : (a : Bool) (v : Bits (₁₊ n)) → ph SWAP (a ∷ v) ≡ 0₈
  ph-SWAP' a (c ∷ y) = ph-SWAP a c y

r-phase : (ℓ : NZ n) (x : Bits n) → ph (r ℓ) x ≡ 0₈
r-phase e₀ x = ph-ε x
r-phase (cx ℓ) (a ∷ x) =
  Eq.trans (ph-•↑ CNOT (r ℓ) a x)
    (Eq.trans (Eq.cong₂ _+_ (r-phase ℓ x) (ph-CNOT' a (fn (r ℓ) x))) (+-identityˡ 0₈))
r-phase (sw ℓ) (a ∷ x) =
  Eq.trans (ph-•↑ SWAP (r ℓ) a x)
    (Eq.trans (Eq.cong₂ _+_ (r-phase ℓ x) (ph-SWAP' a (fn (r ℓ) x))) (+-identityˡ 0₈))

-- The inverse of a phase-free circuit is phase-free.
private
  inv-phase : (w : Circuit n) → (∀ x → ph w x ≡ 0₈) → (y : Bits n) → ph (w ⁻¹) (fn w y) ≡ 0₈
  inv-phase {n} w z y =
    Eq.trans (Eq.sym (+-identityˡ (ph (w ⁻¹) (fn w y))))
    (Eq.trans (Eq.cong (_+ ph (w ⁻¹) (fn w y)) (Eq.sym (z y)))
    (Eq.trans (Eq.sym (ph-• (w ⁻¹) w y))
    (Eq.trans (ph-≈ (Inv.inverseˡ n) y) (ph-ε y))))


dotℤ : NZ n → Bits n → ℤ₈
dotℤ ℓ x = if dot ℓ x then 1₈ else 0₈

DS-P : (ℓ : NZ (₁₊ n)) → DS (P ℓ) (dotℤ ℓ)
DS-P ℓ x = Eq.cong₂ _,_ fn-eq ph-eq
  where
  y = fn (r ℓ) x
  fn-eq : fn (P ℓ) x ≡ x
  fn-eq = Eq.trans (fn-• (r ℓ ⁻¹) (T • r ℓ) x)
          (Eq.trans (Eq.cong (fn (r ℓ ⁻¹)) (fn-• T (r ℓ) x))
          (Eq.trans (Eq.cong (fn (r ℓ ⁻¹)) (Eq.cong proj₁ (DS-T y))) (fn-⁻¹ (r ℓ) x)))
  T-at : ph T y ≡ dotℤ ℓ x
  T-at = Eq.trans (Eq.cong proj₂ (DS-T y))
                  (Eq.cong (λ b → if b then 1₈ else 0₈) (r-head ℓ x))
  ph-Tr : ph (T • r ℓ) x ≡ dotℤ ℓ x
  ph-Tr = Eq.trans (ph-• T (r ℓ) x)
            (Eq.trans (Eq.cong₂ _+_ (r-phase ℓ x) T-at) (+-identityˡ (dotℤ ℓ x)))
  ph-inv : ph (r ℓ ⁻¹) (fn (T • r ℓ) x) ≡ 0₈
  ph-inv = Eq.trans (Eq.cong (ph (r ℓ ⁻¹)) (Eq.trans (fn-• T (r ℓ) x) (Eq.cong proj₁ (DS-T y))))
                    (inv-phase (r ℓ) (r-phase ℓ) x)
  ph-eq : ph (P ℓ) x ≡ dotℤ ℓ x
  ph-eq = Eq.trans (ph-• (r ℓ ⁻¹) (T • r ℓ) x)
            (Eq.trans (Eq.cong₂ _+_ ph-Tr ph-inv) (+-identityʳ (dotℤ ℓ x)))

------------------------------------------------------------------------
-- Diagonal expressions

DS-Pz : (ℓ : NZ n) → DS (Pz ℓ) (dotℤ ℓ)
DS-Pz {suc m} ℓ = DS-P ℓ

φprod : PE n → Bits n → ℤ₈
φprod []             x = 0₈
φprod ((ℓ , k) ∷ pe) x = φprod pe x + powφ k (dotℤ ℓ) x

DS-prod : (pe : PE n) → DS (prod pe) (φprod pe)
DS-prod []             = DS-ε
DS-prod ((ℓ , k) ∷ pe) = DS-• (DS-^ (DS-Pz ℓ) k) (DS-prod pe)

φₑ : ℕ × PE n → Bits n → ℤ₈
φₑ (s , pe) x = φprod pe x + powφ s (λ _ → 1₈) x

DS-ₑ : (e : ℕ × PE n) → DS ⟦ e ⟧ₑ (φₑ e)
DS-ₑ (s , pe) = DS-• (DS-^ DS-ω s) (DS-prod pe)

DS-D : (d : DE n) → DS ⟦ d ⟧ᴰ (φₑ (toPE d))
DS-D d = DS-≈ (D-sound d) (DS-ₑ (toPE d))
