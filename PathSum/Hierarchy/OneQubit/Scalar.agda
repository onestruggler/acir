------------------------------------------------------------------------
-- Presentations of groups
--
-- One qubit: scalars
--
-- A scalar operator commutes with everything and, if unitary, is in
-- 𝒞 2; on one qubit, an operator commuting with X and Z is a scalar
-- (schur).  Part of PathSum.Hierarchy.OneQubit.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.OneQubit.Scalar (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _∨_; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; -[1+_]; _+_; _-_; _*_; _%_; _/_)
open import Data.Integer.DivMod using (a≡a%n+[a/n]*n; n%d<d)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Integer.Properties using
  (_≟_; *-zeroʳ; *-identityʳ; +-identityˡ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (zero; _<_; z≤n; s≤s)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; lookup)
  renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst₂)
open import Relation.Nullary.Decidable using
  (⌊_⌋; yes; no; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using
  ([_]ᶻ; _=ᵇ_; =ᵇ-refl; =ᵇ-true; same; same-≗; ≔-here)
open import PathSum.Compose.Matrix M₀ using (if-⊛; ⊛-if)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ; if-cong; zpow-≡; scale-exp)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; -ᴬ_; _≐_; Σᴮ-cong; zpow; rot; rot-exp; rot-0; rot-anti;
   scale-injective; N)
  renaming (H to Hᶻ)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy M₀
open import PathSum.Hierarchy.Gates M₀
open import PathSum.Hierarchy.Levels M₀
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Hierarchy.Pauli M₀
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ--; ≡ᴺ-N)
open import PathSum.Ring M₀ using (_⊛_; ⊛-cong)
open import PathSum.Ring.Laws M₀ using (⊛-comm)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

open import PathSum.Hierarchy.OneQubit.Code M₀

private
  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Scalars

-- V is the scalar a: a times the identity matrix.

ScalarBy : {n : ℕ} → Op n → Amp → Set
ScalarBy V a = ∀ x z → mat V x z ≐ (if same x z then a else 0ᴬ)

-- On one qubit, V is a scalar: a multiple of the identity matrix.

Scalar : Op 1 → Set
Scalar V = ScalarBy V (mat V 0₁ 0₁)

private
  -- Equal operators with equal normalisations have equal entries.

  ent : {A B : Op 1} → A ≈ B → nrm A ≡ nrm B → ∀ x z → mat A x z ≐ mat B x z
  ent {A} {B} e eq x z = scale-injective (nrm A) (mat A x z) (mat B x z)
    (scale-exp (mat A x z) eq ∙ ≈-at e x z)

  rotX : (w : Assign 1) (a : Amp) → rot (φᴾ ⟦ cX ⟧ᶜ w) a ≐ a
  rotX w a = rot-exp {φᴾ ⟦ cX ⟧ᶜ w} {0ℤ} a (cong₂ _+_ (*-zeroʳ ¼) (*-zeroʳ ½))
             ∙ rot-0 a

  rotZ₀ : (a : Amp) → rot (φᴾ ⟦ cZ ⟧ᶜ 0₁) a ≐ a
  rotZ₀ a = rot-exp {φᴾ ⟦ cZ ⟧ᶜ 0₁} {0ℤ} a (cong₂ _+_ (*-zeroʳ ¼) (*-zeroʳ ½))
            ∙ rot-0 a

-- An operator on one qubit commuting with X and with Z is a scalar.

schur : (V : Op 1) → Unitary V →
        V · pauli ⟦ cX ⟧ᶜ · V † ≈ pauli ⟦ cX ⟧ᶜ →
        V · pauli ⟦ cZ ⟧ᶜ · V † ≈ pauli ⟦ cZ ⟧ᶜ → Scalar V
schur V uV fx fz x z =
  resp V {x} {const (x w₀)} {z} {const (z w₀)} (on₁ x) (on₁ z)
  ∙ sc (x w₀) (z w₀)
  ∙ if-cong {p = same (const (x w₀)) (const (z w₀))} {q = same x z}
            (sym (same-≗ (on₁ x) (on₁ z))) ≐-refl
  where
  cmX : ∀ v u → mat (V · pauli ⟦ cX ⟧ᶜ) v u ≐ mat (pauli ⟦ cX ⟧ᶜ · V) v u
  cmX = ent {V · pauli ⟦ cX ⟧ᶜ} {pauli ⟦ cX ⟧ᶜ · V}
            (conj⇒intertwine V (pauli ⟦ cX ⟧ᶜ) (pauli ⟦ cX ⟧ᶜ) uV fx)
            (ℕ.+-identityʳ (nrm V))

  cmZ : ∀ v u → mat (V · pauli ⟦ cZ ⟧ᶜ) v u ≐ mat (pauli ⟦ cZ ⟧ᶜ · V) v u
  cmZ = ent {V · pauli ⟦ cZ ⟧ᶜ} {pauli ⟦ cZ ⟧ᶜ · V}
            (conj⇒intertwine V (pauli ⟦ cZ ⟧ᶜ) (pauli ⟦ cZ ⟧ᶜ) uV fz)
            (ℕ.+-identityʳ (nrm V))

  -- From X: V(1,1) = V(0,0) and V(1,0) = V(0,1).

  A11 : mat V 1₁ 1₁ ≐ mat V 0₁ 0₁
  A11 = respˣ V 1₁ 1₁ (0₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ) (λ _ → refl)
        ∙ ≐-sym (rotX 0₁ (mat V (0₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ) 1₁))
        ∙ ≐-sym (·-pauli V ⟦ cX ⟧ᶜ 0₁ 1₁)
        ∙ cmX 0₁ 1₁
        ∙ pauli-·′ ⟦ cX ⟧ᶜ V 0₁ 1₁
        ∙ rotX (1₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ) (mat V 0₁ (1₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ))
        ∙ respᶻ V 0₁ (1₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ) 0₁ (λ _ → refl)

  A10 : mat V 1₁ 0₁ ≐ mat V 0₁ 1₁
  A10 = respˣ V 0₁ 1₁ (0₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ) (λ _ → refl)
        ∙ ≐-sym (rotX 0₁ (mat V (0₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ) 0₁))
        ∙ ≐-sym (·-pauli V ⟦ cX ⟧ᶜ 0₁ 0₁)
        ∙ cmX 0₁ 0₁
        ∙ pauli-·′ ⟦ cX ⟧ᶜ V 0₁ 0₁
        ∙ rotX (0₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ) (mat V 0₁ (0₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ))
        ∙ respᶻ V 0₁ (0₁ ⊕ᵛ xs ⟦ cX ⟧ᶜ) 1₁ (λ _ → refl)

  -- From Z: V(0,1) = -V(0,1), so V(0,1) = 0.

  anti : mat V 0₁ 1₁ ≐ -ᴬ (mat V 0₁ 1₁)
  anti = respˣ V 1₁ 0₁ (0₁ ⊕ᵛ xs ⟦ cZ ⟧ᶜ) (λ _ → refl)
         ∙ ≐-sym (rotZ₀ (mat V (0₁ ⊕ᵛ xs ⟦ cZ ⟧ᶜ) 1₁))
         ∙ ≐-sym (·-pauli V ⟦ cZ ⟧ᶜ 0₁ 1₁)
         ∙ cmZ 0₁ 1₁
         ∙ pauli-·′ ⟦ cZ ⟧ᶜ V 0₁ 1₁
         ∙ rot-exp {φᴾ ⟦ cZ ⟧ᶜ (1₁ ⊕ᵛ xs ⟦ cZ ⟧ᶜ)} {0ℤ + (+ Hᶻ)}
                   (mat V 0₁ (1₁ ⊕ᵛ xs ⟦ cZ ⟧ᶜ))
                   (cong₂ _+_ (*-zeroʳ ¼) (*-identityʳ ½))
         ∙ rot-anti 0ℤ (mat V 0₁ (1₁ ⊕ᵛ xs ⟦ cZ ⟧ᶜ))
         ∙ (λ j → cong -_ (trans (rot-0 (mat V 0₁ (1₁ ⊕ᵛ xs ⟦ cZ ⟧ᶜ)) j)
                                 (respᶻ V 0₁ (1₁ ⊕ᵛ xs ⟦ cZ ⟧ᶜ) 1₁
                                        (λ _ → refl) j)))

  A01 : mat V 0₁ 1₁ ≐ 0ᴬ
  A01 i = neg-fixed (mat V 0₁ 1₁ i) (anti i)

  sc : (a b : Bool) →
       mat V (const a) (const b) ≐
       (if same (const a) (const b) then mat V 0₁ 0₁ else 0ᴬ)
  sc false false = ≐-refl
  sc true  true  = A11
  sc false true  = A01
  sc true  false = A10 ∙ A01

-- A scalar commutes with everything.

scalar-comm : {n : ℕ} (V : Op n) (a : Amp) → ScalarBy V a → (A : Op n) →
              V · A ≈ A · V
scalar-comm V a sV A = ≈-by (V · A) (A · V) (ℕ.+-comm (nrm V) (nrm A)) (λ x z →
  Σᴮ-cong (λ w → ⊛-cong {a = mat A x w} ≐-refl (sV w z)
                 ∙ ⊛-if (same w z) (mat A x w) a
                 ∙ if-cong {p = same w z} {q = same z w} (same-sym w z) ≐-refl)
  ∙ Σᴮ-δ z (λ w → mat A x w ⊛ a)
         (λ g h g≗h → ⊛-cong {a = mat A x g} (respᶻ A x g h g≗h) ≐-refl)
  ∙ ⊛-comm (mat A x z) a
  ∙ ≐-sym (Σᴮ-cong (λ w → ⊛-cong {a = mat V x w} (sV x w) ≐-refl
                          ∙ if-⊛ (same x w) a (mat A w z))
           ∙ Σᴮ-δ x (λ w → a ⊛ mat A w z)
                  (λ g h g≗h → ⊛-cong {a = a} ≐-refl (respˣ A z g h g≗h))))

scalar-conj : {n : ℕ} (V : Op n) (a : Amp) → Unitary V → ScalarBy V a →
              (P : Op n) → V · P · V † ≈ P
scalar-conj V a uV sV P =
  ·-congˡ (V †) (scalar-comm V a sV P) ⟨≈⟩ cancelʳ V P uV

-- So a unitary scalar is in 𝒞 2: it is a global phase.

scalar-𝒞₂ : (V : Op 1) → Unitary V → Scalar V → 𝒞 2 V
scalar-𝒞₂ V uV sV = uV , λ p → p , scalar-conj V (mat V 0₁ 0₁) uV sV (pauli p)
