------------------------------------------------------------------------
-- Presentations of groups
--
-- The seven-T Toffoli circuit on any three wires, and its
-- specification (Amy, QPL 2018, example 3.3 and section 5.2)
--
-- tof c₁ c₂ t is the seven-T Toffoli of Nielsen and Chuang's figure
-- 4.9 with the T† and S on the second control merged into one T (both
-- diagonal on that wire; 15 gates, 8 of them Clifford where the figure
-- has 9), over {H, CNOT, T, T†} (T = R_3), with controls c₁, c₂
-- and target t any three distinct wires of an n-wire circuit: the
-- circuit ToffoliC of PathSum.Examples.Toffoli, gate for gate, with
-- c₁, c₂ and t for its wires 0, 1 and 2.  Its specification is the
-- Toffoli function toffoli c₁ c₂ t x = x[t ≔ x_t ⊕ x_c₁ x_c₂], an
-- involution (toffoli-involutive), and the classical path-sum toffoliˢ
-- whose output on t is the lift of the Boolean expression
-- x_t ⊕ x_c₁ x_c₂ (PathSum.Classical).
--
-- Also here, for PathSum.Toffoli's proof: the values the circuit's
-- wires take along a path, which differ from the input only on c₁, c₂
-- and t (w3, with the effect of each CNOT and Hadamard on them), and
-- the sum over the circuit's two path variables of what each path
-- contributes (Σ-pathsum): 2 at the Toffoli function's value, 0
-- elsewhere.  The circuit's vocabulary comes from PathSum.CRK.Path, so
-- that ⟦ tof … ⟧ is a term of the one instance of PathSum.CRK.Circuit
-- that PathSum.CRK.Path's lemmas are about.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Toffoli.Gate (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _xor_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (+_; _+_; _*_)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-comm; ≔-cong; ≔-self; same)
open import PathSum.Base using (PathSum)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (classical; fun; setWire; fun-setWireᵉ)
open import PathSum.CRK.Path M₀ using (H; CNOT; R; R†; Circuit)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _·ᴬ_; _≐_; Σᴮ; zpow)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Polynomial using (x[_])
open import PathSum.Polynomial.Boolean using
  (BExp; var; _⊕ᵉ_; _∧ᵉ_; liftᵉ)
open import PathSum.Reduction M using (½)
open import PathSum.Toffoli.Arith M₀ using (one; pair; outer; select)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The circuit and its specification

-- Controls c₁ and c₂, target t: a doubly controlled Z between two
-- Hadamards on the target, the controlled Z being ⅛ of
--   x₁ + x₂ + y - (x₁ ⊕ x₂) - (x₁ ⊕ y) - (x₂ ⊕ y) + (x₁ ⊕ x₂ ⊕ y)
--   = 4 x₁ x₂ y
-- (T = R 3, T† = R† 3).  The head of the list is applied first.

tof : (c₁ c₂ t : Fin n) → c₁ ≢ c₂ → c₁ ≢ t → c₂ ≢ t → Circuit n
tof c₁ c₂ t c₁≢c₂ c₁≢t c₂≢t =
  H t ∷ CNOT c₂ t c₂≢t ∷ R† 3 t ∷ CNOT c₁ t c₁≢t ∷ R 3 t ∷
  CNOT c₂ t c₂≢t ∷ R† 3 t ∷ CNOT c₁ t c₁≢t ∷ R 3 t ∷ R 3 c₂ ∷ H t ∷
  CNOT c₁ c₂ c₁≢c₂ ∷ R† 3 c₂ ∷ CNOT c₁ c₂ c₁≢c₂ ∷ R 3 c₁ ∷ []

-- The Toffoli function.

toffoli : (c₁ c₂ t : Fin n) → Assign n → Assign n
toffoli c₁ c₂ t x = x [ t ≔ x t xor (x c₁ ∧ x c₂) ]

-- x_t ⊕ x_c₁ x_c₂ as a Boolean expression, and the classical path-sum
-- |x⟩ ↦ |x[t ≔ x_t ⊕ x_c₁ x_c₂]⟩, with the lift of that expression on
-- t (x_t + x_c₁ x_c₂ - 2 x_t x_c₁ x_c₂).

toffoliᵉ : (c₁ c₂ t : Fin n) → BExp n 0
toffoliᵉ c₁ c₂ t = var x[ t ] ⊕ᵉ (var x[ c₁ ] ∧ᵉ var x[ c₂ ])

toffoliˢ : (c₁ c₂ t : Fin n) → PathSum n 0 0
toffoliˢ c₁ c₂ t = classical (setWire t (liftᵉ (toffoliᵉ c₁ c₂ t)))

fun-toffoliˢ : (c₁ c₂ t : Fin n) (x : Assign n) →
               ∀ w → fun (setWire t (liftᵉ (toffoliᵉ c₁ c₂ t))) x w ≡
                     toffoli c₁ c₂ t x w
fun-toffoliˢ c₁ c₂ t x w = fun-setWireᵉ t (toffoliᵉ c₁ c₂ t) x w

-- The Toffoli function is an involution: applied twice, the target
-- reads (x_t ⊕ x_c₁ x_c₂) ⊕ x_c₁ x_c₂ = x_t, the controls being left
-- alone.

private
  xor-cancel : ∀ p q → (p xor q) xor q ≡ p
  xor-cancel false false = refl
  xor-cancel false true  = refl
  xor-cancel true  false = refl
  xor-cancel true  true  = refl

toffoli-involutive : (c₁ c₂ t : Fin n) → c₁ ≢ t → c₂ ≢ t →
                     (x : Assign n) →
                     ∀ u → toffoli c₁ c₂ t (toffoli c₁ c₂ t x) u ≡ x u
toffoli-involutive c₁ c₂ t c₁≢t c₂≢t x u =
  trans (cong (λ b → ((x [ t ≔ v ]) [ t ≔ b ]) u)
              (cong₂ _xor_ (≔-here x t v)
                     (cong₂ _∧_ (≔-there x v c₁≢t) (≔-there x v c₂≢t))))
    (trans (≔-≔ x t v (v xor a) u)
      (trans (cong (λ b → (x [ t ≔ b ]) u) (xor-cancel (x t) a))
             (≔-self x t u)))
  where
  a v : Bool
  a = x c₁ ∧ x c₂
  v = x t xor a


------------------------------------------------------------------------
-- Three wires

-- The circuit writes only to c₂ and t, so along a path its wires read
-- x with c₁, c₂ and t overwritten.  The values are always passed
-- explicitly, so that no lemma below has to be found by unification.

module Wires {n : ℕ} {c₁ c₂ t : Fin n} (c₁≢c₂ : c₁ ≢ c₂) (c₁≢t : c₁ ≢ t)
             (c₂≢t : c₂ ≢ t) (x : Assign n) where

  w3 : Bool → Bool → Bool → Assign n
  w3 α β γ = x [ c₁ ≔ α ] [ c₂ ≔ β ] [ t ≔ γ ]

  w3-t : ∀ α β γ → w3 α β γ t ≡ γ
  w3-t α β γ = ≔-here (x [ c₁ ≔ α ] [ c₂ ≔ β ]) t γ

  w3-c₂ : ∀ α β γ → w3 α β γ c₂ ≡ β
  w3-c₂ α β γ =
    trans (≔-there (x [ c₁ ≔ α ] [ c₂ ≔ β ]) γ c₂≢t)
          (≔-here (x [ c₁ ≔ α ]) c₂ β)

  w3-c₁ : ∀ α β γ → w3 α β γ c₁ ≡ α
  w3-c₁ α β γ =
    trans (≔-there (x [ c₁ ≔ α ] [ c₂ ≔ β ]) γ c₁≢t)
          (trans (≔-there (x [ c₁ ≔ α ]) β c₁≢c₂) (≔-here x c₁ α))

  -- Overwriting t or c₂ once more.

  w3-set-t : ∀ α β γ γ′ u → (w3 α β γ [ t ≔ γ′ ]) u ≡ w3 α β γ′ u
  w3-set-t α β γ γ′ u = ≔-≔ (x [ c₁ ≔ α ] [ c₂ ≔ β ]) t γ γ′ u

  w3-set-c₂ : ∀ α β γ β′ u → (w3 α β γ [ c₂ ≔ β′ ]) u ≡ w3 α β′ γ u
  w3-set-c₂ α β γ β′ u = trans
    (≔-comm (x [ c₁ ≔ α ] [ c₂ ≔ β ]) γ β′ (λ e → c₂≢t (sym e)) u)
    (≔-cong t γ (≔-≔ (x [ c₁ ≔ α ]) c₂ β β′) u)

  -- x itself, with only t overwritten.

  w3-x : ∀ γ u → (x [ t ≔ γ ]) u ≡ w3 (x c₁) (x c₂) γ u
  w3-x γ u = ≔-cong t γ back u
    where
    back : ∀ j → x j ≡ (x [ c₁ ≔ x c₁ ] [ c₂ ≔ x c₂ ]) j
    back j = sym (trans
      (cong (λ b → (x [ c₁ ≔ x c₁ ] [ c₂ ≔ b ]) j)
            (sym (≔-there x (x c₁) (λ e → c₁≢c₂ (sym e)))))
      (trans (≔-self (x [ c₁ ≔ x c₁ ]) c₂ j) (≔-self x c₁ j)))

  -- The circuit's CNOTs and Hadamards, on such values.

  cnot-t : (c : Fin n) (α β γ v : Bool) → w3 α β γ c ≡ v →
           ∀ u → (w3 α β γ [ t ≔ w3 α β γ t xor w3 α β γ c ]) u ≡
                 w3 α β (γ xor v) u
  cnot-t c α β γ v eq u =
    trans (cong (λ b → (w3 α β γ [ t ≔ b ]) u)
                (cong₂ _xor_ (w3-t α β γ) eq))
          (w3-set-t α β γ (γ xor v) u)

  cnot-c₂ : (α β γ : Bool) →
            ∀ u → (w3 α β γ [ c₂ ≔ w3 α β γ c₂ xor w3 α β γ c₁ ]) u ≡
                  w3 α (β xor α) γ u
  cnot-c₂ α β γ u =
    trans (cong (λ b → (w3 α β γ [ c₂ ≔ b ]) u)
                (cong₂ _xor_ (w3-c₂ α β γ) (w3-c₁ α β γ)))
          (w3-set-c₂ α β γ (β xor α) u)

  h-t : (α β γ : Bool) {b : Bool} (b′ : Bool) → b ≡ b′ →
        ∀ u → (w3 α β γ [ t ≔ b ]) u ≡ w3 α β b′ u
  h-t α β γ b′ eq u =
    trans (cong (λ d → (w3 α β γ [ t ≔ d ]) u) eq) (w3-set-t α β γ b′ u)


------------------------------------------------------------------------
-- The sum over the paths

-- What the path Y contributes to the amplitude from x to z, y₂ being
-- Y zero and y₁ Y (suc zero) (PathSum.Toffoli.tof-amp): ζ^(½ y₁ q) if
-- the output x[t ≔ y₂] is z, q being y₂ ⊕ x_t ⊕ x_c₁ x_c₂.

pathsum : (c₁ c₂ t : Fin n) → Assign n → Assign n → Assign 2 → Amp
pathsum c₁ c₂ t x z Y =
  if same (x [ t ≔ Y zero ]) z
  then zpow (½ * [ Y (suc zero) ∧ (Y zero xor (x t xor (x c₁ ∧ x c₂))) ]ᶻ)
  else 0ᴬ

-- Summed: 2 at the Toffoli function's value, and 0 elsewhere.

Σ-pathsum : (c₁ c₂ t : Fin n) (x z : Assign n) →
            Σᴮ (pathsum c₁ c₂ t x z) ≐ (+ 2) ·ᴬ δ (toffoli c₁ c₂ t x) z
Σ-pathsum c₁ c₂ t x z i =
  trans (cong₂ _+_ (pair (s true) (not r) i) (pair (s false) r i))
    (trans (outer r (s true) (s false) i)
           (cong (λ b → ((+ 2) ·ᴬ (if b then one else 0ᴬ)) i) (select s r)))
  where
  r : Bool
  r = x t xor (x c₁ ∧ x c₂)

  s : Bool → Bool
  s b = same (x [ t ≔ b ]) z
