------------------------------------------------------------------------
-- Presentations of groups
--
-- Separating interpretations (Section 5.2 and 5.3)
--
-- Lemma 25: an axiom ρ is independent as soon as some model satisfies
-- the other axioms and not ρ.  Here a model is a monoid per width with
-- a reading of the generators, and Separator turns soundness of each
-- kept rule — the symmetry rules, the structural rules of Circuit.Base
-- and the axioms in Keep ρ b — into independence of ρ, through
-- Circuit.Independence's soundness engine and truncate.
--
-- Weighted is the uniform case of the counting models, occurrence
-- detectors and determinant phases (Definitions 26 to 35, except the
-- projective substitutions): every generator, the swap included, is
-- read as an element of a commutative monoid, whatever its wires, and
-- a circuit as the sum of its letters.  Commutativity validates every
-- comm rule and every naturality square at once, so of the structural
-- rules only σ σ = ε is owed (Remark 27), and the kept axioms are
-- checked once each, on their own wires, which is all the relation
-- states.  count m is (ℕ, +) modulo m
-- (Count_m, Definition 28), and has is (Bool, ∨) (Has).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Independence.Model (Gate : ℕ → Set) where

open import Algebra.Bundles using (Monoid ; CommutativeMonoid)
open import Data.Bool using (Bool ; false)
open import Data.Bool.Properties using (∨-commutativeMonoid)
open import Data.Nat using (_+_ ; _*_ ; _^_ ; _∸_ ; _%_ ; _≤_ ; NonZero)
open import Data.Nat.DivMod using (%-distribˡ-+)
open import Data.Nat.Properties using (+-assoc ; +-comm ; +-identityʳ)
open import Data.Product using (_,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Relation.Nullary.Negation using (¬_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Independence.Prop Gate
import Circuit.Independence PGate as CI

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The monoids of the counting separators

-- (ℕ, +, 0) modulo m.
count : (m : ℕ) .{{_ : NonZero m}} → CommutativeMonoid 0ℓ 0ℓ
count m = record
  { Carrier = ℕ
  ; _≈_ = λ a b → a % m ≡ b % m
  ; _∙_ = _+_
  ; ε = 0
  ; isCommutativeMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record
            { refl = refl ; sym = Eq.sym ; trans = Eq.trans }
          ; ∙-cong = λ {a} {a'} {b} {b'} e f →
              Eq.trans (%-distribˡ-+ a b m)
              (Eq.trans (Eq.cong₂ (λ x y → (x + y) % m) e f)
                        (Eq.sym (%-distribˡ-+ a' b' m)))
          }
        ; assoc = λ a b c → Eq.cong (_% m) (+-assoc a b c)
        }
      ; identity = (λ _ → refl) , (λ a → Eq.cong (_% m) (+-identityʳ a))
      }
    ; comm = λ a b → Eq.cong (_% m) (+-comm a b)
    }
  }

-- (Bool, ∨, false).
has : CommutativeMonoid 0ℓ 0ℓ
has = ∨-commutativeMonoid

-- Weights of the gates, extended to the swap.
counts : (∀ {n} → Gate n → ℕ) → ℕ → PGate n → ℕ
counts f s ⌈ g ⌉ = f g
counts f s swap  = s

occurs : (∀ {n} → Gate n → Bool) → PGate n → Bool
occurs f ⌈ g ⌉ = f g
occurs f swap  = false

-- The scaled determinant phase arg det_k (Definition 35), in units of
-- π/4: a gate g on n ≤ k wires weighs 2^(k−n) arg det ⟦ g ⟧, given as
-- ad g.  The swap has determinant −1, so weighs 2^(k−2) π, which is
-- the paper's θ_k.  Read modulo 8, that is modulo 2π.
argdet : ℕ → (∀ {n} → Gate n → ℕ) → PGate n → ℕ
argdet {n} k ad ⌈ g ⌉ = 2 ^ (k ∸ n) * ad g
argdet     k ad swap  = 2 ^ (k ∸ 2) * 4

------------------------------------------------------------------------
-- Separators for a fragment

module Separators (_SRel,_===_ : (n : ℕ) → CRel n) where

  open Lift-To-Prop _SRel,_===_
  open Axioms _SRel,_===_ public

  private
    variable
      w v : Circuit n

  -- Lemma 25, for a model of the other axioms of arity at most b.
  module Separator
    {m : ℕ} {wρ vρ : Circuit m} (ρ : m SRel, wρ === vρ) (b : ℕ)
    (mon : ℕ → Monoid 0ℓ 0ℓ)
    (⟦_⟧₀ : ∀ {n} → Gen n → Monoid.Carrier (mon n))
    where

    open CI.Structural _Prop,_===_ using (module Soundness)
    open Soundness (Keep ρ b) (λ p → p) mon ⟦_⟧₀ public

    -- The model respects the axiom a.
    Respects : n SRel, w === v → Set
    Respects {w = w} {v} _ = ⟦ w ⟧ ≈ₘ ⟦ v ⟧

    module Separates
      (sound-sym : ∀ {n} {w v : Circuit n} (s : n Sym, w === v) →
                   ⟦ w ⟧ ≈ₘ ⟦ v ⟧)
      (sound-ax : ∀ {n} {w v : Circuit n} (a : n SRel, w === v) →
                  ¬ ⟨ a ⟩ ≡ ⟨ ρ ⟩ → n ≤ b → ⟦ w ⟧ ≈ₘ ⟦ v ⟧)
      (sound-cong↑ : Sound-cong↑)
      (sound-comm₁ : ∀ {n} (h : PGate 1) (g : Gen n) →
                     ⟦ [ g ↥ ]ʷ • [ gate₁ h ]ʷ ⟧ ≈ₘ
                     ⟦ [ gate₁ h ]ʷ • [ g ↥ ]ʷ ⟧)
      (sound-comm₂ : ∀ {n} (h : PGate 2) (g : Gen n) →
                     ⟦ [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ ⟧ ≈ₘ
                     ⟦ [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ ⟧)
      (sound-comm₃ : ∀ {n} (h : PGate 3) (g : Gen n) →
                     ⟦ [ g ↥ ↥ ↥ ]ʷ • [ gate₃ h ]ʷ ⟧ ≈ₘ
                     ⟦ [ gate₃ h ]ʷ • [ g ↥ ↥ ↥ ]ʷ ⟧)
      (sound-ω↑=ω : ∀ {n} (ω : PGate 0) →
                    ⟦ [ gate₀ {n} ω ]ʷ ↑ ⟧ ≈ₘ ⟦ [ gate₀ ω ]ʷ ⟧)
      where

      private
        sound-srel : (s : n Prop, w === v) → Keep ρ b (srel s) →
                     ⟦ w ⟧ ≈ₘ ⟦ v ⟧
        sound-srel (σrel s) _           = sound-sym s
        sound-srel (srel a) (a≢ρ , n≤b) = sound-ax a a≢ρ n≤b

      open Rules sound-srel sound-cong↑
        (λ h g _ → sound-comm₁ h g) (λ h g _ → sound-comm₂ h g)
        (λ h g _ → sound-comm₃ h g)
        (λ ω _ → sound-ω↑=ω ω)
        public

      -- The model separates ρ, so ρ is independent.
      separates : m ≤ b → ¬ (⟦ wρ ⟧ ≈ₘ ⟦ vρ ⟧) → Independent-axiom ρ
      separates m≤b sep =
        upto⇒independent m≤b (independent (srel (srel ρ)) sep)

  ----------------------------------------------------------------------
  -- Weighted models: one commutative monoid at every width

  module Weighted
    (CM : CommutativeMonoid 0ℓ 0ℓ)
    (let open CommutativeMonoid CM using (Carrier ; _≈_ ; _∙_) renaming (ε to e))
    (wt : ∀ {n} → PGate n → Carrier)
    (wt-σ : (wt swap ∙ wt swap) ≈ e)
    where

    open CommutativeMonoid CM using (monoid ; comm ; assoc)
      renaming (refl to ≈-refl ; trans to ≈-trans)

    ⟦_⟧₀ : Gen n → Carrier
    ⟦ gate₀ g ⟧₀ = wt g
    ⟦ gate₁ g ⟧₀ = wt g
    ⟦ gate₂ g ⟧₀ = wt g
    ⟦ gate₃ g ⟧₀ = wt g
    ⟦ g ↥ ⟧₀     = ⟦ g ⟧₀

    module Sep {m : ℕ} {wρ vρ : Circuit m} (ρ : m SRel, wρ === vρ) (b : ℕ) where

      open Separator ρ b (λ _ → monoid) ⟦_⟧₀ public

      -- The checks: every other axiom of arity at most b, on its own
      -- wires.
      module Check
        (sound-rule : ∀ {n} {w v : Circuit n} (a : n SRel, w === v) →
                      ¬ ⟨ a ⟩ ≡ ⟨ ρ ⟩ → n ≤ b → ⟦ w ⟧ ≈ ⟦ v ⟧)
        where

        private
          sound-sym : (s : n Sym, w === v) → ⟦ w ⟧ ≈ ⟦ v ⟧
          sound-sym σ-inv      = wt-σ
          sound-sym (σ-nat₁ h) = comm _ _
          sound-sym (σ-nat₂ h) = comm _ _
          sound-sym (σ-nat₃ h) = comm _ _

          open Shift (λ x → x)
            (record { isMagmaHomomorphism = record
                        { isRelHomomorphism = record { cong = λ e → e }
                        ; homo = λ _ _ → ≈-refl }
                    ; ε-homo = ≈-refl })
            (λ _ → ≈-refl)

        -- ρ is independent when the model tells its sides apart.
        separates : m ≤ b → ¬ (⟦ wρ ⟧ ≈ ⟦ vρ ⟧) → Independent-axiom ρ
        separates =
          Separates.separates sound-sym sound-rule sound-cong↑
            (λ h g → comm _ _) (λ h g → comm _ _) (λ h g → comm _ _)
            (λ ω → ≈-refl)
