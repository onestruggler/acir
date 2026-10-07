------------------------------------------------------------------------
-- Presentations of groups
--
-- Evaluating circuits on basis states
--
-- A circuit's operator sends x to (fn w x , ph w x): the basis state
-- it lands on and the phase picked up on the way.  The interpretation
-- is abstract (Interpretation); here are the equations that let one
-- compute fn and ph on products, shifts and gates, together with the
-- two facts about operators of circuits that come from their being
-- invertible: a circuit can be cancelled on the right of an equation
-- of operators, and fn w is injective.  Both come from soundness and
-- the syntactic inverse of Presentation.GroupLike.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Evaluation where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_ ; if_then_else_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)
open import Presentation.GroupLike using (module Group-Lemmas)

open import Examples.Groups.CNOT+Dihedral.Semantics
open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Interpretation
open import Examples.Groups.CNOT+Dihedral.Soundness using (sound)
open import Examples.Groups.CNOT+Dihedral.Reasoning using (module Width)

private
  variable
    n : ℕ
    a b : Bool
    x y : Bits n
    w v : Circuit n

------------------------------------------------------------------------
-- The syntactic inverse

module Inv (n : ℕ) = Group-Lemmas (n VRel,_===_) (grouplike {n})

infix 8 _⁻¹
_⁻¹ : Circuit n → Circuit n
_⁻¹ {n} = Inv._⁻¹ n

------------------------------------------------------------------------
-- The state and the phase

fn : Circuit n → Bits n → Bits n
fn w x = proj₁ (⟦ w ⟧ x)

ph : Circuit n → Bits n → ℤ₈
ph w x = proj₂ (⟦ w ⟧ x)

fn-• : (w v : Circuit n) (x : Bits n) → fn (w • v) x ≡ fn w (fn v x)
fn-• w v x = Eq.cong proj₁ (⟦⟧-• w v x)

ph-• : (w v : Circuit n) (x : Bits n) → ph (w • v) x ≡ ph v x + ph w (fn v x)
ph-• w v x = Eq.cong proj₂ (⟦⟧-• w v x)

fn-ε : (x : Bits n) → fn ε x ≡ x
fn-ε x = Eq.cong proj₁ (⟦⟧-ε x)

ph-ε : (x : Bits n) → ph ε x ≡ 0₈
ph-ε x = Eq.cong proj₂ (⟦⟧-ε x)

fn-↑ : (w : Circuit n) (a : Bool) (x : Bits n) → fn (w ↑) (a ∷ x) ≡ a ∷ fn w x
fn-↑ w a x = Eq.cong proj₁ (up-word w (a ∷ x))

ph-↑ : (w : Circuit n) (a : Bool) (x : Bits n) → ph (w ↑) (a ∷ x) ≡ ph w x
ph-↑ w a x = Eq.cong proj₂ (up-word w (a ∷ x))

-- The gates.
fn-ω : (x : Bits n) → fn ω x ≡ x
fn-ω x = Eq.cong proj₁ (⟦⟧-gen ω-gen x)

ph-ω : (x : Bits n) → ph ω x ≡ 1₈
ph-ω x = Eq.cong proj₂ (⟦⟧-gen ω-gen x)

fn-X : (a : Bool) (x : Bits n) → fn X (a ∷ x) ≡ not a ∷ x
fn-X a x = Eq.cong proj₁ (⟦⟧-gen X-gen (a ∷ x))

ph-X : (a : Bool) (x : Bits n) → ph X (a ∷ x) ≡ 0₈
ph-X a x = Eq.cong proj₂ (⟦⟧-gen X-gen (a ∷ x))

fn-T : (a : Bool) (x : Bits n) → fn T (a ∷ x) ≡ a ∷ x
fn-T a x = Eq.cong proj₁ (⟦⟧-gen T-gen (a ∷ x))

ph-T : (a : Bool) (x : Bits n) → ph T (a ∷ x) ≡ (if a then 1₈ else 0₈)
ph-T a x = Eq.cong proj₂ (⟦⟧-gen T-gen (a ∷ x))

fn-CNOT : (t c : Bool) (x : Bits n) → fn CNOT (t ∷ c ∷ x) ≡ (c xor t) ∷ c ∷ x
fn-CNOT t c x = Eq.cong proj₁ (⟦⟧-gen CNOT-gen (t ∷ c ∷ x))

ph-CNOT : (t c : Bool) (x : Bits n) → ph CNOT (t ∷ c ∷ x) ≡ 0₈
ph-CNOT t c x = Eq.cong proj₂ (⟦⟧-gen CNOT-gen (t ∷ c ∷ x))

fn-SWAP : (a b : Bool) (x : Bits n) → fn SWAP (a ∷ b ∷ x) ≡ b ∷ a ∷ x
fn-SWAP a b x = Eq.cong proj₁ (⟦⟧-gen SWAP-gen (a ∷ b ∷ x))

ph-SWAP : (a b : Bool) (x : Bits n) → ph SWAP (a ∷ b ∷ x) ≡ 0₈
ph-SWAP a b x = Eq.cong proj₂ (⟦⟧-gen SWAP-gen (a ∷ b ∷ x))

------------------------------------------------------------------------
-- Equal circuits evaluate alike

fn-≈ : n ⊢ w ≈ v → (x : Bits n) → fn w x ≡ fn v x
fn-≈ e x = Eq.cong proj₁ (sound e x)

ph-≈ : n ⊢ w ≈ v → (x : Bits n) → ph w x ≡ ph v x
ph-≈ e x = Eq.cong proj₂ (sound e x)

------------------------------------------------------------------------
-- Circuits are invertible

-- The inverse undoes the state.
fn-⁻¹ : (w : Circuit n) (x : Bits n) → fn (w ⁻¹) (fn w x) ≡ x
fn-⁻¹ {n} w x = Eq.trans (Eq.sym (fn-• (w ⁻¹) w x))
                         (Eq.trans (fn-≈ (Inv.inverseˡ n) x) (fn-ε x))

fn-injective : (w : Circuit n) {x y : Bits n} → fn w x ≡ fn w y → x ≡ y
fn-injective w {x} {y} e =
  Eq.trans (Eq.sym (fn-⁻¹ w x)) (Eq.trans (Eq.cong (fn (w ⁻¹)) e) (fn-⁻¹ w y))

-- A circuit cancels on the right of an equation of operators.
cancelʳ-⟦⟧ : (u v c : Circuit n) → ⟦ u • c ⟧ ≐ ⟦ v • c ⟧ → ⟦ u ⟧ ≐ ⟦ v ⟧
cancelʳ-⟦⟧ {n} u v c e =
  ≐-trans (sound (sym (cancel u)))
    (≐-trans (⟦⟧-• (u • c) (c ⁻¹))
      (≐-trans (⊙-cong e (≐-refl ⟦ c ⁻¹ ⟧))
        (≐-trans (≐-sym (⟦⟧-• (v • c) (c ⁻¹))) (sound (cancel v)))))
  where
  open Width n
  cancel : (t : Circuit n) → n ⊢ (t • c) • c ⁻¹ ≈ t
  cancel t = trans assoc (trans (back t (Inv.inverseʳ n)) right-unit)

-- Equal operators one wire up are equal operators.
↑-reflect : (w v : Circuit n) → ⟦ w ↑ ⟧ ≐ ⟦ v ↑ ⟧ → ⟦ w ⟧ ≐ ⟦ v ⟧
↑-reflect w v e x = Eq.cong₂ _,_ fx px
  where
  fx : fn w x ≡ fn v x
  fx = Eq.cong Data.Vec.tail
         (Eq.trans (Eq.sym (fn-↑ w false x))
           (Eq.trans (Eq.cong proj₁ (e (false ∷ x))) (fn-↑ v false x)))
    where import Data.Vec
  px : ph w x ≡ ph v x
  px = Eq.trans (Eq.sym (ph-↑ w false x))
         (Eq.trans (Eq.cong proj₂ (e (false ∷ x))) (ph-↑ v false x))

------------------------------------------------------------------------
-- Completeness at a width

Complete : ℕ → Set
Complete n = ∀ {w v : Circuit n} → ⟦ w ⟧ ≐ ⟦ v ⟧ → n ⊢ w ≈ v

-- A circuit cancels on the left too.
cancelˡ-⟦⟧ : (c u v : Circuit n) → ⟦ c • u ⟧ ≐ ⟦ c • v ⟧ → ⟦ u ⟧ ≐ ⟦ v ⟧
cancelˡ-⟦⟧ {n} c u v e =
  ≐-trans (sound (sym (cancel u)))
    (≐-trans (⟦⟧-• (c ⁻¹) (c • u))
      (≐-trans (⊙-cong (≐-refl ⟦ c ⁻¹ ⟧) e)
        (≐-trans (≐-sym (⟦⟧-• (c ⁻¹) (c • v))) (sound (cancel v)))))
  where
  open Width n
  cancel : (t : Circuit n) → n ⊢ c ⁻¹ • c • t ≈ t
  cancel t = trans (sym assoc) (trans (front t (Inv.inverseˡ n)) left-unit)
