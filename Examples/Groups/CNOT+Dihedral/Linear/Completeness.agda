------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness for linear circuits (Lafont), one wire at a time
--
-- Two normal forms W ↑ • s₁ u • r ℓ with the same operator agree:
-- the row ℓ is the parity on wire 0, which neither s₁ u nor anything
-- on the upper wires changes; cancelling r ℓ, the vector u is the one
-- sent to e₀ (the upper part keeps 0 and e₀ apart only by wire 0);
-- and cancelling s₁ u, the upper parts have equal operators, so they
-- are equal by completeness one wire down.  Every linear circuit
-- having a normal form (Linear.Steps.decompose), two linear circuits
-- with the same operator are equal.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Linear.Completeness where

open import Data.Bool using (true ; false)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (_∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.CNOT+Dihedral.Semantics
open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Interpretation using (⟦_⟧)
open import Examples.Groups.CNOT+Dihedral.Soundness using (sound)
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Evaluation
open import Examples.Groups.CNOT+Dihedral.Linear.Base
open import Examples.Groups.CNOT+Dihedral.Linear.Steps
open import Examples.Groups.CNOT+Dihedral.Linear.Semantics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Evaluating a normal form

fn-nf : (W : Circuit n) (u : SOne (₁₊ n)) (ℓ : NZ (₁₊ n)) (x : Bits (₁₊ n)) →
        fn ⌜ ⟨ W , u , ℓ ⟩ ⌝ x ≡ fn (W ↑) (fn (s₁ u) (fn (r ℓ) x))
fn-nf W u ℓ x =
  Eq.trans (fn-• (W ↑) (s₁ u • r ℓ) x) (Eq.cong (fn (W ↑)) (fn-• (s₁ u) (r ℓ) x))

head-nf : (W : Circuit n) (u : SOne (₁₊ n)) (ℓ : NZ (₁₊ n)) (x : Bits (₁₊ n)) →
          head (fn ⌜ ⟨ W , u , ℓ ⟩ ⌝ x) ≡ dot ℓ x
head-nf W u ℓ x =
  Eq.trans (Eq.cong head (fn-nf W u ℓ x))
  (Eq.trans (↑-head W (fn (s₁ u) (fn (r ℓ) x)))
  (Eq.trans (s₁-head u (fn (r ℓ) x)) (r-head ℓ x)))

------------------------------------------------------------------------
-- Equal operators, equal normal forms

private
  -- The column part, with the row cancelled.
  column : (W W' : Circuit n) (u u' : SOne (₁₊ n)) →
           ⟦ W ↑ • s₁ u ⟧ ≐ ⟦ W' ↑ • s₁ u' ⟧ → u ≡ u'
  column W W' u u' e =
    Eq.sym (vec₁-injective u' u (fn-injective (W ↑ • s₁ u) key))
    where
    f-at : (V : Circuit _) (t : SOne _) (y : Bits _) →
           fn (V ↑ • s₁ t) y ≡ fn (V ↑) (fn (s₁ t) y)
    f-at V t y = fn-• (V ↑) (s₁ t) y

    at-zero : (V : Circuit _) (t : SOne _) → fn (V ↑ • s₁ t) zeros ≡ false ∷ fn V zeros
    at-zero V t = Eq.trans (f-at V t zeros)
                  (Eq.trans (Eq.cong (fn (V ↑)) (s₁-zero t)) (fn-↑ V false zeros))

    at-vec : (V : Circuit _) (t : SOne _) → fn (V ↑ • s₁ t) (vec₁ t) ≡ true ∷ fn V zeros
    at-vec V t = Eq.trans (f-at V t (vec₁ t))
                 (Eq.trans (Eq.cong (fn (V ↑)) (s₁-vec t)) (fn-↑ V true zeros))

    same-zero : fn W zeros ≡ fn W' zeros
    same-zero = Eq.cong tail
      (Eq.trans (Eq.sym (at-zero W u)) (Eq.trans (Eq.cong proj₁ (e zeros)) (at-zero W' u')))

    key : fn (W ↑ • s₁ u) (vec₁ u') ≡ fn (W ↑ • s₁ u) (vec₁ u)
    key = Eq.trans (Eq.cong proj₁ (e (vec₁ u')))
          (Eq.trans (at-vec W' u')
          (Eq.trans (Eq.cong (true ∷_) (Eq.sym same-zero)) (Eq.sym (at-vec W u))))

private
  same-row : (W W' : Circuit n) (u u' : SOne (₁₊ n)) (ℓ ℓ' : NZ (₁₊ n)) →
             ⟦ ⌜ ⟨ W , u , ℓ ⟩ ⌝ ⟧ ≐ ⟦ ⌜ ⟨ W' , u' , ℓ' ⟩ ⌝ ⟧ → ℓ ≡ ℓ'
  same-row W W' u u' ℓ ℓ' e = dot-injective ℓ ℓ' λ x →
    Eq.trans (Eq.sym (head-nf W u ℓ x))
      (Eq.trans (Eq.cong (λ p → head (proj₁ p)) (e x)) (head-nf W' u' ℓ' x))

  -- Regrouping the normal form, the row last.
  regroup : (W : Circuit n) (u : SOne (₁₊ n)) (ℓ : NZ (₁₊ n)) →
            ⟦ (W ↑ • s₁ u) • r ℓ ⟧ ≐ ⟦ ⌜ ⟨ W , u , ℓ ⟩ ⌝ ⟧
  regroup W u ℓ = sound Width.assoc

  -- The row cancelled.
  no-row : (W W' : Circuit n) (u u' : SOne (₁₊ n)) (ℓ : NZ (₁₊ n)) →
           ⟦ ⌜ ⟨ W , u , ℓ ⟩ ⌝ ⟧ ≐ ⟦ ⌜ ⟨ W' , u' , ℓ ⟩ ⌝ ⟧ →
           ⟦ W ↑ • s₁ u ⟧ ≐ ⟦ W' ↑ • s₁ u' ⟧
  no-row W W' u u' ℓ e =
    cancelʳ-⟦⟧ (W ↑ • s₁ u) (W' ↑ • s₁ u') (r ℓ)
      (≐-trans (regroup W u ℓ) (≐-trans e (≐-sym (regroup W' u' ℓ))))

  finish : Complete n → (W W' : Circuit n) (u u' : SOne (₁₊ n)) (ℓ : NZ (₁₊ n)) →
           u ≡ u' → ⟦ ⌜ ⟨ W , u , ℓ ⟩ ⌝ ⟧ ≐ ⟦ ⌜ ⟨ W' , u' , ℓ ⟩ ⌝ ⟧ →
           (₁₊ n) ⊢ ⌜ ⟨ W , u , ℓ ⟩ ⌝ ≈ ⌜ ⟨ W' , u' , ℓ ⟩ ⌝
  finish {n} IH W W' u .u ℓ Eq.refl e =
    Width.front (₁₊ n) (s₁ u • r ℓ)
      (lift (IH (↑-reflect W W' (cancelʳ-⟦⟧ (W ↑) (W' ↑) (s₁ u) (no-row W W' u u ℓ e)))))

  same-col : Complete n → (W W' : Circuit n) (u u' : SOne (₁₊ n)) (ℓ ℓ' : NZ (₁₊ n)) →
             ℓ ≡ ℓ' → ⟦ ⌜ ⟨ W , u , ℓ ⟩ ⌝ ⟧ ≐ ⟦ ⌜ ⟨ W' , u' , ℓ' ⟩ ⌝ ⟧ →
             (₁₊ n) ⊢ ⌜ ⟨ W , u , ℓ ⟩ ⌝ ≈ ⌜ ⟨ W' , u' , ℓ' ⟩ ⌝
  same-col IH W W' u u' ℓ .ℓ Eq.refl e =
    finish IH W W' u u' ℓ (column W W' u u' (no-row W W' u u' ℓ e)) e

nf-complete : Complete n → (N N' : LNF n) →
              ⟦ ⌜ N ⌝ ⟧ ≐ ⟦ ⌜ N' ⌝ ⟧ → (₁₊ n) ⊢ ⌜ N ⌝ ≈ ⌜ N' ⌝
nf-complete IH ⟨ W , u , ℓ ⟩ ⟨ W' , u' , ℓ' ⟩ e =
  same-col IH W W' u u' ℓ ℓ' (same-row W W' u u' ℓ ℓ' e) e

-- Two linear circuits with the same operator are equal.
linear-complete : Complete n → (L L' : Word (LGen (₁₊ n))) →
                  ⟦ ⌊ L ⌋ ⟧ ≐ ⟦ ⌊ L' ⌋ ⟧ → (₁₊ n) ⊢ ⌊ L ⌋ ≈ ⌊ L' ⌋
linear-complete {n} IH L L' e =
  trans (decompose L)
    (trans (nf-complete IH (lnf L) (lnf L')
              (≐-trans (sound (sym (decompose L))) (≐-trans e (sound (decompose L')))))
           (sym (decompose L')))
  where open Width (₁₊ n)
