------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness for diagonal circuits, one wire at a time
--
-- A diagonal circuit on ₁₊ m wires — a power of ω times phase gates —
-- is an upper part U ↑ times a wire-0 form E e (Diagonal.Decompose).
-- Two with the same operator agree on the inputs with x₀ = 0, where E e
-- does nothing, so their upper parts have the same operator and are
-- equal by completeness one wire down; cancelling them, the forms have
-- the same operator, hence the same data (Diagonal.Unique).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.Complete where

open import Data.Bool using (false)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (_∷_ ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.CNOT+Dihedral.Semantics
open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Interpretation using (⟦_⟧ ; ⟦⟧-• ; up-word)
open import Examples.Groups.CNOT+Dihedral.Soundness using (sound)
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Evaluation
open import Examples.Groups.CNOT+Dihedral.Diagonal.Calculus
open import Examples.Groups.CNOT+Dihedral.Diagonal.Decompose
open import Examples.Groups.CNOT+Dihedral.Diagonal.Unique using (DS-E ; E-unique)

private
  variable
    m : ℕ

-- The diagonal part of a circuit: ω ^ s times phase gates.
dpart : ℕ → PE m → Circuit m
dpart s pe = ω ^ s • prod pe

-- Split along wire 0.
dsplit : (s : ℕ) (pe : PE (₁₊ m)) → (₁₊ m) ⊢ dpart s pe ≈ (dpart s (ups pe)) ↑ • E (es pe)
dsplit {m} s pe = begin
  ω ^ s • prod pe                              ≈⟨ cong (sym (ωᵏ↑ s)) (D-split pe) ⟩
  (ω ^ s) ↑ • (prod (ups pe)) ↑ • E (es pe)    ≈⟨ sym assoc ⟩
  (ω ^ s • prod (ups pe)) ↑ • E (es pe)        ∎
  where open Width (₁₊ m)

private
  -- The upper part, read off at x₀ = 0.
  at-zero : (U : Circuit m) (e : EData m) (x : Bits m) →
            ⟦ U ↑ • E e ⟧ (false ∷ x) ≡ (false ∷ fn U x , ph U x)
  at-zero U e x =
    Eq.trans (⟦⟧-• (U ↑) (E e) (false ∷ x))
      (Eq.trans (Eq.cong (λ p → proj₁ (⟦ U ↑ ⟧ (proj₁ p)) , proj₂ p + proj₂ (⟦ U ↑ ⟧ (proj₁ p)))
                         (DS-E e (false ∷ x)))
        (Eq.trans (Eq.cong (λ p → proj₁ p , 0₈ + proj₂ p) (up-word U (false ∷ x)))
                  (Eq.cong (false ∷ fn U x ,_) (+-identityˡ (ph U x)))))

  forms : Complete m → (U U' : Circuit m) (e e' : EData m) →
          ⟦ U ↑ • E e ⟧ ≐ ⟦ U' ↑ • E e' ⟧ → (₁₊ m) ⊢ U ↑ • E e ≈ U' ↑ • E e'
  forms {m} IH U U' e e' eq =
    trans (front _ (lift UU')) (back _ (refl' (Eq.cong E (E-unique e e' EE'))))
    where
    open Width (₁₊ m)
    -- The upper parts.
    same-U : ⟦ U ⟧ ≐ ⟦ U' ⟧
    same-U x = Eq.cong₂ _,_
      (Eq.cong tail (Eq.cong proj₁ (Eq.trans (Eq.sym (at-zero U e x)) (Eq.trans (eq (false ∷ x)) (at-zero U' e' x)))))
      (Eq.cong proj₂ (Eq.trans (Eq.sym (at-zero U e x)) (Eq.trans (eq (false ∷ x)) (at-zero U' e' x))))
    UU' : m ⊢ U ≈ U'
    UU' = IH same-U
    -- The forms.
    EE' : ⟦ E e ⟧ ≐ ⟦ E e' ⟧
    EE' = cancelˡ-⟦⟧ (U ↑) (E e) (E e')
            (≐-trans eq (sound (front _ (lift (Width.sym UU')))))

diag-complete : Complete m → (s t : ℕ) (pe qe : PE (₁₊ m)) →
                ⟦ dpart s pe ⟧ ≐ ⟦ dpart t qe ⟧ → (₁₊ m) ⊢ dpart s pe ≈ dpart t qe
diag-complete {m} IH s t pe qe eq =
  trans (dsplit s pe)
    (trans (forms IH (dpart s (ups pe)) (dpart t (ups qe)) (es pe) (es qe)
              (≐-trans (sound (sym (dsplit s pe))) (≐-trans eq (sound (dsplit t qe)))))
           (sym (dsplit t qe)))
  where open Width (₁₊ m)
