------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization of seven commuting involutions.  This is the diagonal
-- part of a compact even signed-permutation presentation; it is generic
-- in the containing relation and in the words realizing the phases.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base using (Fin)
open import Word.Base using (Word ; WRel ; ε ; _•_)
import Presentation.Base as PB

module Examples.Groups.CCX+HH.ThreeQubit.PhaseNormalization
  {B : Set} (Γ : WRel B) (phase : Fin 7 → Word B)
  (square : ∀ i → PB._≈_ Γ (phase i • phase i) ε)
  (commute : ∀ i j → PB._≈_ Γ (phase i • phase j) (phase j • phase i))
  where

open import Data.Bool.Base using (Bool ; true ; false ; not)
open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; _ʷ)
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

private
  module P = PB Γ
  module Q = PP Γ

section : ∀ {n} → (Fin n → Fin 7) → Vec Bool n → Word B
section f [] = ε
section f (false ∷ s) = section (λ i → f (suc i)) s
section f (true ∷ s) = phase (f zero) • section (λ i → f (suc i)) s

toggle : ∀ {n} → Fin n → Vec Bool n → Vec Bool n
toggle zero (a ∷ s) = not a ∷ s
toggle (suc i) (a ∷ s) = a ∷ toggle i s

module _ where
  open SR Q.word-setoid

  insert : ∀ {n} (f : Fin n → Fin 7) i s →
    phase (f i) • section f s P.≈ section f (toggle i s)
  insert f zero (false ∷ s) = P.refl
  insert f zero (true ∷ s) = begin
    phase (f zero) • (phase (f zero) • section (λ i → f (suc i)) s)
      ≈⟨ P.sym P.assoc ⟩
    (phase (f zero) • phase (f zero)) • section (λ i → f (suc i)) s
      ≈⟨ P.cong (square (f zero)) P.refl ⟩
    ε • section (λ i → f (suc i)) s ≈⟨ P.left-unit ⟩
    section (λ i → f (suc i)) s ∎
  insert f (suc i) (false ∷ s) = insert (λ j → f (suc j)) i s
  insert f (suc i) (true ∷ s) = begin
    phase (f (suc i)) • (phase (f zero) • section (λ j → f (suc j)) s)
      ≈⟨ P.sym P.assoc ⟩
    (phase (f (suc i)) • phase (f zero)) • section (λ j → f (suc j)) s
      ≈⟨ P.cong (commute (f (suc i)) (f zero)) P.refl ⟩
    (phase (f zero) • phase (f (suc i))) • section (λ j → f (suc j)) s
      ≈⟨ P.assoc ⟩
    phase (f zero) • (phase (f (suc i)) • section (λ j → f (suc j)) s)
      ≈⟨ P.cong P.refl (insert (λ j → f (suc j)) i s) ⟩
    phase (f zero) • section (λ j → f (suc j)) (toggle i s) ∎

  run : Vec Bool 7 → Word (Fin 7) → Vec Bool 7
  run s [ i ]ʷ = toggle i s
  run s ε = s
  run s (u • v) = run (run s v) u

  normalize-from : ∀ w s →
    (phase ʷ) w • section (λ i → i) s P.≈ section (λ i → i) (run s w)
  normalize-from [ i ]ʷ s = insert (λ i → i) i s
  normalize-from ε s = P.left-unit
  normalize-from (u • v) s = begin
    ((phase ʷ) u • (phase ʷ) v) • section (λ i → i) s ≈⟨ P.assoc ⟩
    (phase ʷ) u • ((phase ʷ) v • section (λ i → i) s)
      ≈⟨ P.cong P.refl (normalize-from v s) ⟩
    (phase ʷ) u • section (λ i → i) (run s v)
      ≈⟨ normalize-from u (run s v) ⟩
    section (λ i → i) (run (run s v) u) ∎

  nf : Word (Fin 7) → Vec Bool 7
  nf = run (replicate 7 false)

  normalize : ∀ w → (phase ʷ) w P.≈ section (λ i → i) (nf w)
  normalize w = P.trans (P.sym P.right-unit) (normalize-from w (replicate 7 false))

equal-normal-forms : ∀ {u v} → nf u ≡ nf v → (phase ʷ) u P.≈ (phase ʷ) v
equal-normal-forms {u} {v} eq = P.trans (normalize u)
  (P.trans (P.refl' (Eq.cong (section (λ i → i)) eq)) (P.sym (normalize v)))
