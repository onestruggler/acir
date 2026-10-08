------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar ω = s (1 + i) and its powers
--
-- ω ω = i (from s s + s s = 1 and i i = −1), so ω^(2k) = i^k, which is
-- the phase k mod 4 (ω-even); and the circuit ω^k denotes the scalar
-- matrix ω^k (⟦ω^⟧).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Qubit-Clifford.Semantics.Scalars
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  (i : A) (i² : i * i ≡ - 1#)
  where

open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_) renaming (_^_ to _^ʷ_)

open import Examples.Groups.Qubit-Clifford.Syntactics using (Circuit ; ω)
open import Examples.Groups.Qubit-Clifford.Pauli using (Ph ; p0 ; p1 ; _⊕_)
open import Examples.Groups.Qubit-Clifford.Semantics.Interpretation isCR s s-half i i²
  using ( module AR ; scal ; δb ; _≐_ ; ≐-refl ; ≐-sym ; ≐-trans ; ⊙-cong ; scal-1 ; scal-⊙
        ; ⟦_⟧ᴬ ; ω̂ ; _^_ ; ^-+ ; ιᵍ-1 ; ιᵍ-i ; module ZS )
open ZS using (solve ; _:=_ ; _:+_ ; _:*_ ; con)
open import Examples.Groups.Qubit-Clifford.Semantics.PauliMatrix isCR s s-half i i² using (iph ; iph-⊕)

private
  variable
    n : ℕ

-- ω ω = i.
ω̂² : ω̂ * ω̂ ≡ i
ω̂² = begin
  (s * (1# + i)) * (s * (1# + i))       ≡⟨ solve 2 (λ s i → (s :* (con (+ 1) :+ i)) :* (s :* (con (+ 1) :+ i))
                                              := (s :* s :+ s :* s) :* i :+ (s :* s) :* (i :* i :+ con (+ 1)))
                                             refl s i ⟩
  (s * s + s * s) * i + (s * s) * (i * i + 1#)
                                        ≡⟨ Eq.cong₂ (λ a b → a * i + (s * s) * b) s-half i²+1 ⟩
  1# * i + (s * s) * 0#                 ≡⟨ solve 2 (λ s i → con (+ 1) :* i :+ (s :* s) :* con (+ 0) := i) refl s i ⟩
  i                                     ∎
  where
  open Eq.≡-Reasoning
  i²+1 : i * i + 1# ≡ 0#
  i²+1 = Eq.trans (Eq.cong (_+ 1#) i²) (AR.-‿inverseˡ 1#)

pow-mul : (a b : A) (k : ℕ) → (a * b) ^ k ≡ (a ^ k) * (b ^ k)
pow-mul a b zero    = Eq.sym (AR.*-identityˡ 1#)
pow-mul a b (suc k) = Eq.trans (Eq.cong ((a * b) *_) (pow-mul a b k)) (cross a b (a ^ k) (b ^ k))
  where
  cross : (a b c d : A) → (a * b) * (c * d) ≡ (a * c) * (b * d)
  cross a b c d = solve 4 (λ a b c d → (a :* b) :* (c :* d) := (a :* c) :* (b :* d)) refl a b c d

-- i^k as a phase.
phOf : ℕ → Ph
phOf zero    = p0
phOf (suc k) = phOf k ⊕ p1

i^ : (k : ℕ) → i ^ k ≡ iph (phOf k)
i^ zero    = Eq.sym ιᵍ-1
i^ (suc k) = begin
  i * i ^ k                     ≡⟨ Eq.cong (i *_) (i^ k) ⟩
  i * iph (phOf k)              ≡⟨ AR.*-comm i (iph (phOf k)) ⟩
  iph (phOf k) * i              ≡⟨ Eq.cong (iph (phOf k) *_) (Eq.sym ιᵍ-i) ⟩
  iph (phOf k) * iph p1         ≡⟨ Eq.sym (iph-⊕ (phOf k) p1) ⟩
  iph (phOf k ⊕ p1)             ∎
  where open Eq.≡-Reasoning

ω̂-even : (k : ℕ) → ω̂ ^ (k +ℕ k) ≡ iph (phOf k)
ω̂-even k = Eq.trans (^-+ ω̂ k k) (Eq.trans (Eq.sym (pow-mul ω̂ ω̂ k))
             (Eq.trans (Eq.cong (_^ k) ω̂²) (i^ k)))

-- The matrix of ω^k.
⟦ω^⟧ : (k : ℕ) → ⟦ ω {n} ^ʷ k ⟧ᴬ ≐ scal (ω̂ ^ k)
⟦ω^⟧ zero          = ≐-sym scal-1
⟦ω^⟧ (suc zero)    x y = Eq.cong (_* δb x y) (Eq.sym (AR.*-identityʳ ω̂))
⟦ω^⟧ (suc (suc k)) = ≐-trans (⊙-cong (≐-refl (scal ω̂)) (⟦ω^⟧ (suc k))) (scal-⊙ ω̂ (ω̂ ^ suc k))
