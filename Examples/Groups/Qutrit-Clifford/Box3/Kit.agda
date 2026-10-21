------------------------------------------------------------------------
-- Presentations of groups
--
-- Steps for the derivations of the three-qutrit box relations
--
-- Completeness on two qutrits makes every true equation between
-- circuits on two adjacent wires a step (sem₀₁, and lift⁼ of it one
-- wire up); a word followed or preceded by its inverse cancels
-- (cancelʳ, cancelˡ); and letters on disjoint wires are reordered
-- inside a segment (permE).  The generated parts write these steps in
-- the compact spelling of Qutrit-Clifford.Letters (semℓ, rwPℓ, rwCˡ, …).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Box3.Kit where

open import Data.Bool.Base using (T)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.List.Properties using (++-assoc ; ++-identityʳ)
open import Data.Nat.Base using (ℕ)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Notations using (₂₊)
open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine
  using (Eqn ; eqn ; ⟪_⟫ ; ⟪++⟫ ; ⟪≈⟫ ; ⟪map↥⟫ ; module Canon ; perm-sound ; Step ; rw ; sym⁼)
open import Examples.Groups.Qutrit-Clifford.Letters using (ℓ)
import Examples.Groups.Qutrit-Clifford.Semantics as Sem
open import Examples.Groups.Qutrit-Clifford.Evaluation using (evL ; eqF ; checkedL ; wordL)
open import Examples.Groups.Qutrit-Clifford.Completeness2 using (completeness₂)
open import Examples.Groups.Qutrit-Clifford.Weakening using (weaken)
open import Examples.Groups.Qutrit-Clifford.Inverse using (invL ; invL-r ; invL-l)
open import Examples.Groups.Qutrit-Clifford.Reasoning using (module Width ; lift)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Two-wire steps

⟪↧⟫ : ∀ {m} (xs : List (Gen m)) k → ⟪ map (_↧ᵏ k) xs ⟫ ≡ ⟪ xs ⟫ ↓ᵏ k
⟪↧⟫ []       k = Eq.refl
⟪↧⟫ (x ∷ xs) k = Eq.cong ([ x ↧ᵏ k ]ʷ •_) (⟪↧⟫ xs k)

wordL-⟪⟫ : ∀ {m} (xs : List (Gen m)) → wordL xs ≡ ⟪ xs ⟫
wordL-⟪⟫ []       = Eq.refl
wordL-⟪⟫ (x ∷ xs) = Eq.cong ([ x ]ʷ •_) (wordL-⟪⟫ xs)

-- A true equation between two-wire letter lists, on the bottom two
-- wires of any wider circuit.
sem₀₁ : (l r : List (Gen 2)) → T (eqF (evL l) (evL r)) → Eqn (₂₊ n)
sem₀₁ {n} l r t = eqn (map (_↧ᵏ n) l) (map (_↧ᵏ n) r)
  (Eq.subst₂ (λ a b → (₂₊ n) ⊢ a ≈ b) (Eq.sym (⟪↧⟫ l n)) (Eq.sym (⟪↧⟫ r n))
    (weaken n (completeness₂ (Eq.subst₂ (λ a b → Sem._≈_ (Sem.⟦_⟧ a) (Sem.⟦_⟧ b)) (wordL-⟪⟫ l) (wordL-⟪⟫ r) (checkedL l r t)))))

------------------------------------------------------------------------
-- Inverses

invT : Gen n → List (Gen n)
invT (gate₀ ν-gate)  = gate₀ ν-gate ∷ gate₀ ν-gate ∷ gate₀ ν-gate ∷ gate₀ ν-gate ∷ gate₀ ν-gate ∷ []
invT (gate₁ H-gate)  = gate₁ H-gate ∷ gate₁ H-gate ∷ gate₁ H-gate ∷ []
invT (gate₁ S-gate)  = gate₁ S-gate ∷ gate₁ S-gate ∷ []
invT (gate₂ CZ-gate) = gate₂ CZ-gate ∷ gate₂ CZ-gate ∷ []
invT (g ↥)           = map _↥ (invT g)

-- With an accumulator: the plain recursion, invList xs ++ invT x,
-- nests its appends to the left, and inverting k letters cost k²
-- (the derivations cancel words of hundreds of letters).
invAcc : List (Gen n) → List (Gen n) → List (Gen n)
invAcc []       acc = acc
invAcc (x ∷ xs) acc = invAcc xs (invT x ++ acc)

invList : List (Gen n) → List (Gen n)
invList xs = invAcc xs []

mutual
  invAcc-++ : (xs acc : List (Gen n)) → invAcc xs acc ≡ invList xs ++ acc
  invAcc-++ []       acc = Eq.refl
  invAcc-++ (x ∷ xs) acc = Eq.trans (invAcc-++ xs (invT x ++ acc))
    (Eq.sym (Eq.trans (Eq.cong (_++ acc) (invList-∷ x xs)) (++-assoc (invList xs) (invT x) acc)))

  invList-∷ : (x : Gen n) (xs : List (Gen n)) → invList (x ∷ xs) ≡ invList xs ++ invT x
  invList-∷ x xs = Eq.trans (invAcc-++ xs (invT x ++ [])) (Eq.cong (invList xs ++_) (++-identityʳ (invT x)))

invT-≈ : (g : Gen n) → n ⊢ ⟪ invT g ⟫ ≈ invL g
invT-≈ {n} (gate₀ ν-gate)  = Width.by-assoc n Eq.refl
invT-≈ {n} (gate₁ H-gate)  = Width.by-assoc n Eq.refl
invT-≈ {n} (gate₁ S-gate)  = Width.by-assoc n Eq.refl
invT-≈ {n} (gate₂ CZ-gate) = Width.by-assoc n Eq.refl
invT-≈ (g ↥) = Eq.subst (λ a → _ ⊢ a ≈ invL g ↑) (Eq.sym (⟪map↥⟫ (invT g))) (lift (invT-≈ g))

private
  inv-r′ : (xs : List (Gen n)) → n ⊢ ⟪ xs ⟫ • ⟪ invList xs ⟫ ≈ ε
  inv-r′ []       = Width.left-unit
  inv-r′ {n} (x ∷ xs) = begin
    ([ x ]ʷ • ⟪ xs ⟫) • ⟪ invList (x ∷ xs) ⟫              ≈⟨ back ([ x ]ʷ • ⟪ xs ⟫) (⟪≈⟫ (invList-∷ x xs)) ⟩
    ([ x ]ʷ • ⟪ xs ⟫) • ⟪ invList xs ++ invT x ⟫          ≈⟨ back ([ x ]ʷ • ⟪ xs ⟫) (⟪++⟫ (invList xs) (invT x)) ⟩
    ([ x ]ʷ • ⟪ xs ⟫) • (⟪ invList xs ⟫ • ⟪ invT x ⟫)     ≈⟨ trans assoc (back [ x ]ʷ (sym assoc)) ⟩
    [ x ]ʷ • ((⟪ xs ⟫ • ⟪ invList xs ⟫) • ⟪ invT x ⟫)     ≈⟨ back [ x ]ʷ (front ⟪ invT x ⟫ (inv-r′ xs)) ⟩
    [ x ]ʷ • (ε • ⟪ invT x ⟫)                             ≈⟨ back [ x ]ʷ (trans left-unit (invT-≈ x)) ⟩
    [ x ]ʷ • invL x                                       ≈⟨ invL-r x ⟩
    ε                                                     ∎
    where open Width n

  inv-l′ : (xs : List (Gen n)) → n ⊢ ⟪ invList xs ⟫ • ⟪ xs ⟫ ≈ ε
  inv-l′ []       = Width.left-unit
  inv-l′ {n} (x ∷ xs) = begin
    ⟪ invList (x ∷ xs) ⟫ • ([ x ]ʷ • ⟪ xs ⟫)              ≈⟨ front ([ x ]ʷ • ⟪ xs ⟫) (⟪≈⟫ (invList-∷ x xs)) ⟩
    ⟪ invList xs ++ invT x ⟫ • ([ x ]ʷ • ⟪ xs ⟫)          ≈⟨ front ([ x ]ʷ • ⟪ xs ⟫) (⟪++⟫ (invList xs) (invT x)) ⟩
    (⟪ invList xs ⟫ • ⟪ invT x ⟫) • ([ x ]ʷ • ⟪ xs ⟫)     ≈⟨ trans assoc (back ⟪ invList xs ⟫ (sym assoc)) ⟩
    ⟪ invList xs ⟫ • ((⟪ invT x ⟫ • [ x ]ʷ) • ⟪ xs ⟫)     ≈⟨ back ⟪ invList xs ⟫ (front ⟪ xs ⟫ (trans (front [ x ]ʷ (invT-≈ x)) (invL-l x))) ⟩
    ⟪ invList xs ⟫ • (ε • ⟪ xs ⟫)                         ≈⟨ back ⟪ invList xs ⟫ left-unit ⟩
    ⟪ invList xs ⟫ • ⟪ xs ⟫                               ≈⟨ inv-l′ xs ⟩
    ε                                                     ∎
    where open Width n

-- xs followed by its inverse, and preceded by it.
cancelʳ : List (Gen n) → Eqn n
cancelʳ xs = eqn (xs ++ invList xs) [] (PB.trans (⟪++⟫ xs (invList xs)) (inv-r′ xs))

cancelˡ : List (Gen n) → Eqn n
cancelˡ xs = eqn (invList xs ++ xs) [] (PB.trans (⟪++⟫ (invList xs) xs) (inv-l′ xs))

------------------------------------------------------------------------
-- Reordering a segment

permE : (xs ys : List (Gen n)) → Canon.comm-canonical xs ≡ Canon.comm-canonical ys → Eqn n
permE xs ys h = eqn xs ys (perm-sound xs ys h)

------------------------------------------------------------------------
-- The steps without parentheses (see Qutrit-Clifford.Letters)

semℓ : (l r : String) → T (eqF (evL (ℓ l)) (evL (ℓ r))) → Eqn (₂₊ n)
semℓ l r = sem₀₁ (ℓ l) (ℓ r)

rwPℓ : ℕ → (xs ys : String) →
       Canon.comm-canonical (ℓ {n} xs) ≡ Canon.comm-canonical (ℓ ys) → Step n
rwPℓ i xs ys h = rw i (permE (ℓ xs) (ℓ ys) h)

rwCˡ rwCˡˢ rwCʳ rwCʳˢ : ℕ → String → Step n
rwCˡ  i s = rw i (cancelˡ (ℓ s))
rwCˡˢ i s = rw i (sym⁼ (cancelˡ (ℓ s)))
rwCʳ  i s = rw i (cancelʳ (ℓ s))
rwCʳˢ i s = rw i (sym⁼ (cancelʳ (ℓ s)))
