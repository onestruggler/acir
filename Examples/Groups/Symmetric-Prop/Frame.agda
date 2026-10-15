------------------------------------------------------------------------
-- Presentations of groups
--
-- A placement depends only on where the network sends the placed wires,
-- in any PROP.
--
-- Two networks N and N′ whose permutations send the bottom k wires to
-- the same places (their inverses agree there) place a circuit on those
-- k wires alike (`frame-perm`).  The permutation of N′⁻¹ N fixes the
-- bottom k wires, so it is a permutation of the wires above them
-- lifted k times (`peel`, from the standard library's `remove`), which
-- Symmetric's presentation realises by a network k wires up; then
-- Placement.frame applies.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)
import Circuit.Base

module Examples.Groups.Symmetric-Prop.Frame
  (Gate : ℕ → Set) (Ex-gate : Gate 2)
  (_SRel,_===_ : (n : ℕ) → Circuit.Base.CRel Gate n)
  where

open import Data.Fin.Base using (Fin ; zero ; suc ; inject+)
import Data.Fin.Properties as FP
open import Data.Fin.Permutation
  using (Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; inverseˡ ; inverseʳ ; lift₀ ; remove ; lift₀-remove)
open import Data.Nat.Base using (zero ; suc ; _+_)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊)
import Presentation.Base as PB

open import Circuit.Prop Gate Ex-gate
open Lift-To-Prop _SRel,_===_

import Examples.Groups.Symmetric.Syntactics as S
import Examples.Groups.Symmetric.Interpretation as SI
import Examples.Groups.Symmetric.Surjectivity as SSurj
open import Examples.Groups.Symmetric.Semantics using (Perm)
open import Examples.Groups.Symmetric-Prop.Networks Gate Ex-gate _SRel,_===_
  using (net ; perm ; perm-≈)
open import Examples.Groups.Symmetric-Prop.Placement Gate Ex-gate _SRel,_===_
  using (rev ; place ; frame)

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- Permutations of networks

private
  ⟦_⟧ : Word (S.Gen n) → Perm n
  ⟦_⟧ = SI.⟦_⟧

  -- The permutation of Networks is Symmetric's interpretation.
  perm≡ : (w : Word (S.Gen n)) (i : Fin n) → perm w ⟨$⟩ʳ i ≡ ⟦ w ⟧ ⟨$⟩ʳ i
  perm≡ w i = Eq.refl

  -- Every letter is an involution.
  letter-invol : (g : S.Gen n) (i : Fin n) →
    SI.⟦ g ⟧ᵍ ⟨$⟩ʳ (SI.⟦ g ⟧ᵍ ⟨$⟩ʳ i) ≡ i
  letter-invol (S.gate₀ ())
  letter-invol (S.gate₁ ())
  letter-invol (S.gate₂ S.σ-gate) zero             = Eq.refl
  letter-invol (S.gate₂ S.σ-gate) (suc zero)       = Eq.refl
  letter-invol (S.gate₂ S.σ-gate) (suc (suc i))    = Eq.refl
  letter-invol (g S.↥) zero    = Eq.refl
  letter-invol (g S.↥) (suc i) = Eq.cong suc (letter-invol g i)

-- The reverse undoes a network.
rev-undo : (w : Word (S.Gen n)) (i : Fin n) → ⟦ w ⟧ ⟨$⟩ʳ (⟦ rev w ⟧ ⟨$⟩ʳ i) ≡ i
rev-undo [ g ]ʷ  i = letter-invol g i
rev-undo ε       i = Eq.refl
rev-undo (u • v) i =
  Eq.trans (Eq.cong (⟦ v ⟧ ⟨$⟩ʳ_) (rev-undo u (⟦ rev v ⟧ ⟨$⟩ʳ i))) (rev-undo v i)

-- So the reverse denotes the inverse.
rev-perm : (w : Word (S.Gen n)) (i : Fin n) → ⟦ rev w ⟧ ⟨$⟩ʳ i ≡ ⟦ w ⟧ ⟨$⟩ˡ i
rev-perm w i = Eq.trans (Eq.sym (inverseˡ ⟦ w ⟧))
  (Eq.cong (⟦ w ⟧ ⟨$⟩ˡ_) (rev-undo w i))

------------------------------------------------------------------------
-- A permutation fixing the bottom k wires is lifted from the rest

liftᵏ : ∀ k → Perm m → Perm (k + m)
liftᵏ zero    π = π
liftᵏ (suc k) π = lift₀ (liftᵏ k π)

liftᵏ-cong : ∀ k {π ρ : Perm m} → (∀ i → π ⟨$⟩ʳ i ≡ ρ ⟨$⟩ʳ i) →
  ∀ i → liftᵏ k π ⟨$⟩ʳ i ≡ liftᵏ k ρ ⟨$⟩ʳ i
liftᵏ-cong zero    e i       = e i
liftᵏ-cong (suc k) e zero    = Eq.refl
liftᵏ-cong (suc k) e (suc i) = Eq.cong suc (liftᵏ-cong k e i)

peel : ∀ k (π : Perm (k + m)) →
  (∀ (j : Fin k) → π ⟨$⟩ʳ inject+ m j ≡ inject+ m j) →
  Σ (Perm m) λ π′ → ∀ i → liftᵏ k π′ ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i
peel zero    π fix = π , λ i → Eq.refl
peel {m} (suc k) π fix = π′ , agree
  where
  p : π ⟨$⟩ʳ zero ≡ zero
  p = fix zero
  π₀ : Perm (k + m)
  π₀ = remove zero π
  lifted : ∀ i → lift₀ π₀ ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i
  lifted = lift₀-remove π p
  fix₀ : ∀ (j : Fin k) → π₀ ⟨$⟩ʳ inject+ m j ≡ inject+ m j
  fix₀ j = FP.suc-injective (Eq.trans (lifted (suc (inject+ m j))) (fix (suc j)))
  rest = peel k π₀ fix₀
  π′ = proj₁ rest
  agree : ∀ i → liftᵏ (suc k) π′ ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i
  agree zero    = Eq.sym p
  agree (suc i) = Eq.trans (Eq.cong suc (proj₂ rest i)) (lifted (suc i))

------------------------------------------------------------------------
-- A network k wires up denotes a lifted permutation

private
  ↑ᵏ-suc : (w : Word (S.Gen n)) (j : ℕ) → w S.↑ᵏ suc j ≡ (w S.↑ᵏ j) S.↑
  ↑ᵏ-suc [ g ]ʷ  j = Eq.refl
  ↑ᵏ-suc ε       j = Eq.refl
  ↑ᵏ-suc (u • v) j = Eq.cong₂ _•_ (↑ᵏ-suc u j) (↑ᵏ-suc v j)

  ↑ᵏ-zero : (w : Word (S.Gen n)) (i : Fin n) → ⟦ w S.↑ᵏ 0 ⟧ ⟨$⟩ʳ i ≡ ⟦ w ⟧ ⟨$⟩ʳ i
  ↑ᵏ-zero [ g ]ʷ  i = Eq.refl
  ↑ᵏ-zero ε       i = Eq.refl
  ↑ᵏ-zero (u • v) i =
    Eq.trans (Eq.cong (⟦ v S.↑ᵏ 0 ⟧ ⟨$⟩ʳ_) (↑ᵏ-zero u i)) (↑ᵏ-zero v _)

up : ∀ (w : Word (S.Gen m)) k (i : Fin (k + m)) →
  ⟦ w S.↑ᵏ k ⟧ ⟨$⟩ʳ i ≡ liftᵏ k ⟦ w ⟧ ⟨$⟩ʳ i
up w zero    i = ↑ᵏ-zero w i
up w (suc k) i =
  Eq.trans (Eq.cong (λ x → ⟦ x ⟧ ⟨$⟩ʳ i) (↑ᵏ-suc w k))
  (Eq.trans (SI.⟦↑⟧ (w S.↑ᵏ k) i) (go i))
  where
  go : ∀ i → lift₀ ⟦ w S.↑ᵏ k ⟧ ⟨$⟩ʳ i ≡ lift₀ (liftᵏ k ⟦ w ⟧) ⟨$⟩ʳ i
  go zero    = Eq.refl
  go (suc i) = Eq.cong suc (up w k i)

------------------------------------------------------------------------
-- The frame

module _
  (scalars-comm : ∀ {n} (h h′ : Gate 0) →
     n ⊢ [ gate₀ h′ ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h′ ]ʷ)
  where

  -- Two networks sending the bottom k wires to the same places place a
  -- circuit on them alike.
  frame-perm : (N N′ : Word (S.Gen (k + m))) →
    (∀ (j : Fin k) → ⟦ N ⟧ ⟨$⟩ˡ inject+ m j ≡ ⟦ N′ ⟧ ⟨$⟩ˡ inject+ m j) →
    (w : Circuit k) → (k + m) ⊢ place N (w ↓ᵏ m) ≈ place N′ (w ↓ᵏ m)
  frame-perm {k} {m} N N′ agree w =
    PB.trans (PB.cong same same⁻)
      (frame scalars-comm N′ M′ w)
    where
    -- N′⁻¹ N fixes the bottom k wires ...
    π : Perm (k + m)
    π = ⟦ rev N′ • N ⟧
    fix : ∀ (j : Fin k) → π ⟨$⟩ʳ inject+ m j ≡ inject+ m j
    fix j = Eq.trans (Eq.cong (⟦ N ⟧ ⟨$⟩ʳ_) (rev-perm N′ (inject+ m j)))
      (Eq.trans (Eq.cong (⟦ N ⟧ ⟨$⟩ʳ_) (Eq.sym (agree j))) (inverseʳ ⟦ N ⟧))
    -- ... so it is a network k wires up.
    peeled = peel k π fix
    M′ : Word (S.Gen m)
    M′ = proj₁ (SSurj.surjective (proj₁ peeled))
    M′-sem : ∀ i → ⟦ M′ ⟧ ⟨$⟩ʳ i ≡ proj₁ peeled ⟨$⟩ʳ i
    M′-sem = proj₂ (SSurj.surjective (proj₁ peeled)) PB.refl
    X : Word (S.Gen (k + m))
    X = N′ • (M′ S.↑ᵏ k)
    -- N and N′ (N′⁻¹ N) denote the same permutation.
    sem : ∀ i → ⟦ N ⟧ ⟨$⟩ʳ i ≡ ⟦ X ⟧ ⟨$⟩ʳ i
    sem i = Eq.sym (Eq.trans (up M′ k (⟦ N′ ⟧ ⟨$⟩ʳ i))
      (Eq.trans (liftᵏ-cong k M′-sem (⟦ N′ ⟧ ⟨$⟩ʳ i))
      (Eq.trans (proj₂ peeled (⟦ N′ ⟧ ⟨$⟩ʳ i))
      (Eq.trans (Eq.cong (⟦ N ⟧ ⟨$⟩ʳ_) (rev-perm N′ (⟦ N′ ⟧ ⟨$⟩ʳ i)))
        (Eq.cong (⟦ N ⟧ ⟨$⟩ʳ_) (inverseˡ ⟦ N′ ⟧))))))
    sem⁻ : ∀ i → ⟦ rev N ⟧ ⟨$⟩ʳ i ≡ ⟦ rev X ⟧ ⟨$⟩ʳ i
    sem⁻ i = Eq.trans (rev-perm N i) (Eq.trans (inv-unique i) (Eq.sym (rev-perm X i)))
      where
      inv-unique : ∀ i → ⟦ N ⟧ ⟨$⟩ˡ i ≡ ⟦ X ⟧ ⟨$⟩ˡ i
      inv-unique i = Eq.trans (Eq.sym (inverseˡ ⟦ X ⟧))
        (Eq.cong (⟦ X ⟧ ⟨$⟩ˡ_) (Eq.trans (Eq.sym (sem (⟦ N ⟧ ⟨$⟩ˡ i))) (inverseʳ ⟦ N ⟧)))
    same : (k + m) ⊢ net N ≈ net X
    same = perm-≈ {u = N} {v = X} sem
    same⁻ : (k + m) ⊢ (w ↓ᵏ m) • net (rev N) ≈ (w ↓ᵏ m) • net (rev X)
    same⁻ = PB.cong PB.refl (perm-≈ {u = rev N} {v = rev X} sem⁻)
