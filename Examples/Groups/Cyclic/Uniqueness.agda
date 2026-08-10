------------------------------------------------------------------------
-- Presentations of groups
--
-- Unique normal form for the ℤ/Nℤ semantics of the cyclic groups:
-- normal forms with equal denotations are equal.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Cyclic.Uniqueness where

open import Data.Fin using (Fin ; zero ; suc ; toℕ ; inject₁)
open import Data.Fin.Induction using (<-weakInduction)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s)
  renaming (_+_ to _+ℕ_)
open import Data.Nat.DivMod using (_%_ ; m%n<n ; m<n⇒m%n≡m)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; trans ; sym ; cong ; subst)

import Data.Fin.Properties as FP
import Data.Integer as Int
import Data.Nat.Properties as NP

open import ForStdlib.Data.Fin.Mod using (_+_ ; +-identityˡ)
import Normalization.NormalForm.Propositional as NFBase
open import Notations
open import Word.Base using (_^'_)

open import Examples.Groups.Cyclic.Normalization
open import Examples.Groups.Cyclic.Semantics

------------------------------------------------------------------------
-- Reading the denotation of a power back off as its exponent

-- In the free-monoid semantics (N = 0) the denotation of Tᵏ is the
-- integer +k.
sem0 : ∀ k → ⟦_⟧ {0} (T ^' k) ≡ Int.+ k
sem0 zero          = refl
sem0 (suc zero)    = refl
sem0 (suc (suc k)) =
  trans (cong (Int._+ Int.+ 1) (sem0 (suc k)))
        (cong Int.+_ (cong suc (NP.+-comm k 1)))

-- In ℤ/(2+N)ℤ, appending one more generator is adding ₁.
sem-suc : ∀ {N} k → ⟦_⟧ {₂₊ N} (T ^' suc k) ≡ ⟦_⟧ {₂₊ N} (T ^' k) + ₁
sem-suc {N} zero    = sym (+-identityˡ ₁)
sem-suc {N} (suc k) = refl

-- Adding ₁ to the embedding of i realises the Fin successor.
inj+1 : ∀ {N} (i : Fin (₁₊ N)) → inject₁ i + ₁ ≡ suc i
inj+1 {N} i = FP.toℕ-injective
  (trans (FP.toℕ-fromℕ< (m%n<n (toℕ (inject₁ i) +ℕ 1) (₂₊ N)))
  (trans (cong (λ z → (z +ℕ 1) % ₂₊ N) (FP.toℕ-inject₁ i))
  (trans (m<n⇒m%n≡m bound)
         (NP.+-comm (toℕ i) 1))))
  where
  bound : toℕ i +ℕ 1 < ₂₊ N
  bound = subst (_< ₂₊ N) (sym (NP.+-comm (toℕ i) 1)) (s≤s (FP.toℕ<n i))

-- In ℤ/(2+N)ℤ, the denotation of the normal form [ u ] recovers u.
pow-id : ∀ {N} (u : Fin (₂₊ N)) → ⟦_⟧ {₂₊ N} (T ^' toℕ u) ≡ u
pow-id {N} = <-weakInduction P refl step
  where
  P : Fin (₂₊ N) → Set
  P u = ⟦_⟧ {₂₊ N} (T ^' toℕ u) ≡ u

  step : ∀ (i : Fin (₁₊ N)) → P (inject₁ i) → P (suc i)
  step i ih =
    trans (sem-suc (toℕ i))
    (trans (cong (_+ ₁)
              (subst (λ z → ⟦_⟧ {₂₊ N} (T ^' z) ≡ inject₁ i)
                     (FP.toℕ-inject₁ i) ih))
           (inj+1 i))

------------------------------------------------------------------------
-- Semantic injectivity of the normal-form section

-- Normal forms with equal denotations are equal.  N = 0 is decided by
-- injectivity of the integer embedding, N = 1 is trivial (ℤ/1ℤ is a
-- singleton), and N ≥ 2 uses pow-id.
unique-lemma : ∀ n {u v : NF n} → ⟦_⟧ {n} [ u ] ≡ ⟦_⟧ {n} [ v ] → u ≡ v
unique-lemma zero          {u} {v}       eq =
  cong Int.∣_∣ (trans (sym (sem0 u)) (trans eq (sem0 v)))
unique-lemma (suc zero)    {zero} {zero} eq = refl
unique-lemma (suc (suc N)) {u} {v}       eq =
  trans (sym (pow-id u)) (trans eq (pow-id v))

------------------------------------------------------------------------
-- Unique normal form for the semantics

-- The normal form of Examples.Groups.Cyclic.Normalization is unique
-- for the ℤ/Nℤ semantics: the NormalForm witness is packaged together
-- with uniqueness, given by unique-lemma.
unique-nf : ∀ n → NFBase.UniqueNormalForm
  (pres n) (NF n) (Eq.setoid (Cn n)) (⟦_⟧ {n}) (nfp' n)
unique-nf n = record
  { unique = unique-lemma n
  }
