------------------------------------------------------------------------
-- Presentations of groups
--
-- Gates on the bottom wires, and the shift
--
-- A generator is a gate on the bottom one or two wires, or a generator
-- shifted up a wire.  This module gives both their operators —
--
--     emb M = M ⊗ I      a k-wire matrix acting on wires 0 … k−1,
--     up  M = I₂ ⊗ M     an operator moved up one wire —
--
-- and proves what the interpretation needs of them.  Everything is an
-- instance of the mixed product law Algebra.tensor-⊙: products of local
-- gates are local (emb-⊙), shifts compose (up-⊙), and a bottom gate
-- commutes with anything shifted past it (emb-up-comm) because both
-- orders are M ⊗ N.  That last one is comm₁ and comm₂ at once.
--
-- The level-raising lemmas emb-pad / up-emb are what let a relation
-- whose letters live on different wires be checked at a single width.
-- They are stated at the concrete widths 1 and 2 because the general
-- statement does not typecheck: (k + 1) + n and k + (1 + n) are only
-- propositionally equal, while for a literal k they are definitional.
--
-- This is Examples.Groups.Clifford.Qubit.Model.Local over ℤ[√2].
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Semantics.Local where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra

private
  variable
    k l m n : ℕ

------------------------------------------------------------------------
-- The two constructions

-- A k-wire matrix, acting on the bottom k wires of k + n.
emb : Mat k → Op (k +ℕ n)
emb M = tensor (ix M) Idₒ

-- An operator moved up one wire.
up : Op n → Op (₁₊ n)
up M = tensor (Idₒ {1}) M

-- ... and up k wires, which is what comm₁ and comm₂ shift past.
upk : (k : ℕ) → Op n → Op (k +ℕ n)
upk k M = tensor (Idₒ {k}) M

emb-cong : {M N : Mat k} → ix M ≐ ix N → emb {k} {n} M ≐ emb N
emb-cong e = tensor-cong e (≐-refl Idₒ)

up-cong : {M N : Op n} → M ≐ N → up M ≐ up N
up-cong e = tensor-cong (≐-refl Idₒ) e

------------------------------------------------------------------------
-- Products

emb-⊙ : (M N : Mat k) → (emb {k} {n} M ⊙ emb N) ≐ emb (mulM M N)
emb-⊙ {k} {n} M N =
  ≐-trans (tensor-⊙ (ix M) (ix N) Idₒ Idₒ)
          (tensor-cong (≐-sym (ix-mul M N)) (⊙-identityˡ Idₒ))

emb-id : emb {k} {n} idM ≐ Idₒ
emb-id {k} {n} =
  ≐-trans (tensor-cong {m = k} {n = n} ix-id (≐-refl Idₒ))
          (≐-sym (tensor-Id {m = k} {n = n}))

up-⊙ : (M N : Op n) → (up M ⊙ up N) ≐ up (M ⊙ N)
up-⊙ M N =
  ≐-trans (tensor-⊙ Idₒ Idₒ M N) (tensor-cong (⊙-identityˡ Idₒ) (≐-refl (M ⊙ N)))

up-Id : up (Idₒ {n}) ≐ Idₒ
up-Id {n} = ≐-sym (tensor-Id {m = 1} {n = n})

------------------------------------------------------------------------
-- Commutation
--
-- A gate on the bottom k wires and an operator shifted up past them
-- commute: both products are ix M ⊗ N.  With k = 1 this is comm₁ and
-- with k = 2 comm₂.

emb-up-comm : (M : Mat k) (N : Op n) →
              (emb {k} {n} M ⊙ upk k N) ≐ (upk k N ⊙ emb M)
emb-up-comm {k} {n} M N =
  ≐-trans (tensor-⊙ (ix M) Idₒ Idₒ N)
    (≐-trans (tensor-cong (⊙-identityʳ (ix M)) (⊙-identityˡ N))
      (≐-trans (tensor-cong (≐-sym (⊙-identityˡ (ix M))) (≐-sym (⊙-identityʳ N)))
               (≐-sym (tensor-⊙ Idₒ (ix M) N Idₒ))))

-- Two shifts are a shift by two, which is the form comm₂ wants.
up-up : (M : Op n) → up (up M) ≐ upk 2 M
up-up M (a ∷ b ∷ x) (a' ∷ b' ∷ y) =
  Eq.sym (Eq.trans (Eq.cong (_* M x y)
                     (tensor-Id {1} {1} (a ∷ b ∷ []) (a' ∷ b' ∷ [])))
                   (*-assoc (δb (a ∷ []) (a' ∷ [])) (δb (b ∷ []) (b' ∷ [])) (M x y)))

------------------------------------------------------------------------
-- Raising a gate to a wider block
--
-- A gate on the bottom wires of a k-wire block is the same gate on the
-- bottom wires of a wider block, with the extra wires idle; a shifted
-- one is the same with an idle wire below.  These are what let a whole
-- circuit at width k, read at width k + n, be recognised as one matrix
-- (Interpretation.localise).

-- A scalar factor passes through the first argument of ⊗.
tensor-scaleˡ : (s : 𝔽) (B : Op m) (C : Op n) → ∀ x y →
                tensor (λ u v → s * B u v) C x y ≡ s * tensor B C x y
tensor-scaleˡ {₀}    s B C x       y       = *-assoc s (B [] []) (C x y)
tensor-scaleˡ {₁₊ m} s B C (a ∷ x) (b ∷ y) =
  tensor-scaleˡ {m} s (λ u v → B (a ∷ u) (b ∷ v)) C x y

tensor-assoc₁ : (A : Op 1) (B : Op m) (C : Op n) →
                tensor (tensor A B) C ≐ tensor A (tensor B C)
tensor-assoc₁ A B C (a ∷ x) (b ∷ y) =
  tensor-scaleˡ (A (a ∷ []) (b ∷ [])) B C x y

tensor-assoc₂ : (A : Op 2) (B : Op m) (C : Op n) →
                tensor (tensor A B) C ≐ tensor A (tensor B C)
tensor-assoc₂ A B C (a ∷ a' ∷ x) (b ∷ b' ∷ y) =
  tensor-scaleˡ (A (a ∷ a' ∷ []) (b ∷ b' ∷ [])) B C x y

tensor-assoc₃ : (A : Op 3) (B : Op m) (C : Op n) →
                tensor (tensor A B) C ≐ tensor A (tensor B C)
tensor-assoc₃ A B C (a ∷ a' ∷ a'' ∷ x) (b ∷ b' ∷ b'' ∷ y) =
  tensor-scaleˡ (A (a ∷ a' ∷ a'' ∷ []) (b ∷ b' ∷ b'' ∷ [])) B C x y

emb-pad₁ : (M : Mat 1) → emb {1} {m +ℕ n} M ≐ emb {₁₊ m} {n} (tenM M (idM {m}))
emb-pad₁ {m} {n} M =
  ≐-trans (tensor-cong {m = 1} {n = m +ℕ n} (≐-refl (ix M)) (tensor-Id {m} {n}))
    (≐-trans (≐-sym (tensor-assoc₁ (ix M) (Idₒ {m}) (Idₒ {n})))
             (tensor-cong (≐-sym (≐-trans (ix-tenM M (idM {m}))
                                          (tensor-cong (≐-refl (ix M)) ix-id)))
                          (≐-refl Idₒ)))

emb-pad₂ : (M : Mat 2) → emb {2} {m +ℕ n} M ≐ emb {₂₊ m} {n} (tenM M (idM {m}))
emb-pad₂ {m} {n} M =
  ≐-trans (tensor-cong {m = 2} {n = m +ℕ n} (≐-refl (ix M)) (tensor-Id {m} {n}))
    (≐-trans (≐-sym (tensor-assoc₂ (ix M) (Idₒ {m}) (Idₒ {n})))
             (tensor-cong (≐-sym (≐-trans (ix-tenM M (idM {m}))
                                          (tensor-cong (≐-refl (ix M)) ix-id)))
                          (≐-refl Idₒ)))

emb-pad₃ : (M : Mat 3) → emb {3} {m +ℕ n} M ≐ emb {₃₊ m} {n} (tenM M (idM {m}))
emb-pad₃ {m} {n} M =
  ≐-trans (tensor-cong {m = 3} {n = m +ℕ n} (≐-refl (ix M)) (tensor-Id {m} {n}))
    (≐-trans (≐-sym (tensor-assoc₃ (ix M) (Idₒ {m}) (Idₒ {n})))
             (tensor-cong (≐-sym (≐-trans (ix-tenM M (idM {m}))
                                          (tensor-cong (≐-refl (ix M)) ix-id)))
                          (≐-refl Idₒ)))

up-emb : (M : Mat k) → up (emb {k} {n} M) ≐ emb {₁₊ k} {n} (tenM (idM {1}) M)
up-emb {k} {n} M =
  ≐-trans (≐-sym (tensor-assoc₁ (Idₒ {1}) (ix M) (Idₒ {n})))
          (tensor-cong (≐-sym (≐-trans (ix-tenM (idM {1}) M)
                                       (tensor-cong ix-id (≐-refl (ix M)))))
                       (≐-refl Idₒ))
