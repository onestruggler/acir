------------------------------------------------------------------------
-- Presentations of groups
--
-- Gates on the bottom wires, and the shift
--
-- A Figure-8 generator is either the scalar, a gate on the bottom one or
-- two wires, or a generator shifted up a wire.  This module gives the
-- last two their operators —
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
-- whose letters live on different wires be checked at a single width: a
-- one-wire gate is a two-wire gate tensored with I, and a shifted
-- one-wire gate is I tensored with it, so both sides of C5–C11 become
-- products of Mat 2 and both sides of C12–C15 products of Mat 3.  They
-- are stated at the concrete widths 1 and 2 because the general
-- statement does not typecheck: (k + 1) + n and k + (1 + n) are only
-- propositionally equal, while for a literal k they are definitional.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Model.Local where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Clifford.Qubit.Model.Algebra

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
--
-- Local gates multiply locally, and this is where a chain of operator
-- products becomes a single trie product that Agda can compute.

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
-- Scalars
--
-- The scalar operator is a local gate too — it is c · I on any number of
-- wires — which is how ω⁻¹ joins the Mat 2 computation of C10 and C11.
-- And it is width-independent, which is ω↑=ω.

tensor-scal : (c : 𝔽) → tensor (scal {m} c) (Idₒ {n}) ≐ scal {m +ℕ n} c
tensor-scal {₀}    c x y =
  Eq.cong (_* δb x y) (*-identityʳ c)
tensor-scal {₁₊ m} c (true ∷ x)  (true ∷ y)  = tensor-scal {m} c x y
tensor-scal {₁₊ m} c (false ∷ x) (false ∷ y) = tensor-scal {m} c x y
tensor-scal {₁₊ m} {n} c (true ∷ x) (false ∷ y) =
  Eq.trans (tensor-cong {m = m} {n = n}
                        {M = λ u v → c * δb (true ∷ u) (false ∷ v)}
                        {M' = λ _ _ → 0}
                        (λ u v → *-zeroʳ c) (≐-refl Idₒ) x y)
    (Eq.trans (tensor-zeroˡ {n = n} {m = m} Idₒ x y) (Eq.sym (*-zeroʳ c)))
tensor-scal {₁₊ m} {n} c (false ∷ x) (true ∷ y) =
  Eq.trans (tensor-cong {m = m} {n = n}
                        {M = λ u v → c * δb (false ∷ u) (true ∷ v)}
                        {M' = λ _ _ → 0}
                        (λ u v → *-zeroʳ c) (≐-refl Idₒ) x y)
    (Eq.trans (tensor-zeroˡ {n = n} {m = m} Idₒ x y) (Eq.sym (*-zeroʳ c)))

-- The scalar does not see the extra wire: on the diagonal the shift
-- contributes a 1, off it both sides are 0.
up-scal : (c : 𝔽) → up (scal {n} c) ≐ scal c
up-scal c (true ∷ x)  (true ∷ y)  = *-identityˡ (c * δb x y)
up-scal c (false ∷ x) (false ∷ y) = *-identityˡ (c * δb x y)
up-scal c (true ∷ x)  (false ∷ y) =
  Eq.trans (*-zeroˡ (c * δb x y)) (Eq.sym (*-zeroʳ c))
up-scal c (false ∷ x) (true ∷ y)  =
  Eq.trans (*-zeroˡ (c * δb x y)) (Eq.sym (*-zeroʳ c))

------------------------------------------------------------------------
-- Raising a gate to a wider block
--
-- A gate on the bottom wires of a k-wire block is the same gate on the
-- bottom wires of a wider block, with the extra wires idle; a shifted
-- one is the same with an idle wire below.  These are what let a whole
-- circuit at width k, read at width k + n, be recognised as one matrix
-- (Model.Gates.localise).
--
-- Associativity of ⊗ is stated only with a first factor of literal
-- arity: for a variable k, (k + m) + n and k + (m + n) are merely
-- propositionally equal, while for a literal they are definitional —
-- and arities 1 and 2 are all the gates need.

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

up-emb : (M : Mat k) → up (emb {k} {n} M) ≐ emb {₁₊ k} {n} (tenM (idM {1}) M)
up-emb {k} {n} M =
  ≐-trans (≐-sym (tensor-assoc₁ (Idₒ {1}) (ix M) (Idₒ {n})))
          (tensor-cong (≐-sym (≐-trans (ix-tenM (idM {1}) M)
                                       (tensor-cong ix-id (≐-refl (ix M)))))
                       (≐-refl Idₒ))

-- The scalar as a local gate, at any width.
scalM : 𝔽 → Mat k
scalM c = matOf (scal c)

scal-emb : (c : 𝔽) → scal {k +ℕ n} c ≐ emb {k} {n} (scalM c)
scal-emb {k} {n} c =
  ≐-trans (≐-sym (tensor-scal {k} {n} c))
          (tensor-cong (≐-sym (ix-matOf (scal {k} c))) (≐-refl Idₒ))
