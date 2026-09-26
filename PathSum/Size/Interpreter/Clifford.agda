------------------------------------------------------------------------
-- Presentations of groups
--
-- The sparse interpreter over {H, S, CZ} (for Amy, QPL 2018,
-- corollary 2.15)
--
-- PathSum.Size.Interpreter (whose header has the plan) interprets
-- circuits over {H, CNOT, R_k, R_k†} on sparse data.  Here the same is
-- done for PathSum.Circuit's {H, S, CZ} and definition 2.9's ⟦ C ⟧,
-- where a Hadamard always allocates a path variable (runᵁ).  Over
-- these gates a wire holds a single variable, not a form, so every
-- gate prepends exactly one term: S on a wire holding u adds ¼ u, CZ
-- on wires holding u and v adds ½ u v, and H adds ½ u y₀ after
-- reading the other terms with the fresh y₀ (runᶜˢ).  So the result
-- has exactly |C| terms (interpᶜ-length), each of degree at most 2
-- (interpᶜ-small), and at most 2 (n + |C| + M + 1)^2 bits
-- (interpᶜ-size); it denotes ⟦ C ⟧ (interpᶜ-correct, the outputs
-- being the variables on the wires, PathSum.Size.μ-lifted).  Compacted
-- at degree 2 it has at most (n + |C| + 1)^2 terms (compactᶜ-length),
-- and is then exactly the representation PathSum.Size reads off the
-- dense phase (compactᶜ≡repᶜ).  As there, these bound the size of the
-- computation's data, not a running time, and no complexity class is
-- formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Size.Interpreter.Clifford (M : ℕ) where

open import Data.Fin.Base using (Fin; zero)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import PathSum.Base using (PathSum; ⟨_,_⟩)
open import PathSum.Circuit M using (wkPoly)
open import PathSum.Linear using (varᴸ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using
  (Var; x[_]; y[_]; ⟪_⟫; ∥_∥; _∪ᵐ_; _≈[_]_; _·ᴾ_; μ)
open import PathSum.Polynomial.Product using (≈-sym)
open import PathSum.Polynomial.Properties using (i∣0; ∥⟪v⟫∥≡1; ∥∪ᵐ∥≤)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Size M using (μ-lifted; paths≤lengthᶜ; repᶜ)
open import PathSum.Size.Interpreter M using
  (Denotes; denotes; denotes-paths; denotes-represents; compact;
   denotes-compact; compact-length; size-bound-list)
open import PathSum.Size.Sparse M using
  (Term; ⟦_⟧ˢ; Rep; rep; terms; Represents; Small; size; residue;
   sparse; size-bound)
open import PathSum.Size.Terms M using
  (≈-++; wkᵀ; wk-≈; term-≈; sparse-cong)

import Data.List.Properties as List
import Data.List.Relation.Unary.All.Properties as AllP
import Data.Nat.Properties as ℕ
import PathSum.Circuit

private
  module Q = PathSum.Circuit M

open Q using (_[_↦_])

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The interpreter

-- A list of terms, and the variable on each wire.

Stateᶜ : ℕ → ℕ → Set
Stateᶜ n m = List (Term n m) × (Fin n → Var n m)

initᶜ : Stateᶜ n 0
initᶜ = [] , x[_]

-- The terms each gate adds.

termS : Fin n → (Fin n → Var n m) → Term n m
termS w σ = ⟪ σ w ⟫ , residue ¼

termCZ : Fin n → Fin n → (Fin n → Var n m) → Term n m
termCZ w v σ = ⟪ σ w ⟫ ∪ᵐ ⟪ σ v ⟫ , residue ½

termH : Fin n → (Fin n → Var n m) → Term n (suc m)
termH w σ = ⟪ Q.wkVar (σ w) ⟫ ∪ᵐ ⟪ y[ zero ] ⟫ , residue ½

stepSˢ : Fin n → Stateᶜ n m → Stateᶜ n m
stepSˢ w (ts , σ) = termS w σ ∷ ts , σ

stepCZˢ : Fin n → Fin n → Stateᶜ n m → Stateᶜ n m
stepCZˢ w v (ts , σ) = termCZ w v σ ∷ ts , σ

allocHˢ : Fin n → Stateᶜ n m → Stateᶜ n (suc m)
allocHˢ w (ts , σ) =
  termH w σ ∷ map wkᵀ ts , (λ v → Q.wkVar (σ v)) [ w ↦ y[ zero ] ]

runᶜˢ : Q.Circuit n → Stateᶜ n m → ∃ (Stateᶜ n)
runᶜˢ []            s = _ , s
runᶜˢ (Q.H w ∷ C)    s = runᶜˢ C (allocHˢ w s)
runᶜˢ (Q.S w ∷ C)    s = runᶜˢ C (stepSˢ w s)
runᶜˢ (Q.CZ w v ∷ C) s = runᶜˢ C (stepCZˢ w v s)

-- The result as a representation: the forms are the variables.

toRep : Stateᶜ n m → Rep n m
toRep (ts , σ) = rep ts (λ w → varᴸ (σ w))

interpᶜ : Q.Circuit n → ∃ (Rep n)
interpᶜ C = proj₁ (runᶜˢ C initᶜ) , toRep (proj₂ (runᶜˢ C initᶜ))


------------------------------------------------------------------------
-- Correctness

data Agreeᶜ {n : ℕ} : ∃ (Stateᶜ n) → ∃ (Q.State n) → Set where
  agreeᶜ : ∀ {m} (ts : List (Term n m)) (st : Q.State n m) →
          Q.poly st ≈[ pow M ] ⟦ ts ⟧ˢ →
          Agreeᶜ (m , (ts , Q.sig st)) (m , st)

runᶜˢ-agree : (C : Q.Circuit n) (ts : List (Term n m)) (st : Q.State n m) →
              Q.poly st ≈[ pow M ] ⟦ ts ⟧ˢ →
              Agreeᶜ (runᶜˢ C (ts , Q.sig st)) (Q.runᵁ C st)
runᶜˢ-agree []            ts st h = agreeᶜ ts st h
runᶜˢ-agree (Q.H w ∷ C)    ts st h =
  runᶜˢ-agree C (termH w (Q.sig st) ∷ map wkᵀ ts) (Q.allocH w st)
    (≈-++ {P = wkPoly (Q.poly st)} {Q = ½ ·ᴾ Q.mono δ} (map wkᵀ ts)
          (termH w (Q.sig st) ∷ []) (wk-≈ {P = Q.poly st} ts h)
          (term-≈ ½ δ))
  where
  δ = ⟪ Q.wkVar (Q.sig st w) ⟫ ∪ᵐ ⟪ y[ zero ] ⟫
runᶜˢ-agree (Q.S w ∷ C)    ts st h =
  runᶜˢ-agree C (termS w (Q.sig st) ∷ ts) (Q.stepS w st)
    (≈-++ {P = Q.poly st} {Q = ¼ ·ᴾ Q.mono ⟪ Q.sig st w ⟫} ts
          (termS w (Q.sig st) ∷ []) h (term-≈ ¼ ⟪ Q.sig st w ⟫))
runᶜˢ-agree (Q.CZ w v ∷ C) ts st h =
  runᶜˢ-agree C (termCZ w v (Q.sig st) ∷ ts) (Q.stepCZ w v st)
    (≈-++ {P = Q.poly st} {Q = ½ ·ᴾ Q.mono δ} ts
          (termCZ w v (Q.sig st) ∷ []) h (term-≈ ½ δ))
  where
  δ = ⟪ Q.sig st w ⟫ ∪ᵐ ⟪ Q.sig st v ⟫

private
  psᵈ : ∀ {k} (q : ∃ (Q.State n)) → PathSum n k (proj₁ q)
  psᵈ q = ⟨ Q.poly (proj₂ q) , (λ w → μ (Q.sig (proj₂ q) w)) ⟩

  agree⇒denotes : ∀ {k} (p : ∃ (Stateᶜ n)) (q : ∃ (Q.State n)) →
                  Agreeᶜ p q →
                  Denotes (psᵈ {k = k} q) (proj₁ p , toRep (proj₂ p))
  agree⇒denotes _ _ (agreeᶜ ts st h) =
    denotes (toRep (ts , Q.sig st)) (h , λ w γ → μ-lifted (Q.sig st w) γ)

-- The interpreter computes ⟦ C ⟧.

interpᶜ-agree : (C : Q.Circuit n) →
                Agreeᶜ (runᶜˢ C initᶜ) (Q.runᵁ C Q.init)
interpᶜ-agree {n} C = runᶜˢ-agree C [] (Q.init {n}) (λ γ → i∣0)

interpᶜ-correct : (C : Q.Circuit n) → Denotes Q.⟦ C ⟧ (interpᶜ C)
interpᶜ-correct C = agree⇒denotes {k = Q.norm C} (runᶜˢ C initᶜ)
  (Q.runᵁ C Q.init) (interpᶜ-agree C)

interpᶜ-paths : (C : Q.Circuit n) → proj₁ (interpᶜ C) ≡ Q.pathsᵁ C
interpᶜ-paths C = denotes-paths (interpᶜ C) (interpᶜ-correct C)

interpᶜ-represents : (C : Q.Circuit n) →
  Represents Q.⟦ C ⟧ (subst (Rep n) (interpᶜ-paths C) (proj₂ (interpᶜ C)))
interpᶜ-represents C = denotes-represents (interpᶜ C) (interpᶜ-correct C)

interpᶜ-paths≤ : (C : Q.Circuit n) → proj₁ (interpᶜ C) ≤ length C
interpᶜ-paths≤ C =
  ℕ.≤-trans (ℕ.≤-reflexive (interpᶜ-paths C)) (paths≤lengthᶜ C)


------------------------------------------------------------------------
-- One term per gate

runᶜˢ-length : (C : Q.Circuit n) (s : Stateᶜ n m) →
               length (proj₁ (proj₂ (runᶜˢ C s))) ≡
               length C + length (proj₁ s)
runᶜˢ-length []            s = refl
runᶜˢ-length (Q.H w ∷ C)    (ts , σ) = trans
  (runᶜˢ-length C (allocHˢ w (ts , σ)))
  (trans (cong (λ z → length C + suc z)
               (List.length-map wkᵀ ts))
         (ℕ.+-suc (length C) (length ts)))
runᶜˢ-length (Q.S w ∷ C)    (ts , σ) = trans
  (runᶜˢ-length C (stepSˢ w (ts , σ))) (ℕ.+-suc (length C) (length ts))
runᶜˢ-length (Q.CZ w v ∷ C) (ts , σ) = trans
  (runᶜˢ-length C (stepCZˢ w v (ts , σ)))
  (ℕ.+-suc (length C) (length ts))

interpᶜ-length : (C : Q.Circuit n) →
                 length (terms (proj₂ (interpᶜ C))) ≡ length C
interpᶜ-length C =
  trans (runᶜˢ-length C initᶜ) (ℕ.+-identityʳ (length C))

-- Each of degree at most 2.

private
  ∥⟪⟫∪⟪⟫∥≤2 : (u v : Var n m) → ∥ ⟪ u ⟫ ∪ᵐ ⟪ v ⟫ ∥ ≤ 2
  ∥⟪⟫∪⟪⟫∥≤2 u v = ℕ.≤-trans (∥∪ᵐ∥≤ ⟪ u ⟫ ⟪ v ⟫)
    (ℕ.≤-reflexive (cong₂ _+_ (∥⟪v⟫∥≡1 u) (∥⟪v⟫∥≡1 v)))

runᶜˢ-small : (C : Q.Circuit n) (s : Stateᶜ n m) →
              All (λ t → ∥ proj₁ t ∥ ≤ 2) (proj₁ s) →
              All (λ t → ∥ proj₁ t ∥ ≤ 2) (proj₁ (proj₂ (runᶜˢ C s)))
runᶜˢ-small []            s        small = small
runᶜˢ-small (Q.H w ∷ C)    (ts , σ) small = runᶜˢ-small C (allocHˢ w (ts , σ))
  (∥⟪⟫∪⟪⟫∥≤2 (Q.wkVar (σ w)) y[ zero ] ∷ AllP.map⁺ {f = wkᵀ} small)
runᶜˢ-small (Q.S w ∷ C)    (ts , σ) small = runᶜˢ-small C (stepSˢ w (ts , σ))
  (ℕ.≤-trans (ℕ.≤-reflexive (∥⟪v⟫∥≡1 (σ w))) (s≤s z≤n) ∷ small)
runᶜˢ-small (Q.CZ w v ∷ C) (ts , σ) small =
  runᶜˢ-small C (stepCZˢ w v (ts , σ)) (∥⟪⟫∪⟪⟫∥≤2 (σ w) (σ v) ∷ small)

interpᶜ-small : (C : Q.Circuit n) → Small 2 (proj₂ (interpᶜ C))
interpᶜ-small C = runᶜˢ-small C initᶜ []

-- At most 2 (n + |C| + M + 1)^2 bits.

interpᶜ-size : (C : Q.Circuit n) →
               size (proj₂ (interpᶜ C)) ≤ 2 * suc (n + length C + M) ^ 2
interpᶜ-size C = size-bound-list 0 (length C) (proj₂ (interpᶜ C))
  (interpᶜ-paths≤ C)
  (ℕ.≤-reflexive (trans (interpᶜ-length C)
                        (sym (ℕ.*-identityʳ (length C)))))


------------------------------------------------------------------------
-- Compaction

compactᶜ : Q.Circuit n → ∃ (Rep n)
compactᶜ C = proj₁ (interpᶜ C) , compact 2 (proj₂ (interpᶜ C))

compactᶜ-correct : (C : Q.Circuit n) → Denotes Q.⟦ C ⟧ (compactᶜ C)
compactᶜ-correct C = denotes-compact 2 (interpᶜ C) (interpᶜ-correct C)
  (interpᶜ-small C)

-- It is exactly the representation PathSum.Size reads off the dense
-- phase, repᶜ C.

compactᶜ≡repᶜ : (C : Q.Circuit n) → compactᶜ C ≡ (Q.pathsᵁ C , repᶜ C)
compactᶜ≡repᶜ C = by-agree (runᶜˢ C initᶜ) (Q.runᵁ C Q.init)
  (interpᶜ-agree C)
  where
  by-agree : (p : ∃ (Stateᶜ n)) (q : ∃ (Q.State n)) → Agreeᶜ p q →
             (proj₁ p , compact 2 (toRep (proj₂ p))) ≡
             (proj₁ q , rep (sparse 2 (Q.poly (proj₂ q)))
                            (λ w → varᴸ (Q.sig (proj₂ q) w)))
  by-agree _ _ (agreeᶜ {m} ts st h) =
    cong (λ us → (m , rep us (λ w → varᴸ (Q.sig st w))))
         (sparse-cong 2 {P = ⟦ ts ⟧ˢ} {Q = Q.poly st}
                      (≈-sym {P = Q.poly st} {Q = ⟦ ts ⟧ˢ} h))

compactᶜ-length : (C : Q.Circuit n) →
                  length (terms (proj₂ (compactᶜ C))) ≤ suc (n + length C) ^ 2
compactᶜ-length {n} C = ℕ.≤-trans
  (compact-length 2 (proj₂ (interpᶜ C)))
  (ℕ.^-monoˡ-≤ 2 (s≤s (ℕ.+-monoʳ-≤ n (interpᶜ-paths≤ C))))

compactᶜ-size : (C : Q.Circuit n) →
                size (proj₂ (compactᶜ C)) ≤ 2 * suc (n + length C + M) ^ 3
compactᶜ-size C = size-bound 2 (length C) (proj₂ (compactᶜ C)) (s≤s z≤n)
  (interpᶜ-paths≤ C) (compact-length 2 (proj₂ (interpᶜ C)))


------------------------------------------------------------------------
-- Corollary 2.15, computed

corollary-2-15ᶜ-sparse : (C : Q.Circuit n) →
  Denotes Q.⟦ C ⟧ (interpᶜ C) ×
  length (terms (proj₂ (interpᶜ C))) ≡ length C ×
  Small 2 (proj₂ (interpᶜ C)) ×
  size (proj₂ (interpᶜ C)) ≤ 2 * suc (n + length C + M) ^ 2 ×
  Denotes Q.⟦ C ⟧ (compactᶜ C) ×
  length (terms (proj₂ (compactᶜ C))) ≤ suc (n + length C) ^ 2
corollary-2-15ᶜ-sparse C =
  interpᶜ-correct C , interpᶜ-length C , interpᶜ-small C ,
  interpᶜ-size C , compactᶜ-correct C , compactᶜ-length C
