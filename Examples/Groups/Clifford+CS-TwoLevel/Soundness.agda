------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness (Remark in §3.1): every relation of Figure 1 holds in
-- Uₙ(𝔻[i]).
--
-- The relations (4)–(9) say that generators with disjoint indices
-- commute, which holds for any indices (EmbedAction.comm-sound).  Each
-- of the others involves at most four indices in a known order, so it
-- is the image, under an increasing embedding, of the same relation in
-- dimension at most 4, where both sides are concrete matrices over
-- 𝔻[i] and are compared by computation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Soundness where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ ; suc ; z≤n ; s≤s)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (recompute)
open import Data.Empty using (⊥-elim)

open import Quantum.Synthesis.Matrix using (_·*·_)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)
open import Quantum.Synthesis.Ring.Properties using (isCommutativeRing-DComplex ; adj-DComplex)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (ⅈ ; γ⁻)
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Embedding
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics


private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Concrete indices

private
  -- Dimension 1.
  f0¹ : Fin 1
  f0¹ = zero

  -- Dimension 2.
  f0² f1² : Fin 2
  f0² = zero
  f1² = suc zero
  0<1² : f0² < f1²
  0<1² = s≤s z≤n

  -- Dimension 3.
  f0³ f1³ f2³ : Fin 3
  f0³ = zero
  f1³ = suc zero
  f2³ = suc (suc zero)
  0<1³ : f0³ < f1³
  0<1³ = s≤s z≤n
  0<2³ : f0³ < f2³
  0<2³ = s≤s z≤n
  1<2³ : f1³ < f2³
  1<2³ = s≤s (s≤s z≤n)

  -- Dimension 4.
  f0⁴ f1⁴ f2⁴ f3⁴ : Fin 4
  f0⁴ = zero
  f1⁴ = suc zero
  f2⁴ = suc (suc zero)
  f3⁴ = suc (suc (suc zero))
  0<1⁴ : f0⁴ < f1⁴
  0<1⁴ = s≤s z≤n
  0<2⁴ : f0⁴ < f2⁴
  0<2⁴ = s≤s z≤n
  1<3⁴ : f1⁴ < f3⁴
  1<3⁴ = s≤s (s≤s z≤n)
  2<3⁴ : f2⁴ < f3⁴
  2<3⁴ = s≤s (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- The relations in dimension at most 4, checked by computation
--
-- The words are transparent, so that their embeddings compute; the
-- equations are proved in an opaque block that unfolds the vector
-- updates, which the matrices of concrete words must compute through.

private
  -- (1)–(3)
  l1 : Word (Gen 1)
  l1 = i f0¹ ^ 4
  l2 l3 : Word (Gen 2)
  l2 = X f0² f1² 0<1² ^ 2
  l3 = K f0² f1² 0<1² ^ 8

  -- (10)–(12′)
  l10 r10 : Word (Gen 2)
  l10 = i f1² • X f0² f1² 0<1²
  r10 = X f0² f1² 0<1² • i f0²

  l11 r11 l11′ r11′ l12 r12 l12′ r12′ : Word (Gen 3)
  l11 = X f1³ f2³ 1<2³ • X f0³ f1³ 0<1³
  r11 = X f0³ f1³ 0<1³ • X f0³ f2³ 0<2³
  l11′ = X f0³ f2³ 0<2³ • X f1³ f2³ 1<2³
  r11′ = X f1³ f2³ 1<2³ • X f0³ f1³ 0<1³
  l12 = K f1³ f2³ 1<2³ • X f0³ f1³ 0<1³
  r12 = X f0³ f1³ 0<1³ • K f0³ f2³ 0<2³
  l12′ = K f0³ f2³ 0<2³ • X f1³ f2³ 1<2³
  r12′ = X f1³ f2³ 1<2³ • K f0³ f1³ 0<1³

  -- (13)–(16)
  l13 r13 l14 r14 l15 r15 l16 : Word (Gen 2)
  l13 = K f0² f1² 0<1² • i f1² ^ 2
  r13 = X f0² f1² 0<1² • K f0² f1² 0<1²
  l14 = K f0² f1² 0<1² • i f1² ^ 3
  r14 = i f1² • K f0² f1² 0<1² • i f1² • K f0² f1² 0<1²
  l15 = K f0² f1² 0<1² • i f0² • i f1²
  r15 = i f0² • i f1² • K f0² f1² 0<1²
  l16 = K f0² f1² 0<1² ^ 2 • i f0² • i f1²

  -- (17), for the two orders of k and l.
  l17 r17 : Word (Gen 4)
  l17 = K f0⁴ f1⁴ 0<1⁴ • K f2⁴ f3⁴ 2<3⁴ • K f0⁴ f2⁴ 0<2⁴ • K f1⁴ f3⁴ 1<3⁴
  r17 = K f0⁴ f2⁴ 0<2⁴ • K f1⁴ f3⁴ 1<3⁴ • K f0⁴ f1⁴ 0<1⁴ • K f2⁴ f3⁴ 2<3⁴

opaque
  unfolding set₁ set₂

  private
    order-i₁ : ⟦ l1 ⟧ᵐ ≡ ⟦ ε ⟧ᵐ
    order-i₁ = refl

    order-X₂ : ⟦ l2 ⟧ᵐ ≡ ⟦ ε ⟧ᵐ
    order-X₂ = refl

    order-K₂ : ⟦ l3 ⟧ᵐ ≡ ⟦ ε ⟧ᵐ
    order-K₂ = refl

    swap-iX₂ : ⟦ l10 ⟧ᵐ ≡ ⟦ r10 ⟧ᵐ
    swap-iX₂ = refl

    swap-XX₃ : ⟦ l11 ⟧ᵐ ≡ ⟦ r11 ⟧ᵐ
    swap-XX₃ = refl

    swap-XX′₃ : ⟦ l11′ ⟧ᵐ ≡ ⟦ r11′ ⟧ᵐ
    swap-XX′₃ = refl

    swap-KX₃ : ⟦ l12 ⟧ᵐ ≡ ⟦ r12 ⟧ᵐ
    swap-KX₃ = refl

    swap-KX′₃ : ⟦ l12′ ⟧ᵐ ≡ ⟦ r12′ ⟧ᵐ
    swap-KX′₃ = refl

    rel-13₂ : ⟦ l13 ⟧ᵐ ≡ ⟦ r13 ⟧ᵐ
    rel-13₂ = refl

    rel-14₂ : ⟦ l14 ⟧ᵐ ≡ ⟦ r14 ⟧ᵐ
    rel-14₂ = refl

    rel-15₂ : ⟦ l15 ⟧ᵐ ≡ ⟦ r15 ⟧ᵐ
    rel-15₂ = refl

    rel-16₂ : ⟦ l16 ⟧ᵐ ≡ ⟦ ε ⟧ᵐ
    rel-16₂ = refl

    rel-17₄ : ⟦ l17 ⟧ᵐ ≡ ⟦ r17 ⟧ᵐ
    rel-17₄ = refl

    rel-17₄′ : ⟦ r17 ⟧ᵐ ≡ ⟦ l17 ⟧ᵐ
    rel-17₄′ = sym rel-17₄

------------------------------------------------------------------------
-- Soundness of the axioms

-- Relevant proofs of order, recomputed from irrelevant ones.
private
  rc : {a b : Fin n} → .(a < b) → a < b
  rc {a = a} {b} p = recompute (a FinP.<? b) p

sound-axiom : {w v : Word (Gen n)} → w === v → ⟦ w ⟧ᵐ ≡ ⟦ v ⟧ᵐ
sound-axiom (order-i {j = j}) = emb-sound (emb₁ j) l1 ε order-i₁
sound-axiom (order-X {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l2 ε order-X₂
sound-axiom (order-K {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l3 ε order-K₂
sound-axiom (comm-ii {j = j} {k = k} jk) =
  comm-sound (i-gen j) (i-gen k) λ { x i-a i-a → jk refl }
sound-axiom (comm-iX {k = k} {l = l} {j = j} p jk jl) =
  comm-sound (i-gen j) (X-gen k l p) λ { x i-a X-a → jk refl ; x i-a X-b → jl refl }
sound-axiom (comm-iK {k = k} {l = l} {j = j} p jk jl) =
  comm-sound (i-gen j) (K-gen k l p) λ { x i-a K-a → jk refl ; x i-a K-b → jl refl }
sound-axiom (comm-XX {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  comm-sound (X-gen j k p) (X-gen l m q)
    λ { x X-a X-a → jl refl ; x X-a X-b → jm refl ; x X-b X-a → kl refl ; x X-b X-b → km refl }
sound-axiom (comm-XK {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  comm-sound (X-gen j k p) (K-gen l m q)
    λ { x X-a K-a → jl refl ; x X-a K-b → jm refl ; x X-b K-a → kl refl ; x X-b K-b → km refl }
sound-axiom (comm-KK {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  comm-sound (K-gen j k p) (K-gen l m q)
    λ { x K-a K-a → jl refl ; x K-a K-b → jm refl ; x K-b K-a → kl refl ; x K-b K-b → km refl }
sound-axiom (swap-iX {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l10 r10 swap-iX₂
sound-axiom (swap-XX {j = j} {k = k} {l = l} p q) = emb-sound (emb₃ j k l p q) l11 r11 swap-XX₃
sound-axiom (swap-XX′ {j = j} {k = k} {l = l} p q) = emb-sound (emb₃ j k l p q) l11′ r11′ swap-XX′₃
sound-axiom (swap-KX {j = j} {k = k} {l = l} p q) = emb-sound (emb₃ j k l p q) l12 r12 swap-KX₃
sound-axiom (swap-KX′ {j = j} {k = k} {l = l} p q) = emb-sound (emb₃ j k l p q) l12′ r12′ swap-KX′₃
sound-axiom (rel-13 {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l13 r13 rel-13₂
sound-axiom (rel-14 {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l14 r14 rel-14₂
sound-axiom (rel-15 {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l15 r15 rel-15₂
sound-axiom (rel-16 {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l16 ε rel-16₂
sound-axiom (rel-17 {j = j} {k = k} {l = l} {m = m} jk lm jl km k≢l) =
  tri-elim (FinP.<-cmp k l)
    (λ k<l → emb-sound (emb₄ j k l m (rc jk) k<l (rc lm)) l17 r17 rel-17₄)
    (λ k≡l → ⊥-elim (k≢l k≡l))
    (λ l<k → emb-sound (emb₄ j l k m (rc jl) l<k (rc km)) r17 l17 rel-17₄′)
  where
  -- Case analysis without with-abstraction, which would normalise the
  -- goal: the matrices of four symbolic generators.
  tri-elim : ∀ {A B C X : Set} → Tri A B C → (A → X) → (B → X) → (C → X) → X
  tri-elim (tri< a _ _) f g h = f a
  tri-elim (tri≈ _ b _) f g h = g b
  tri-elim (tri> _ _ c) f g h = h c
