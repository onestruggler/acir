------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness (Lemma 3.5): every relation of Table 1 holds in
-- Uₙ(𝔻[ω]).
--
-- The relations (4)–(9) say that generators with disjoint indices
-- commute, which holds for any indices (EmbedAction.comm-sound).  Each
-- of the others involves at most four indices in a known order, so it
-- is the image, under an increasing embedding, of the same relation in
-- dimension at most 4, where both sides are concrete matrices over
-- 𝔻[ω] and are compared by computation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Soundness where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ ; suc ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (recompute)

open import Word.Base

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Embedding
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics

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
-- equations are proved in an opaque block that unfolds the action, the
-- vector updates and the arithmetic of 𝔻[ω], which the matrices of
-- concrete words compute through.

private
  -- (1)–(3)
  l1 : Word (Gen 1)
  l1 = ω f0¹ ^ 8
  l2 l3 : Word (Gen 2)
  l2 = H f0² f1² 0<1² ^ 2
  l3 = X f0² f1² 0<1² ^ 2

  -- (10)–(11)
  l10 r10 l11 r11 : Word (Gen 2)
  l10 = X f0² f1² 0<1² • ω f1²
  r10 = ω f0² • X f0² f1² 0<1²
  l11 = X f0² f1² 0<1² • ω f0²
  r11 = ω f1² • X f0² f1² 0<1²

  -- (12)–(15), with the indices 0 < 1 < 2.
  l12 r12 l13 r13 l14 r14 l15 r15 : Word (Gen 3)
  l12 = X f0³ f1³ 0<1³ • X f0³ f2³ 0<2³
  r12 = X f1³ f2³ 1<2³ • X f0³ f1³ 0<1³
  l13 = X f1³ f2³ 1<2³ • X f0³ f1³ 0<1³
  r13 = X f0³ f2³ 0<2³ • X f1³ f2³ 1<2³
  l14 = X f0³ f1³ 0<1³ • H f0³ f2³ 0<2³
  r14 = H f1³ f2³ 1<2³ • X f0³ f1³ 0<1³
  l15 = X f1³ f2³ 1<2³ • H f0³ f1³ 0<1³
  r15 = H f0³ f2³ 0<2³ • X f1³ f2³ 1<2³

  -- (16)–(19)
  l16 r16 l17 r17 l18 r18 l19 r19 : Word (Gen 2)
  l16 = ω f0² • ω f1² • X f0² f1² 0<1²
  r16 = X f0² f1² 0<1² • ω f0² • ω f1²
  l17 = ω f0² • ω f1² • H f0² f1² 0<1²
  r17 = H f0² f1² 0<1² • ω f0² • ω f1²
  l18 = H f0² f1² 0<1² • X f0² f1² 0<1²
  r18 = ω f1² ^ 4 • H f0² f1² 0<1²
  l19 = H f0² f1² 0<1² • ω f0² ^ 2 • H f0² f1² 0<1²
  r19 = ω f0² ^ 6 • H f0² f1² 0<1² • ω f0² ^ 3 • ω f1² ^ 5

  -- (20)
  l20 r20 : Word (Gen 4)
  l20 = H f0⁴ f1⁴ 0<1⁴ • H f2⁴ f3⁴ 2<3⁴ • H f0⁴ f2⁴ 0<2⁴ • H f1⁴ f3⁴ 1<3⁴
  r20 = H f0⁴ f2⁴ 0<2⁴ • H f1⁴ f3⁴ 1<3⁴ • H f0⁴ f1⁴ 0<1⁴ • H f2⁴ f3⁴ 2<3⁴

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  private
    order-ω₁ : ⟦ l1 ⟧ᵐ ≡ ⟦ ε ⟧ᵐ
    order-ω₁ = refl

    order-H₂ : ⟦ l2 ⟧ᵐ ≡ ⟦ ε ⟧ᵐ
    order-H₂ = refl

    order-X₂ : ⟦ l3 ⟧ᵐ ≡ ⟦ ε ⟧ᵐ
    order-X₂ = refl

    swap-Xω₂ : ⟦ l10 ⟧ᵐ ≡ ⟦ r10 ⟧ᵐ
    swap-Xω₂ = refl

    swap-Xω′₂ : ⟦ l11 ⟧ᵐ ≡ ⟦ r11 ⟧ᵐ
    swap-Xω′₂ = refl

    swap-XX₃ : ⟦ l12 ⟧ᵐ ≡ ⟦ r12 ⟧ᵐ
    swap-XX₃ = refl

    swap-XX′₃ : ⟦ l13 ⟧ᵐ ≡ ⟦ r13 ⟧ᵐ
    swap-XX′₃ = refl

    swap-XH₃ : ⟦ l14 ⟧ᵐ ≡ ⟦ r14 ⟧ᵐ
    swap-XH₃ = refl

    swap-XH′₃ : ⟦ l15 ⟧ᵐ ≡ ⟦ r15 ⟧ᵐ
    swap-XH′₃ = refl

    scalar-X₂ : ⟦ l16 ⟧ᵐ ≡ ⟦ r16 ⟧ᵐ
    scalar-X₂ = refl

    scalar-H₂ : ⟦ l17 ⟧ᵐ ≡ ⟦ r17 ⟧ᵐ
    scalar-H₂ = refl

    rel-18₂ : ⟦ l18 ⟧ᵐ ≡ ⟦ r18 ⟧ᵐ
    rel-18₂ = refl

    rel-19₂ : ⟦ l19 ⟧ᵐ ≡ ⟦ r19 ⟧ᵐ
    rel-19₂ = refl

    rel-20₄ : ⟦ l20 ⟧ᵐ ≡ ⟦ r20 ⟧ᵐ
    rel-20₄ = refl

------------------------------------------------------------------------
-- Soundness of the axioms

-- Relevant proofs of order, recomputed from irrelevant ones.
private
  rc : {a b : Fin n} → .(a < b) → a < b
  rc {a = a} {b} p = recompute (a FinP.<? b) p

sound-axiom : {w v : Word (Gen n)} → w === v → ⟦ w ⟧ᵐ ≡ ⟦ v ⟧ᵐ
sound-axiom (order-ω {j = j}) = emb-sound (emb₁ j) l1 ε order-ω₁
sound-axiom (order-H {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l2 ε order-H₂
sound-axiom (order-X {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l3 ε order-X₂
sound-axiom (comm-ωω {j = j} {k = k} jk) =
  comm-sound (ω-gen j) (ω-gen k) λ { x i-a i-a → jk refl }
sound-axiom (comm-ωH {k = k} {l = l} {j = j} p jk jl) =
  comm-sound (ω-gen j) (H-gen k l p) λ { x i-a K-a → jk refl ; x i-a K-b → jl refl }
sound-axiom (comm-ωX {k = k} {l = l} {j = j} p jk jl) =
  comm-sound (ω-gen j) (X-gen k l p) λ { x i-a X-a → jk refl ; x i-a X-b → jl refl }
sound-axiom (comm-HH {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  comm-sound (H-gen j k p) (H-gen l m q)
    λ { x K-a K-a → jl refl ; x K-a K-b → jm refl ; x K-b K-a → kl refl ; x K-b K-b → km refl }
sound-axiom (comm-HX {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  comm-sound (H-gen j k p) (X-gen l m q)
    λ { x K-a X-a → jl refl ; x K-a X-b → jm refl ; x K-b X-a → kl refl ; x K-b X-b → km refl }
sound-axiom (comm-XX {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  comm-sound (X-gen j k p) (X-gen l m q)
    λ { x X-a X-a → jl refl ; x X-a X-b → jm refl ; x X-b X-a → kl refl ; x X-b X-b → km refl }
sound-axiom (swap-Xω {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l10 r10 swap-Xω₂
sound-axiom (swap-Xω′ {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l11 r11 swap-Xω′₂
sound-axiom (swap-XX {j = j} {k = k} {l = l} p q) = emb-sound (emb₃ j k l (rc p) (rc q)) l12 r12 swap-XX₃
sound-axiom (swap-XX′ {l = l} {j = j} {k = k} p q) = emb-sound (emb₃ l j k (rc p) (rc q)) l13 r13 swap-XX′₃
sound-axiom (swap-XH {j = j} {k = k} {l = l} p q) = emb-sound (emb₃ j k l (rc p) (rc q)) l14 r14 swap-XH₃
sound-axiom (swap-XH′ {l = l} {j = j} {k = k} p q) = emb-sound (emb₃ l j k (rc p) (rc q)) l15 r15 swap-XH′₃
sound-axiom (scalar-X {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l16 r16 scalar-X₂
sound-axiom (scalar-H {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l17 r17 scalar-H₂
sound-axiom (rel-18 {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l18 r18 rel-18₂
sound-axiom (rel-19 {j = j} {k = k} p) = emb-sound (emb₂ j k (rc p)) l19 r19 rel-19₂
sound-axiom (rel-20 {j = j} {k = k} {l = l} {m = m} jk kl lm) =
  emb-sound (emb₄ j k l m (rc jk) (rc kl) (rc lm)) l20 r20 rel-20₄
