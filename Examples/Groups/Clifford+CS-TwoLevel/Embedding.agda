------------------------------------------------------------------------
-- Presentations of groups
--
-- Embedding a smaller dimension: a strictly increasing map of indices
-- ι : Fin d → Fin n relabels generators, and it carries every relation
-- of Figure 1 in dimension d to the same relation in dimension n.  So
-- a relation derived in a small fixed dimension, over concrete
-- indices, holds at any increasing choice of indices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Embedding where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics

private
  variable
    d n : ℕ

------------------------------------------------------------------------
-- Increasing maps of indices

record Emb (d n : ℕ) : Set where
  field
    ι    : Fin d → Fin n
    mono : ∀ {a b : Fin d} → a < b → ι a < ι b

  injective : ∀ {a b : Fin d} → a ≢ b → ι a ≢ ι b
  injective {a} {b} a≢b with FinP.<-cmp a b
  ... | tri< a<b _ _ = λ eq → FinP.<-irrefl eq (mono a<b)
  ... | tri≈ _ a≡b _ = λ _ → a≢b a≡b
  ... | tri> _ _ b<a = λ eq → FinP.<-irrefl (sym eq) (mono b<a)

  -- Relabelling generators and words.
  gen : Gen d → Gen n
  gen (X-gen a b p) = X-gen (ι a) (ι b) (mono p)
  gen (K-gen a b p) = K-gen (ι a) (ι b) (mono p)
  gen (i-gen a)     = i-gen (ι a)

  word : Word (Gen d) → Word (Gen n)
  word = wmap gen

open Emb public

------------------------------------------------------------------------
-- Embeddings carry relations to relations

module _ (e : Emb d n) where

  private
    module D = PB (_===_ {d})
    module N = PB (_===_ {n})
    ι′ = ι e
    inj = injective e

  -- Each axiom goes to the same axiom.
  word-axiom : ∀ {w v} → w === v → word e w N.≈ word e v
  word-axiom order-i = N.axiom order-i
  word-axiom (order-X p) = N.axiom (order-X (mono e p))
  word-axiom (order-K p) = N.axiom (order-K (mono e p))
  word-axiom (comm-ii jk) = N.axiom (comm-ii (inj jk))
  word-axiom (comm-iX p jk jl) = N.axiom (comm-iX (mono e p) (inj jk) (inj jl))
  word-axiom (comm-iK p jk jl) = N.axiom (comm-iK (mono e p) (inj jk) (inj jl))
  word-axiom (comm-XX p q a b c d) = N.axiom (comm-XX (mono e p) (mono e q) (inj a) (inj b) (inj c) (inj d))
  word-axiom (comm-XK p q a b c d) = N.axiom (comm-XK (mono e p) (mono e q) (inj a) (inj b) (inj c) (inj d))
  word-axiom (comm-KK p q a b c d) = N.axiom (comm-KK (mono e p) (mono e q) (inj a) (inj b) (inj c) (inj d))
  word-axiom (swap-iX p) = N.axiom (swap-iX (mono e p))
  word-axiom (swap-XX p q) = N.axiom (swap-XX (mono e p) (mono e q))
  word-axiom (swap-XX′ p q) = N.axiom (swap-XX′ (mono e p) (mono e q))
  word-axiom (swap-KX p q) = N.axiom (swap-KX (mono e p) (mono e q))
  word-axiom (swap-KX′ p q) = N.axiom (swap-KX′ (mono e p) (mono e q))
  word-axiom (rel-13 p) = N.axiom (rel-13 (mono e p))
  word-axiom (rel-14 p) = N.axiom (rel-14 (mono e p))
  word-axiom (rel-15 p) = N.axiom (rel-15 (mono e p))
  word-axiom (rel-16 p) = N.axiom (rel-16 (mono e p))
  word-axiom (rel-17 jk lm jl km k≢l) = N.axiom (rel-17 (mono e jk) (mono e lm) (mono e jl) (mono e km) (inj k≢l))

  -- And hence derivable equations to derivable equations.
  word-≈ : ∀ {w v} → w D.≈ v → word e w N.≈ word e v
  word-≈ = PP.GenCongruence.fʷ-cong (_===_ {d}) (_===_ {n}) (gen e) word-axiom

------------------------------------------------------------------------
-- Concrete embeddings of dimensions 1 to 4

emb₁ : Fin n → Emb 1 n
emb₁ j = record { ι = λ _ → j ; mono = λ { {zero} {zero} () } }

emb₂ : (j k : Fin n) → j < k → Emb 2 n
emb₂ {n} j k jk = record { ι = ι₂ ; mono = mono₂ }
  where
  ι₂ : Fin 2 → Fin n
  ι₂ zero = j
  ι₂ (suc zero) = k
  mono₂ : ∀ {a b : Fin 2} → a < b → ι₂ a < ι₂ b
  mono₂ {zero} {suc zero} _ = jk
  mono₂ {zero} {zero} ()
  mono₂ {suc zero} {zero} ()
  mono₂ {suc zero} {suc zero} (s≤s ())

emb₃ : (j k l : Fin n) → j < k → k < l → Emb 3 n
emb₃ {n} j k l jk kl = record { ι = ι₃ ; mono = mono₃ }
  where
  ι₃ : Fin 3 → Fin n
  ι₃ zero = j
  ι₃ (suc zero) = k
  ι₃ (suc (suc zero)) = l
  mono₃ : ∀ {a b : Fin 3} → a < b → ι₃ a < ι₃ b
  mono₃ {zero} {suc zero} _ = jk
  mono₃ {zero} {suc (suc zero)} _ = FinP.<-trans jk kl
  mono₃ {suc zero} {suc (suc zero)} _ = kl
  mono₃ {zero} {zero} ()
  mono₃ {suc zero} {zero} ()
  mono₃ {suc zero} {suc zero} (s≤s ())
  mono₃ {suc (suc zero)} {zero} ()
  mono₃ {suc (suc zero)} {suc zero} (s≤s ())
  mono₃ {suc (suc zero)} {suc (suc zero)} (s≤s (s≤s ()))

emb₄ : (j k l m : Fin n) → j < k → k < l → l < m → Emb 4 n
emb₄ {n} j k l m jk kl lm = record { ι = ι₄ ; mono = mono₄ }
  where
  ι₄ : Fin 4 → Fin n
  ι₄ zero = j
  ι₄ (suc zero) = k
  ι₄ (suc (suc zero)) = l
  ι₄ (suc (suc (suc zero))) = m
  mono₄ : ∀ {a b : Fin 4} → a < b → ι₄ a < ι₄ b
  mono₄ {zero} {suc zero} _ = jk
  mono₄ {zero} {suc (suc zero)} _ = FinP.<-trans jk kl
  mono₄ {zero} {suc (suc (suc zero))} _ = FinP.<-trans jk (FinP.<-trans kl lm)
  mono₄ {suc zero} {suc (suc zero)} _ = kl
  mono₄ {suc zero} {suc (suc (suc zero))} _ = FinP.<-trans kl lm
  mono₄ {suc (suc zero)} {suc (suc (suc zero))} _ = lm
  mono₄ {zero} {zero} ()
  mono₄ {suc zero} {zero} ()
  mono₄ {suc zero} {suc zero} (s≤s ())
  mono₄ {suc (suc zero)} {zero} ()
  mono₄ {suc (suc zero)} {suc zero} (s≤s ())
  mono₄ {suc (suc zero)} {suc (suc zero)} (s≤s (s≤s ()))
  mono₄ {suc (suc (suc zero))} {zero} ()
  mono₄ {suc (suc (suc zero))} {suc zero} (s≤s ())
  mono₄ {suc (suc (suc zero))} {suc (suc zero)} (s≤s (s≤s ()))
  mono₄ {suc (suc (suc zero))} {suc (suc (suc zero))} (s≤s (s≤s (s≤s ())))
