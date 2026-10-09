------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the relations (Theorem 4.3): every relation of Table 1
-- holds in Oₙ(ℤ[1/2]).
--
-- The relations (2a)–(2f) say that generators with disjoint indices
-- commute, which holds for any indices (EmbedAction.comm-sound).  Each
-- of the others involves at most eight indices in a known order, so it
-- is the image, under an increasing embedding, of the same relation in
-- dimension at most 8, where both sides are concrete matrices over 𝔻
-- and are compared by computation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Soundness where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ ; z≤n ; s≤s)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (recompute)

open import Word.Base

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Embedding
open import Examples.Groups.CCX+HH-TwoLevel.Semantics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Concrete indices

private
  f1-0 : Fin 1
  f1-0 = zero

private
  f2-0 f2-1 : Fin 2
  f2-0 = zero
  f2-1 = (suc zero)
  lt2-01 : f2-0 < f2-1
  lt2-01 = s≤s z≤n

private
  f3-0 f3-1 f3-2 : Fin 3
  f3-0 = zero
  f3-1 = (suc zero)
  f3-2 = (suc (suc zero))
  lt3-01 : f3-0 < f3-1
  lt3-01 = s≤s z≤n
  lt3-02 : f3-0 < f3-2
  lt3-02 = s≤s z≤n
  lt3-12 : f3-1 < f3-2
  lt3-12 = s≤s (s≤s z≤n)

private
  f4-0 f4-1 f4-2 f4-3 : Fin 4
  f4-0 = zero
  f4-1 = (suc zero)
  f4-2 = (suc (suc zero))
  f4-3 = (suc (suc (suc zero)))
  lt4-01 : f4-0 < f4-1
  lt4-01 = s≤s z≤n
  lt4-12 : f4-1 < f4-2
  lt4-12 = s≤s (s≤s z≤n)
  lt4-13 : f4-1 < f4-3
  lt4-13 = s≤s (s≤s z≤n)
  lt4-23 : f4-2 < f4-3
  lt4-23 = s≤s (s≤s (s≤s z≤n))

private
  f5-0 f5-1 f5-2 f5-3 f5-4 : Fin 5
  f5-0 = zero
  f5-1 = (suc zero)
  f5-2 = (suc (suc zero))
  f5-3 = (suc (suc (suc zero)))
  f5-4 = (suc (suc (suc (suc zero))))
  lt5-01 : f5-0 < f5-1
  lt5-01 = s≤s z≤n
  lt5-02 : f5-0 < f5-2
  lt5-02 = s≤s z≤n
  lt5-12 : f5-1 < f5-2
  lt5-12 = s≤s (s≤s z≤n)
  lt5-13 : f5-1 < f5-3
  lt5-13 = s≤s (s≤s z≤n)
  lt5-23 : f5-2 < f5-3
  lt5-23 = s≤s (s≤s (s≤s z≤n))
  lt5-24 : f5-2 < f5-4
  lt5-24 = s≤s (s≤s (s≤s z≤n))
  lt5-34 : f5-3 < f5-4
  lt5-34 = s≤s (s≤s (s≤s (s≤s z≤n)))

private
  f6-0 f6-1 f6-2 f6-3 f6-4 f6-5 : Fin 6
  f6-0 = zero
  f6-1 = (suc zero)
  f6-2 = (suc (suc zero))
  f6-3 = (suc (suc (suc zero)))
  f6-4 = (suc (suc (suc (suc zero))))
  f6-5 = (suc (suc (suc (suc (suc zero)))))
  lt6-01 : f6-0 < f6-1
  lt6-01 = s≤s z≤n
  lt6-12 : f6-1 < f6-2
  lt6-12 = s≤s (s≤s z≤n)
  lt6-13 : f6-1 < f6-3
  lt6-13 = s≤s (s≤s z≤n)
  lt6-23 : f6-2 < f6-3
  lt6-23 = s≤s (s≤s (s≤s z≤n))
  lt6-24 : f6-2 < f6-4
  lt6-24 = s≤s (s≤s (s≤s z≤n))
  lt6-34 : f6-3 < f6-4
  lt6-34 = s≤s (s≤s (s≤s (s≤s z≤n)))
  lt6-45 : f6-4 < f6-5
  lt6-45 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

private
  f8-0 f8-1 f8-2 f8-3 f8-4 f8-5 f8-6 f8-7 : Fin 8
  f8-0 = zero
  f8-1 = (suc zero)
  f8-2 = (suc (suc zero))
  f8-3 = (suc (suc (suc zero)))
  f8-4 = (suc (suc (suc (suc zero))))
  f8-5 = (suc (suc (suc (suc (suc zero)))))
  f8-6 = (suc (suc (suc (suc (suc (suc zero))))))
  f8-7 = (suc (suc (suc (suc (suc (suc (suc zero)))))))
  lt8-01 : f8-0 < f8-1
  lt8-01 = s≤s z≤n
  lt8-04 : f8-0 < f8-4
  lt8-04 = s≤s z≤n
  lt8-12 : f8-1 < f8-2
  lt8-12 = s≤s (s≤s z≤n)
  lt8-23 : f8-2 < f8-3
  lt8-23 = s≤s (s≤s (s≤s z≤n))
  lt8-34 : f8-3 < f8-4
  lt8-34 = s≤s (s≤s (s≤s (s≤s z≤n)))
  lt8-45 : f8-4 < f8-5
  lt8-45 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
  lt8-56 : f8-5 < f8-6
  lt8-56 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
  lt8-67 : f8-6 < f8-7
  lt8-67 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

------------------------------------------------------------------------
-- The relations in small dimensions, checked by computation
--
-- The words are transparent, so that their embeddings compute; the
-- equations are proved in an opaque block that unfolds the action, the
-- vector updates and the arithmetic of 𝔻, which the matrices of
-- concrete words compute through.

private
  l-1a r-1a : Word (Gen 2)
  l-1a = X f2-0 f2-1 lt2-01 • X f2-0 f2-1 lt2-01
  r-1a = ε
  l-1b r-1b : Word (Gen 1)
  l-1b = M f1-0 • M f1-0
  r-1b = ε
  l-1c r-1c : Word (Gen 4)
  l-1c = K f4-0 f4-1 f4-2 f4-3 lt4-01 lt4-12 lt4-23 • K f4-0 f4-1 f4-2 f4-3 lt4-01 lt4-12 lt4-23
  r-1c = ε
  l-3a r-3a : Word (Gen 3)
  l-3a = X f3-0 f3-1 lt3-01 • X f3-0 f3-2 lt3-02
  r-3a = X f3-1 f3-2 lt3-12 • X f3-0 f3-1 lt3-01
  l-3b r-3b : Word (Gen 3)
  l-3b = X f3-1 f3-2 lt3-12 • X f3-0 f3-1 lt3-01
  r-3b = X f3-0 f3-2 lt3-02 • X f3-1 f3-2 lt3-12
  l-3c r-3c : Word (Gen 2)
  l-3c = X f2-0 f2-1 lt2-01 • M f2-1
  r-3c = M f2-0 • X f2-0 f2-1 lt2-01
  l-3d r-3d : Word (Gen 5)
  l-3d = X f5-0 f5-1 lt5-01 • K f5-0 f5-2 f5-3 f5-4 lt5-02 lt5-23 lt5-34
  r-3d = K f5-1 f5-2 f5-3 f5-4 lt5-12 lt5-23 lt5-34 • X f5-0 f5-1 lt5-01
  l-3e r-3e : Word (Gen 5)
  l-3e = X f5-1 f5-2 lt5-12 • K f5-0 f5-1 f5-3 f5-4 lt5-01 lt5-13 lt5-34
  r-3e = K f5-0 f5-2 f5-3 f5-4 lt5-02 lt5-23 lt5-34 • X f5-1 f5-2 lt5-12
  l-3f r-3f : Word (Gen 5)
  l-3f = X f5-2 f5-3 lt5-23 • K f5-0 f5-1 f5-2 f5-4 lt5-01 lt5-12 lt5-24
  r-3f = K f5-0 f5-1 f5-3 f5-4 lt5-01 lt5-13 lt5-34 • X f5-2 f5-3 lt5-23
  l-3g r-3g : Word (Gen 5)
  l-3g = X f5-3 f5-4 lt5-34 • K f5-0 f5-1 f5-2 f5-3 lt5-01 lt5-12 lt5-23
  r-3g = K f5-0 f5-1 f5-2 f5-4 lt5-01 lt5-12 lt5-24 • X f5-3 f5-4 lt5-34
  l-4a r-4a : Word (Gen 4)
  l-4a = X f4-0 f4-1 lt4-01 • K f4-0 f4-1 f4-2 f4-3 lt4-01 lt4-12 lt4-23
  r-4a = K f4-0 f4-1 f4-2 f4-3 lt4-01 lt4-12 lt4-23 • X f4-1 f4-3 lt4-13 • M f4-1 • M f4-3
  l-4b r-4b : Word (Gen 4)
  l-4b = X f4-1 f4-2 lt4-12 • K f4-0 f4-1 f4-2 f4-3 lt4-01 lt4-12 lt4-23
  r-4b = M f4-0 • K f4-0 f4-1 f4-2 f4-3 lt4-01 lt4-12 lt4-23 • M f4-0 • K f4-0 f4-1 f4-2 f4-3 lt4-01 lt4-12 lt4-23 • M f4-0
  l-4c r-4c : Word (Gen 4)
  l-4c = X f4-2 f4-3 lt4-23 • K f4-0 f4-1 f4-2 f4-3 lt4-01 lt4-12 lt4-23
  r-4c = K f4-0 f4-1 f4-2 f4-3 lt4-01 lt4-12 lt4-23 • X f4-1 f4-3 lt4-13
  l-5a r-5a : Word (Gen 6)
  l-5a = K f6-0 f6-1 f6-2 f6-3 lt6-01 lt6-12 lt6-23 • K f6-1 f6-3 f6-4 f6-5 lt6-13 lt6-34 lt6-45
  r-5a = K f6-2 f6-3 f6-4 f6-5 lt6-23 lt6-34 lt6-45 • K f6-0 f6-1 f6-2 f6-4 lt6-01 lt6-12 lt6-24
  l-6a r-6a : Word (Gen 8)
  l-6a = M f8-0 • M f8-4 • X f8-0 f8-4 lt8-04 • K f8-4 f8-5 f8-6 f8-7 lt8-45 lt8-56 lt8-67 • K f8-0 f8-1 f8-2 f8-3 lt8-01 lt8-12 lt8-23 • X f8-3 f8-4 lt8-34 • K f8-0 f8-1 f8-2 f8-3 lt8-01 lt8-12 lt8-23 • K f8-4 f8-5 f8-6 f8-7 lt8-45 lt8-56 lt8-67 • X f8-0 f8-4 lt8-04 • M f8-0 • M f8-4
  r-6a = K f8-4 f8-5 f8-6 f8-7 lt8-45 lt8-56 lt8-67 • K f8-0 f8-1 f8-2 f8-3 lt8-01 lt8-12 lt8-23 • X f8-3 f8-4 lt8-34 • K f8-0 f8-1 f8-2 f8-3 lt8-01 lt8-12 lt8-23 • K f8-4 f8-5 f8-6 f8-7 lt8-45 lt8-56 lt8-67

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  private
    m-1a : ⟦ l-1a ⟧ᵐ ≡ ⟦ r-1a ⟧ᵐ
    m-1a = refl

    m-1b : ⟦ l-1b ⟧ᵐ ≡ ⟦ r-1b ⟧ᵐ
    m-1b = refl

    m-1c : ⟦ l-1c ⟧ᵐ ≡ ⟦ r-1c ⟧ᵐ
    m-1c = refl

    m-3a : ⟦ l-3a ⟧ᵐ ≡ ⟦ r-3a ⟧ᵐ
    m-3a = refl

    m-3b : ⟦ l-3b ⟧ᵐ ≡ ⟦ r-3b ⟧ᵐ
    m-3b = refl

    m-3c : ⟦ l-3c ⟧ᵐ ≡ ⟦ r-3c ⟧ᵐ
    m-3c = refl

    m-3d : ⟦ l-3d ⟧ᵐ ≡ ⟦ r-3d ⟧ᵐ
    m-3d = refl

    m-3e : ⟦ l-3e ⟧ᵐ ≡ ⟦ r-3e ⟧ᵐ
    m-3e = refl

    m-3f : ⟦ l-3f ⟧ᵐ ≡ ⟦ r-3f ⟧ᵐ
    m-3f = refl

    m-3g : ⟦ l-3g ⟧ᵐ ≡ ⟦ r-3g ⟧ᵐ
    m-3g = refl

    m-4a : ⟦ l-4a ⟧ᵐ ≡ ⟦ r-4a ⟧ᵐ
    m-4a = refl

    m-4b : ⟦ l-4b ⟧ᵐ ≡ ⟦ r-4b ⟧ᵐ
    m-4b = refl

    m-4c : ⟦ l-4c ⟧ᵐ ≡ ⟦ r-4c ⟧ᵐ
    m-4c = refl

    m-5a : ⟦ l-5a ⟧ᵐ ≡ ⟦ r-5a ⟧ᵐ
    m-5a = refl

    m-6a : ⟦ l-6a ⟧ᵐ ≡ ⟦ r-6a ⟧ᵐ
    m-6a = refl

------------------------------------------------------------------------
-- Soundness of the axioms

-- Relevant proofs of order, recomputed from irrelevant ones.
private
  rc : {a b : Fin n} → .(a < b) → a < b
  rc {a = a} {b} p = recompute (a FinP.<? b) p

sound-axiom : {w v : Word (Gen n)} → w === v → ⟦ w ⟧ᵐ ≡ ⟦ v ⟧ᵐ
sound-axiom (r1a {a = a} {b = b} p) =
  emb-sound (emb (a ∷ b ∷ []) (rc p ∷ᵢ [ b ]ᵢ)) l-1a r-1a m-1a
sound-axiom (r1b {a = a}) =
  emb-sound (emb (a ∷ []) [ a ]ᵢ) l-1b r-1b m-1b
sound-axiom (r1c {a = a} {b = b} {c = c} {d = d} p q r) =
  emb-sound (emb (a ∷ b ∷ c ∷ d ∷ []) (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ [ d ]ᵢ)) l-1c r-1c m-1c
sound-axiom (r2a {a = a} {b = b} {c = c} {d = d} p q ac ad bc bd) =
  comm-sound (X-gen a b p) (X-gen c d q)
    λ { x X-a X-a → ac refl ; x X-a X-b → ad refl ; x X-b X-a → bc refl ; x X-b X-b → bd refl }
sound-axiom (r2b {a = a} {b = b} {c = c} p ca cb) =
  comm-sound (X-gen a b p) (M-gen c) λ { x X-a M-a → ca refl ; x X-b M-a → cb refl }
sound-axiom (r2c {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} p q r s ac ad ae af bc bd be bf) =
  comm-sound (X-gen a b p) (K-gen c d e f q r s)
    λ { x X-a K-a → ac refl ; x X-a K-b → ad refl ; x X-a K-c → ae refl ; x X-a K-d → af refl
      ; x X-b K-a → bc refl ; x X-b K-b → bd refl ; x X-b K-c → be refl ; x X-b K-d → bf refl }
sound-axiom (r2d {a = a} {b = b} ab) =
  comm-sound (M-gen a) (M-gen b) λ { x M-a M-a → ab refl }
sound-axiom (r2e {b = b} {c = c} {d = d} {e = e} {a = a} p q r ab ac ad ae) =
  comm-sound (M-gen a) (K-gen b c d e p q r)
    λ { x M-a K-a → ab refl ; x M-a K-b → ac refl ; x M-a K-c → ad refl ; x M-a K-d → ae refl }
sound-axiom (r2f {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} p q r s t u
                 ae af ag ah be bf bg bh ce cf cg ch de df dg dh) =
  comm-sound (K-gen a b c d p q r) (K-gen e f g h s t u)
    λ { x K-a K-a → ae refl ; x K-a K-b → af refl ; x K-a K-c → ag refl ; x K-a K-d → ah refl
      ; x K-b K-a → be refl ; x K-b K-b → bf refl ; x K-b K-c → bg refl ; x K-b K-d → bh refl
      ; x K-c K-a → ce refl ; x K-c K-b → cf refl ; x K-c K-c → cg refl ; x K-c K-d → ch refl
      ; x K-d K-a → de refl ; x K-d K-b → df refl ; x K-d K-c → dg refl ; x K-d K-d → dh refl }
sound-axiom (r3a {a = a} {a′ = a′} {b = b} p q r) =
  emb-sound (emb (a ∷ a′ ∷ b ∷ []) (rc p ∷ᵢ rc q ∷ᵢ [ b ]ᵢ)) l-3a r-3a m-3a
sound-axiom (r3b {a = a} {b = b} {b′ = b′} p q r) =
  emb-sound (emb (a ∷ b ∷ b′ ∷ []) (rc p ∷ᵢ rc q ∷ᵢ [ b′ ]ᵢ)) l-3b r-3b m-3b
sound-axiom (r3c {a = a} {b = b} p) =
  emb-sound (emb (a ∷ b ∷ []) (rc p ∷ᵢ [ b ]ᵢ)) l-3c r-3c m-3c
sound-axiom (r3d {a = a} {a′ = a′} {b = b} {c = c} {d = d} p q r s t) =
  emb-sound (emb (a ∷ a′ ∷ b ∷ c ∷ d ∷ []) (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ rc s ∷ᵢ [ d ]ᵢ)) l-3d r-3d m-3d
sound-axiom (r3e {a = a} {b = b} {b′ = b′} {c = c} {d = d} p q r s t u) =
  emb-sound (emb (a ∷ b ∷ b′ ∷ c ∷ d ∷ []) (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ rc s ∷ᵢ [ d ]ᵢ)) l-3e r-3e m-3e
sound-axiom (r3f {a = a} {b = b} {c = c} {c′ = c′} {d = d} p q r s t u) =
  emb-sound (emb (a ∷ b ∷ c ∷ c′ ∷ d ∷ []) (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ rc s ∷ᵢ [ d ]ᵢ)) l-3f r-3f m-3f
sound-axiom (r3g {a = a} {b = b} {c = c} {d = d} {d′ = d′} p q r s t) =
  emb-sound (emb (a ∷ b ∷ c ∷ d ∷ d′ ∷ []) (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ rc s ∷ᵢ [ d′ ]ᵢ)) l-3g r-3g m-3g
sound-axiom (r4a {a = a} {b = b} {c = c} {d = d} p q r s) =
  emb-sound (emb (a ∷ b ∷ c ∷ d ∷ []) (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ [ d ]ᵢ)) l-4a r-4a m-4a
sound-axiom (r4b {a = a} {b = b} {c = c} {d = d} p q r) =
  emb-sound (emb (a ∷ b ∷ c ∷ d ∷ []) (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ [ d ]ᵢ)) l-4b r-4b m-4b
sound-axiom (r4c {a = a} {b = b} {c = c} {d = d} p q r s) =
  emb-sound (emb (a ∷ b ∷ c ∷ d ∷ []) (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ [ d ]ᵢ)) l-4c r-4c m-4c
sound-axiom (r5a {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} p q r s t u v) =
  emb-sound (emb (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ rc s ∷ᵢ rc t ∷ᵢ [ f ]ᵢ)) l-5a r-5a m-5a
sound-axiom (r6a {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} p q r s t u v w) =
  emb-sound (emb (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])
                 (rc p ∷ᵢ rc q ∷ᵢ rc r ∷ᵢ rc s ∷ᵢ rc t ∷ᵢ rc u ∷ᵢ rc v ∷ᵢ [ h ]ᵢ))
            l-6a r-6a m-6a
