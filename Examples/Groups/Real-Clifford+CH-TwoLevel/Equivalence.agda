------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of Figure 6 and Clément's (Clement) are equivalent:
-- they generate the same congruence on words, in every dimension
-- (equivalent).
--
-- * Clément's (1)–(19) are derivable from Figure 6 (ToClement), and
--   Figure 6's local relations (a1)–(d2) from Clément's (ClementLocal).
-- * (20) and (d3) are equivalent given the local relations and (f1),
--   which is Clément's (19) (Four); (21) and (d4) are equivalent given
--   the local relations alone (Six).  Each is derived on the first four
--   or six indices, in a set of relations pulled back along the
--   inclusion (Embedding.Pull).
-- * Clément's (20) and (21) are stated on those indices; Figure 6's
--   (d3) and (d4) hold at any indices, which in Clément's relations
--   come from the first ones by conjugation with transpositions
--   (ClementLocal.move, Places), case by case on the order of the
--   indices (the leaves).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; _<_ ; _↑ˡ_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat.Base as ℕ using (ℕ ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ ; _,_ ; _×_)
open import Function.Bundles using (_⇔_ ; mk⇔)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
import Presentation.Tactics.Words as TW
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
import Examples.Groups.Real-Clifford+CH-TwoLevel.Local as L
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Embedding using (Emb ; ι ; word ; incl+ ; module Pull)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Pairings as Pairings
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.Four as Four
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.Six as Six
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.ToClement as TC
import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.ClementLocal as CL
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.Places

private
  ⟪_⟫ : ∀ {m} → List (Gen m) → Word (Gen m)
  ⟪_⟫ = TW.Associative.word-of-list

------------------------------------------------------------------------
-- Axioms derivable in Δ give the congruence of Δ

lift : ∀ {X : Set} {Γ Δ : WRel X} → (∀ {u v} → Γ u v → PB._≈_ Δ u v) →
       ∀ {u v} → PB._≈_ Γ u v → PB._≈_ Δ u v
lift {Γ = Γ} {Δ} f = go
  where
  open PB Γ using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
  open PB Δ using () renaming (_≈_ to _≈₂_)
  go : ∀ {u v} → u ≈ v → u ≈₂ v
  go refl = _≈₂_.refl
  go (sym h) = _≈₂_.sym (go h)
  go (trans h k) = _≈₂_.trans (go h) (go k)
  go (cong h k) = _≈₂_.cong (go h) (go k)
  go assoc = _≈₂_.assoc
  go left-unit = _≈₂_.left-unit
  go right-unit = _≈₂_.right-unit
  go (axiom a) = f a

------------------------------------------------------------------------
-- n is m + k when an index is at least m - 1

split4 : ∀ {n} (i : Fin n) → 3 ℕ.≤ toℕ i → Σ ℕ (λ k → n ≡ 4 ℕ.+ k)
split4 (suc (suc (suc zero))) _ = _ , ≡.refl
split4 (suc (suc (suc (suc i)))) _ = _ , ≡.refl
split4 zero ()
split4 (suc zero) (s≤s ())
split4 (suc (suc zero)) (s≤s (s≤s ()))

split6 : ∀ {n} (i : Fin n) → 5 ℕ.≤ toℕ i → Σ ℕ (λ k → n ≡ 6 ℕ.+ k)
split6 (suc (suc (suc (suc (suc zero))))) _ = _ , ≡.refl
split6 (suc (suc (suc (suc (suc (suc i)))))) _ = _ , ≡.refl
split6 zero ()
split6 (suc zero) (s≤s ())
split6 (suc (suc zero)) (s≤s (s≤s ()))
split6 (suc (suc (suc zero))) (s≤s (s≤s (s≤s ())))
split6 (suc (suc (suc (suc zero)))) (s≤s (s≤s (s≤s (s≤s ()))))

------------------------------------------------------------------------
-- Letter lists on 4 indices (as in Four)

module W4 where
  h01 : Gen 4
  h01 = H-gen zero (suc zero) (s≤s z≤n)
  h02 : Gen 4
  h02 = H-gen zero (suc (suc zero)) (s≤s z≤n)
  h13 : Gen 4
  h13 = H-gen (suc zero) (suc (suc (suc zero))) (s≤s (s≤s z≤n))
  h23 : Gen 4
  h23 = H-gen (suc (suc zero)) (suc (suc (suc zero))) (s≤s (s≤s (s≤s z≤n)))
  z0 : Gen 4
  z0 = Z-gen zero
  z1 : Gen 4
  z1 = Z-gen (suc zero)

  Ld3 : List (Gen 4)
  Ld3 = (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
  Rd3 : List (Gen 4)
  Rd3 = (h01 ∷ h23 ∷ [])
  L20 : List (Gen 4)
  L20 = (h01 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
  R20 : List (Gen 4)
  R20 = (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
  Lf1 : List (Gen 4)
  Lf1 = (h01 ∷ h23 ∷ h02 ∷ h13 ∷ [])
  Rf1 : List (Gen 4)
  Rf1 = (h02 ∷ h13 ∷ h01 ∷ h23 ∷ [])
  Ld3-bc : List (Gen 4)
  Ld3-bc = (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
  Rd3-bc : List (Gen 4)
  Rd3-bc = (h01 ∷ h23 ∷ [])
  Ld3-cb : List (Gen 4)
  Ld3-cb = (h13 ∷ h01 ∷ h23 ∷ h13 ∷ h01 ∷ h23 ∷ h13 ∷ h01 ∷ h23 ∷ h13 ∷ h01 ∷ h23 ∷ [])
  Rd3-cb : List (Gen 4)
  Rd3-cb = (h02 ∷ h13 ∷ [])

------------------------------------------------------------------------
-- Letter lists on 6 indices (as in Six)

module W6 where
  h01 : Gen 6
  h01 = H-gen zero (suc zero) (s≤s z≤n)
  h02 : Gen 6
  h02 = H-gen zero (suc (suc zero)) (s≤s z≤n)
  h03 : Gen 6
  h03 = H-gen zero (suc (suc (suc zero))) (s≤s z≤n)
  h04 : Gen 6
  h04 = H-gen zero (suc (suc (suc (suc zero)))) (s≤s z≤n)
  h12 : Gen 6
  h12 = H-gen (suc zero) (suc (suc zero)) (s≤s (s≤s z≤n))
  h13 : Gen 6
  h13 = H-gen (suc zero) (suc (suc (suc zero))) (s≤s (s≤s z≤n))
  h14 : Gen 6
  h14 = H-gen (suc zero) (suc (suc (suc (suc zero)))) (s≤s (s≤s z≤n))
  h15 : Gen 6
  h15 = H-gen (suc zero) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s z≤n))
  h23 : Gen 6
  h23 = H-gen (suc (suc zero)) (suc (suc (suc zero))) (s≤s (s≤s (s≤s z≤n)))
  h24 : Gen 6
  h24 = H-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) (s≤s (s≤s (s≤s z≤n)))
  h25 : Gen 6
  h25 = H-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s (s≤s z≤n)))
  h34 : Gen 6
  h34 = H-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) (s≤s (s≤s (s≤s (s≤s z≤n))))
  h35 : Gen 6
  h35 = H-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s (s≤s (s≤s z≤n))))
  h45 : Gen 6
  h45 = H-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
  x12 : Gen 6
  x12 = X-gen (suc zero) (suc (suc zero)) (s≤s (s≤s z≤n))
  x13 : Gen 6
  x13 = X-gen (suc zero) (suc (suc (suc zero))) (s≤s (s≤s z≤n))
  x14 : Gen 6
  x14 = X-gen (suc zero) (suc (suc (suc (suc zero)))) (s≤s (s≤s z≤n))
  x23 : Gen 6
  x23 = X-gen (suc (suc zero)) (suc (suc (suc zero))) (s≤s (s≤s (s≤s z≤n)))
  x24 : Gen 6
  x24 = X-gen (suc (suc zero)) (suc (suc (suc (suc zero)))) (s≤s (s≤s (s≤s z≤n)))
  x25 : Gen 6
  x25 = X-gen (suc (suc zero)) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s (s≤s z≤n)))
  x34 : Gen 6
  x34 = X-gen (suc (suc (suc zero))) (suc (suc (suc (suc zero)))) (s≤s (s≤s (s≤s (s≤s z≤n))))
  x35 : Gen 6
  x35 = X-gen (suc (suc (suc zero))) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s (s≤s (s≤s z≤n))))
  x45 : Gen 6
  x45 = X-gen (suc (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
  z0 : Gen 6
  z0 = Z-gen zero
  z1 : Gen 6
  z1 = Z-gen (suc zero)

  Ld4 : List (Gen 6)
  Ld4 = (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
  Rd4 : List (Gen 6)
  Rd4 = (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ x24 ∷ x35 ∷ [])
  L21 : List (Gen 6)
  L21 = (h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
  R21 : List (Gen 6)
  R21 = (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
  Ld4-bcde : List (Gen 6)
  Ld4-bcde = (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
  Rd4-bcde : List (Gen 6)
  Rd4-bcde = (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ x24 ∷ x35 ∷ [])
  Ld4-bced : List (Gen 6)
  Ld4-bced = (h02 ∷ h14 ∷ h01 ∷ h02 ∷ h14 ∷ x23 ∷ x45 ∷ h02 ∷ h14 ∷ h01 ∷ h02 ∷ h14 ∷ x23 ∷ x45 ∷ h02 ∷ h14 ∷ h01 ∷ h02 ∷ h14 ∷ x23 ∷ x45 ∷ [])
  Rd4-bced : List (Gen 6)
  Rd4-bced = (h23 ∷ h45 ∷ h35 ∷ h23 ∷ h45 ∷ x23 ∷ x45 ∷ [])
  Ld4-cbde : List (Gen 6)
  Ld4-cbde = (h01 ∷ h23 ∷ h02 ∷ h01 ∷ h23 ∷ x14 ∷ x35 ∷ h01 ∷ h23 ∷ h02 ∷ h01 ∷ h23 ∷ x14 ∷ x35 ∷ h01 ∷ h23 ∷ h02 ∷ h01 ∷ h23 ∷ x14 ∷ x35 ∷ [])
  Rd4-cbde : List (Gen 6)
  Rd4-cbde = (h14 ∷ h35 ∷ h45 ∷ h14 ∷ h35 ∷ x14 ∷ x35 ∷ [])
  Ld4-cbed : List (Gen 6)
  Ld4-cbed = (h01 ∷ h24 ∷ h02 ∷ h01 ∷ h24 ∷ x13 ∷ x45 ∷ h01 ∷ h24 ∷ h02 ∷ h01 ∷ h24 ∷ x13 ∷ x45 ∷ h01 ∷ h24 ∷ h02 ∷ h01 ∷ h24 ∷ x13 ∷ x45 ∷ [])
  Rd4-cbed : List (Gen 6)
  Rd4-cbed = (h13 ∷ h45 ∷ h35 ∷ h13 ∷ h45 ∷ x13 ∷ x45 ∷ [])
  Ld4-bdce : List (Gen 6)
  Ld4-bdce = (h03 ∷ h12 ∷ h01 ∷ h03 ∷ h12 ∷ x34 ∷ x25 ∷ h03 ∷ h12 ∷ h01 ∷ h03 ∷ h12 ∷ x34 ∷ x25 ∷ h03 ∷ h12 ∷ h01 ∷ h03 ∷ h12 ∷ x34 ∷ x25 ∷ [])
  Rd4-bdce : List (Gen 6)
  Rd4-bdce = (h34 ∷ h25 ∷ h45 ∷ h34 ∷ h25 ∷ x34 ∷ x25 ∷ [])
  Ld4-cebd : List (Gen 6)
  Ld4-cebd = (h01 ∷ h34 ∷ h03 ∷ h01 ∷ h34 ∷ x12 ∷ x45 ∷ h01 ∷ h34 ∷ h03 ∷ h01 ∷ h34 ∷ x12 ∷ x45 ∷ h01 ∷ h34 ∷ h03 ∷ h01 ∷ h34 ∷ x12 ∷ x45 ∷ [])
  Rd4-cebd : List (Gen 6)
  Rd4-cebd = (h12 ∷ h45 ∷ h25 ∷ h12 ∷ h45 ∷ x12 ∷ x45 ∷ [])

------------------------------------------------------------------------
-- On the first four indices of 4 + k

module Base4 (k : ℕ) where

  e : Emb 4 (4 ℕ.+ k)
  e = incl+ 4 k

  private
    f0 f1 f2 f3 : Fin (4 ℕ.+ k)
    f0 = zero
    f1 = suc zero
    f2 = suc (suc zero)
    f3 = suc (suc (suc zero))
    l01 : f0 < f1
    l01 = s≤s z≤n
    l02 : f0 < f2
    l02 = s≤s z≤n
    l12 : f1 < f2
    l12 = s≤s (s≤s z≤n)
    l13 : f1 < f3
    l13 = s≤s (s≤s z≤n)
    l23 : f2 < f3
    l23 = s≤s (s≤s (s≤s z≤n))

  -- Figure 6 derives (20) on them.
  module HPside where
    open PB (_===_ {4 ℕ.+ k}) hiding (_===_)
    open PP (_===_ {4 ℕ.+ k})
    module P = Pull e (_===_ {4 ℕ.+ k})
    open Four P.pull (P.pull-local (λ x → axiom (L.local⇒ x))) using (module FromD3)

    d3w : word e ⟪ W4.Ld3 ⟫ ≈ word e ⟪ W4.Rd3 ⟫
    d3w = trans (by-assoc auto) (trans (axiom (d3 l01 l02 l13 l23 (λ ()))) (by-assoc auto))

    f1w : word e ⟪ W4.Lf1 ⟫ ≈ word e ⟪ W4.Rf1 ⟫
    f1w = trans (by-assoc auto) (trans (Pairings.Sorted.f1 {4 ℕ.+ k} l01 l12 l23) (by-assoc auto))

    r20 : word e ⟪ W4.L20 ⟫ ≈ word e ⟪ W4.R20 ⟫
    r20 = P.push (FromD3.r20 (P.hyp d3w) (P.hyp f1w))

  -- Clément's relations derive (d3) on them.
  module Cside where
    open PB (_===ᶜ_ {4 ℕ.+ k}) hiding (_===_)
    open PP (_===ᶜ_ {4 ℕ.+ k})
    module P = Pull e (_===ᶜ_ {4 ℕ.+ k})
    open Four P.pull (P.pull-local CL.c-local) using (module FromR20)

    r20w : word e ⟪ W4.L20 ⟫ ≈ word e ⟪ W4.R20 ⟫
    r20w = trans (by-assoc auto) (trans (axiom (e20 ≡.refl ≡.refl ≡.refl ≡.refl l01 l02 l13)) (by-assoc auto))

    f1w : word e ⟪ W4.Lf1 ⟫ ≈ word e ⟪ W4.Rf1 ⟫
    f1w = trans (by-assoc auto)
      (trans (axiom (e19 {j = f0} {f1} {f2} {f3} (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))) (by-assoc auto))

    d3₀ : word e ⟪ W4.Ld3 ⟫ ≈ word e ⟪ W4.Rd3 ⟫
    d3₀ = P.push (FromR20.d3 (P.hyp r20w) (P.hyp f1w))

  -- As templates.
  c-base : PB._≈_ (_===ᶜ_ {4 ℕ.+ k}) (CL.⟦_⟧ (CL.place (_↑ˡ k) (map CL.ofGen W4.Ld3)))
                                     (CL.⟦_⟧ (CL.place (_↑ˡ k) (map CL.ofGen W4.Rd3)))
  c-base = PB.trans (CL.placeW e W4.Ld3) (PB.trans Cside.d3₀ (PB.sym (CL.placeW e W4.Rd3)))

------------------------------------------------------------------------
-- On the first six indices of 6 + k

module Base6 (k : ℕ) where

  e : Emb 6 (6 ℕ.+ k)
  e = incl+ 6 k

  private
    f0 f1 f2 f3 f4 f5 : Fin (6 ℕ.+ k)
    f0 = zero
    f1 = suc zero
    f2 = suc (suc zero)
    f3 = suc (suc (suc zero))
    f4 = suc (suc (suc (suc zero)))
    f5 = suc (suc (suc (suc (suc zero))))
    l01 : f0 < f1
    l01 = s≤s z≤n
    l02 : f0 < f2
    l02 = s≤s z≤n
    l04 : f0 < f4
    l04 = s≤s z≤n
    l13 : f1 < f3
    l13 = s≤s (s≤s z≤n)
    l15 : f1 < f5
    l15 = s≤s (s≤s z≤n)
    l24 : f2 < f4
    l24 = s≤s (s≤s (s≤s z≤n))
    l35 : f3 < f5
    l35 = s≤s (s≤s (s≤s (s≤s z≤n)))
    l45 : f4 < f5
    l45 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

  -- Figure 6 derives (21) on them.
  module HPside where
    open PB (_===_ {6 ℕ.+ k}) hiding (_===_)
    open PP (_===_ {6 ℕ.+ k})
    module P = Pull e (_===_ {6 ℕ.+ k})
    open Six P.pull (P.pull-local (λ x → axiom (L.local⇒ x))) using (module FromD4)

    d4w : word e ⟪ W6.Ld4 ⟫ ≈ word e ⟪ W6.Rd4 ⟫
    d4w = trans (by-assoc auto)
      (trans (axiom (d4 l01 l02 l13 l24 l35 l45 (λ ()) (λ ()) (λ ()) (λ ()))) (by-assoc auto))

    r21 : word e ⟪ W6.L21 ⟫ ≈ word e ⟪ W6.R21 ⟫
    r21 = P.push (FromD4.r21 (P.hyp d4w))

  -- Clément's relations derive (d4) on them.
  module Cside where
    open PB (_===ᶜ_ {6 ℕ.+ k}) hiding (_===_)
    open PP (_===ᶜ_ {6 ℕ.+ k})
    module P = Pull e (_===ᶜ_ {6 ℕ.+ k})
    open Six P.pull (P.pull-local CL.c-local) using (module FromR21)

    r21w : word e ⟪ W6.L21 ⟫ ≈ word e ⟪ W6.R21 ⟫
    r21w = trans (by-assoc auto)
      (trans (axiom (e21 ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl l01 l02 l13 l04 l15)) (by-assoc auto))

    d4₀ : word e ⟪ W6.Ld4 ⟫ ≈ word e ⟪ W6.Rd4 ⟫
    d4₀ = P.push (FromR21.d4 (P.hyp r21w))

  -- As templates.
  c-base : PB._≈_ (_===ᶜ_ {6 ℕ.+ k}) (CL.⟦_⟧ (CL.place (_↑ˡ k) (map CL.ofGen W6.Ld4)))
                                     (CL.⟦_⟧ (CL.place (_↑ˡ k) (map CL.ofGen W6.Rd4)))
  c-base = PB.trans (CL.placeW e W6.Ld4) (PB.trans Cside.d4₀ (PB.sym (CL.placeW e W6.Rd4)))

------------------------------------------------------------------------
-- Figure 6 derives Clément's (20) and (21), on the first indices

hp-e20 : ∀ {n} {i₀ i₁ i₂ i₃ : Fin n} → toℕ i₀ ≡ 0 → toℕ i₁ ≡ 1 → toℕ i₂ ≡ 2 → toℕ i₃ ≡ 3 →
         (p01 : i₀ < i₁) (p02 : i₀ < i₂) (p13 : i₁ < i₃) →
         PB._≈_ (_===_ {n}) (⟨20⟩ˡ p01 p02 p13) (⟨20⟩ʳ p01 p02 p13)
hp-e20 {n} {i₀} {i₁} {i₂} {i₃} t0 t1 t2 t3 p01 p02 p13 with split4 i₃ (ℕP.≤-reflexive (≡.sym t3))
... | k , ≡.refl
  with FinP.toℕ-injective {i = i₀} {j = zero} t0 | FinP.toℕ-injective {i = i₁} {j = suc zero} t1
     | FinP.toℕ-injective {i = i₂} {j = suc (suc zero)} t2 | FinP.toℕ-injective {i = i₃} {j = suc (suc (suc zero))} t3
... | ≡.refl | ≡.refl | ≡.refl | ≡.refl =
  PB.trans (PP.by-assoc _ auto) (PB.trans (Base4.HPside.r20 k) (PP.by-assoc _ auto))

hp-e21 : ∀ {n} {i₀ i₁ i₂ i₃ i₄ i₅ : Fin n} →
         toℕ i₀ ≡ 0 → toℕ i₁ ≡ 1 → toℕ i₂ ≡ 2 → toℕ i₃ ≡ 3 → toℕ i₄ ≡ 4 → toℕ i₅ ≡ 5 →
         (p01 : i₀ < i₁) (p02 : i₀ < i₂) (p13 : i₁ < i₃) (p04 : i₀ < i₄) (p15 : i₁ < i₅) →
         PB._≈_ (_===_ {n}) (⟨21⟩ˡ p01 p02 p13 p04 p15) (⟨21⟩ʳ p01 p02 p13 p04 p15)
hp-e21 {n} {i₀} {i₁} {i₂} {i₃} {i₄} {i₅} t0 t1 t2 t3 t4 t5 p01 p02 p13 p04 p15
  with split6 i₅ (ℕP.≤-reflexive (≡.sym t5))
... | k , ≡.refl
  with FinP.toℕ-injective {i = i₀} {j = zero} t0 | FinP.toℕ-injective {i = i₁} {j = suc zero} t1
     | FinP.toℕ-injective {i = i₂} {j = suc (suc zero)} t2 | FinP.toℕ-injective {i = i₃} {j = suc (suc (suc zero))} t3
     | FinP.toℕ-injective {i = i₄} {j = suc (suc (suc (suc zero)))} t4
     | FinP.toℕ-injective {i = i₅} {j = suc (suc (suc (suc (suc zero))))} t5
... | ≡.refl | ≡.refl | ≡.refl | ≡.refl | ≡.refl | ≡.refl =
  PB.trans (PP.by-assoc _ auto) (PB.trans (Base6.HPside.r21 k) (PP.by-assoc _ auto))

------------------------------------------------------------------------
-- In Clément's relations, (d3) and (d4) on sorted indices, from the
-- first ones (one lemma for each order of the roles)

-- bc: the sorted indices take the roles a b c d.
leaf4-bc : ∀ {n} {s0 s1 s2 s3 : Fin n} (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) →
            PB._≈_ (_===ᶜ_ {n}) (word (Emb4.emb p0 p1 p2) ⟪ W4.Ld3-bc ⟫) (word (Emb4.emb p0 p1 p2) ⟪ W4.Rd3-bc ⟫)
leaf4-bc {n} {s0} {s1} {s2} {s3} p0 p1 p2 with split4 s3 (Emb4.b3 p0 p1 p2)
... | k , ≡.refl = trans (sym (CL.placeW S.emb W4.Ld3-bc)) (trans moved (CL.placeW S.emb W4.Rd3-bc))
  where
  module S = Sorted4 {k} p0 p1 p2
  open PB (_===ᶜ_ {4 ℕ.+ k}) hiding (_===_)
  qs : List (Fin (4 ℕ.+ k) × Fin (4 ℕ.+ k))
  qs = []
  sg : Fin 4 → Fin 4
  sg zero = zero
  sg (suc zero) = (suc zero)
  sg (suc (suc zero)) = (suc (suc zero))
  sg (suc (suc (suc zero))) = (suc (suc (suc zero)))
  fact : ∀ i → CL.τs (S.ps ++ qs) (S.f i) ≡ S.σ (sg i)
  fact zero = ≡.trans (CL.τs-++ S.ps qs (S.f zero)) (S.place zero)
  fact (suc zero) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc zero))) (S.place (suc zero))
  fact (suc (suc zero)) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc zero)))) (S.place (suc (suc zero)))
  fact (suc (suc (suc zero))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc zero))))) (S.place (suc (suc (suc zero))))
  moved = CL.move (S.ps ++ qs) {S.f} {λ i → S.σ (sg i)} fact {map CL.ofGen W4.Ld3} {map CL.ofGen W4.Rd3} (Base4.c-base k)

-- cb: the sorted indices take the roles a c b d.
leaf4-cb : ∀ {n} {s0 s1 s2 s3 : Fin n} (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) →
            PB._≈_ (_===ᶜ_ {n}) (word (Emb4.emb p0 p1 p2) ⟪ W4.Ld3-cb ⟫) (word (Emb4.emb p0 p1 p2) ⟪ W4.Rd3-cb ⟫)
leaf4-cb {n} {s0} {s1} {s2} {s3} p0 p1 p2 with split4 s3 (Emb4.b3 p0 p1 p2)
... | k , ≡.refl = trans (sym (CL.placeW S.emb W4.Ld3-cb)) (trans moved (CL.placeW S.emb W4.Rd3-cb))
  where
  module S = Sorted4 {k} p0 p1 p2
  open PB (_===ᶜ_ {4 ℕ.+ k}) hiding (_===_)
  qs : List (Fin (4 ℕ.+ k) × Fin (4 ℕ.+ k))
  qs = (S.f (suc zero) , S.f (suc (suc zero))) ∷ []
  sg : Fin 4 → Fin 4
  sg zero = zero
  sg (suc zero) = (suc (suc zero))
  sg (suc (suc zero)) = (suc zero)
  sg (suc (suc (suc zero))) = (suc (suc (suc zero)))
  fact : ∀ i → CL.τs (S.ps ++ qs) (S.f i) ≡ S.σ (sg i)
  fact zero = ≡.trans (CL.τs-++ S.ps qs (S.f zero)) (S.place zero)
  fact (suc zero) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc zero))) (S.place (suc (suc zero)))
  fact (suc (suc zero)) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc zero)))) (S.place (suc zero))
  fact (suc (suc (suc zero))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc zero))))) (S.place (suc (suc (suc zero))))
  moved = CL.move (S.ps ++ qs) {S.f} {λ i → S.σ (sg i)} fact {map CL.ofGen W4.Ld3} {map CL.ofGen W4.Rd3} (Base4.c-base k)

-- bcde: the sorted indices take the roles a b c d e f.
leaf6-bcde : ∀ {n} {s0 s1 s2 s3 s4 s5 : Fin n} (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) (p3 : s3 < s4) (p4 : s4 < s5) →
            PB._≈_ (_===ᶜ_ {n}) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Ld4-bcde ⟫) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Rd4-bcde ⟫)
leaf6-bcde {n} {s0} {s1} {s2} {s3} {s4} {s5} p0 p1 p2 p3 p4 with split6 s5 (Emb6.b5 p0 p1 p2 p3 p4)
... | k , ≡.refl = trans (sym (CL.placeW S.emb W6.Ld4-bcde)) (trans moved (CL.placeW S.emb W6.Rd4-bcde))
  where
  module S = Sorted6 {k} p0 p1 p2 p3 p4
  open PB (_===ᶜ_ {6 ℕ.+ k}) hiding (_===_)
  qs : List (Fin (6 ℕ.+ k) × Fin (6 ℕ.+ k))
  qs = []
  sg : Fin 6 → Fin 6
  sg zero = zero
  sg (suc zero) = (suc zero)
  sg (suc (suc zero)) = (suc (suc zero))
  sg (suc (suc (suc zero))) = (suc (suc (suc zero)))
  sg (suc (suc (suc (suc zero)))) = (suc (suc (suc (suc zero))))
  sg (suc (suc (suc (suc (suc zero))))) = (suc (suc (suc (suc (suc zero)))))
  fact : ∀ i → CL.τs (S.ps ++ qs) (S.f i) ≡ S.σ (sg i)
  fact zero = ≡.trans (CL.τs-++ S.ps qs (S.f zero)) (S.place zero)
  fact (suc zero) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc zero))) (S.place (suc zero))
  fact (suc (suc zero)) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc zero)))) (S.place (suc (suc zero)))
  fact (suc (suc (suc zero))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc zero))))) (S.place (suc (suc (suc zero))))
  fact (suc (suc (suc (suc zero)))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc zero)))))) (S.place (suc (suc (suc (suc zero)))))
  fact (suc (suc (suc (suc (suc zero))))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc (suc zero))))))) (S.place (suc (suc (suc (suc (suc zero))))))
  moved = CL.move (S.ps ++ qs) {S.f} {λ i → S.σ (sg i)} fact {map CL.ofGen W6.Ld4} {map CL.ofGen W6.Rd4} (Base6.c-base k)

-- bced: the sorted indices take the roles a b c e d f.
leaf6-bced : ∀ {n} {s0 s1 s2 s3 s4 s5 : Fin n} (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) (p3 : s3 < s4) (p4 : s4 < s5) →
            PB._≈_ (_===ᶜ_ {n}) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Ld4-bced ⟫) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Rd4-bced ⟫)
leaf6-bced {n} {s0} {s1} {s2} {s3} {s4} {s5} p0 p1 p2 p3 p4 with split6 s5 (Emb6.b5 p0 p1 p2 p3 p4)
... | k , ≡.refl = trans (sym (CL.placeW S.emb W6.Ld4-bced)) (trans moved (CL.placeW S.emb W6.Rd4-bced))
  where
  module S = Sorted6 {k} p0 p1 p2 p3 p4
  open PB (_===ᶜ_ {6 ℕ.+ k}) hiding (_===_)
  qs : List (Fin (6 ℕ.+ k) × Fin (6 ℕ.+ k))
  qs = (S.f (suc (suc (suc zero))) , S.f (suc (suc (suc (suc zero))))) ∷ []
  sg : Fin 6 → Fin 6
  sg zero = zero
  sg (suc zero) = (suc zero)
  sg (suc (suc zero)) = (suc (suc zero))
  sg (suc (suc (suc zero))) = (suc (suc (suc (suc zero))))
  sg (suc (suc (suc (suc zero)))) = (suc (suc (suc zero)))
  sg (suc (suc (suc (suc (suc zero))))) = (suc (suc (suc (suc (suc zero)))))
  fact : ∀ i → CL.τs (S.ps ++ qs) (S.f i) ≡ S.σ (sg i)
  fact zero = ≡.trans (CL.τs-++ S.ps qs (S.f zero)) (S.place zero)
  fact (suc zero) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc zero))) (S.place (suc zero))
  fact (suc (suc zero)) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc zero)))) (S.place (suc (suc zero)))
  fact (suc (suc (suc zero))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc zero))))) (S.place (suc (suc (suc (suc zero)))))
  fact (suc (suc (suc (suc zero)))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc zero)))))) (S.place (suc (suc (suc zero))))
  fact (suc (suc (suc (suc (suc zero))))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc (suc zero))))))) (S.place (suc (suc (suc (suc (suc zero))))))
  moved = CL.move (S.ps ++ qs) {S.f} {λ i → S.σ (sg i)} fact {map CL.ofGen W6.Ld4} {map CL.ofGen W6.Rd4} (Base6.c-base k)

-- cbde: the sorted indices take the roles a c b d e f.
leaf6-cbde : ∀ {n} {s0 s1 s2 s3 s4 s5 : Fin n} (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) (p3 : s3 < s4) (p4 : s4 < s5) →
            PB._≈_ (_===ᶜ_ {n}) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Ld4-cbde ⟫) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Rd4-cbde ⟫)
leaf6-cbde {n} {s0} {s1} {s2} {s3} {s4} {s5} p0 p1 p2 p3 p4 with split6 s5 (Emb6.b5 p0 p1 p2 p3 p4)
... | k , ≡.refl = trans (sym (CL.placeW S.emb W6.Ld4-cbde)) (trans moved (CL.placeW S.emb W6.Rd4-cbde))
  where
  module S = Sorted6 {k} p0 p1 p2 p3 p4
  open PB (_===ᶜ_ {6 ℕ.+ k}) hiding (_===_)
  qs : List (Fin (6 ℕ.+ k) × Fin (6 ℕ.+ k))
  qs = (S.f (suc zero) , S.f (suc (suc zero))) ∷ []
  sg : Fin 6 → Fin 6
  sg zero = zero
  sg (suc zero) = (suc (suc zero))
  sg (suc (suc zero)) = (suc zero)
  sg (suc (suc (suc zero))) = (suc (suc (suc zero)))
  sg (suc (suc (suc (suc zero)))) = (suc (suc (suc (suc zero))))
  sg (suc (suc (suc (suc (suc zero))))) = (suc (suc (suc (suc (suc zero)))))
  fact : ∀ i → CL.τs (S.ps ++ qs) (S.f i) ≡ S.σ (sg i)
  fact zero = ≡.trans (CL.τs-++ S.ps qs (S.f zero)) (S.place zero)
  fact (suc zero) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc zero))) (S.place (suc (suc zero)))
  fact (suc (suc zero)) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc zero)))) (S.place (suc zero))
  fact (suc (suc (suc zero))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc zero))))) (S.place (suc (suc (suc zero))))
  fact (suc (suc (suc (suc zero)))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc zero)))))) (S.place (suc (suc (suc (suc zero)))))
  fact (suc (suc (suc (suc (suc zero))))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc (suc zero))))))) (S.place (suc (suc (suc (suc (suc zero))))))
  moved = CL.move (S.ps ++ qs) {S.f} {λ i → S.σ (sg i)} fact {map CL.ofGen W6.Ld4} {map CL.ofGen W6.Rd4} (Base6.c-base k)

-- cbed: the sorted indices take the roles a c b e d f.
leaf6-cbed : ∀ {n} {s0 s1 s2 s3 s4 s5 : Fin n} (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) (p3 : s3 < s4) (p4 : s4 < s5) →
            PB._≈_ (_===ᶜ_ {n}) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Ld4-cbed ⟫) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Rd4-cbed ⟫)
leaf6-cbed {n} {s0} {s1} {s2} {s3} {s4} {s5} p0 p1 p2 p3 p4 with split6 s5 (Emb6.b5 p0 p1 p2 p3 p4)
... | k , ≡.refl = trans (sym (CL.placeW S.emb W6.Ld4-cbed)) (trans moved (CL.placeW S.emb W6.Rd4-cbed))
  where
  module S = Sorted6 {k} p0 p1 p2 p3 p4
  open PB (_===ᶜ_ {6 ℕ.+ k}) hiding (_===_)
  qs : List (Fin (6 ℕ.+ k) × Fin (6 ℕ.+ k))
  qs = (S.f (suc (suc (suc zero))) , S.f (suc (suc (suc (suc zero))))) ∷ (S.f (suc zero) , S.f (suc (suc zero))) ∷ []
  sg : Fin 6 → Fin 6
  sg zero = zero
  sg (suc zero) = (suc (suc zero))
  sg (suc (suc zero)) = (suc zero)
  sg (suc (suc (suc zero))) = (suc (suc (suc (suc zero))))
  sg (suc (suc (suc (suc zero)))) = (suc (suc (suc zero)))
  sg (suc (suc (suc (suc (suc zero))))) = (suc (suc (suc (suc (suc zero)))))
  fact : ∀ i → CL.τs (S.ps ++ qs) (S.f i) ≡ S.σ (sg i)
  fact zero = ≡.trans (CL.τs-++ S.ps qs (S.f zero)) (S.place zero)
  fact (suc zero) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc zero))) (S.place (suc (suc zero)))
  fact (suc (suc zero)) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc zero)))) (S.place (suc zero))
  fact (suc (suc (suc zero))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc zero))))) (S.place (suc (suc (suc (suc zero)))))
  fact (suc (suc (suc (suc zero)))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc zero)))))) (S.place (suc (suc (suc zero))))
  fact (suc (suc (suc (suc (suc zero))))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc (suc zero))))))) (S.place (suc (suc (suc (suc (suc zero))))))
  moved = CL.move (S.ps ++ qs) {S.f} {λ i → S.σ (sg i)} fact {map CL.ofGen W6.Ld4} {map CL.ofGen W6.Rd4} (Base6.c-base k)

-- bdce: the sorted indices take the roles a b d c e f.
leaf6-bdce : ∀ {n} {s0 s1 s2 s3 s4 s5 : Fin n} (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) (p3 : s3 < s4) (p4 : s4 < s5) →
            PB._≈_ (_===ᶜ_ {n}) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Ld4-bdce ⟫) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Rd4-bdce ⟫)
leaf6-bdce {n} {s0} {s1} {s2} {s3} {s4} {s5} p0 p1 p2 p3 p4 with split6 s5 (Emb6.b5 p0 p1 p2 p3 p4)
... | k , ≡.refl = trans (sym (CL.placeW S.emb W6.Ld4-bdce)) (trans moved (CL.placeW S.emb W6.Rd4-bdce))
  where
  module S = Sorted6 {k} p0 p1 p2 p3 p4
  open PB (_===ᶜ_ {6 ℕ.+ k}) hiding (_===_)
  qs : List (Fin (6 ℕ.+ k) × Fin (6 ℕ.+ k))
  qs = (S.f (suc (suc zero)) , S.f (suc (suc (suc zero)))) ∷ []
  sg : Fin 6 → Fin 6
  sg zero = zero
  sg (suc zero) = (suc zero)
  sg (suc (suc zero)) = (suc (suc (suc zero)))
  sg (suc (suc (suc zero))) = (suc (suc zero))
  sg (suc (suc (suc (suc zero)))) = (suc (suc (suc (suc zero))))
  sg (suc (suc (suc (suc (suc zero))))) = (suc (suc (suc (suc (suc zero)))))
  fact : ∀ i → CL.τs (S.ps ++ qs) (S.f i) ≡ S.σ (sg i)
  fact zero = ≡.trans (CL.τs-++ S.ps qs (S.f zero)) (S.place zero)
  fact (suc zero) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc zero))) (S.place (suc zero))
  fact (suc (suc zero)) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc zero)))) (S.place (suc (suc (suc zero))))
  fact (suc (suc (suc zero))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc zero))))) (S.place (suc (suc zero)))
  fact (suc (suc (suc (suc zero)))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc zero)))))) (S.place (suc (suc (suc (suc zero)))))
  fact (suc (suc (suc (suc (suc zero))))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc (suc zero))))))) (S.place (suc (suc (suc (suc (suc zero))))))
  moved = CL.move (S.ps ++ qs) {S.f} {λ i → S.σ (sg i)} fact {map CL.ofGen W6.Ld4} {map CL.ofGen W6.Rd4} (Base6.c-base k)

-- cebd: the sorted indices take the roles a c e b d f.
leaf6-cebd : ∀ {n} {s0 s1 s2 s3 s4 s5 : Fin n} (p0 : s0 < s1) (p1 : s1 < s2) (p2 : s2 < s3) (p3 : s3 < s4) (p4 : s4 < s5) →
            PB._≈_ (_===ᶜ_ {n}) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Ld4-cebd ⟫) (word (Emb6.emb p0 p1 p2 p3 p4) ⟪ W6.Rd4-cebd ⟫)
leaf6-cebd {n} {s0} {s1} {s2} {s3} {s4} {s5} p0 p1 p2 p3 p4 with split6 s5 (Emb6.b5 p0 p1 p2 p3 p4)
... | k , ≡.refl = trans (sym (CL.placeW S.emb W6.Ld4-cebd)) (trans moved (CL.placeW S.emb W6.Rd4-cebd))
  where
  module S = Sorted6 {k} p0 p1 p2 p3 p4
  open PB (_===ᶜ_ {6 ℕ.+ k}) hiding (_===_)
  qs : List (Fin (6 ℕ.+ k) × Fin (6 ℕ.+ k))
  qs = (S.f (suc (suc zero)) , S.f (suc (suc (suc (suc zero))))) ∷ (S.f (suc (suc zero)) , S.f (suc zero)) ∷ (S.f (suc zero) , S.f (suc (suc (suc zero)))) ∷ []
  sg : Fin 6 → Fin 6
  sg zero = zero
  sg (suc zero) = (suc (suc (suc zero)))
  sg (suc (suc zero)) = (suc zero)
  sg (suc (suc (suc zero))) = (suc (suc (suc (suc zero))))
  sg (suc (suc (suc (suc zero)))) = (suc (suc zero))
  sg (suc (suc (suc (suc (suc zero))))) = (suc (suc (suc (suc (suc zero)))))
  fact : ∀ i → CL.τs (S.ps ++ qs) (S.f i) ≡ S.σ (sg i)
  fact zero = ≡.trans (CL.τs-++ S.ps qs (S.f zero)) (S.place zero)
  fact (suc zero) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc zero))) (S.place (suc (suc (suc zero))))
  fact (suc (suc zero)) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc zero)))) (S.place (suc zero))
  fact (suc (suc (suc zero))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc zero))))) (S.place (suc (suc (suc (suc zero)))))
  fact (suc (suc (suc (suc zero)))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc zero)))))) (S.place (suc (suc zero)))
  fact (suc (suc (suc (suc (suc zero))))) = ≡.trans (CL.τs-++ S.ps qs (S.f (suc (suc (suc (suc (suc zero))))))) (S.place (suc (suc (suc (suc (suc zero))))))
  moved = CL.move (S.ps ++ qs) {S.f} {λ i → S.σ (sg i)} fact {map CL.ofGen W6.Ld4} {map CL.ofGen W6.Rd4} (Base6.c-base k)

------------------------------------------------------------------------
-- Clément's relations derive (d3) and (d4), at any indices

c-d3 : ∀ {n} {a b c d : Fin n} (ab : a < b) (ac : a < c) (bd : b < d) (cd : c < d) → b ≢ c →
       PB._≈_ (_===ᶜ_ {n}) ((H c d cd • H a c ac • H b d bd) ^ 4) (H a b ab • H c d cd)
c-d3 {n} {a} {b} {c} {d} ab ac bd cd b≢c with FinP.<-cmp b c
... | tri< b<c _ _ = PB.trans (PP.by-assoc _ auto) (PB.trans (leaf4-bc ab b<c cd) (PP.by-assoc _ auto))
... | tri≈ _ e _ = ⊥-elim (b≢c e)
... | tri> _ _ c<b = PB.trans (PP.by-assoc _ auto) (PB.trans (leaf4-cb ac c<b bd) (PP.by-assoc _ auto))

c-d4 : ∀ {n} {a b c d e f : Fin n}
       (ab : a < b) (ac : a < c) (bd : b < d) (ce : c < e) (df : d < f) (ef : e < f) →
       b ≢ c → b ≢ e → d ≢ c → d ≢ e →
       PB._≈_ (_===ᶜ_ {n})
         ((H a c ac • H b d bd • H a b ab • H a c ac • H b d bd • X c e ce • X d f df) ^ 3)
         (H c e ce • H d f df • H e f ef • H c e ce • H d f df • X c e ce • X d f df)
c-d4 {n} {a} {b} {c} {d} {e} {f} ab ac bd ce df ef b≢c b≢e d≢c d≢e with FinP.<-cmp b c
... | tri≈ _ eq _ = ⊥-elim (b≢c eq)
... | tri< b<c _ _ with FinP.<-cmp d c
...   | tri< d<c _ _ = PB.trans (PP.by-assoc _ auto) (PB.trans (leaf6-bdce ab bd d<c ce ef) (PP.by-assoc _ auto))
...   | tri≈ _ eq _ = ⊥-elim (d≢c eq)
...   | tri> _ _ c<d with FinP.<-cmp d e
...     | tri< d<e _ _ = PB.trans (PP.by-assoc _ auto) (PB.trans (leaf6-bcde ab b<c c<d d<e ef) (PP.by-assoc _ auto))
...     | tri≈ _ eq _ = ⊥-elim (d≢e eq)
...     | tri> _ _ e<d = PB.trans (PP.by-assoc _ auto) (PB.trans (leaf6-bced ab b<c ce e<d df) (PP.by-assoc _ auto))
c-d4 {n} {a} {b} {c} {d} {e} {f} ab ac bd ce df ef b≢c b≢e d≢c d≢e | tri> _ _ c<b with FinP.<-cmp e b
...   | tri< e<b _ _ = PB.trans (PP.by-assoc _ auto) (PB.trans (leaf6-cebd ac ce e<b bd df) (PP.by-assoc _ auto))
...   | tri≈ _ eq _ = ⊥-elim (b≢e (≡.sym eq))
...   | tri> _ _ b<e with FinP.<-cmp d e
...     | tri< d<e _ _ = PB.trans (PP.by-assoc _ auto) (PB.trans (leaf6-cbde ac c<b bd d<e ef) (PP.by-assoc _ auto))
...     | tri≈ _ eq _ = ⊥-elim (d≢e eq)
...     | tri> _ _ e<d = PB.trans (PP.by-assoc _ auto) (PB.trans (leaf6-cbed ac c<b b<e e<d df) (PP.by-assoc _ auto))

------------------------------------------------------------------------
-- The two sets of relations generate the same congruence

module _ {n : ℕ} where

  -- Figure 6 derives each of Clément's relations.
  fig6⇒clement : ∀ {u v} → u ===ᶜ v → PB._≈_ (_===_ {n}) u v
  fig6⇒clement e1 = TC.e1′
  fig6⇒clement (e2 jk) = TC.e2′ jk
  fig6⇒clement (e3 jk) = TC.e3′ jk
  fig6⇒clement (e4 jk) = TC.e4′ jk
  fig6⇒clement (e5 jk lj lk) = TC.e5′ jk lj lk
  fig6⇒clement (e6 jk lj lk) = TC.e6′ jk lj lk
  fig6⇒clement (e7 x₁ x₂ x₃ x₄ x₅ x₆) = TC.e7′ x₁ x₂ x₃ x₄ x₅ x₆
  fig6⇒clement (e8 x₁ x₂ x₃ x₄ x₅ x₆) = TC.e8′ x₁ x₂ x₃ x₄ x₅ x₆
  fig6⇒clement (e9 x₁ x₂ x₃ x₄ x₅ x₆) = TC.e9′ x₁ x₂ x₃ x₄ x₅ x₆
  fig6⇒clement (e10 jk) = TC.e10′ jk
  fig6⇒clement (e11 jk) = TC.e11′ jk
  fig6⇒clement (e12 x₁ x₂ x₃) = TC.e12′ x₁ x₂ x₃
  fig6⇒clement (e13 x₁ x₂ x₃) = TC.e13′ x₁ x₂ x₃
  fig6⇒clement (e14 x₁ x₂ x₃) = TC.e14′ x₁ x₂ x₃
  fig6⇒clement (e15 x₁ x₂ x₃) = TC.e15′ x₁ x₂ x₃
  fig6⇒clement (e16 jk) = TC.e16′ jk
  fig6⇒clement (e17 jk) = TC.e17′ jk
  fig6⇒clement (e18 jk) = TC.e18′ jk
  fig6⇒clement (e19 x₁ x₂ x₃ x₄ x₅) = TC.e19′ x₁ x₂ x₃ x₄ x₅
  fig6⇒clement (e20 t0 t1 t2 t3 p01 p02 p13) = hp-e20 t0 t1 t2 t3 p01 p02 p13
  fig6⇒clement (e21 t0 t1 t2 t3 t4 t5 p01 p02 p13 p04 p15) = hp-e21 t0 t1 t2 t3 t4 t5 p01 p02 p13 p04 p15

  -- Clément's relations derive each relation of Figure 6.
  clement⇒fig6 : ∀ {u v} → u === v → PB._≈_ (_===ᶜ_ {n}) u v
  clement⇒fig6 a1 = CL.c-local L.a1
  clement⇒fig6 (a2 p) = CL.c-local (L.a2 p)
  clement⇒fig6 (a3 p) = CL.c-local (L.a3 p)
  clement⇒fig6 (b1 x) = CL.c-local (L.b1 x)
  clement⇒fig6 (b2 p x y) = CL.c-local (L.b2 p x y)
  clement⇒fig6 (b3 p q x y z t) = CL.c-local (L.b3 p q x y z t)
  clement⇒fig6 (b4 p x y) = CL.c-local (L.b4 p x y)
  clement⇒fig6 (b5 p q x y z t) = CL.c-local (L.b5 p q x y z t)
  clement⇒fig6 (b6 p q x y z t) = CL.c-local (L.b6 p q x y z t)
  clement⇒fig6 (c1 p) = CL.c-local (L.c1 p)
  clement⇒fig6 (c2 p q) = CL.c-local (L.c2 p q)
  clement⇒fig6 (c3 p q) = CL.c-local (L.c3 p q)
  clement⇒fig6 (c4 p q) = CL.c-local (L.c4 p q)
  clement⇒fig6 (c5 p q) = CL.c-local (L.c5 p q)
  clement⇒fig6 (d1 p) = CL.c-local (L.d1 p)
  clement⇒fig6 (d2 p) = CL.c-local (L.d2 p)
  clement⇒fig6 (d3 ab ac bd cd bc) = c-d3 ab ac bd cd bc
  clement⇒fig6 (d4 ab ac bd ce df ef bc be dc de) = c-d4 ab ac bd ce df ef bc be dc de

  -- The congruences coincide.
  equivalent : ∀ {u v : Word (Gen n)} → PB._≈_ (_===_ {n}) u v ⇔ PB._≈_ (_===ᶜ_ {n}) u v
  equivalent = mk⇔ (lift clement⇒fig6) (lift fig6⇒clement)
