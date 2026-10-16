------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffCS₂'s encodings into Bian and Selinger's Clifford+CS
-- presentations, with their scalars
--
-- On three wires into the 3-qubit presentation (Examples.Groups.
-- Clifford+CS-3qubit): H on wire k is K_k, with one ω (H = ω K), S and
-- CS are theirs (CS on the wires 0 1 their CS01, on 1 2 CS12), the swap
-- three CNOTs (their Swap01, Swap12), and ω is ε with one ω.  On two
-- wires, one and none, into the two-level presentation of U₄, U₂ and
-- U₁ over 𝔻[i] (Examples.Groups.Clifford+CS-TwoLevel), index a = 2 x₀ +
-- x₁ with wire 0 the high bit: H is K on both pairs of indices its wire
-- exchanges, S the phase i on the indices where its wire is 1, CS on
-- index 3, the swap X_[1,2].  The scalar i is iI, resp. i on every
-- index.  Every gate is checked as a closed matrix (Clifford+CS.Bridge,
-- ViaS).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Encodings where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; T)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (ℕ ; z≤n ; s≤s)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (proj₁)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; trans ; sym ; cong)
open import Relation.Nullary using (does ; yes)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Quantum.Synthesis.Matrix using (Matrix)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring using (D ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_ ; _≟ᴰ_)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics as TS
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
import Examples.Groups.Clifford+CS-TwoLevel.Semantics as CSS
open CSS using (actV ; set₁ ; set₂)
open import Examples.Groups.Clifford+CS-3qubit.Theorem using (module CliffordCS)
import Examples.Groups.Clifford+CS-3qubit.Presentation as BSP

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Clifford+CS.Semantics as Sem
open import Examples.Independence.Clifford+CS.Bridge
open import Examples.Independence.Semantics.Reading using (⟪_⟫ ; _ᵀ ; module Mat)

module BS = CliffordCS

------------------------------------------------------------------------
-- Indices

private
  0<1 : _<_ {4} {4} ₀ ₁
  0<1 = s≤s z≤n
  0<2 : _<_ {4} {4} ₀ ₂
  0<2 = s≤s z≤n
  1<2 : _<_ {4} {4} ₁ ₂
  1<2 = s≤s (s≤s z≤n)
  1<3 : _<_ {4} {4} ₁ ₃
  1<3 = s≤s (s≤s z≤n)
  2<3 : _<_ {4} {4} ₂ ₃
  2<3 = s≤s (s≤s (s≤s z≤n))
  0<1′ : _<_ {2} {2} ₀ ₁
  0<1′ = s≤s z≤n

------------------------------------------------------------------------
-- The encodings and their ω counts

ℰ₃ : Gen 3 → Word BS.Gen
ℰ₃ (gate₀ ⌈ ω-gate ⌉)       = ε
ℰ₃ (gate₁ ⌈ H-gate ⌉)       = BS.K0
ℰ₃ (gate₁ ⌈ S-gate ⌉)       = BS.S0
ℰ₃ (gate₂ ⌈ CS-gate ⌉)      = BS.CS01
ℰ₃ (gate₂ swap)             = BS.Swap01
ℰ₃ (gate₀ ⌈ ω-gate ⌉ ↥)     = ε
ℰ₃ (gate₁ ⌈ H-gate ⌉ ↥)     = BS.K1
ℰ₃ (gate₁ ⌈ S-gate ⌉ ↥)     = BS.S1
ℰ₃ (gate₂ ⌈ CS-gate ⌉ ↥)    = BS.CS12
ℰ₃ (gate₂ swap ↥)           = BS.Swap12
ℰ₃ (gate₀ ⌈ ω-gate ⌉ ↥ ↥)   = ε
ℰ₃ (gate₁ ⌈ H-gate ⌉ ↥ ↥)   = BS.K2
ℰ₃ (gate₁ ⌈ S-gate ⌉ ↥ ↥)   = BS.S2
ℰ₃ (gate₀ ⌈ ω-gate ⌉ ↥ ↥ ↥) = ε
ℰ₃ (gate₃ ⌈ () ⌉)

c₃ : Gen 3 → ℕ
c₃ (gate₀ ⌈ ω-gate ⌉)       = 1
c₃ (gate₁ ⌈ H-gate ⌉)       = 1
c₃ (gate₀ ⌈ ω-gate ⌉ ↥)     = 1
c₃ (gate₁ ⌈ H-gate ⌉ ↥)     = 1
c₃ (gate₀ ⌈ ω-gate ⌉ ↥ ↥)   = 1
c₃ (gate₁ ⌈ H-gate ⌉ ↥ ↥)   = 1
c₃ (gate₀ ⌈ ω-gate ⌉ ↥ ↥ ↥) = 1
c₃ _                        = 0

ℰ₂ : Gen 2 → Word (TL.Gen 4)
ℰ₂ (gate₀ ⌈ ω-gate ⌉)     = ε
ℰ₂ (gate₁ ⌈ H-gate ⌉)     = TL.K ₀ ₂ 0<2 • TL.K ₁ ₃ 1<3
ℰ₂ (gate₁ ⌈ S-gate ⌉)     = TL.i ₂ • TL.i ₃
ℰ₂ (gate₂ ⌈ CS-gate ⌉)    = TL.i ₃
ℰ₂ (gate₂ swap)           = TL.X ₁ ₂ 1<2
ℰ₂ (gate₀ ⌈ ω-gate ⌉ ↥)   = ε
ℰ₂ (gate₁ ⌈ H-gate ⌉ ↥)   = TL.K ₀ ₁ 0<1 • TL.K ₂ ₃ 2<3
ℰ₂ (gate₁ ⌈ S-gate ⌉ ↥)   = TL.i ₁ • TL.i ₃
ℰ₂ (gate₀ ⌈ ω-gate ⌉ ↥ ↥) = ε

c₂ : Gen 2 → ℕ
c₂ (gate₀ ⌈ ω-gate ⌉)     = 1
c₂ (gate₁ ⌈ H-gate ⌉)     = 1
c₂ (gate₀ ⌈ ω-gate ⌉ ↥)   = 1
c₂ (gate₁ ⌈ H-gate ⌉ ↥)   = 1
c₂ (gate₀ ⌈ ω-gate ⌉ ↥ ↥) = 1
c₂ _                      = 0

ℰ₁ : Gen 1 → Word (TL.Gen 2)
ℰ₁ (gate₀ ⌈ ω-gate ⌉)   = ε
ℰ₁ (gate₁ ⌈ H-gate ⌉)   = TL.K ₀ ₁ 0<1′
ℰ₁ (gate₁ ⌈ S-gate ⌉)   = TL.i ₁
ℰ₁ (gate₀ ⌈ ω-gate ⌉ ↥) = ε

c₁ : Gen 1 → ℕ
c₁ (gate₁ ⌈ S-gate ⌉) = 0
c₁ _                  = 1

ℰ₀ : Gen 0 → Word (TL.Gen 1)
ℰ₀ (gate₀ ⌈ ω-gate ⌉) = ε

c₀ : Gen 0 → ℕ
c₀ _ = 1

-- The scalar i.
J₃ : Word BS.Gen
J₃ = BS.iI

J₂ : Word (TL.Gen 4)
J₂ = TL.i ₀ • TL.i ₁ • TL.i ₂ • TL.i ₃

J₁ : Word (TL.Gen 2)
J₁ = TL.i ₀ • TL.i ₁

J₀ : Word (TL.Gen 1)
J₀ = TL.i ₀

------------------------------------------------------------------------
-- Matrices decided entry by entry, as one boolean
--
-- Eq.refl between two matrices makes the conversion checker compare them
-- entry by entry, reducing each entry afresh, so that the matrix of an
-- encoded word is computed again for every entry; the boolean is one
-- evaluation.

private
  ∧-l : (x y : Bool) → T (x ∧ y) → T x
  ∧-l true y t = tt

  ∧-r : (x y : Bool) → T (x ∧ y) → T y
  ∧-r true y t = t

  allF : (k : ℕ) → (Fin k → Bool) → Bool
  allF ℕ.zero    f = true
  allF (ℕ.suc k) f = f zero ∧ allF k (λ i → f (suc i))

  allF-sound : (k : ℕ) (f : Fin k → Bool) → T (allF k f) → (i : Fin k) → T (f i)
  allF-sound (ℕ.suc k) f t zero    = ∧-l (f zero) (allF k (λ i → f (suc i))) t
  allF-sound (ℕ.suc k) f t (suc i) =
    allF-sound k (λ j → f (suc j)) (∧-r (f zero) (allF k (λ i → f (suc i))) t) i

  dec-sound : (a b : D) → T (does (a ≟ᴰ b)) → a ≡ b
  dec-sound a b t with a ≟ᴰ b
  ... | yes e = e

  eqMat : {m n : ℕ} → Matrix m n D → Matrix m n D → Bool
  eqMat {m} {n} M N = allF m (λ r → allF n (λ c → does (TS.ent M r c ≟ᴰ TS.ent N r c)))

  eqMat-sound : {m n : ℕ} (M N : Matrix m n D) → T (eqMat M N) → M ≡ N
  eqMat-sound {m} {n} M N t = TS.mat-ext λ r c →
    dec-sound (TS.ent M r c) (TS.ent N r c)
      (allF-sound n (λ c → does (TS.ent M r c ≟ᴰ TS.ent N r c))
        (allF-sound m (λ r → allF n (λ c → does (TS.ent M r c ≟ᴰ TS.ent N r c))) t r) c)

------------------------------------------------------------------------
-- The matrices

F₃ : Word BS.Gen → _
F₃ u = proj₁ (BSP.⟦ u ⟧)

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  gen₃ : (g : Gen 3) → Mat.mat (⟪ Sem.⟦ g ⟧₀ ⟫ ᵀ) ≡ ωs (c₃ g) (mapι (F₃ (ℰ₃ g)))
  gen₃ (gate₀ ⌈ ω-gate ⌉) = eqMat-sound _ _ tt
  gen₃ (gate₁ ⌈ H-gate ⌉) = eqMat-sound _ _ tt
  gen₃ (gate₁ ⌈ S-gate ⌉) = eqMat-sound _ _ tt
  gen₃ (gate₂ ⌈ CS-gate ⌉) = eqMat-sound _ _ tt
  gen₃ (gate₂ swap) = eqMat-sound _ _ tt
  gen₃ (gate₀ ⌈ ω-gate ⌉ ↥) = eqMat-sound _ _ tt
  gen₃ (gate₁ ⌈ H-gate ⌉ ↥) = eqMat-sound _ _ tt
  gen₃ (gate₁ ⌈ S-gate ⌉ ↥) = eqMat-sound _ _ tt
  gen₃ (gate₂ ⌈ CS-gate ⌉ ↥) = eqMat-sound _ _ tt
  gen₃ (gate₂ swap ↥) = eqMat-sound _ _ tt
  gen₃ (gate₀ ⌈ ω-gate ⌉ ↥ ↥) = eqMat-sound _ _ tt
  gen₃ (gate₁ ⌈ H-gate ⌉ ↥ ↥) = eqMat-sound _ _ tt
  gen₃ (gate₁ ⌈ S-gate ⌉ ↥ ↥) = eqMat-sound _ _ tt
  gen₃ (gate₀ ⌈ ω-gate ⌉ ↥ ↥ ↥) = eqMat-sound _ _ tt
  gen₃ (gate₃ ⌈ () ⌉)

  gen₂ : (g : Gen 2) → Mat.mat (⟪ Sem.⟦ g ⟧₀ ⟫ ᵀ) ≡ ωs (c₂ g) (mapι (CSS.⟦ ℰ₂ g ⟧ᵐ))
  gen₂ (gate₀ ⌈ ω-gate ⌉) = eqMat-sound _ _ tt
  gen₂ (gate₁ ⌈ H-gate ⌉) = eqMat-sound _ _ tt
  gen₂ (gate₁ ⌈ S-gate ⌉) = eqMat-sound _ _ tt
  gen₂ (gate₂ ⌈ CS-gate ⌉) = eqMat-sound _ _ tt
  gen₂ (gate₂ swap) = eqMat-sound _ _ tt
  gen₂ (gate₀ ⌈ ω-gate ⌉ ↥) = eqMat-sound _ _ tt
  gen₂ (gate₁ ⌈ H-gate ⌉ ↥) = eqMat-sound _ _ tt
  gen₂ (gate₁ ⌈ S-gate ⌉ ↥) = eqMat-sound _ _ tt
  gen₂ (gate₀ ⌈ ω-gate ⌉ ↥ ↥) = eqMat-sound _ _ tt

  gen₁ : (g : Gen 1) → Mat.mat (⟪ Sem.⟦ g ⟧₀ ⟫ ᵀ) ≡ ωs (c₁ g) (mapι (CSS.⟦ ℰ₁ g ⟧ᵐ))
  gen₁ (gate₀ ⌈ ω-gate ⌉) = eqMat-sound _ _ tt
  gen₁ (gate₁ ⌈ H-gate ⌉) = eqMat-sound _ _ tt
  gen₁ (gate₁ ⌈ S-gate ⌉) = eqMat-sound _ _ tt
  gen₁ (gate₀ ⌈ ω-gate ⌉ ↥) = eqMat-sound _ _ tt

  gen₀ : (g : Gen 0) → Mat.mat (⟪ Sem.⟦ g ⟧₀ ⟫ ᵀ) ≡ ωs (c₀ g) (mapι (CSS.⟦ ℰ₀ g ⟧ᵐ))
  gen₀ (gate₀ ⌈ ω-gate ⌉) = eqMat-sound _ _ tt

  -- The scalar words are i times the identity.
  J₃-i : mapι (F₃ J₃) ≡ ωs 2 (mapι (CSS.𝕀 {8}))
  J₃-i = eqMat-sound _ _ tt

  J₂-i : mapι (CSS.⟦ J₂ ⟧ᵐ) ≡ ωs 2 (mapι (CSS.𝕀 {4}))
  J₂-i = eqMat-sound _ _ tt

  J₁-i : mapι (CSS.⟦ J₁ ⟧ᵐ) ≡ ωs 2 (mapι (CSS.𝕀 {2}))
  J₁-i = eqMat-sound _ _ tt

  J₀-i : mapι (CSS.⟦ J₀ ⟧ᵐ) ≡ ωs 2 (mapι (CSS.𝕀 {1}))
  J₀-i = eqMat-sound _ _ tt
