------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level reading of P′: the kit
--
-- Every rule of `Rules` is sound for the two-level congruence: the
-- asG-images of its sides are equal by Bian and Selinger's relations.
-- This module holds what those derivations share — the word kit over
-- the two-level relation, total commutation of the phases, and the
-- crossing lemmas: a phase crosses an exchange with its index
-- transposed (`cross`, `crossʳ`, through the model's swapF), and the
-- phase pair of an exchange's own indices passes a K pair (relation
-- (17)).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.SoundBase (N : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (zero ; suc ; _+_)
open import Data.Fin.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.Reasoning.Setoid as SR
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _^_)

import Presentation.Base as PB
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (i ; X ; K ; X-gen ; K-gen ; i-gen)

open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm N
  using (swapF ; swapF-a ; swapF-b ; swapF-o ; swapF-invol)

open PB (TL._===_ {N}) public
  using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
open import Presentation.Properties (TL._===_ {N}) public
  using (word-setoid ; ^-suc ; ^-+ ; pow-comm ; comm⇒pow-comm ; ^-• ; ^^ ;
         ^-cong ; ε^k=ε ; by-assoc)
open SR word-setoid public

private
  WT : Set
  WT = Word (TL.Gen N)

------------------------------------------------------------------------
-- The kit

front : ∀ {a b} (s : WT) → a ≈ b → a • s ≈ b • s
front s e = cong e refl

back : ∀ (p : WT) {a b} → a ≈ b → p • a ≈ p • b
back p e = cong refl e

refl≡ : ∀ {w v : WT} → w ≡ v → w ≈ v
refl≡ Eq.refl = refl

-- Cancelling an inverse pair at the left.
cancelˡ⁻ : ∀ {c c′} (s : WT) → c • c′ ≈ ε → c • (c′ • s) ≈ s
cancelˡ⁻ s e = trans (sym assoc) (trans (front s e) left-unit)

-- An involution flips a crossing equation.
conj-flip : ∀ {x a b : WT} → x • x ≈ ε → a • x ≈ x • b → x • a ≈ b • x
conj-flip {x} {a} {b} ii e = begin
  x • a                ≈⟨ sym right-unit ⟩
  (x • a) • ε          ≈⟨ back (x • a) (sym ii) ⟩
  (x • a) • (x • x)    ≈⟨ assoc ⟩
  x • (a • (x • x))    ≈⟨ back x (sym assoc) ⟩
  x • ((a • x) • x)    ≈⟨ back x (front x e) ⟩
  x • ((x • b) • x)    ≈⟨ sym assoc ⟩
  (x • (x • b)) • x    ≈⟨ front x (sym assoc) ⟩
  ((x • x) • b) • x    ≈⟨ front x (front b ii) ⟩
  (ε • b) • x          ≈⟨ front x left-unit ⟩
  b • x ∎

-- Two two-factor words commute once every factor of one commutes with
-- every factor of the other.
comm-pair : ∀ (u v x y : WT) →
            u • x ≈ x • u → u • y ≈ y • u → v • x ≈ x • v → v • y ≈ y • v →
            (u • v) • (x • y) ≈ (x • y) • (u • v)
comm-pair u v x y ux uy vx vy = begin
  (u • v) • (x • y)    ≈⟨ assoc ⟩
  u • (v • (x • y))    ≈⟨ back u (sym assoc) ⟩
  u • ((v • x) • y)    ≈⟨ back u (front y vx) ⟩
  u • ((x • v) • y)    ≈⟨ back u assoc ⟩
  u • (x • (v • y))    ≈⟨ back u (back x vy) ⟩
  u • (x • (y • v))    ≈⟨ sym assoc ⟩
  (u • x) • (y • v)    ≈⟨ front (y • v) ux ⟩
  (x • u) • (y • v)    ≈⟨ assoc ⟩
  x • (u • (y • v))    ≈⟨ back x (sym assoc) ⟩
  x • ((u • y) • v)    ≈⟨ back x (front v uy) ⟩
  x • ((y • u) • v)    ≈⟨ back x assoc ⟩
  x • (y • (u • v))    ≈⟨ sym assoc ⟩
  (x • y) • (u • v) ∎

------------------------------------------------------------------------
-- The phases commute, totally

icomm : ∀ (x y : Fin N) → i x • i y ≈ i y • i x
icomm x y = go (x ≟ y)
  where
  go : Dec (x ≡ y) → i x • i y ≈ i y • i x
  go (yes Eq.refl) = refl
  go (no ne)       = axiom (TL.comm-ii ne)

-- Powers of phases commute with powers of phases.
ipow-comm : ∀ (x y : Fin N) (m n : ℕ) → i x ^ m • i y ^ n ≈ i y ^ n • i x ^ m
ipow-comm x y m n = comm⇒pow-comm m n (icomm x y)

-- The order of a phase.
i⁴ : ∀ (x : Fin N) → i x ^ 4 ≈ ε
i⁴ x = axiom TL.order-i

------------------------------------------------------------------------
-- A phase crosses an exchange, its index transposed

module _ (a b : Fin N) .(ab : Data.Fin._<_ a b) where

  private
    Xab : WT
    Xab = X a b ab

  X² : Xab • Xab ≈ ε
  X² = axiom (TL.order-X ab)

  -- i k • X j k = X j k • i j is the axiom; the other three
  -- configurations come from it by the involution and disjointness.
  cross : ∀ (x : Fin N) → i x • Xab ≈ Xab • i (swapF a b x)
  cross x = go (x ≟ a) (x ≟ b)
    where
    go : Dec (x ≡ a) → Dec (x ≡ b) → i x • Xab ≈ Xab • i (swapF a b x)
    go (yes Eq.refl) _ =
      trans (sym (conj-flip X² (axiom (TL.swap-iX ab))))
            (back Xab (refl≡ (Eq.cong i (Eq.sym (swapF-a a b)))))
    go (no xa) (yes Eq.refl) =
      trans (axiom (TL.swap-iX ab))
            (back Xab (refl≡ (Eq.cong i (Eq.sym (swapF-b a b)))))
    go (no xa) (no xb) =
      trans (axiom (TL.comm-iX ab xa xb))
            (back Xab (refl≡ (Eq.cong i (Eq.sym (swapF-o a b x xa xb)))))

  crossʳ : ∀ (x : Fin N) → Xab • i x ≈ i (swapF a b x) • Xab
  crossʳ x = conj-flip X² (cross x)

  -- A power crosses the same way.
  cross-pow : ∀ (x : Fin N) (n : ℕ) →
              i x ^ n • Xab ≈ Xab • i (swapF a b x) ^ n
  cross-pow x zero = trans left-unit (sym right-unit)
  cross-pow x (suc zero) = cross x
  cross-pow x (suc (suc n)) = begin
    (i x • i x ^ suc n) • Xab
      ≈⟨ assoc ⟩
    i x • (i x ^ suc n • Xab)
      ≈⟨ back (i x) (cross-pow x (suc n)) ⟩
    i x • (Xab • i (swapF a b x) ^ suc n)
      ≈⟨ sym assoc ⟩
    (i x • Xab) • i (swapF a b x) ^ suc n
      ≈⟨ front _ (cross x) ⟩
    (Xab • i (swapF a b x)) • i (swapF a b x) ^ suc n
      ≈⟨ assoc ⟩
    Xab • (i (swapF a b x) • i (swapF a b x) ^ suc n) ∎

  crossʳ-pow : ∀ (x : Fin N) (n : ℕ) →
               Xab • i x ^ n ≈ i (swapF a b x) ^ n • Xab
  crossʳ-pow x n = conj-flip X² (cross-pow x n)

  -- The crossings with the image named.
  cross-at : ∀ {x y : Fin N} → swapF a b x ≡ y → i x • Xab ≈ Xab • i y
  cross-at {x} e = trans (cross x) (back Xab (refl≡ (Eq.cong i e)))

  crossʳ-at : ∀ {x y : Fin N} → swapF a b x ≡ y → Xab • i x ≈ i y • Xab
  crossʳ-at {x} e = trans (crossʳ x) (front Xab (refl≡ (Eq.cong i e)))

  cross-pow-at : ∀ {x y : Fin N} (n : ℕ) → swapF a b x ≡ y →
                 i x ^ n • Xab ≈ Xab • i y ^ n
  cross-pow-at {x} n e =
    trans (cross-pow x n) (back Xab (refl≡ (Eq.cong (λ z → i z ^ n) e)))

  crossʳ-pow-at : ∀ {x y : Fin N} (n : ℕ) → swapF a b x ≡ y →
                  Xab • i x ^ n ≈ i y ^ n • Xab
  crossʳ-pow-at {x} n e =
    trans (crossʳ-pow x n) (front Xab (refl≡ (Eq.cong (λ z → i z ^ n) e)))

------------------------------------------------------------------------
-- The pair of a K's own phases

-- Relation (17): the phase pair of a K's indices passes it.
iiK : ∀ (c d : Fin N) .(cd : Data.Fin._<_ c d) →
      (i c • i d) • K c d cd ≈ K c d cd • (i c • i d)
iiK c d cd = trans assoc (sym (axiom (TL.rel-15 cd)))

-- Relation (18): a K squared against its phases vanishes.
K²ii : ∀ (c d : Fin N) .(cd : Data.Fin._<_ c d) →
       K c d cd • (K c d cd • (i c • i d)) ≈ ε
K²ii c d cd = trans (sym assoc) (axiom (TL.rel-16 cd))

-- A fifth phase cancels.
i-mod4 : ∀ (x : Fin N) (t : ℕ) → i x ^ (4 + t) ≈ i x ^ t
i-mod4 x t = begin
  i x ^ (4 + t)         ≈⟨ ^-+ (i x) 4 t ⟩
  i x ^ 4 • i x ^ t     ≈⟨ front _ (i⁴ x) ⟩
  ε • i x ^ t           ≈⟨ left-unit ⟩
  i x ^ t ∎
