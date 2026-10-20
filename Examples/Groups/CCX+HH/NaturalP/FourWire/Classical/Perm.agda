------------------------------------------------------------------------
-- Presentations of groups
--
-- Permutations of n points, as the vector of the images.
--
-- `mul a b` is the composite in which b acts first (the matrix product
-- A B), and it is a monoid: `mul-assoc`, `mul-idˡ`, `mul-idʳ`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Perm (n : ℕ) where

open import Data.Fin.Base using (Fin)
open import Data.Vec.Base using (Vec ; map ; lookup ; tabulate)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; cong ; sym ; trans)

P : Set
P = Vec (Fin n) n

ID : P
ID = tabulate (λ i → i)

mul : P → P → P
mul a b = map (lookup a) b

vec-ext : ∀ {A : Set} {v w : Vec A n} → (∀ i → lookup v i ≡ lookup w i) → v ≡ w
vec-ext {v = v} {w} p = trans (sym (VP.tabulate∘lookup v))
  (trans (VP.tabulate-cong p) (VP.tabulate∘lookup w))

lookup-mul : ∀ a b i → lookup (mul a b) i ≡ lookup a (lookup b i)
lookup-mul a b i = VP.lookup-map i (lookup a) b

mul-assoc : ∀ a b c → mul (mul a b) c ≡ mul a (mul b c)
mul-assoc a b c = vec-ext λ i → trans (lookup-mul (mul a b) c i)
  (trans (lookup-mul a b (lookup c i))
    (sym (trans (lookup-mul a (mul b c) i) (cong (lookup a) (lookup-mul b c i)))))

mul-idˡ : ∀ b → mul ID b ≡ b
mul-idˡ b = vec-ext λ i → trans (lookup-mul ID b i) (VP.lookup∘tabulate (λ j → j) (lookup b i))

mul-idʳ : ∀ a → mul a ID ≡ a
mul-idʳ a = vec-ext λ i → trans (lookup-mul a ID i) (cong (lookup a) (VP.lookup∘tabulate (λ j → j) i))
