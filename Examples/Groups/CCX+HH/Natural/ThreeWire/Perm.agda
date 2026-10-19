------------------------------------------------------------------------
-- Presentations of groups
--
-- Signed permutations of the eight levels of three wires.
--
-- A signed permutation is the vector of the images of the levels, each
-- with a sign (true: negated).  `mul a b` is the matrix product A B
-- (b acts first), and it is a monoid: `mul-assoc`, `mul-idˡ`,
-- `mul-idʳ`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Perm where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
import Data.Bool.Properties as BP
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; map ; lookup ; tabulate)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; cong ; cong₂ ; sym ; trans)

SP : Set
SP = Vec (Fin 8 × Bool) 8

ID : SP
ID = tabulate (λ i → i , false)

act : SP → Fin 8 × Bool → Fin 8 × Bool
act a (j , s) = proj₁ (lookup a j) , (s xor proj₂ (lookup a j))

mul : SP → SP → SP
mul a b = map (act a) b

vec-ext : ∀ {A : Set} {v w : Vec A 8} → (∀ i → lookup v i ≡ lookup w i) → v ≡ w
vec-ext {v = v} {w} p = trans (sym (VP.tabulate∘lookup v))
  (trans (VP.tabulate-cong p) (VP.tabulate∘lookup w))

lookup-mul : ∀ a b i → lookup (mul a b) i ≡ act a (lookup b i)
lookup-mul a b i = VP.lookup-map i (act a) b

mul-assoc : ∀ a b c → mul (mul a b) c ≡ mul a (mul b c)
mul-assoc a b c = vec-ext λ i → trans (lookup-mul (mul a b) c i)
  (trans (step (lookup c i)) (sym (trans (lookup-mul a (mul b c) i)
    (cong (act a) (lookup-mul b c i)))))
  where
  step : ∀ p → act (mul a b) p ≡ act a (act b p)
  step (j , s) rewrite lookup-mul a b j =
    cong (proj₁ (lookup a (proj₁ (lookup b j))) ,_)
      (sym (BP.xor-assoc s (proj₂ (lookup b j)) (proj₂ (lookup a (proj₁ (lookup b j))))))

mul-idˡ : ∀ b → mul ID b ≡ b
mul-idˡ b = vec-ext λ i → trans (lookup-mul ID b i) (step (lookup b i))
  where
  step : ∀ p → act ID p ≡ p
  step (j , s) rewrite VP.lookup∘tabulate (λ i → i , false) j =
    cong (j ,_) (BP.xor-identityʳ s)

mul-idʳ : ∀ a → mul a ID ≡ a
mul-idʳ a = vec-ext λ i → trans (lookup-mul a ID i)
  (Eq.cong (act a) (VP.lookup∘tabulate (λ i → i , false) i))
