------------------------------------------------------------------------
-- Presentations of groups
--
-- Adjacent-pair operators respect concatenation of complete pair blocks.
-- This elementary vector lemma bridges the source IH recursion and the
-- independent tensor specification of a physical Hadamard.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.PairBlocks {A : Set}
  (pair : A → A → A) (pair′ : A → A → A) where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; _++_)
import Data.Vec.Base as Vec
import Data.List.Base as List
open import Relation.Binary.PropositionalEquality

cast : ∀ {m n} → m ≡ n → Vec A m → Vec A n
cast refl v = v

flat : ∀ k → Vec A (k * 2) → Vec A (k * 2)
flat zero [] = []
flat (suc k) (a ∷ b ∷ v) = pair a b ∷ pair′ a b ∷ flat k v

flat-list : List.List A → List.List A
flat-list List.[] = List.[]
flat-list (a List.∷ List.[]) = a List.∷ List.[]
flat-list (a List.∷ b List.∷ v) = pair a b List.∷ pair′ a b List.∷ flat-list v

toList-flat : ∀ k v → Vec.toList (flat k v) ≡ flat-list (Vec.toList v)
toList-flat zero [] = refl
toList-flat (suc k) (a ∷ b ∷ v) =
  cong (λ w → pair a b List.∷ pair′ a b List.∷ w) (toList-flat k v)

toList-cast : ∀ {m n} (p : m ≡ n) v → Vec.toList (cast p v) ≡ Vec.toList v
toList-cast refl v = refl

flat-list-append : ∀ k (u : Vec A (k * 2)) v →
  flat-list (Vec.toList u List.++ v) ≡ flat-list (Vec.toList u) List.++ flat-list v
flat-list-append zero [] v = refl
flat-list-append (suc k) (a ∷ b ∷ u) v =
  cong (λ w → pair a b List.∷ pair′ a b List.∷ w) (flat-list-append k u v)

flat-list-append-even : ∀ {m} k (p : m ≡ k * 2) (u : Vec A m) v →
  flat-list (Vec.toList u List.++ v) ≡ flat-list (Vec.toList u) List.++ flat-list v
flat-list-append-even k refl = flat-list-append k

-- Consume the left input two entries at a time, so the type equality
-- governing the total number of pairs computes with the recursion.
join : ∀ k l → Vec A (k * 2) → Vec A (l * 2) → Vec A ((k + l) * 2)
join zero l [] v = v
join (suc k) l (a ∷ b ∷ u) v = a ∷ b ∷ join k l u v

flat-join : ∀ k l u v →
  flat (k + l) (join k l u v) ≡ join k l (flat k u) (flat l v)
flat-join zero l [] v = refl
flat-join (suc k) l (a ∷ b ∷ u) v =
  cong (λ w → pair a b ∷ pair′ a b ∷ w) (flat-join k l u v)

length-join : ∀ k l → (k + l) * 2 ≡ k * 2 + l * 2
length-join zero l = refl
length-join (suc k) l = cong (λ z → suc (suc z)) (length-join k l)

cast-cons₂ : ∀ {m n} (p : m ≡ n) a b (v : Vec A m) →
  cast (cong (λ z → suc (suc z)) p) (a ∷ b ∷ v) ≡ a ∷ b ∷ cast p v
cast-cons₂ refl a b v = refl

join-append : ∀ k l u v → cast (length-join k l) (join k l u v) ≡ u ++ v
join-append zero l [] v = refl
join-append (suc k) l (a ∷ b ∷ u) v =
  trans (cast-cons₂ (length-join k l) a b (join k l u v))
    (cong (λ w → a ∷ b ∷ w) (join-append k l u v))

cast-sym : ∀ {m n} (p : m ≡ n) v → cast (sym p) (cast p v) ≡ v
cast-sym refl v = refl

append-join : ∀ k l u v → cast (sym (length-join k l)) (u ++ v) ≡ join k l u v
append-join k l u v = trans
  (cong (cast (sym (length-join k l))) (sym (join-append k l u v)))
  (cast-sym (length-join k l) (join k l u v))

flat-append : ∀ k l u v →
  cast (length-join k l)
    (flat (k + l) (cast (sym (length-join k l)) (u ++ v))) ≡
  flat k u ++ flat l v
flat-append k l u v = trans
  (cong (λ w → cast (length-join k l) (flat (k + l) w)) (append-join k l u v))
  (trans (cong (cast (length-join k l)) (flat-join k l u v))
    (join-append k l (flat k u) (flat l v)))
