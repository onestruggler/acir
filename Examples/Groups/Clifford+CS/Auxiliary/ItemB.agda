------------------------------------------------------------------------
-- Presentations of groups
--
-- Item (b) of the Reidemeister–Schreier method
--
-- The coset action respects every rule of the two-level presentation
-- at every coset.  The eight K-free rules are `ItemBFree`.  For the
-- eleven with a K, pick a sink g off 0 and the rule's indices: along
-- either side the action is the frame's conjugation of Φ_g
-- (`Frame.run`), the two sides land in the same coset (`cos-rule`),
-- and Φ_g of the rule is a rule of the hybrid letter at g (`Rules`) —
-- or, for the order of K, follows from the square (18) and (17).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)

module Examples.Groups.Clifford+CS.Auxiliary.ItemB
  (N′ : ℕ) (big : 16 ≤ suc N′) where

open import Data.Fin using (Fin ; zero) renaming (_<_ to _<ᶠ_)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.All using ([] ; _∷_)
open import Data.Nat using (z≤n ; s≤s)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
import Relation.Binary.Reasoning.Setoid as SR
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _ᵗ ; _^_)

import Presentation.Base as PB

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (_===_)
open _===_

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (pw)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules
  using (_R,_===_ ; kiw ; pp-comm ; pp-ord ; ki-pp ; ki-px ; ki-ki ; ki-swap
       ; ki-swap′ ; ki-x ; ki-16 ; ki-ii ; ki-sq ; ki-yb)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets using (Coset)
open import Examples.Groups.Clifford+CS.Auxiliary.CosetAction N′ big
  using (act ; run-cos)
open import Examples.Groups.Clifford+CS.Auxiliary.Fresh (suc N′) big
  using (Off ; Fresh3 ; fresh3)
open import Examples.Groups.Clifford+CS.Auxiliary.ItemBFree N′ big
  using (cos-rule ; item-b-free)
open import Examples.Groups.Clifford+CS.Auxiliary.RS N′ big
  using (module RSF ; Item-b)
import Examples.Groups.Clifford+CS.Auxiliary.Frame as Frame

private
  N : ℕ
  N = suc N′

  W : Set
  W = Word (GenP N)

open PB (N R,_===_)
  using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
open import Presentation.Properties (N R,_===_)
  using (word-setoid ; by-assoc ; ^-• ; ^-cong ; ε^k=ε)
open SR word-setoid

private
  front : ∀ {a b} (s : W) → a ≈ b → a • s ≈ b • s
  front s e = cong e refl

  back : ∀ (p : W) {a b} → a ≈ b → p • a ≈ p • b
  back p e = cong refl e

  refl≡ : ∀ {w v : W} → w ≡ v → w ≈ v
  refl≡ Eq.refl = refl

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

------------------------------------------------------------------------
-- Through a frame

module Via (g : Fin N) (g0 : g ≢ zero) where

  open Frame N′ big g g0 using (T ; T⁻ ; Φʷ ; Avʷ ; run)

  via : ∀ (c : Coset) {u t : Word (TL.Gen N)} → u === t →
        Avʷ u → Avʷ t → Φʷ u ≈ Φʷ t →
        RSF._~_ ((act ᵗ) c u) ((act ᵗ) c t)
  via c {u} {t} r au at e = word , coset
    where
    coset : proj₂ ((act ᵗ) c u) ≡ proj₂ ((act ᵗ) c t)
    coset = Eq.trans (run-cos c u) (Eq.trans (cos-rule c r) (Eq.sym (run-cos c t)))

    word : proj₁ ((act ᵗ) c u) ≈ proj₁ ((act ᵗ) c t)
    word = trans (run c u au)
                 (trans (back (T c) (cong e (refl≡ (Eq.cong T⁻ coset))))
                        (sym (run c t at)))

  -- The order of K: the hybrid squared is the inverse of a phase
  -- pair it commutes with, whose fourth power vanishes.
  ki⁸ : ∀ (j k : Fin N) .(p : j <ᶠ k) → g ≢ j → g ≢ k →
        Φʷ (TL.K j k p ^ 8) ≈ ε
  ki⁸ j k p gj gk = begin
    Φʷ (TL.K j k p ^ 8)
      ≈⟨ by-assoc Eq.refl ⟩
    (κ • κ) ^ 4
      ≈⟨ sym right-unit ⟩
    (κ • κ) ^ 4 • ε
      ≈⟨ back _ (sym P⁴) ⟩
    (κ • κ) ^ 4 • P ^ 4
      ≈⟨ sym (^-• (κ • κ) P 4 κκP) ⟩
    ((κ • κ) • P) ^ 4
      ≈⟨ ^-cong ((κ • κ) • P) ε 4 (axiom (ki-sq j k g p gj gk)) ⟩
    ε ^ 4
      ≈⟨ ε^k=ε 4 ⟩
    ε ∎
    where
    κ = kiw j k g p
    P = pw j g • pw k g

    κP : κ • P ≈ P • κ
    κP = trans (axiom (ki-ii j k g p gj gk)) (sym assoc)

    κκP : (κ • κ) • P ≈ P • (κ • κ)
    κκP = begin
      (κ • κ) • P    ≈⟨ assoc ⟩
      κ • (κ • P)    ≈⟨ back κ κP ⟩
      κ • (P • κ)    ≈⟨ sym assoc ⟩
      (κ • P) • κ    ≈⟨ front κ κP ⟩
      (P • κ) • κ    ≈⟨ assoc ⟩
      P • (κ • κ) ∎

    P⁴ : P ^ 4 ≈ ε
    P⁴ = begin
      P ^ 4
        ≈⟨ ^-• (pw j g) (pw k g) 4 (axiom (pp-comm j g k g)) ⟩
      pw j g ^ 4 • pw k g ^ 4
        ≈⟨ cong (axiom (pp-ord j g)) (axiom (pp-ord k g)) ⟩
      ε • ε
        ≈⟨ left-unit ⟩
      ε ∎

------------------------------------------------------------------------
-- Sinks

private
  off3 : ∀ {x a b c : Fin N} → Off (a ∷ b ∷ c ∷ []) x → x ≢ a × x ≢ b × x ≢ c
  off3 (p ∷ q ∷ r ∷ []) = p , q , r

  off4 : ∀ {x a b c d : Fin N} → Off (a ∷ b ∷ c ∷ d ∷ []) x →
         x ≢ a × x ≢ b × x ≢ c × x ≢ d
  off4 (p ∷ q ∷ r ∷ s ∷ []) = p , q , r , s

  off5 : ∀ {x a b c d e : Fin N} → Off (a ∷ b ∷ c ∷ d ∷ e ∷ []) x →
         x ≢ a × x ≢ b × x ≢ c × x ≢ d × x ≢ e
  off5 (p ∷ q ∷ r ∷ s ∷ t ∷ []) = p , q , r , s , t

  -- A sink off 0 and two, three or four indices.
  module S2 (j k : Fin N) where
    F  = fresh3 (zero ∷ j ∷ k ∷ []) (s≤s (s≤s (s≤s z≤n)))
    g  = Fresh3.f₁ F
    o  = off3 (Fresh3.off₁ F)
    g0 = proj₁ o
    gj = proj₁ (proj₂ o)
    gk = proj₂ (proj₂ o)

  module S3 (j k l : Fin N) where
    F  = fresh3 (zero ∷ j ∷ k ∷ l ∷ []) (s≤s (s≤s (s≤s (s≤s z≤n))))
    g  = Fresh3.f₁ F
    o  = off4 (Fresh3.off₁ F)
    g0 = proj₁ o
    gj = proj₁ (proj₂ o)
    gk = proj₁ (proj₂ (proj₂ o))
    gl = proj₂ (proj₂ (proj₂ o))

  module S4 (j k l m : Fin N) where
    F  = fresh3 (zero ∷ j ∷ k ∷ l ∷ m ∷ []) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
    g  = Fresh3.f₁ F
    o  = off5 (Fresh3.off₁ F)
    g0 = proj₁ o
    gj = proj₁ (proj₂ o)
    gk = proj₁ (proj₂ (proj₂ o))
    gl = proj₁ (proj₂ (proj₂ (proj₂ o)))
    gm = proj₂ (proj₂ (proj₂ (proj₂ o)))

------------------------------------------------------------------------
-- Item (b)

item-b : Item-b
-- The K-free rules.
item-b c r@order-i                = item-b-free c r (tt , tt , tt , tt) tt
item-b c r@(order-X _)            = item-b-free c r (tt , tt) tt
item-b c r@(comm-ii _)            = item-b-free c r (tt , tt) (tt , tt)
item-b c r@(comm-iX _ _ _)        = item-b-free c r (tt , tt) (tt , tt)
item-b c r@(comm-XX _ _ _ _ _ _)  = item-b-free c r (tt , tt) (tt , tt)
item-b c r@(swap-iX _)            = item-b-free c r (tt , tt) (tt , tt)
item-b c r@(swap-XX _ _)          = item-b-free c r (tt , tt) (tt , tt)
item-b c r@(swap-XX′ _ _)         = item-b-free c r (tt , tt) (tt , tt)
-- The rules with a K.
item-b c r@(order-K {j = j} {k = k} p) =
  Via.via g g0 c r (a , a , a , a , a , a , a , a) tt (Via.ki⁸ g g0 j k p gj gk)
  where
  open S2 j k
  a = gj , gk
item-b c r@(comm-iK {k = k} {l = l} {j = j} p jk jl) =
  Via.via g g0 c r (tt , (gk , gl)) ((gk , gl) , tt)
          (axiom (ki-pp k l g j p jk jl gk gl))
  where open S3 j k l
item-b c r@(comm-XK {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  Via.via g g0 c r ((gj , gk) , (gl , gm)) ((gl , gm) , (gj , gk))
          (axiom (ki-px l m g j k q p jl jm kl km gl gm gj gk))
  where open S4 j k l m
item-b c r@(comm-KK {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) =
  Via.via g g0 c r ((gj , gk) , (gl , gm)) ((gl , gm) , (gj , gk))
          (axiom (ki-ki j k l m g p q (≢sym jl) (≢sym kl) (≢sym jm) (≢sym km)
                        gj gk gl gm))
  where open S4 j k l m
item-b c r@(swap-KX {j = j} {k = k} {l = l} p q) =
  Via.via g g0 c r ((gk , gl) , (gj , gk)) ((gj , gk) , (gj , gl))
          (axiom (ki-swap j k l g p q gj gk gl))
  where open S3 j k l
item-b c r@(swap-KX′ {j = j} {k = k} {l = l} p q) =
  Via.via g g0 c r ((gj , gl) , (gk , gl)) ((gk , gl) , (gj , gk))
          (axiom (ki-swap′ j k l g p q gj gk gl))
  where open S3 j k l
item-b c r@(rel-13 {j = j} {k = k} p) =
  Via.via g g0 c r ((gj , gk) , (tt , tt)) ((gj , gk) , (gj , gk))
          (axiom (ki-x j k g p gj gk))
  where open S2 j k
item-b c r@(rel-14 {j = j} {k = k} p) =
  Via.via g g0 c r ((gj , gk) , (tt , (tt , tt)))
          (tt , ((gj , gk) , (tt , (gj , gk))))
          (axiom (ki-16 j k g p gj gk))
  where open S2 j k
item-b c r@(rel-15 {j = j} {k = k} p) =
  Via.via g g0 c r ((gj , gk) , (tt , tt)) (tt , (tt , (gj , gk)))
          (axiom (ki-ii j k g p gj gk))
  where open S2 j k
item-b c r@(rel-16 {j = j} {k = k} p) =
  Via.via g g0 c r (((gj , gk) , (gj , gk)) , (tt , tt)) tt
          (axiom (ki-sq j k g p gj gk))
  where open S2 j k
item-b c r@(rel-17 {j = j} {k = k} {l = l} {m = m} jk lm jl km kl) =
  Via.via g g0 c r ((gj , gk) , ((gl , gm) , ((gj , gl) , (gk , gm))))
          ((gj , gl) , ((gk , gm) , ((gj , gk) , (gl , gm))))
          (axiom (ki-yb j k l m g jk lm jl km kl gj gk gl gm))
  where open S4 j k l m
