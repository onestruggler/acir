------------------------------------------------------------------------
-- Presentations of groups
--
-- The Reidemeister–Schreier theorem for monoids (Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators",
-- Theorem 4.2), in the interface of the Agda code accompanying the
-- paper (CC BY 2.0), as an instance of Normalization.Reidemeister-
-- Schreier:
--
-- * Reidemeister-Schreier-Simplified: given f : X → Word Y and a
--   translation back g with (a) x ~ g* (f x) and (b) g* respecting the
--   relations Δ, f* reflects Δ-derivability into Γ;
-- * Reidemeister-Schreier-Full: the same from a coset action
--   h : C → Y → Word X × C with a distinguished coset I, under
--   (a) h**(I, f x) ~ (x , I) and (b) h**(c, -) respecting Δ.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Presentation.Tactics.Reidemeister-Schreier where

open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base
import Normalization.Reidemeister-Schreier as RS
open import Presentation.Tactics.Judgement

------------------------------------------------------------------------
-- Derivations between pairs of a word and a coset

infix 5 _⊢ₚ_===_

_⊢ₚ_===_ : {X C : Set} (Γ : Context X) → Word X × C → Word X × C → Set
Γ ⊢ₚ (u , c) === (t , c′) = Γ ⊢ u === t × c ≡ c′

lemma-refl-⊢ₚ : ∀ {X Γ C} {p q : Word X × C} → p ≡ q → Γ ⊢ₚ p === q
lemma-refl-⊢ₚ Eq.refl = (refl , Eq.refl)

lemma-symm-⊢ₚ : ∀ {X Γ C} {p q : Word X × C} → Γ ⊢ₚ p === q → Γ ⊢ₚ q === p
lemma-symm-⊢ₚ (hyp , eq) = (symm hyp , Eq.sym eq)

lemma-trans-⊢ₚ : ∀ {X Γ C} {p q r : Word X × C} → Γ ⊢ₚ p === q → Γ ⊢ₚ q === r → Γ ⊢ₚ p === r
lemma-trans-⊢ₚ (hyp1 , eq1) (hyp2 , eq2) = (trans hyp1 hyp2 , Eq.trans eq1 eq2)

lemma-⊢ₚ-fst : ∀ {X Γ C} (lhs rhs : Word X × C) → Γ ⊢ₚ lhs === rhs → Γ ⊢ proj₁ lhs === proj₁ rhs
lemma-⊢ₚ-fst _ _ hyp = proj₁ hyp

lemma-⊢ₚ-snd : ∀ {X Γ C} (lhs rhs : Word X × C) → Γ ⊢ₚ lhs === rhs → proj₂ lhs ≡ proj₂ rhs
lemma-⊢ₚ-snd _ _ hyp = proj₂ hyp

------------------------------------------------------------------------
-- The two versions

module Reidemeister-Schreier-Simplified
       {X : Set} {Γ : Context X}
       {Y : Set} {Δ : Context Y}
       (f : X → Word Y)
       (g : Y → Word X)
       (hypA : ∀ (x : X) → Γ ⊢ [ x ]ʷ === (g ʷ) (f x))
       (hypB : ∀ (u t : Word Y) → u === t ∈ Δ → Γ ⊢ (g ʷ) u === (g ʷ) t)
  where

  private
    module S = RS.Star-Injective-Simplified.Reidemeister-Schreier-Simplified Γ Δ f g (λ {u} {t} → hypB u t) hypA

  lemma-a : ∀ (w : Word X) → Γ ⊢ w === (g ʷ) ((f ʷ) w)
  lemma-a = S.left-inv

  lemma-b : ∀ {u t : Word Y} → Δ ⊢ u === t → Γ ⊢ (g ʷ) u === (g ʷ) t
  lemma-b = S.lemma-b

  reidemeister-schreier-simplified : (w v : Word X) → Δ ⊢ (f ʷ) w === (f ʷ) v → Γ ⊢ w === v
  reidemeister-schreier-simplified = S.reidemeister-schreier-simplified

module Reidemeister-Schreier-Full
       {X : Set} {Γ : Context X}
       {Y : Set} {Δ : Context Y}
       (C : Set)
       (I : C)
       (f : X → Word Y)
       (h : C → Y → Word X × C)
       (hypA : ∀ (x : X) → Γ ⊢ₚ (h ᵗ) I (f x) === ([ x ]ʷ , I))
       (hypB : ∀ (c : C) {w w′ : Word Y} → w === w′ ∈ Δ → Γ ⊢ₚ (h ᵗ) c w === (h ᵗ) c w′)
  where

  private
    module S = RS.Star-Injective-Full.Reidemeister-Schreier-Full Γ Δ C I f h
                 (λ x → lemma-symm-⊢ₚ {Γ = Γ} {p = (h ᵗ) I (f x)} {q = [ x ]ʷ , I} (hypA x))
                 (λ c → hypB c)

  -- Special words: those that do not leave the coset I.
  special : Word Y → Set
  special = S.special

  lemma-special-f : ∀ (x : X) → special (f x)
  lemma-special-f = S.lemma-special-f

  lemma-special-f* : ∀ (w : Word X) → special ((f ʷ) w)
  lemma-special-f* = S.lemma-special-fʷ

  -- The translation back, on special words.
  g : Word Y → Word X
  g = S.g

  lemma-a : ∀ (w : Word X) → Γ ⊢ w === g ((f ʷ) w)
  lemma-a = S.lemma-a

  lemma-hypB : ∀ (c : C) (u t : Word Y) → Δ ⊢ u === t → Γ ⊢ₚ (h ᵗ) c u === (h ᵗ) c t
  lemma-hypB = S.lemma-hypB

  lemma-b : ∀ (u t : Word Y) → Δ ⊢ u === t → Γ ⊢ g u === g t
  lemma-b = S.lemma-b

  reidemeister-schreier : (w v : Word X) → Δ ⊢ (f ʷ) w === (f ʷ) v → Γ ⊢ w === v
  reidemeister-schreier = S.reidemeister-schreier

------------------------------------------------------------------------
-- Composing translations

-- g* ∘ f* = (g* ∘ f)*.
lemma-*-* : ∀ {X Y Z : Set} → (f : X → Word Y) → (g : Y → Word Z) → ∀ (w : Word X) →
            (g ʷ) ((f ʷ) w) ≡ ((λ y → (g ʷ) (f y)) ʷ) w
lemma-*-* f g [ x ]ʷ = Eq.refl
lemma-*-* f g ε = Eq.refl
lemma-*-* f g (w • w′) = Eq.cong₂ _•_ (lemma-*-* f g w) (lemma-*-* f g w′)

-- Two ways of composing a translation with a coset action.
infix 6 _◐_ _◑_

_◐_ : ∀ {X Y Z C : Set} → (g : Word Y → Word Z) → (f : C → X → Word Y × C) → (C → X → Word Z × C)
(g ◐ f) c x = g (proj₁ (f c x)) , proj₂ (f c x)

_◑_ : ∀ {X Y Z C : Set} → (g : C → Word Y → Word Z × C) → (f : X → Word Y) → (C → X → Word Z × C)
(g ◑ f) c x = g c (f x)

-- g* ◐ f** = (g* ◐ f)**.
lemma-*-** : ∀ {X Y Z C : Set} → (g : Y → Word Z) → (f : C → X → Word Y × C) → ∀ (c : C) (w : Word X) →
             ((g ʷ) ◐ (f ᵗ)) c w ≡ (((g ʷ) ◐ f) ᵗ) c w
lemma-*-** g f c [ x ]ʷ = Eq.refl
lemma-*-** g f c ε = Eq.refl
lemma-*-** g f c (w • v) =
  Eq.trans (Eq.cong (λ q → ((g ʷ) (proj₁ ((f ᵗ) c w)) • proj₁ q , proj₂ q))
                    (lemma-*-** g f (proj₂ ((f ᵗ) c w)) v))
           (Eq.cong (λ p → (proj₁ p • proj₁ ((((g ʷ) ◐ f) ᵗ) (proj₂ p) v) , proj₂ ((((g ʷ) ◐ f) ᵗ) (proj₂ p) v)))
                    (lemma-*-** g f c w))

-- g** ◑ f* = (g** ◑ f)**.
lemma-**-* : ∀ {X Y Z C : Set} → (g : C → Y → Word Z × C) → (f : X → Word Y) → ∀ (c : C) (w : Word X) →
             ((g ᵗ) ◑ (f ʷ)) c w ≡ (((g ᵗ) ◑ f) ᵗ) c w
lemma-**-* g f c [ x ]ʷ = Eq.refl
lemma-**-* g f c ε = Eq.refl
lemma-**-* g f c (w • v) =
  Eq.trans (Eq.cong (λ q → (proj₁ ((g ᵗ) c ((f ʷ) w)) • proj₁ q , proj₂ q))
                    (lemma-**-* g f (proj₂ ((g ᵗ) c ((f ʷ) w))) v))
           (Eq.cong (λ p → (proj₁ p • proj₁ ((((g ᵗ) ◑ f) ᵗ) (proj₂ p) v) , proj₂ ((((g ᵗ) ◑ f) ᵗ) (proj₂ p) v)))
                    (lemma-**-* g f c w))

------------------------------------------------------------------------
-- Composing two applications of the theorem

-- Composing two applications of the simplified Reidemeister-Schreier
-- procedure. Note that the roles of X (Γ) and Y (Δ) are switched
-- compared to the module Reidemeister-Schreier-Simplified.

module Reidemeister-Schreier-SS
       {X : Set} {Γ : Context X} 
       {Y : Set} {Δ : Context Y} 
       {Z : Set} {ζ : Context Z} 
       (f : X -> Word Y)
       (g : Y -> Word X)
       (h : Y -> Word Z)
       (k : Z -> Word Y)
       (hypA1 : ∀ (y : Y) -> Δ ⊢ [ y ]ʷ === (f ʷ) (g y))
       (hypB1 : ∀ (u t : Word X) -> u === t ∈ Γ -> Δ ⊢ (f ʷ) u === (f ʷ) t)
       (hypA2 : ∀ (z : Z) -> ζ ⊢ [ z ]ʷ === (h ʷ) (k z))
       (hypB2 : ∀ (u t : Word Y) -> u === t ∈ Δ -> ζ ⊢ (h ʷ) u === (h ʷ) t)
  where

  module R1 = Reidemeister-Schreier-Simplified {Y} {Δ} {X} {Γ} g f hypA1 hypB1
  module R2 = Reidemeister-Schreier-Simplified {Z} {ζ} {Y} {Δ} k h hypA2 hypB2
  
  hf : X -> Word Z
  hf x = (h ʷ) (f x)

  gk : Z -> Word X
  gk z = (g ʷ) (k z)

  hypA3 : ∀ (z : Z) -> ζ ⊢ [ z ]ʷ === (hf ʷ) (gk z)
  hypA3 z with R1.lemma-a (k z)
  ... | hyp with hypA2 z
  ... | hyp2 with lemma-*-* f h ((g ʷ) (k z))
  ... | hyp3 rewrite (Eq.sym hyp3) = trans hyp2 (R2.lemma-b hyp)

  hypB3 : ∀ (u t : Word X) -> u === t ∈ Γ -> ζ ⊢ (hf ʷ) u === (hf ʷ) t
  hypB3 u t ax with hypB1 u t ax
  ... | h1 with R2.lemma-b h1
  ... | h2 with lemma-*-* f h u | lemma-*-* f h t
  ... | h3 | h4 rewrite (Eq.sym h3) | (Eq.sym h4) = h2

  open Reidemeister-Schreier-Simplified {Z} {ζ} {X} {Γ} gk hf hypA3 hypB3 public

-- Composing the simplified and full Reidemeister-Schreier procedures
-- (full followed by simplified). Note that the roles of X (Γ) and Y
-- (Δ) are switched compared to the module Reidemeister-Schreier-Full.

module Reidemeister-Schreier-SF
       {X : Set} {Γ : Context X} 
       {Y : Set} {Δ : Context Y} 
       {Z : Set} {ζ : Context Z}
       (C : Set)
       (I : C)
       (f : C -> X -> Word Y × C)
       (g : Y -> Word X)
       (h : Y -> Word Z)
       (k : Z -> Word Y)
       (hypA1 : ∀ (y : Y) -> Δ ⊢ₚ (f ᵗ) I (g y) === ([ y ]ʷ , I))
       (hypB1 : ∀ (c : C) {w w' : Word X} -> w === w' ∈ Γ -> Δ ⊢ₚ (f ᵗ) c w === (f ᵗ) c w')
       (hypA2 : ∀ (z : Z) -> ζ ⊢ [ z ]ʷ === (h ʷ) (k z))
       (hypB2 : ∀ (u t : Word Y) -> u === t ∈ Δ -> ζ ⊢ (h ʷ) u === (h ʷ) t)
  where

  module R1 = Reidemeister-Schreier-Full {Y} {Δ} {X} {Γ} C I g f hypA1 hypB1
  module R2 = Reidemeister-Schreier-Simplified {Z} {ζ} {Y} {Δ} k h hypA2 hypB2
  
  hf : C -> X -> Word Z × C
  hf c x = ((h ʷ) (proj₁ (f c x))) , (proj₂ (f c x))

  gk : Z -> Word X
  gk z = (g ʷ) (k z)

  hypA3 : ∀ (z : Z) -> ζ ⊢ₚ (hf ᵗ) I (gk z) === ([ z ]ʷ , I)
  hypA3 z with R1.lemma-a (k z)
  ... | hyp with hypA2 z
  ... | hyp2 with lemma-*-** h f I ((g ʷ) (k z))
  ... | hs rewrite (Eq.sym hs) with R1.lemma-special-f* (k z)
  ... | sfs' = trans (R2.lemma-b (symm hyp)) (symm hyp2) , sfs'
  
  hypB3 : ∀ (c : C) {w w' : Word X} -> w === w' ∈ Γ -> ζ ⊢ₚ (hf ᵗ) c w === (hf ᵗ) c w'
  hypB3 c {u} {t} ax with hypB1 c ax
  ... | h1 with lemma-⊢ₚ-fst ((f ᵗ) c u) ((f ᵗ) c t) h1 | lemma-⊢ₚ-snd ((f ᵗ) c u) ((f ᵗ) c t) h1
  ... | fh | sh with R2.lemma-b fh | lemma-*-** h f c u | lemma-*-** h f c t
  ... | h2 | ss1 | ss2 rewrite (Eq.sym ss1) | (Eq.sym ss2) = R2.lemma-b fh , sh

  open Reidemeister-Schreier-Full {Z} {ζ} {X} {Γ} C I gk hf hypA3 hypB3 public


-- Composing the simplified and full Reidemeister-Schreier procedures
-- (simplified followed by full). Note that the roles of X (Γ) and Y
-- (Δ) are switched compared to the module Reidemeister-Schreier-Simplified.

module Reidemeister-Schreier-FS
       {X : Set} {Γ : Context X} 
       {Y : Set} {Δ : Context Y} 
       {Z : Set} {ζ : Context Z}
       (C : Set)
       (I : C)
       (f : X -> Word Y)
       (g : Y -> Word X)
       (h : C -> Y -> Word Z × C)
       (k : Z -> Word Y)
       (hypA1 : ∀ (y : Y) -> Δ ⊢ [ y ]ʷ === (f ʷ) (g y))
       (hypB1 : ∀ (u t : Word X) -> u === t ∈ Γ -> Δ ⊢ (f ʷ) u === (f ʷ) t)
       (hypA2 : ∀ (z : Z) -> ζ ⊢ₚ (h ᵗ) I (k z) === ([ z ]ʷ , I))
       (hypB2 : ∀ (c : C) {w w' : Word Y} -> w === w' ∈ Δ -> ζ ⊢ₚ (h ᵗ) c w === (h ᵗ) c w')
  where

  module R1 = Reidemeister-Schreier-Simplified {Y} {Δ} {X} {Γ} g f hypA1 hypB1
  module R2 = Reidemeister-Schreier-Full {Z} {ζ} {Y} {Δ} C I k h hypA2 hypB2
  
  hf : C -> X -> Word Z × C
  hf = (h ᵗ) ◑ f

  gk : Z -> Word X
  gk z = (g ʷ) (k z)

  hypA3 : ∀ (z : Z) -> ζ ⊢ₚ (hf ᵗ) I (gk z) === ([ z ]ʷ , I)
  hypA3 z =
    Eq.subst (λ p → ζ ⊢ₚ p === ([ z ]ʷ , I)) (lemma-**-* h f I ((g ʷ) (k z)))
      (lemma-trans-⊢ₚ {p = (h ᵗ) I ((f ʷ) ((g ʷ) (k z)))} {q = (h ᵗ) I (k z)} {r = [ z ]ʷ , I}
        (lemma-symm-⊢ₚ {p = (h ᵗ) I (k z)} {q = (h ᵗ) I ((f ʷ) ((g ʷ) (k z)))}
          (R2.lemma-hypB I (k z) ((f ʷ) ((g ʷ) (k z))) (R1.lemma-a (k z))))
        (hypA2 z))

  hypB3 : ∀ (c : C) {w w' : Word X} -> w === w' ∈ Γ -> ζ ⊢ₚ (hf ᵗ) c w === (hf ᵗ) c w'
  hypB3 c {u} {t} ax with hypB1 u t ax
  ... | h1 with R2.lemma-hypB c ((f ʷ) u) ((f ʷ) t) h1 | lemma-**-* h f c u | lemma-**-* h f c t
  ... | h2 | ss1 | ss2 rewrite (Eq.sym ss1) | (Eq.sym ss2) = h2

  open Reidemeister-Schreier-Full {Z} {ζ} {X} {Γ} C I gk hf hypA3 hypB3 public

