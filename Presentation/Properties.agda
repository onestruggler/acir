------------------------------------------------------------------------
-- Presentations of groups
--
-- Basic algebraic structures and proof tools for presented monoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base

module Presentation.Properties {X : Set} (Γ : WRel X) where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Nat as Nat using (ℕ ; zero ; suc)
import Data.Nat.Properties as NP
open import Data.Product using (_,_)
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations

import Presentation.Base as PB
open import Presentation.Base Γ

open import Algebra.Structures {A = Word X} _≈_
open import Algebra.Bundles using (Magma ; Semigroup ; Monoid)

------------------------------------------------------------------------
-- Algebraic structures

≈-isEquivalence : IsEquivalence {A = Word X} _≈_
≈-isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

word-setoid : Setoid 0ℓ 0ℓ
word-setoid = record
  { Carrier       = Word X
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

•-isMagma : IsMagma _•_
•-isMagma = record
  { isEquivalence = ≈-isEquivalence
  ; ∙-cong        = cong
  }

•-isSemigroup : IsSemigroup _•_
•-isSemigroup = record
  { isMagma = •-isMagma
  ; assoc   = λ x y z → assoc
  }

•-ε-isMonoid : IsMonoid _•_ ε
•-ε-isMonoid = record
  { isSemigroup = •-isSemigroup
  ; identity    = (λ x → left-unit) , (λ x → right-unit)
  }

------------------------------------------------------------------------
-- Algebraic bundles

•-magma : Magma 0ℓ 0ℓ
•-magma = record { isMagma = •-isMagma }

•-semigroup : Semigroup 0ℓ 0ℓ
•-semigroup = record { isSemigroup = •-isSemigroup }

•-ε-monoid : Monoid 0ℓ 0ℓ
•-ε-monoid = record { isMonoid = •-ε-isMonoid }

------------------------------------------------------------------------
-- Congruence of the induced maps
--
-- If f respects the raw relations of Γ, then its free extension (f *)
-- — or the generator lift wmap f — respects the whole congruence ≈,
-- sending the source presentation Γ into a target presentation Δ.

module StarCongruence {B : Set} (Δ : WRel B)
  (f : X → Word B)
  (let open PB Δ hiding (_===_) renaming (_≈_ to _≈₂_))
  (f-well-defined : ∀ {w v} → w === v → (f *) w ≈₂ (f *) v)
  where

  f*-cong : ∀ {w v : Word X} → w ≈ v → (f *) w ≈₂ (f *) v
  f*-cong refl        = _≈₂_.refl
  f*-cong (sym h)     = _≈₂_.sym (f*-cong h)
  f*-cong (trans h k) = _≈₂_.trans (f*-cong h) (f*-cong k)
  f*-cong (cong h k)  = _≈₂_.cong (f*-cong h) (f*-cong k)
  f*-cong assoc       = _≈₂_.assoc
  f*-cong left-unit   = _≈₂_.left-unit
  f*-cong right-unit  = _≈₂_.right-unit
  f*-cong (axiom a)   = f-well-defined a


module GenCongruence {B : Set} (Δ : WRel B)
  (f : X → B)
  (let open PB Δ renaming (_≈_ to _≈₂_))
  (f-well-defined : ∀ {w v} → Γ w v → wmap f w ≈₂ wmap f v)
  where

  f* = wmap f

  f*-cong : ∀ {w v : Word X} → w ≈ v → f* w ≈₂ f* v
  f*-cong refl        = _≈₂_.refl
  f*-cong (sym h)     = _≈₂_.sym (f*-cong h)
  f*-cong (trans h k) = _≈₂_.trans (f*-cong h) (f*-cong k)
  f*-cong (cong h k)  = _≈₂_.cong (f*-cong h) (f*-cong k)
  f*-cong assoc       = _≈₂_.assoc
  f*-cong left-unit   = _≈₂_.left-unit
  f*-cong right-unit  = _≈₂_.right-unit
  f*-cong (axiom a)   = f-well-defined a

------------------------------------------------------------------------
-- Associativity solver
--
-- The solver lives in Presentation.Tactic.AssociativitySolver; imported
-- here (not re-exported) for word-comm's use of special-assoc.  Other
-- clients should import AssociativitySolver directly.

open import Presentation.Tactic.AssociativitySolver Γ

------------------------------------------------------------------------
-- Word power lemmas

word-comm : ∀ {w} {v} a b →
  w • v ≈ v • w → w ^ a • v ^ b ≈ v ^ b • w ^ a
word-comm {w} {v} zero    zero    eq = refl
word-comm {w} {v} zero    (₁₊ b) eq = trans left-unit (sym right-unit)
word-comm {w} {v} (₁₊ a) zero    eq = trans right-unit (sym left-unit)
word-comm {w} {v} (₁₊ zero) (₁₊ b@(₁₊ b')) eq =
  begin w • v ^ ₁₊ b       ≈⟨ sym assoc ⟩
    (w • v) • v ^ b          ≈⟨ cong eq refl ⟩
    (v • w) • v ^ b          ≈⟨ assoc ⟩
    v • w • v ^ b            ≈⟨ cong refl (word-comm 1 b eq) ⟩
    v • v ^ b • w            ≈⟨ sym assoc ⟩
    v ^ ₁₊ b • w ∎
  where open SR word-setoid
word-comm {w} {v} (₁₊ a@(₁₊ a')) (₁₊ zero) eq =
  begin (w • w ^ ₁₊ a') • v  ≈⟨ assoc ⟩
    w • w ^ ₁₊ a' • v         ≈⟨ cong refl (word-comm a 1 eq) ⟩
    w • v • w ^ ₁₊ a'         ≈⟨ sym assoc ⟩
    (w • v) • w ^ ₁₊ a'       ≈⟨ cong eq refl ⟩
    (v • w) • w ^ ₁₊ a'       ≈⟨ assoc ⟩
    v • w • w ^ ₁₊ a' ∎
  where open SR word-setoid
word-comm (₁₊ zero)       (₁₊ zero)       eq = eq
word-comm {w} {v} (₂₊ a) (₂₊ b) eq =
  begin w ^ ₂₊ a • v ^ ₂₊ b
      ≈⟨ special-assoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    w • (w ^ (₁₊ a) • v) • v ^ (₁₊ b)
      ≈⟨ cong refl (cong (word-comm (₁₊ a) 1 eq) refl) ⟩
    w • (v • w ^ (₁₊ a)) • v ^ (₁₊ b)
      ≈⟨ special-assoc (□ • (□ • □) • □) (□ ^ 2 • □ ^ 2) Eq.refl ⟩
    (w • v) • (w ^ (₁₊ a) • v ^ (₁₊ b))
      ≈⟨ cong eq (word-comm (₁₊ a) (₁₊ b) eq) ⟩
    (v • w) • (v ^ (₁₊ b) • w ^ (₁₊ a))
      ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) Eq.refl ⟩
    v • (w • v ^ (₁₊ b)) • w ^ (₁₊ a)
      ≈⟨ cong refl (cong (word-comm 1 (₁₊ b) eq) refl) ⟩
    v • (v ^ (₁₊ b) • w) • w ^ (₁₊ a)
      ≈⟨ special-assoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) Eq.refl ⟩
    v ^ ₂₊ b • w ^ ₂₊ a ∎
  where
    open SR word-setoid
    open Pattern-Assoc

^'=^ : {n : ℕ} {w : Word X} → w ^' n ≈ w ^ n
^'=^ {zero}           {w} = refl
^'=^ {₁₊ zero}       {w} = refl
^'=^ {₂₊ zero} {w} = refl
^'=^ {₃₊ n} {w} =
  begin ((w ^' ₁₊ n) • w) • w   ≈⟨ cong (^'=^ {n = ₂₊ n}) refl ⟩
    (w • (w ^ ₁₊ n)) • w         ≈⟨ assoc ⟩
    w • (w ^ ₁₊ n) • w           ≈⟨ cong refl (cong (sym (^'=^ {n = ₁₊ n})) refl) ⟩
    w • (w ^' ₁₊ n) • w          ≈⟨ cong refl (^'=^ {n = ₂₊ n}) ⟩
    w • (w • (w ^ ₁₊ n)) ∎
  where open SR word-setoid

lemma-^-suc : ∀ (w : Word X) a → w ^ ₁₊ a ≈ w • w ^ a
lemma-^-suc w zero    = sym right-unit
lemma-^-suc w (₁₊ a) = refl

lemma-^-+ : ∀ (w : Word X) a b → w ^ (a Nat.+ b) ≈ w ^ a • w ^ b
lemma-^-+ w zero          b       = sym left-unit
lemma-^-+ w (₁₊ zero)    zero    = sym right-unit
lemma-^-+ w (₁₊ zero)    (₁₊ b) = refl
lemma-^-+ w (₂₊ a) b =
  begin w ^ suc (₁₊ a Nat.+ b)        ≈⟨ refl ⟩
    w • w ^ (₁₊ a Nat.+ b)             ≈⟨ cong refl (lemma-^-+ w (₁₊ a) b) ⟩
    w • w ^ ₁₊ a • w ^ b              ≈⟨ sym assoc ⟩
    w ^ ₂₊ a • w ^ b ∎
  where open SR word-setoid

lemma-^-• : ∀ (w v : Word X) a → w • v ≈ v • w → (w • v) ^ a ≈ w ^ a • v ^ a
lemma-^-• w v zero    eq = sym left-unit
lemma-^-• w v (₁₊ zero) eq = refl
lemma-^-• w v (₂₊ a) eq =
  begin (w • v) • (w • v) ^ ₁₊ a
      ≈⟨ cong refl (lemma-^-• w v (₁₊ a) eq) ⟩
    (w • v) • w ^ ₁₊ a • v ^ ₁₊ a
      ≈⟨ sym assoc ⟩
    ((w • v) • w ^ ₁₊ a) • v ^ ₁₊ a
      ≈⟨ cong assoc refl ⟩
    (w • (v • w ^ ₁₊ a)) • v ^ ₁₊ a
      ≈⟨ cong (cong refl (word-comm 1 (₁₊ a) (sym eq))) refl ⟩
    (w • (w ^ ₁₊ a • v)) • v ^ ₁₊ a
      ≈⟨ sym (cong assoc refl) ⟩
    ((w • w ^ ₁₊ a) • v) • v ^ ₁₊ a
      ≈⟨ assoc ⟩
    (w • w ^ ₁₊ a) • v • v ^ ₁₊ a ∎
  where open SR word-setoid

lemma-comm-wᵃwᵇ : ∀ (w : Word X) a b → w ^ a • w ^ b ≈ w ^ b • w ^ a
lemma-comm-wᵃwᵇ w zero    zero    = refl
lemma-comm-wᵃwᵇ w zero    (₁₊ b) = trans left-unit (sym right-unit)
lemma-comm-wᵃwᵇ w (₁₊ a) zero    = trans right-unit (sym left-unit)
lemma-comm-wᵃwᵇ w (₁₊ zero) (₁₊ zero) = refl
lemma-comm-wᵃwᵇ w (₁₊ zero) (₂₊ b) =
  begin w • w • w ^ ₁₊ b                ≈⟨ cong refl (lemma-comm-wᵃwᵇ w 1 (₁₊ b)) ⟩
    w • w ^ ₁₊ b • w                     ≈⟨ sym assoc ⟩
    (w • w ^ ₁₊ b) • w ∎
  where open SR word-setoid
lemma-comm-wᵃwᵇ w (₂₊ a) (₁₊ zero) =
  begin (w • w ^ ₁₊ a) • w              ≈⟨ assoc ⟩
    w • w ^ ₁₊ a • w                     ≈⟨ cong refl (lemma-comm-wᵃwᵇ w (₁₊ a) 1) ⟩
    w • w • w ^ ₁₊ a ∎
  where open SR word-setoid
lemma-comm-wᵃwᵇ w (₂₊ a) (₂₊ b) =
  begin (w • w ^ ₁₊ a) • w • w ^ ₁₊ b
      ≈⟨ sym assoc ⟩
    ((w • w ^ ₁₊ a) • w) • w ^ ₁₊ b
      ≈⟨ cong assoc refl ⟩
    (w • w ^ ₁₊ a • w) • w ^ ₁₊ b
      ≈⟨ cong (cong refl (lemma-comm-wᵃwᵇ w (₁₊ a) 1)) refl ⟩
    (w • w • w ^ ₁₊ a) • w ^ ₁₊ b
      ≈⟨ assoc ⟩
    w • (w • w ^ ₁₊ a) • w ^ ₁₊ b
      ≈⟨ cong refl assoc ⟩
    w • w • w ^ ₁₊ a • w ^ ₁₊ b
      ≈⟨ cong refl (cong refl (lemma-comm-wᵃwᵇ w (₁₊ a) (₁₊ b))) ⟩
    w • w • w ^ ₁₊ b • w ^ ₁₊ a
      ≈⟨ cong refl (sym assoc) ⟩
    w • (w • w ^ ₁₊ b) • w ^ ₁₊ a
      ≈⟨ cong refl (cong (lemma-comm-wᵃwᵇ w 1 (₁₊ b)) refl) ⟩
    w • (w ^ ₁₊ b • w) • w ^ ₁₊ a
      ≈⟨ sym assoc ⟩
    (w • (w ^ ₁₊ b • w)) • w ^ ₁₊ a
      ≈⟨ sym (cong assoc refl) ⟩
    ((w • w ^ ₁₊ b) • w) • w ^ ₁₊ a
      ≈⟨ assoc ⟩
    (w • w ^ ₁₊ b) • w • w ^ ₁₊ a ∎
  where open SR word-setoid

lemma-^^ : ∀ (w : Word X) a b → (w ^ a) ^ b ≈ w ^ (a Nat.* b)
lemma-^^ w zero    zero    = refl
lemma-^^ w zero    (₁₊ zero) = PB.refl
lemma-^^ w zero    (₂₊ b) = trans left-unit (lemma-^^ w zero (₁₊ b))
lemma-^^ w (₁₊ zero) b = refl' (Eq.cong (w ^_) (Eq.sym (NP.+-identityʳ b)))
lemma-^^ w (₂₊ a) b =
  begin (w • w ^ ₁₊ a) ^ b
      ≈⟨ lemma-^-• w (w ^ ₁₊ a) b (lemma-comm-wᵃwᵇ w 1 (₁₊ a)) ⟩
    w ^ b • (w ^ ₁₊ a) ^ b
      ≈⟨ cong refl (lemma-^^ w (₁₊ a) b) ⟩
    w ^ b • w ^ (₁₊ a Nat.* b)
      ≈⟨ sym (lemma-^-+ w b (₁₊ a Nat.* b)) ⟩
    w ^ (b Nat.+ (b Nat.+ a Nat.* b)) ∎
  where open SR word-setoid

lemma-^^' : ∀ (w : Word X) a b → (w ^ a) ^ b ≈ (w ^ b) ^ a
lemma-^^' w a b =
  begin (w ^ a) ^ b     ≈⟨ lemma-^^ w a b ⟩
    w ^ (a Nat.* b)     ≡⟨ Eq.cong (w ^_) (NP.*-comm a b) ⟩
    w ^ (b Nat.* a)     ≈⟨ sym (lemma-^^ w b a) ⟩
    (w ^ b) ^ a ∎
  where open SR word-setoid

lemma-^-cong : ∀ (w v : Word X) a → w ≈ v → w ^ a ≈ v ^ a
lemma-^-cong w v 0         eq = refl
lemma-^-cong w v 1         eq = eq
lemma-^-cong w v (₂₊ a) eq =
  begin w ^ ₂₊ a   ≈⟨ refl ⟩
    w • w ^ ₁₊ a          ≈⟨ cong eq (lemma-^-cong w v (₁₊ a) eq) ⟩
    v • v ^ ₁₊ a          ≈⟨ refl ⟩
    v ^ ₂₊ a ∎
  where open SR word-setoid

lemma-ε^k=ε : ∀ k → ε ^ k ≈ ε
lemma-ε^k=ε zero        = refl
lemma-ε^k=ε (₁₊ zero)  = refl
lemma-ε^k=ε (₂₊ k) = trans left-unit (lemma-ε^k=ε (₁₊ k))

------------------------------------------------------------------------
-- Congruence lemmas for wfoldr / wfoldl

lemma-wfoldr :
  {X Y : Set} {_⊕_ : X → Y → Y} (R : Y → Y → Set) →
  (hyp : (a : X) → ∀ {b1 b2} → R b1 b2 → R (a ⊕ b1) (a ⊕ b2)) →
  ∀ (w : Word X) → ∀ {b1 b2} → R b1 b2 →
  let _⊕'_ = wfoldr _⊕_ in R (w ⊕' b1) (w ⊕' b2)
lemma-wfoldr R hyp [ x ]ʷ  eq = hyp x eq
lemma-wfoldr R hyp ε        eq = eq
lemma-wfoldr {_⊕_ = _⊕_} R hyp (w • w₁) eq
  with lemma-wfoldr R hyp w₁ eq
... | ih with (let _⊕'_ = wfoldr _⊕_ in lemma-wfoldr R hyp w {w₁ ⊕' _} {w₁ ⊕' _})
... | ih2 = ih2 ih

lemma-wfoldl :
  {X Y : Set} {_⊕_ : Y → X → Y} (R : Y → Y → Set) →
  (hyp : (a : X) → ∀ {b1 b2} → R b1 b2 → R (b1 ⊕ a) (b2 ⊕ a)) →
  ∀ (w : Word X) → ∀ {b1 b2} → R b1 b2 →
  let _⊕'_ = wfoldl _⊕_ in R (b1 ⊕' w) (b2 ⊕' w)
lemma-wfoldl R hyp [ x ]ʷ  eq = hyp x eq
lemma-wfoldl R hyp ε        eq = eq
lemma-wfoldl {_⊕_ = _⊕_} R hyp (w • w₁) eq
  with lemma-wfoldl R hyp w eq
... | ih with (let _⊕'_ = wfoldl _⊕_ in lemma-wfoldl R hyp w₁ {_ ⊕' w} {_ ⊕' w})
... | ih2 = ih2 ih
