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
-- here (not re-exported) for comm⇒pow-comm's use of special-assoc.  Other
-- clients should import AssociativitySolver directly.

open import Presentation.Tactic.AssociativitySolver Γ

------------------------------------------------------------------------
-- Word power lemmas

comm⇒pow-comm : ∀ {w} {v} a b →
  w • v ≈ v • w → w ^ a • v ^ b ≈ v ^ b • w ^ a
comm⇒pow-comm {w} {v} zero    zero    eq = refl
comm⇒pow-comm {w} {v} zero    (₁₊ b) eq = trans left-unit (sym right-unit)
comm⇒pow-comm {w} {v} (₁₊ a) zero    eq = trans right-unit (sym left-unit)
comm⇒pow-comm {w} {v} (₁₊ zero) (₁₊ b@(₁₊ b')) eq =
  begin w • v ^ ₁₊ b       ≈⟨ sym assoc ⟩
    (w • v) • v ^ b          ≈⟨ cong eq refl ⟩
    (v • w) • v ^ b          ≈⟨ assoc ⟩
    v • w • v ^ b            ≈⟨ cong refl (comm⇒pow-comm 1 b eq) ⟩
    v • v ^ b • w            ≈⟨ sym assoc ⟩
    v ^ ₁₊ b • w ∎
  where open SR word-setoid
comm⇒pow-comm {w} {v} (₁₊ a@(₁₊ a')) (₁₊ zero) eq =
  begin (w • w ^ ₁₊ a') • v  ≈⟨ assoc ⟩
    w • w ^ ₁₊ a' • v         ≈⟨ cong refl (comm⇒pow-comm a 1 eq) ⟩
    w • v • w ^ ₁₊ a'         ≈⟨ sym assoc ⟩
    (w • v) • w ^ ₁₊ a'       ≈⟨ cong eq refl ⟩
    (v • w) • w ^ ₁₊ a'       ≈⟨ assoc ⟩
    v • w • w ^ ₁₊ a' ∎
  where open SR word-setoid
comm⇒pow-comm (₁₊ zero)       (₁₊ zero)       eq = eq
comm⇒pow-comm {w} {v} (₂₊ a) (₂₊ b) eq =
  begin w ^ ₂₊ a • v ^ ₂₊ b
      ≈⟨ special-assoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    w • (w ^ (₁₊ a) • v) • v ^ (₁₊ b)
      ≈⟨ cong refl (cong (comm⇒pow-comm (₁₊ a) 1 eq) refl) ⟩
    w • (v • w ^ (₁₊ a)) • v ^ (₁₊ b)
      ≈⟨ special-assoc (□ • (□ • □) • □) (□ ^ 2 • □ ^ 2) Eq.refl ⟩
    (w • v) • (w ^ (₁₊ a) • v ^ (₁₊ b))
      ≈⟨ cong eq (comm⇒pow-comm (₁₊ a) (₁₊ b) eq) ⟩
    (v • w) • (v ^ (₁₊ b) • w ^ (₁₊ a))
      ≈⟨ special-assoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) Eq.refl ⟩
    v • (w • v ^ (₁₊ b)) • w ^ (₁₊ a)
      ≈⟨ cong refl (cong (comm⇒pow-comm 1 (₁₊ b) eq) refl) ⟩
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

^-suc : ∀ (w : Word X) a → w ^ ₁₊ a ≈ w • w ^ a
^-suc w zero    = sym right-unit
^-suc w (₁₊ a) = refl

^-+ : ∀ (w : Word X) a b → w ^ (a Nat.+ b) ≈ w ^ a • w ^ b
^-+ w zero          b       = sym left-unit
^-+ w (₁₊ zero)    zero    = sym right-unit
^-+ w (₁₊ zero)    (₁₊ b) = refl
^-+ w (₂₊ a) b =
  begin w ^ suc (₁₊ a Nat.+ b)        ≈⟨ refl ⟩
    w • w ^ (₁₊ a Nat.+ b)             ≈⟨ cong refl (^-+ w (₁₊ a) b) ⟩
    w • w ^ ₁₊ a • w ^ b              ≈⟨ sym assoc ⟩
    w ^ ₂₊ a • w ^ b ∎
  where open SR word-setoid

^-• : ∀ (w v : Word X) a → w • v ≈ v • w → (w • v) ^ a ≈ w ^ a • v ^ a
^-• w v zero    eq = sym left-unit
^-• w v (₁₊ zero) eq = refl
^-• w v (₂₊ a) eq =
  begin (w • v) • (w • v) ^ ₁₊ a
      ≈⟨ cong refl (^-• w v (₁₊ a) eq) ⟩
    (w • v) • w ^ ₁₊ a • v ^ ₁₊ a
      ≈⟨ sym assoc ⟩
    ((w • v) • w ^ ₁₊ a) • v ^ ₁₊ a
      ≈⟨ cong assoc refl ⟩
    (w • (v • w ^ ₁₊ a)) • v ^ ₁₊ a
      ≈⟨ cong (cong refl (comm⇒pow-comm 1 (₁₊ a) (sym eq))) refl ⟩
    (w • (w ^ ₁₊ a • v)) • v ^ ₁₊ a
      ≈⟨ sym (cong assoc refl) ⟩
    ((w • w ^ ₁₊ a) • v) • v ^ ₁₊ a
      ≈⟨ assoc ⟩
    (w • w ^ ₁₊ a) • v • v ^ ₁₊ a ∎
  where open SR word-setoid

-- Different powers of a word commute: the same-base special case of
-- comm⇒pow-comm (a word commutes with itself, so the hypothesis is refl).
pow-comm : ∀ (w : Word X) a b → w ^ a • w ^ b ≈ w ^ b • w ^ a
pow-comm w a b = comm⇒pow-comm {w} {w} a b refl

^^ : ∀ (w : Word X) a b → (w ^ a) ^ b ≈ w ^ (a Nat.* b)
^^ w zero    zero    = refl
^^ w zero    (₁₊ zero) = PB.refl
^^ w zero    (₂₊ b) = trans left-unit (^^ w zero (₁₊ b))
^^ w (₁₊ zero) b = refl' (Eq.cong (w ^_) (Eq.sym (NP.+-identityʳ b)))
^^ w (₂₊ a) b =
  begin (w • w ^ ₁₊ a) ^ b
      ≈⟨ ^-• w (w ^ ₁₊ a) b (pow-comm w 1 (₁₊ a)) ⟩
    w ^ b • (w ^ ₁₊ a) ^ b
      ≈⟨ cong refl (^^ w (₁₊ a) b) ⟩
    w ^ b • w ^ (₁₊ a Nat.* b)
      ≈⟨ sym (^-+ w b (₁₊ a Nat.* b)) ⟩
    w ^ (b Nat.+ (b Nat.+ a Nat.* b)) ∎
  where open SR word-setoid

^^' : ∀ (w : Word X) a b → (w ^ a) ^ b ≈ (w ^ b) ^ a
^^' w a b =
  begin (w ^ a) ^ b     ≈⟨ ^^ w a b ⟩
    w ^ (a Nat.* b)     ≡⟨ Eq.cong (w ^_) (NP.*-comm a b) ⟩
    w ^ (b Nat.* a)     ≈⟨ sym (^^ w b a) ⟩
    (w ^ b) ^ a ∎
  where open SR word-setoid

^-cong : ∀ (w v : Word X) a → w ≈ v → w ^ a ≈ v ^ a
^-cong w v 0         eq = refl
^-cong w v 1         eq = eq
^-cong w v (₂₊ a) eq =
  begin w ^ ₂₊ a   ≈⟨ refl ⟩
    w • w ^ ₁₊ a          ≈⟨ cong eq (^-cong w v (₁₊ a) eq) ⟩
    v • v ^ ₁₊ a          ≈⟨ refl ⟩
    v ^ ₂₊ a ∎
  where open SR word-setoid

ε^k=ε : ∀ k → ε ^ k ≈ ε
ε^k=ε zero        = refl
ε^k=ε (₁₊ zero)  = refl
ε^k=ε (₂₊ k) = trans left-unit (ε^k=ε (₁₊ k))

------------------------------------------------------------------------
-- Congruence lemmas for wfoldr / wfoldl

wfoldr-cong :
  {X Y : Set} {_⊕_ : X → Y → Y} (R : Y → Y → Set) →
  (hyp : (a : X) → ∀ {b1 b2} → R b1 b2 → R (a ⊕ b1) (a ⊕ b2)) →
  ∀ (w : Word X) → ∀ {b1 b2} → R b1 b2 →
  let _⊕'_ = wfoldr _⊕_ in R (w ⊕' b1) (w ⊕' b2)
wfoldr-cong R hyp [ x ]ʷ  eq = hyp x eq
wfoldr-cong R hyp ε        eq = eq
wfoldr-cong {_⊕_ = _⊕_} R hyp (w • w₁) eq
  with wfoldr-cong R hyp w₁ eq
... | ih with (let _⊕'_ = wfoldr _⊕_ in wfoldr-cong R hyp w {w₁ ⊕' _} {w₁ ⊕' _})
... | ih2 = ih2 ih

wfoldl-cong :
  {X Y : Set} {_⊕_ : Y → X → Y} (R : Y → Y → Set) →
  (hyp : (a : X) → ∀ {b1 b2} → R b1 b2 → R (b1 ⊕ a) (b2 ⊕ a)) →
  ∀ (w : Word X) → ∀ {b1 b2} → R b1 b2 →
  let _⊕'_ = wfoldl _⊕_ in R (b1 ⊕' w) (b2 ⊕' w)
wfoldl-cong R hyp [ x ]ʷ  eq = hyp x eq
wfoldl-cong R hyp ε        eq = eq
wfoldl-cong {_⊕_ = _⊕_} R hyp (w • w₁) eq
  with wfoldl-cong R hyp w eq
... | ih with (let _⊕'_ = wfoldl _⊕_ in wfoldl-cong R hyp w₁ {_ ⊕' w} {_ ⊕' w})
... | ih2 = ih2 ih
