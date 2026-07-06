------------------------------------------------------------------------
-- Presentations of groups
--
-- Basic algebraic structures and proof tools for presented monoids
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

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
  (f-well-defined : let open PB Δ renaming (_≈_ to _≈₂_) in
                    ∀ {w v} → Γ w v → (f *) w ≈₂ (f *) v)
  where

  open PB Δ using () renaming (_≈_ to _≈₂_)

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
  (f-well-defined : let f* = wmap f; open PB Δ renaming (_≈_ to _≈₂_) in
                    ∀ {w v} → Γ w v → f* w ≈₂ f* v)
  where

  open PB Δ using () renaming (_≈_ to _≈₂_)

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
-- Converts a word to a flat list of generators, then compares the lists
-- to decide associativity.

to-list : ∀ {X} → Word X → List X
to-list [ x ]ʷ  = x ∷ []
to-list ε        = []
to-list (w • w₁) = to-list w ++ to-list w₁

from-list : ∀ {X} → List X → Word X
from-list []       = ε
from-list (x ∷ xs) = [ x ]ʷ • from-list xs

from-list-homo : ∀ {X} {R : WRel X} (xs ys : List X) →
  let open PB R renaming (_≈_ to _≈₁_) in
  from-list (xs ++ ys) ≈₁ from-list xs • from-list ys
from-list-homo {R = R} [] ys = _≈₁_.sym _≈₁_.left-unit
  where open PB R renaming (_≈_ to _≈₁_)
from-list-homo {R = R} (x ∷ xs) ys =
    _≈₁_.trans
      (_≈₁_.cong _≈₁_.refl (from-list-homo xs ys))
      (_≈₁_.sym _≈₁_.assoc)
  where open PB R renaming (_≈_ to _≈₁_)

lemma-from-to : ∀ {w} → from-list (to-list w) ≈ w
lemma-from-to {[ x ]ʷ}  = right-unit
lemma-from-to {ε}        = refl
lemma-from-to {w • w₁}  with lemma-from-to {w} | lemma-from-to {w₁}
... | ih1 | ih2 = trans (from-list-homo (to-list w) (to-list w₁)) (cong ih1 ih2)

-- Normalise a word up to associativity and units.
mod-assoc : ∀ w → Word X
mod-assoc w = from-list (to-list w)

-- Prove w ≈ v by comparing flattened generator lists (typically by
-- refl).
by-assoc : ∀ {w} {v} → to-list w ≡ to-list v → w ≈ v
by-assoc {w} {v} eq =
  trans (sym lemma-from-to) (trans (refl' (Eq.cong from-list eq)) lemma-from-to)

-- Chain a known equation a ≈ b with associativity steps on both sides.
by-assoc-and : ∀ {w} {v} {a} {b} →
  a ≈ b → to-list w ≡ to-list a → to-list b ≡ to-list v → w ≈ v
by-assoc-and {w} {v} {a} {b} eq eq1 eq2 =
  trans (by-assoc eq1) (trans eq (by-assoc eq2))

------------------------------------------------------------------------
-- Pattern-guided associativity solver

module Pattern-Assoc where

  open import Data.Unit using (⊤ ; tt)

  -- Placeholder symbol for use in pattern words, e.g. (□ • □) • □.
  □ : Word ⊤
  □ = [ tt ]ʷ

  -- Like to-list, but guided by a pattern word: subwords at positions
  -- marked by □ are kept intact without further flattening.
  to-list-special : ∀ {X} → Word X → Word ⊤ → List (Word X)
  to-list-special w         ([ gen ]ʷ) = w ∷ []
  to-list-special ([ x ]ʷ) ε          = [ x ]ʷ ∷ []
  to-list-special ([ x ]ʷ) (p • q)    = [ x ]ʷ ∷ []
  to-list-special ε         ε          = []
  to-list-special ε         (p • q)    = []
  to-list-special (w • v)   ε          = to-list-special w ε ++ to-list-special v ε
  to-list-special (w • v)   (p • q)    = to-list-special w p ++ to-list-special v q

  flatten-word : ∀ {X} → Word (Word X) → Word X
  flatten-word ([ w ]ʷ) = w
  flatten-word ε         = ε
  flatten-word (w • v)   = flatten-word w • flatten-word v

  -- The empty relation: words of words up to associativity only.
  data ∅ {X : Set} : WRel X where

  lemma-flatten-word : ∀ {xs ys : Word (Word X)} →
    let open PB (∅ {Word X}) renaming (_≈_ to _≈₀_) in
    xs ≈₀ ys → flatten-word xs ≈ flatten-word ys
  lemma-flatten-word (axiom ())
  lemma-flatten-word refl           = refl
  lemma-flatten-word (sym hyp)      = sym (lemma-flatten-word hyp)
  lemma-flatten-word (trans hyp h₁) = trans (lemma-flatten-word hyp) (lemma-flatten-word h₁)
  lemma-flatten-word (cong hyp h₁)  = cong (lemma-flatten-word hyp) (lemma-flatten-word h₁)
  lemma-flatten-word assoc           = assoc
  lemma-flatten-word left-unit       = left-unit
  lemma-flatten-word right-unit      = right-unit

  lemma-to-list-special : ∀ (w : Word X) (p : Word ⊤) →
    flatten-word (from-list (to-list-special w p)) ≈ w
  lemma-to-list-special w         ([ gen ]ʷ) = right-unit
  lemma-to-list-special ([ x ]ʷ) ε          = right-unit
  lemma-to-list-special ([ x ]ʷ) (p • q)    = right-unit
  lemma-to-list-special ε         ε          = refl
  lemma-to-list-special ε         (p • q)    = refl
  lemma-to-list-special (w • v)   ε =
    begin flatten-word (from-list (to-list-special w ε ++ to-list-special v ε))
        ≈⟨ lemma-flatten-word (from-list-homo (to-list-special w ε) (to-list-special v ε)) ⟩
      flatten-word (from-list (to-list-special w ε) • from-list (to-list-special v ε))
        ≈⟨ refl ⟩
      flatten-word (from-list (to-list-special w ε)) • flatten-word (from-list (to-list-special v ε))
        ≈⟨ cong (lemma-to-list-special w ε) (lemma-to-list-special v ε) ⟩
      w • v ∎
    where open SR word-setoid
  lemma-to-list-special (w • v) (p • q) =
    begin flatten-word (from-list (to-list-special w p ++ to-list-special v q))
        ≈⟨ lemma-flatten-word (from-list-homo (to-list-special w p) (to-list-special v q)) ⟩
      flatten-word (from-list (to-list-special w p) • from-list (to-list-special v q))
        ≈⟨ refl ⟩
      flatten-word (from-list (to-list-special w p)) • flatten-word (from-list (to-list-special v q))
        ≈⟨ cong (lemma-to-list-special w p) (lemma-to-list-special v q) ⟩
      w • v ∎
    where open SR word-setoid

  -- Prove w ≈ v by giving matching pattern words p and q such that
  -- to-list-special w p ≡ to-list-special v q (checked by refl).
  --
  -- Example: to prove (a • b) • (c • d) ≈ a • (b • c) • d, write
  --   special-assoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) refl
  special-assoc : ∀ {w v : Word X} (p q : Word ⊤) →
    to-list-special w p ≡ to-list-special v q → w ≈ v
  special-assoc {w = w} {v = v} p q hyp =
    begin w
        ≈⟨ sym (lemma-to-list-special w p) ⟩
      flatten-word (from-list (to-list-special w p))
        ≈⟨ refl' (Eq.cong (λ □ → flatten-word (from-list □)) hyp) ⟩
      flatten-word (from-list (to-list-special v q))
        ≈⟨ lemma-to-list-special v q ⟩
      v ∎
    where open SR word-setoid

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
