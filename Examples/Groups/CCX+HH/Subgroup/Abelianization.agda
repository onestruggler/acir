------------------------------------------------------------------------
-- Presentations of groups
--
-- The abelianization of the dyadic two-level presentation has exactly
-- four elements, at every dimension at least two.  The quotient below
-- adds only commutation of words to Table 1.  Its normal form is the
-- already constructed four-state charge, with representatives
--   epsilon, M_0, X_01, M_0 X_01.
-- Thus its identity class (the commutator subgroup of the source
-- group) is exactly charge 00.  This is a theorem about Table 1, not
-- an additional axiom of either physical circuit presentation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; s≤s ; z≤n)

module Examples.Groups.CCX+HH.Subgroup.Abelianization (N : ℕ) where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FP
open import Relation.Nullary.Decidable using (recompute)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)
import Presentation.GroupLike as GL
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
open import Examples.Groups.CCX+HH.Subgroup.Action
  using (Coset ; c00 ; c10 ; c11 ; c01 ; dyadic-step)
import Examples.Groups.CCX+HH.Subgroup.Action as Action
import Examples.Groups.CCX+HH.Subgroup.Charge as Charge
open import Examples.Groups.CCX+HH.Subgroup.AbelianizationCore (2 + N) public

private
  n = 2 + N
  module A = Action.At n

open import Presentation.Properties Relations using (by-assoc ; word-setoid)
open import Relation.Binary.Reasoning.Setoid word-setoid

private
  module G = GL.Group-Lemmas Relations grouplike
  open G using (•-cancelʳ)
  i j : Fin n
  i = zero
  j = suc zero
  ij : i < j
  ij = s≤s z≤n

  sign-reference : ∀ a → U.M a ≈ U.M i
  sign-reference zero = refl
  sign-reference (suc a) = •-cancelʳ (trans
    (axiom (commute (U.M (suc a)) (U.X i (suc a) (s≤s z≤n))))
    (axiom (source (U.r3c (s≤s z≤n)))))

  triangle-left : ∀ (a b c : Fin n) (ab : a < b) (bc : b < c) →
    U.X a b ab ≈ U.X a c (FP.<-trans ab bc)
  triangle-left a b c ab bc = •-cancelʳ (trans
    (axiom (commute (U.X a b ab) (U.X b c bc)))
    (axiom (source (U.r3b ab bc (FP.<-trans ab bc)))))

  triangle-right : ∀ (a b c : Fin n) (ab : a < b) (bc : b < c) →
    U.X a c (FP.<-trans ab bc) ≈ U.X b c bc
  triangle-right a b c ab bc = •-cancelʳ (trans
    (axiom (commute (U.X a c (FP.<-trans ab bc)) (U.X a b ab)))
    (axiom (source (U.r3a ab bc (FP.<-trans ab bc)))))

  exchange-zero : ∀ (b : Fin n) (ib : i < b) → U.X i b ib ≈ U.X i j ij
  exchange-zero zero ()
  exchange-zero (suc zero) ib = refl
  exchange-zero (suc (suc b)) ib =
    sym (triangle-left zero (suc zero) (suc (suc b)) ij (s≤s (s≤s z≤n)))

  exchange-reference : ∀ (a b : Fin n) (ab : a < b) → U.X a b ab ≈ U.X i j ij
  exchange-reference zero b ab = exchange-zero b ab
  exchange-reference (suc a) zero ()
  exchange-reference (suc a) (suc b) ab = trans
    (sym (triangle-right zero (suc a) (suc b) (s≤s z≤n) ab))
    (exchange-zero (suc b) (s≤s z≤n))

  mixed-square : ∀ (a b c d : Fin n) .(ab : a < b) .(bc : b < c) .(cd : c < d) →
    ((U.M a • U.X b c bc) • U.K a b c d ab bc cd) ≈
    ((U.K a b c d ab bc cd • U.M a) • (U.K a b c d ab bc cd • U.M a))
  mixed-square a b c d ab bc cd = begin
    (m • U.X b c bc) • k ≈⟨ assoc ⟩
    m • (U.X b c bc • k) ≈⟨ cong refl (axiom (source (U.r4b ab bc cd))) ⟩
    m • (m • k • m • k • m) ≈⟨ by-assoc Eq.refl ⟩
    (m • m) • ((k • m) • (k • m)) ≈⟨ cong (axiom (source U.r1b)) refl ⟩
    ε • ((k • m) • (k • m)) ≈⟨ left-unit ⟩
    (k • m) • (k • m) ∎
    where
    m = U.M a
    k = U.K a b c d ab bc cd

mixed-trivial : ∀ (a b c d : Fin n) .(ab : a < b) .(bc : b < c) .(cd : c < d) →
  ((U.M a • U.X b c bc) • U.K a b c d ab bc cd) ≈ ε
mixed-trivial a b c d ab bc cd = begin
  (m • U.X b c bc) • k ≈⟨ mixed-square a b c d ab bc cd ⟩
  (k • m) • (k • m) ≈⟨ by-assoc Eq.refl ⟩
  k • ((m • k) • m) ≈⟨ cong refl (cong (axiom (commute m k)) refl) ⟩
  k • ((k • m) • m) ≈⟨ by-assoc Eq.refl ⟩
  (k • k) • (m • m) ≈⟨ cong (axiom (source (U.r1c ab bc cd))) (axiom (source U.r1b)) ⟩
  ε • ε ≈⟨ left-unit ⟩
  ε ∎
  where
  m = U.M a
  k = U.K a b c d ab bc cd

rep : Coset → Word (U.Gen n)
rep c00 = ε
rep c10 = U.M i
rep c11 = U.X i j ij
rep c01 = U.M i • U.X i j ij

private
  m x : Word (U.Gen n)
  m = U.M i
  x = U.X i j ij
  mm : m • m ≈ ε
  mm = axiom (source U.r1b)
  xx : x • x ≈ ε
  xx = axiom (source (U.r1a ij))

gen-reference : ∀ g → [ g ]ʷ ≈ rep (A.state c00 [ g ]ʷ)
gen-reference (U.M-gen a) = sign-reference a
gen-reference (U.X-gen a b ab) = exchange-reference a b (recompute (a FP.<? b) ab)
gen-reference (U.K-gen a b c d ab bc cd) = trans
  (•-cancelʳ (trans (axiom (source (U.r1c ab bc cd)))
    (sym (mixed-trivial a b c d ab bc cd))))
  (cong (sign-reference a) (exchange-reference b c (recompute (b FP.<? c) bc)))

rep-product : ∀ c d → rep c • rep d ≈ rep (A.state c (rep d))
rep-product c00 c00 = left-unit
rep-product c00 c10 = left-unit
rep-product c00 c11 = left-unit
rep-product c00 c01 = left-unit
rep-product c10 c00 = right-unit
rep-product c10 c10 = mm
rep-product c10 c11 = refl
rep-product c10 c01 = trans (sym assoc) (trans (cong mm refl) left-unit)
rep-product c11 c00 = right-unit
rep-product c11 c10 = axiom (commute x m)
rep-product c11 c11 = xx
rep-product c11 c01 = begin
  x • (m • x) ≈⟨ sym assoc ⟩
  (x • m) • x ≈⟨ cong (axiom (commute x m)) refl ⟩
  (m • x) • x ≈⟨ assoc ⟩
  m • (x • x) ≈⟨ cong refl xx ⟩
  m • ε ≈⟨ right-unit ⟩
  m ∎
rep-product c01 c00 = right-unit
rep-product c01 c10 = begin
  (m • x) • m ≈⟨ assoc ⟩
  m • (x • m) ≈⟨ cong refl (axiom (commute x m)) ⟩
  m • (m • x) ≈⟨ sym assoc ⟩
  (m • m) • x ≈⟨ cong mm refl ⟩
  ε • x ≈⟨ left-unit ⟩
  x ∎
rep-product c01 c11 = trans assoc (trans (cong refl xx) right-unit)
rep-product c01 c01 = begin
  (m • x) • (m • x) ≈⟨ by-assoc Eq.refl ⟩
  m • ((x • m) • x) ≈⟨ cong refl (cong (axiom (commute x m)) refl) ⟩
  m • ((m • x) • x) ≈⟨ by-assoc Eq.refl ⟩
  (m • m) • (x • x) ≈⟨ cong mm xx ⟩
  ε • ε ≈⟨ left-unit ⟩
  ε ∎

private
  letter-state : ∀ c (g : U.Gen n) → dyadic-step c g ≡ A.state c (rep (dyadic-step c00 g))
  letter-state c00 (U.M-gen _) = Eq.refl
  letter-state c10 (U.M-gen _) = Eq.refl
  letter-state c11 (U.M-gen _) = Eq.refl
  letter-state c01 (U.M-gen _) = Eq.refl
  letter-state c00 (U.X-gen _ _ _) = Eq.refl
  letter-state c10 (U.X-gen _ _ _) = Eq.refl
  letter-state c11 (U.X-gen _ _ _) = Eq.refl
  letter-state c01 (U.X-gen _ _ _) = Eq.refl
  letter-state c00 (U.K-gen _ _ _ _ _ _ _) = Eq.refl
  letter-state c10 (U.K-gen _ _ _ _ _ _ _) = Eq.refl
  letter-state c11 (U.K-gen _ _ _ _ _ _ _) = Eq.refl
  letter-state c01 (U.K-gen _ _ _ _ _ _ _) = Eq.refl

normalization-from : ∀ c w → rep c • w ≈ rep (A.state c w)
normalization-from c [ g ]ʷ = trans (cong refl (gen-reference g))
  (trans (rep-product c (dyadic-step c00 g))
    (refl' (Eq.cong rep (Eq.sym (letter-state c g)))))
normalization-from c ε = right-unit
normalization-from c (u • v) = trans (sym assoc)
  (trans (cong (normalization-from c u) refl) (normalization-from (A.state c u) v))

normalization : ∀ w → w ≈ rep (A.state c00 w)
normalization w = trans (sym left-unit) (normalization-from c00 w)

completeness : ∀ {u v} → A.state c00 u ≡ A.state c00 v → u ≈ v
completeness {u} {v} eq = trans (normalization u)
  (trans (refl' (Eq.cong rep eq)) (sym (normalization v)))

kernel : ∀ {w} → A.state c00 w ≡ c00 → w ≈ ε
kernel {w} = completeness {u = w} {v = ε}

kernel-only : ∀ {w} → w ≈ ε → A.state c00 w ≡ c00
kernel-only = soundness

square : ∀ w → (w • w) ≈ ε
square w = kernel (Charge.word-involutive c00 w)

-- All four classes occur, and no two distinct representatives become
-- equal after freely imposing commutation.
representatives : ∀ c → A.state c00 (rep c) ≡ c
representatives c00 = Eq.refl
representatives c10 = Eq.refl
representatives c11 = Eq.refl
representatives c01 = Eq.refl

representatives-injective : ∀ {c d} → rep c ≈ rep d → c ≡ d
representatives-injective {c} {d} eq = Eq.trans (Eq.sym (representatives c))
  (Eq.trans (soundness eq) (representatives d))
