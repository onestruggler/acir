------------------------------------------------------------------------
-- Presentations of groups
--
-- Localization in the first eight basis levels, with identity on
-- all other levels.  Physical HH conjugation respects localization:
-- every complementary Hadamard block occurs twice and cancels.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.LocalEight where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.Nat.Base using (zero ; suc ; _^_ ; _+_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (isCommutativeRing-D ; adj-D ; ½ᴰ)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι ; mono ; word)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (contiguous)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition using (left)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-compose ; parallel-cong ; encode-parallel-correct)
open import Examples.Groups.CCX+HH.GeneralN.LocalHadamard using (hh-involutive)

width : ℕ → ℕ
width n = suc (suc (suc n))

local : ∀ n → (Q.State (width 0) → Q.State (width 0)) → Q.State (width n) → Q.State (width n)
local zero f = f
local (suc n) f = parallel (contiguous (2 ^ width n)) (local n f) (λ v → v)

local-cong : ∀ n {f g} → (∀ v → f v ≡ g v) → ∀ v → local n f v ≡ local n g v
local-cong zero eq = eq
local-cong (suc n) eq = parallel-cong (contiguous (2 ^ width n))
  {g = λ x → x} {g′ = λ x → x} (local-cong n eq) (λ v → refl)

local-compose : ∀ n f g v → local n f (local n g v) ≡ local n (λ x → f (g x)) v
local-compose zero f g v = refl
local-compose (suc n) f g v = trans
  (parallel-compose (contiguous (2 ^ width n)) (local n f) (λ x → x) (local n g) (λ x → x) v)
  (parallel-cong (contiguous (2 ^ width n))
    {g = λ x → x} {g′ = λ x → x} (local-compose n f g) (λ v → refl) v)

localized : ∀ n → Word (T.Gen (2 ^ width 0)) → Word (T.Gen (2 ^ width n))
localized zero w = w
localized (suc n) w = word (left (contiguous _)) (localized n w)

local-action : ∀ n w v → A.actVʷ (localized n w) v ≡ local n (A.actVʷ w) v
local-action zero w v = refl
local-action (suc n) w v = trans (encode-parallel-correct (contiguous _) (localized n w) ε v)
  (parallel-cong (contiguous (2 ^ width n))
    {g = λ x → x} {g′ = λ x → x} (local-action n w) (λ v → refl) v)

level : ∀ n → Fin (2 ^ width 0) → Fin (2 ^ width n)
level zero i = i
level (suc n) i = ι (left (contiguous _)) (level n i)

level-increasing : ∀ n {i j} → i < j → level n i < level n j
level-increasing zero p = p
level-increasing (suc n) p = mono (left (contiguous _)) (level-increasing n p)

localized-M : ∀ n i → localized n (T.M i) ≡ T.M (level n i)
localized-M zero i = refl
localized-M (suc n) i = cong (word (left (contiguous _))) (localized-M n i)

localized-X : ∀ n i j (p : i < j) → localized n (T.X i j p) ≡
  T.X (level n i) (level n j) (level-increasing n p)
localized-X zero i j p = refl
localized-X (suc n) i j p = cong (word (left (contiguous _))) (localized-X n i j p)

localized-K : ∀ n a b c d (p : a < b) (q : b < c) (r : c < d) →
  localized n (T.K a b c d p q r) ≡
  T.K (level n a) (level n b) (level n c) (level n d)
    (level-increasing n p) (level-increasing n q) (level-increasing n r)
localized-K zero a b c d p q r = refl
localized-K (suc n) a b c d p q r = cong (word (left (contiguous _))) (localized-K n a b c d p q r)

localized-• : ∀ n u w → localized n (u • w) ≡ localized n u • localized n w
localized-• zero u w = refl
localized-• (suc n) u w = cong (word (left (contiguous _))) (localized-• n u w)

conjugate : ∀ n f g → (∀ v → Q.hh 1 (f (Q.hh 1 v)) ≡ g v) →
  ∀ v → Q.hh (suc n) (local n f (Q.hh (suc n) v)) ≡ local n g v
conjugate zero f g eq = eq
conjugate (suc n) f g eq v = trans
  (cong (parallel (contiguous _) (Q.hh (suc n)) (Q.hh (suc n)))
    (parallel-compose (contiguous _) (local n f) (λ x → x) (Q.hh (suc n)) (Q.hh (suc n)) v))
  (trans (parallel-compose (contiguous _) (Q.hh (suc n)) (Q.hh (suc n))
      (λ x → local n f (Q.hh (suc n) x)) (Q.hh (suc n)) v)
    (parallel-cong (contiguous _) (conjugate n f g eq) (hh-involutive (suc n)) v))

conjugate-word : ∀ n u w → A.⟦ E.HH-block 1 • u • E.HH-block 1 ⟧ᵐ ≡ A.⟦ w ⟧ᵐ →
  ∀ v → Q.hh (suc n) (A.actVʷ (localized n u) (Q.hh (suc n) v)) ≡ A.actVʷ (localized n w) v
conjugate-word n u w eq v = trans (cong (Q.hh (suc n)) (local-action n u (Q.hh (suc n) v)))
  (trans (conjugate n (A.actVʷ u) (A.actVʷ w) base v) (sym (local-action n w v)))
  where
  hh-action : ∀ v → A.actVʷ (E.HH-block 1) v ≡ Q.hh 1 v
  hh-action = Q.encoding-correct-action (H.gate₂ {1} H.HH-gate)
  base : ∀ v → Q.hh 1 (A.actVʷ u (Q.hh 1 v)) ≡ A.actVʷ w v
  base v = trans (cong (Q.hh 1) (cong (A.actVʷ u) (sym (hh-action v))))
    (trans (sym (hh-action (A.actVʷ u (A.actVʷ (E.HH-block 1) v))))
      (A.same-action (E.HH-block 1 • u • E.HH-block 1) w eq v))
