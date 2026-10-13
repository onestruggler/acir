------------------------------------------------------------------------
-- Presentations of groups
--
-- Conjugating a single four-level block by a physical HH.  Additional
-- spectator blocks cancel in pairs; no spectator is initialized.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.LocalHadamard where

open import Data.Fin.Base using (Fin ; _<_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_ ; s≤s ; z≤n)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₀ ; ₁ ; ₂ ; ₃)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (isCommutativeRing-D ; adj-D ; ½ᴰ)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH.Semantics as Q
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι ; mono ; word)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (contiguous)
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition using (left)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-id ; parallel-compose ; parallel-cong ; encode-parallel-correct)

K₀ : T.Gen 4
K₀ = T.K-gen ₀ ₁ ₂ ₃ (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n)))

opaque
  unfolding A.actV A.set₁ A.set₂

  hh₀-action : ∀ v → A.actV K₀ v ≡ Q.hh₀ v
  hh₀-action (a ∷ b ∷ c ∷ d ∷ []) = refl

hh-involutive : ∀ n v → Q.hh n (Q.hh n v) ≡ v
hh-involutive zero v = trans (sym (hh₀-action (Q.hh₀ v)))
  (trans (cong (A.actV K₀) (sym (hh₀-action v))) (A.actV-invol K₀ v))
hh-involutive (suc n) v = trans (parallel-compose (contiguous _) (Q.hh n) (Q.hh n) (Q.hh n) (Q.hh n) v)
  (trans (parallel-cong (contiguous (2 ^ suc (suc n)))
      {f′ = λ x → x} {g′ = λ x → x} (hh-involutive n) (hh-involutive n) v)
    (parallel-id (contiguous (2 ^ suc (suc n))) v))

-- Lift only the first block, retaining the identity on its complement.
local : ∀ n → (Q.State 2 → Q.State 2) → Q.State (suc (suc n)) → Q.State (suc (suc n))
local zero f = f
local (suc n) f = parallel (contiguous (2 ^ suc (suc n))) (local n f) (λ v → v)

local-cong : ∀ n {f g} → (∀ v → f v ≡ g v) → ∀ v → local n f v ≡ local n g v
local-cong zero eq = eq
local-cong (suc n) eq = parallel-cong (contiguous (2 ^ suc (suc n)))
  {g = λ x → x} {g′ = λ x → x} (local-cong n eq) (λ v → refl)

localized : ∀ n → Word (T.Gen 4) → Word (T.Gen (2 ^ suc (suc n)))
localized zero w = w
localized (suc n) w = word (left (contiguous _)) (localized n w)

local-action : ∀ n w v → A.actVʷ (localized n w) v ≡ local n (A.actVʷ w) v
local-action zero w v = refl
local-action (suc n) w v = trans (encode-parallel-correct (contiguous _) (localized n w) ε v)
  (parallel-cong (contiguous (2 ^ suc (suc n)))
    {g = λ x → x} {g′ = λ x → x} (local-action n w) (λ v → refl) v)

level : ∀ n → Fin 4 → Fin (2 ^ suc (suc n))
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

localized-• : ∀ n u w → localized n (u • w) ≡ localized n u • localized n w
localized-• zero u w = refl
localized-• (suc n) u w = cong (word (left (contiguous _))) (localized-• n u w)

-- Any four-level conjugation equation lifts to arbitrary width, even
-- though the physical HH acts on every spectator block at once.
conjugate : ∀ n (f g : Q.State 2 → Q.State 2) →
  (∀ v → Q.hh₀ (f (Q.hh₀ v)) ≡ g v) →
  ∀ v → Q.hh n (local n f (Q.hh n v)) ≡ local n g v
conjugate zero f g eq = eq
conjugate (suc n) f g eq v = trans
  (cong (parallel (contiguous _) (Q.hh n) (Q.hh n))
    (parallel-compose (contiguous _) (local n f) (λ x → x) (Q.hh n) (Q.hh n) v))
  (trans (parallel-compose (contiguous _) (Q.hh n) (Q.hh n)
      (λ x → local n f (Q.hh n x)) (Q.hh n) v)
    (parallel-cong (contiguous _) (conjugate n f g eq) (hh-involutive n) v))

conjugate-word : ∀ n u w → A.⟦ [ K₀ ]ʷ • u • [ K₀ ]ʷ ⟧ᵐ ≡ A.⟦ w ⟧ᵐ →
  ∀ v → Q.hh n (A.actVʷ (localized n u) (Q.hh n v)) ≡ A.actVʷ (localized n w) v
conjugate-word n u w eq v = trans (cong (Q.hh n) (local-action n u (Q.hh n v)))
  (trans (conjugate n (A.actVʷ u) (A.actVʷ w) base v) (sym (local-action n w v)))
  where
  base : ∀ v → Q.hh₀ (A.actVʷ u (Q.hh₀ v)) ≡ A.actVʷ w v
  base v = trans (cong Q.hh₀ (cong (A.actVʷ u) (sym (hh₀-action v))))
    (trans (sym (hh₀-action (A.actVʷ u (A.actV K₀ v))))
      (A.same-action ([ K₀ ]ʷ • u • [ K₀ ]ʷ) w eq v))
