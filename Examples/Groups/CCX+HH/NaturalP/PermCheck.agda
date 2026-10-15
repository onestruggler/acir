------------------------------------------------------------------------
-- Presentations of groups
--
-- Two-level words of X letters act by permuting coordinates.
--
-- A word of X letters sends a vector v to the vector whose entry y is
-- v at πʷ w y (`perm-act`), πʷ w composing the transpositions of the
-- letters.  So two such words act alike as soon as their permutations
-- agree at every index (`same-perm-sound`), a boolean about indices
-- alone.  Evaluating the actions themselves, as NaturalP.Columns does,
-- costs about a millisecond per letter, column and entry: some four
-- minutes for 240 letters on five wires, where this takes seconds.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.PermCheck where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; T)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; lookup)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (Dec ; yes ; no ; isYes ; toWitness)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
open import Examples.Groups.CCX+HH.NaturalP.Columns using (allFin ; allFin-sound)

private
  variable
    N : ℕ

  T-∧ : ∀ {x y} → T (x ∧ y) → T x × T y
  T-∧ {true} {true} _ = tt , tt

------------------------------------------------------------------------
-- Transpositions

private
  pick : {y a b : Fin N} → Dec (y ≡ a) → Dec (y ≡ b) → Fin N
  pick {b = b} (yes _) _       = b
  pick {a = a} (no _)  (yes _) = a
  pick {y = y} (no _)  (no _)  = y

-- The transposition of a and b.
tr : Fin N → Fin N → Fin N → Fin N
tr a b y = pick (y ≟ a) (y ≟ b)

tr-act : (a b : Fin N) .(p : a Data.Fin.Base.< b) (v : Vec D N) (y : Fin N) →
  lookup (A.actV (TL.X-gen a b p) v) y ≡ lookup v (tr a b y)
tr-act a b p v y = go (y ≟ a) (y ≟ b)
  where
  go : (da : Dec (y ≡ a)) (db : Dec (y ≡ b)) →
    lookup (A.actV (TL.X-gen a b p) v) y ≡ lookup v (pick da db)
  go (yes ya) _ = trans (cong (lookup (A.actV (TL.X-gen a b p) v)) ya) (A.actV-Xa p v)
  go (no _) (yes yb) = trans (cong (lookup (A.actV (TL.X-gen a b p) v)) yb) (A.actV-Xb p v)
  go (no ya) (no yb) = A.actV-X≢ p v ya yb

------------------------------------------------------------------------
-- Words of X letters

-- Whether every letter is an X letter.
xonly : Word (TL.Gen N) → Bool
xonly [ TL.M-gen _ ]ʷ               = false
xonly [ TL.X-gen _ _ _ ]ʷ           = true
xonly [ TL.K-gen _ _ _ _ _ _ _ ]ʷ   = false
xonly ε                             = true
xonly (u • w)                       = xonly u ∧ xonly w

-- The permutation of the indices: entry y of the image is entry πʷ w y.
πʷ : Word (TL.Gen N) → Fin N → Fin N
πʷ [ TL.M-gen _ ]ʷ y             = y
πʷ [ TL.X-gen a b _ ]ʷ y         = tr a b y
πʷ [ TL.K-gen _ _ _ _ _ _ _ ]ʷ y = y
πʷ ε y                           = y
πʷ (u • w) y                     = πʷ w (πʷ u y)

perm-act : (w : Word (TL.Gen N)) → T (xonly w) → ∀ v y →
  lookup (A.actVʷ w v) y ≡ lookup v (πʷ w y)
perm-act [ TL.M-gen _ ]ʷ () v y
perm-act [ TL.X-gen a b p ]ʷ _ v y = tr-act a b p v y
perm-act [ TL.K-gen _ _ _ _ _ _ _ ]ʷ () v y
perm-act ε _ v y = refl
perm-act (u • w) t v y =
  trans (perm-act u (proj₁ (T-∧ {xonly u} t)) (A.actVʷ w v) y)
    (perm-act w (proj₂ (T-∧ {xonly u} t)) v (πʷ u y))

-- Both words are of X letters, and their permutations agree.
same-perm : (w w′ : Word (TL.Gen N)) → Bool
same-perm w w′ = xonly w ∧ (xonly w′ ∧ allFin λ y → isYes (πʷ w y ≟ πʷ w′ y))

same-perm-sound : (w w′ : Word (TL.Gen N)) → T (same-perm w w′) →
  ∀ v → A.actVʷ w v ≡ A.actVʷ w′ v
same-perm-sound w w′ t v = A.vec-ext λ y →
  trans (perm-act w xw v y)
  (trans (cong (lookup v) (toWitness {a? = πʷ w y ≟ πʷ w′ y} (allFin-sound _ ok y)))
    (sym (perm-act w′ xw′ v y)))
  where
  xw  = proj₁ (T-∧ {xonly w} t)
  xw′ = proj₁ (T-∧ {xonly w′} (proj₂ (T-∧ {xonly w} t)))
  ok  = proj₂ (T-∧ {xonly w′} (proj₂ (T-∧ {xonly w} t)))
