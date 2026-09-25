------------------------------------------------------------------------
-- Presentations of groups
--
-- The branches of Definition A.2's action, one lemma each
--
-- `act` and its classifier `cls` are defined by `with`, which a goal
-- does not see through, so each branch the transport of `Frame` needs
-- is computed here once, by the same chain of decisions the definition
-- makes.  They are stated over the action's own parameters, the two
-- distinguished indices as *variables*: at the concrete `RS.z₀` and
-- `RS.o₁` every with-abstraction unfolds `Gray.fin8` and the proof it
-- carries, and thirty of these lemmas took two gigabytes where over
-- variables they take a few megabytes each.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.FrameAct (m : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (ε ; _•_ ; [_]ʷ)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets
  using (⟨ε⟩ ; ⟨M⟩ ; ⟨K⟩ ; ⟨KM⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (−1−1 ; −1X ; XX ; HH)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics using (−1[_] ; X[_,_] ; H[_,_])

import Examples.Groups.Real-Clifford+CH.Auxiliary.CosetAction as CA

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

module Branches (z o : Fin N) (z≢o : z ≢ o) where

  open CA (₃₊ m) z o z≢o using (act)

  -- At ⟨ε⟩.
  aεX-deg : ∀ (a : Fin N) → act ⟨ε⟩ X[ a , a ] ≡ (ε , ⟨ε⟩)
  aεX-deg a with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aεX-o : ∀ (b : Fin N) (ob : o ≢ b) → act ⟨ε⟩ X[ o , b ] ≡ ([ −1X b o b ob ]ʷ , ⟨M⟩)
  aεX-o b ob with o ≟ b
  ... | yes h = ⊥-elim (ob h)
  ... | no  _ with o ≟ o
  ...         | yes _  = Eq.refl
  ...         | no  ne = ⊥-elim (ne Eq.refl)

  aεX-o′ : ∀ (a : Fin N) (ao : a ≢ o) → act ⟨ε⟩ X[ a , o ] ≡ ([ −1X a a o ao ]ʷ , ⟨M⟩)
  aεX-o′ a ao with a ≟ o
  ... | yes h = ⊥-elim (ao h)
  ... | no  _ with a ≟ o
  ...         | yes h = ⊥-elim (ao h)
  ...         | no  _ with o ≟ o
  ...                 | yes _  = Eq.refl
  ...                 | no  ne = ⊥-elim (ne Eq.refl)

  aεX-off : ∀ (a b : Fin N) (ab : a ≢ b) → a ≢ o → b ≢ o →
            act ⟨ε⟩ X[ a , b ] ≡ ([ −1X o a b ab ]ʷ , ⟨M⟩)
  aεX-off a b ab ao bo with a ≟ b
  ... | yes h = ⊥-elim (ab h)
  ... | no  _ with a ≟ o
  ...         | yes h = ⊥-elim (ao h)
  ...         | no  _ with b ≟ o
  ...                 | yes h = ⊥-elim (bo h)
  ...                 | no  _ = Eq.refl

  aεH-deg : ∀ (a : Fin N) → act ⟨ε⟩ H[ a , a ] ≡ (ε , ⟨ε⟩)
  aεH-deg a with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aεH : ∀ (a b : Fin N) (ab : a ≢ b) → act ⟨ε⟩ H[ a , b ] ≡ ([ HH a b z o ab z≢o ]ʷ , ⟨K⟩)
  aεH a b ab with a ≟ b
  ... | yes h = ⊥-elim (ab h)
  ... | no  _ = Eq.refl

  -- At ⟨M⟩.
  aMX-deg : ∀ (a : Fin N) → act ⟨M⟩ X[ a , a ] ≡ (ε , ⟨M⟩)
  aMX-deg a with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aMX : ∀ (a b : Fin N) (ab : a ≢ b) → act ⟨M⟩ X[ a , b ] ≡ ([ −1X o a b ab ]ʷ , ⟨ε⟩)
  aMX a b ab with a ≟ b
  ... | yes h = ⊥-elim (ab h)
  ... | no  _ = Eq.refl

  aMH-deg : ∀ (a : Fin N) → act ⟨M⟩ H[ a , a ] ≡ (ε , ⟨M⟩)
  aMH-deg a with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aMH-o : ∀ (b : Fin N) (ob : o ≢ b) →
          act ⟨M⟩ H[ o , b ] ≡ ([ −1X b o b ob ]ʷ • [ HH o b z o ob z≢o ]ʷ , ⟨KM⟩)
  aMH-o b ob with o ≟ b
  ... | yes h = ⊥-elim (ob h)
  ... | no  _ with o ≟ o
  ...         | yes _  = Eq.refl
  ...         | no  ne = ⊥-elim (ne Eq.refl)

  aMH-o′ : ∀ (a : Fin N) (ao : a ≢ o) →
           act ⟨M⟩ H[ a , o ] ≡ ([ −1X o a o ao ]ʷ • [ HH a o z o ao z≢o ]ʷ , ⟨KM⟩)
  aMH-o′ a ao with a ≟ o
  ... | yes h = ⊥-elim (ao h)
  ... | no  _ with a ≟ o
  ...         | yes h = ⊥-elim (ao h)
  ...         | no  _ with o ≟ o
  ...                 | yes _  = Eq.refl
  ...                 | no  ne = ⊥-elim (ne Eq.refl)

  aMH-off : ∀ (a b : Fin N) (ab : a ≢ b) → a ≢ o → b ≢ o →
            act ⟨M⟩ H[ a , b ] ≡ ([ HH a b z o ab z≢o ]ʷ , ⟨KM⟩)
  aMH-off a b ab ao bo with a ≟ b
  ... | yes h = ⊥-elim (ab h)
  ... | no  _ with a ≟ o
  ...         | yes h = ⊥-elim (ao h)
  ...         | no  _ with b ≟ o
  ...                 | yes h = ⊥-elim (bo h)
  ...                 | no  _ = Eq.refl

  -- At ⟨K⟩.
  aKZ-z : act ⟨K⟩ −1[ z ] ≡ ([ −1−1 o z ]ʷ , ⟨KM⟩)
  aKZ-z with z ≟ z
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aKZ-o : act ⟨K⟩ −1[ o ] ≡ ([ −1−1 o o ]ʷ , ⟨KM⟩)
  aKZ-o with o ≟ z
  ... | yes h = ⊥-elim (z≢o (Eq.sym h))
  ... | no  _ with o ≟ o
  ...         | yes _  = Eq.refl
  ...         | no  ne = ⊥-elim (ne Eq.refl)

  aKZ-off : ∀ (a : Fin N) → a ≢ z → a ≢ o → act ⟨K⟩ −1[ a ] ≡ ([ −1X a z o z≢o ]ʷ , ⟨KM⟩)
  aKZ-off a az ao with a ≟ z
  ... | yes h = ⊥-elim (az h)
  ... | no  _ with a ≟ o
  ...         | yes h = ⊥-elim (ao h)
  ...         | no  _ = Eq.refl

  aKX-deg : ∀ (a : Fin N) → act ⟨K⟩ X[ a , a ] ≡ (ε , ⟨K⟩)
  aKX-deg a with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aKX-zo : act ⟨K⟩ X[ z , o ] ≡ ([ −1X o z o z≢o ]ʷ , ⟨KM⟩)
  aKX-zo with z ≟ o
  ... | yes h = ⊥-elim (z≢o h)
  ... | no  _ with z ≟ z
  ...         | no  ne = ⊥-elim (ne Eq.refl)
  ...         | yes _ with o ≟ o
  ...                 | no  ne = ⊥-elim (ne Eq.refl)
  ...                 | yes _  = Eq.refl

  aKX-oz : act ⟨K⟩ X[ o , z ] ≡ ([ −1X o z o z≢o ]ʷ , ⟨KM⟩)
  aKX-oz with o ≟ z
  ... | yes h = ⊥-elim (z≢o (Eq.sym h))
  ... | no  _ with o ≟ z
  ...         | yes h = ⊥-elim (z≢o (Eq.sym h))
  ...         | no  _ with z ≟ z
  ...                 | no  ne = ⊥-elim (ne Eq.refl)
  ...                 | yes _ with o ≟ o
  ...                         | no  ne = ⊥-elim (ne Eq.refl)
  ...                         | yes _  = Eq.refl

  aKX-zt : ∀ (t : Fin N) (zt : z ≢ t) (t≢o : t ≢ o) →
           act ⟨K⟩ X[ z , t ]
           ≡ ([ XX z o z t z≢o zt ]ʷ • [ HH t o z o t≢o z≢o ]ʷ , ⟨KM⟩)
  aKX-zt t zt t≢o with z ≟ t
  ... | yes h = ⊥-elim (zt h)
  ... | no  _ with z ≟ z
  ...         | no  ne = ⊥-elim (ne Eq.refl)
  ...         | yes _ with t ≟ o
  ...                 | yes h = ⊥-elim (t≢o h)
  ...                 | no  _ = Eq.refl

  aKX-tz : ∀ (t : Fin N) (t≢z : t ≢ z) (t≢o : t ≢ o) →
           act ⟨K⟩ X[ t , z ]
           ≡ ([ XX z o t z z≢o t≢z ]ʷ • [ HH t o z o t≢o z≢o ]ʷ , ⟨KM⟩)
  aKX-tz t t≢z t≢o with t ≟ z
  ... | yes h = ⊥-elim (t≢z h)
  ... | no  _ with t ≟ z
  ...         | yes h = ⊥-elim (t≢z h)
  ...         | no  _ with z ≟ z
  ...                 | no  ne = ⊥-elim (ne Eq.refl)
  ...                 | yes _ with t ≟ o
  ...                         | yes h = ⊥-elim (t≢o h)
  ...                         | no  _ = Eq.refl

  aKX-ot : ∀ (t : Fin N) (t≢z : t ≢ z) (ot : o ≢ t) →
           act ⟨K⟩ X[ o , t ]
           ≡ ([ −1X t o t ot ]ʷ • [ HH z t z o (λ h → t≢z (Eq.sym h)) z≢o ]ʷ , ⟨KM⟩)
  aKX-ot t t≢z ot with o ≟ t
  ... | yes h = ⊥-elim (ot h)
  ... | no  _ with o ≟ z
  ...         | yes h = ⊥-elim (z≢o (Eq.sym h))
  ...         | no  _ with t ≟ z
  ...                 | yes h = ⊥-elim (t≢z h)
  ...                 | no  _ with o ≟ o
  ...                         | no  ne = ⊥-elim (ne Eq.refl)
  ...                         | yes _  = Eq.refl

  aKX-to : ∀ (t : Fin N) (t≢z : t ≢ z) (t≢o : t ≢ o) →
           act ⟨K⟩ X[ t , o ]
           ≡ ([ −1X t t o t≢o ]ʷ • [ HH z t z o (λ h → t≢z (Eq.sym h)) z≢o ]ʷ , ⟨KM⟩)
  aKX-to t t≢z t≢o with t ≟ o
  ... | yes h = ⊥-elim (t≢o h)
  ... | no  _ with t ≟ z
  ...         | yes h = ⊥-elim (t≢z h)
  ...         | no  _ with o ≟ z
  ...                 | yes h = ⊥-elim (z≢o (Eq.sym h))
  ...                 | no  _ with t ≟ o
  ...                         | yes h = ⊥-elim (t≢o h)
  ...                         | no  _ with o ≟ o
  ...                                 | no  ne = ⊥-elim (ne Eq.refl)
  ...                                 | yes _  = Eq.refl

  aKX-none : ∀ (a b : Fin N) (ab : a ≢ b) → a ≢ z → b ≢ z → a ≢ o → b ≢ o →
             act ⟨K⟩ X[ a , b ] ≡ ([ XX a b z o ab z≢o ]ʷ , ⟨KM⟩)
  aKX-none a b ab az bz ao bo with a ≟ b
  ... | yes h = ⊥-elim (ab h)
  ... | no  _ with a ≟ z
  ...         | yes h = ⊥-elim (az h)
  ...         | no  _ with b ≟ z
  ...                 | yes h = ⊥-elim (bz h)
  ...                 | no  _ with a ≟ o
  ...                         | yes h = ⊥-elim (ao h)
  ...                         | no  _ with b ≟ o
  ...                                 | yes h = ⊥-elim (bo h)
  ...                                 | no  _ = Eq.refl

  aKH-deg : ∀ (a : Fin N) → act ⟨K⟩ H[ a , a ] ≡ (ε , ⟨K⟩)
  aKH-deg a with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aKH : ∀ (a b : Fin N) (ab : a ≢ b) → act ⟨K⟩ H[ a , b ] ≡ ([ HH z o a b z≢o ab ]ʷ , ⟨ε⟩)
  aKH a b ab with a ≟ b
  ... | yes h = ⊥-elim (ab h)
  ... | no  _ = Eq.refl

  -- At ⟨KM⟩.
  aKMZ-z : act ⟨KM⟩ −1[ z ] ≡ ([ −1−1 o z ]ʷ , ⟨K⟩)
  aKMZ-z with z ≟ z
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aKMZ-o : act ⟨KM⟩ −1[ o ] ≡ ([ −1−1 o o ]ʷ , ⟨K⟩)
  aKMZ-o with o ≟ z
  ... | yes h = ⊥-elim (z≢o (Eq.sym h))
  ... | no  _ with o ≟ o
  ...         | yes _  = Eq.refl
  ...         | no  ne = ⊥-elim (ne Eq.refl)

  aKMZ-off : ∀ (a : Fin N) → a ≢ z → a ≢ o → act ⟨KM⟩ −1[ a ] ≡ ([ −1X a z o z≢o ]ʷ , ⟨K⟩)
  aKMZ-off a az ao with a ≟ z
  ... | yes h = ⊥-elim (az h)
  ... | no  _ with a ≟ o
  ...         | yes h = ⊥-elim (ao h)
  ...         | no  _ = Eq.refl

  aKMX-deg : ∀ (a : Fin N) → act ⟨KM⟩ X[ a , a ] ≡ (ε , ⟨KM⟩)
  aKMX-deg a with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aKMX-zo : act ⟨KM⟩ X[ z , o ] ≡ ([ −1X z z o z≢o ]ʷ , ⟨K⟩)
  aKMX-zo with z ≟ o
  ... | yes h = ⊥-elim (z≢o h)
  ... | no  _ with z ≟ z
  ...         | no  ne = ⊥-elim (ne Eq.refl)
  ...         | yes _ with o ≟ o
  ...                 | no  ne = ⊥-elim (ne Eq.refl)
  ...                 | yes _  = Eq.refl

  aKMX-oz : act ⟨KM⟩ X[ o , z ] ≡ ([ −1X z z o z≢o ]ʷ , ⟨K⟩)
  aKMX-oz with o ≟ z
  ... | yes h = ⊥-elim (z≢o (Eq.sym h))
  ... | no  _ with o ≟ z
  ...         | yes h = ⊥-elim (z≢o (Eq.sym h))
  ...         | no  _ with z ≟ z
  ...                 | no  ne = ⊥-elim (ne Eq.refl)
  ...                 | yes _ with o ≟ o
  ...                         | no  ne = ⊥-elim (ne Eq.refl)
  ...                         | yes _  = Eq.refl

  aKMX-zt : ∀ (t : Fin N) (zt : z ≢ t) (t≢o : t ≢ o) →
            act ⟨KM⟩ X[ z , t ]
            ≡ ([ XX z o z t z≢o zt ]ʷ • [ HH t o z o t≢o z≢o ]ʷ , ⟨K⟩)
  aKMX-zt t zt t≢o with z ≟ t
  ... | yes h = ⊥-elim (zt h)
  ... | no  _ with z ≟ z
  ...         | no  ne = ⊥-elim (ne Eq.refl)
  ...         | yes _ with t ≟ o
  ...                 | yes h = ⊥-elim (t≢o h)
  ...                 | no  _ = Eq.refl

  aKMX-tz : ∀ (t : Fin N) (t≢z : t ≢ z) (t≢o : t ≢ o) →
            act ⟨KM⟩ X[ t , z ]
            ≡ ([ XX z o t z z≢o t≢z ]ʷ • [ HH t o z o t≢o z≢o ]ʷ , ⟨K⟩)
  aKMX-tz t t≢z t≢o with t ≟ z
  ... | yes h = ⊥-elim (t≢z h)
  ... | no  _ with t ≟ z
  ...         | yes h = ⊥-elim (t≢z h)
  ...         | no  _ with z ≟ z
  ...                 | no  ne = ⊥-elim (ne Eq.refl)
  ...                 | yes _ with t ≟ o
  ...                         | yes h = ⊥-elim (t≢o h)
  ...                         | no  _ = Eq.refl

  aKMX-ot : ∀ (t : Fin N) (t≢z : t ≢ z) (ot : o ≢ t) →
            act ⟨KM⟩ X[ o , t ]
            ≡ ([ XX z o o t z≢o ot ]ʷ • [ HH z t z o (λ h → t≢z (Eq.sym h)) z≢o ]ʷ , ⟨K⟩)
  aKMX-ot t t≢z ot with o ≟ t
  ... | yes h = ⊥-elim (ot h)
  ... | no  _ with o ≟ z
  ...         | yes h = ⊥-elim (z≢o (Eq.sym h))
  ...         | no  _ with t ≟ z
  ...                 | yes h = ⊥-elim (t≢z h)
  ...                 | no  _ with o ≟ o
  ...                         | no  ne = ⊥-elim (ne Eq.refl)
  ...                         | yes _  = Eq.refl

  aKMX-to : ∀ (t : Fin N) (t≢z : t ≢ z) (t≢o : t ≢ o) →
            act ⟨KM⟩ X[ t , o ]
            ≡ ([ XX z o t o z≢o t≢o ]ʷ • [ HH z t z o (λ h → t≢z (Eq.sym h)) z≢o ]ʷ , ⟨K⟩)
  aKMX-to t t≢z t≢o with t ≟ o
  ... | yes h = ⊥-elim (t≢o h)
  ... | no  _ with t ≟ z
  ...         | yes h = ⊥-elim (t≢z h)
  ...         | no  _ with o ≟ z
  ...                 | yes h = ⊥-elim (z≢o (Eq.sym h))
  ...                 | no  _ with t ≟ o
  ...                         | yes h = ⊥-elim (t≢o h)
  ...                         | no  _ with o ≟ o
  ...                                 | no  ne = ⊥-elim (ne Eq.refl)
  ...                                 | yes _  = Eq.refl

  aKMX-none : ∀ (a b : Fin N) (ab : a ≢ b) → a ≢ z → b ≢ z → a ≢ o → b ≢ o →
              act ⟨KM⟩ X[ a , b ] ≡ ([ XX a b z o ab z≢o ]ʷ , ⟨K⟩)
  aKMX-none a b ab az bz ao bo with a ≟ b
  ... | yes h = ⊥-elim (ab h)
  ... | no  _ with a ≟ z
  ...         | yes h = ⊥-elim (az h)
  ...         | no  _ with b ≟ z
  ...                 | yes h = ⊥-elim (bz h)
  ...                 | no  _ with a ≟ o
  ...                         | yes h = ⊥-elim (ao h)
  ...                         | no  _ with b ≟ o
  ...                                 | yes h = ⊥-elim (bo h)
  ...                                 | no  _ = Eq.refl

  aKMH-deg : ∀ (a : Fin N) → act ⟨KM⟩ H[ a , a ] ≡ (ε , ⟨KM⟩)
  aKMH-deg a with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  aKMH-o : ∀ (b : Fin N) (ob : o ≢ b) →
           act ⟨KM⟩ H[ o , b ] ≡ ([ HH z o o b z≢o ob ]ʷ • [ −1X o o b ob ]ʷ , ⟨M⟩)
  aKMH-o b ob with o ≟ b
  ... | yes h = ⊥-elim (ob h)
  ... | no  _ with o ≟ o
  ...         | yes _  = Eq.refl
  ...         | no  ne = ⊥-elim (ne Eq.refl)

  aKMH-o′ : ∀ (a : Fin N) (ao : a ≢ o) →
            act ⟨KM⟩ H[ a , o ] ≡ ([ HH z o a o z≢o ao ]ʷ • [ −1X a a o ao ]ʷ , ⟨M⟩)
  aKMH-o′ a ao with a ≟ o
  ... | yes h = ⊥-elim (ao h)
  ... | no  _ with a ≟ o
  ...         | yes h = ⊥-elim (ao h)
  ...         | no  _ with o ≟ o
  ...                 | yes _  = Eq.refl
  ...                 | no  ne = ⊥-elim (ne Eq.refl)

  aKMH-off : ∀ (a b : Fin N) (ab : a ≢ b) → a ≢ o → b ≢ o →
             act ⟨KM⟩ H[ a , b ] ≡ ([ HH z o a b z≢o ab ]ʷ , ⟨M⟩)
  aKMH-off a b ab ao bo with a ≟ b
  ... | yes h = ⊥-elim (ab h)
  ... | no  _ with a ≟ o
  ...         | yes h = ⊥-elim (ao h)
  ...         | no  _ with b ≟ o
  ...                 | yes h = ⊥-elim (bo h)
  ...                 | no  _ = Eq.refl
