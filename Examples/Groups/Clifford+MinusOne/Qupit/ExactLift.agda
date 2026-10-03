------------------------------------------------------------------------
-- Presentations of groups
--
-- Lifting a derivation mod scalars to an exact one, its scalar
-- computed by the phase Φ.
--
-- A Paper-V0 derivation u ≈ v holds in the exact Clifford group only up
-- to a power of ω.  Which power is what the exact group's cocycle says:
-- reading a circuit there with every gate lifted trivially, it picks up
-- the scalar ω ^ Φ w (Clifford.Qupit.SemRealises.Width.scal≈).  So if
-- Φ u = c + Φ v in ℤ/pℤ, then
--
--     [ u ]ᵣ  ≈  [ ω ^ c ]ₗ • [ v ]ᵣ        in n Exact,_===_,
--
-- and, along the left embedding, ⌜ u ⌝ ≈ ω^c • ⌜ v ⌝ in the rule set
-- with -1.  This is how every Figure-1 rule that is a theorem of
-- Paper-V0 mod scalars becomes exact: the gate parts are related mod
-- scalars, and the scalar is read off Φ instead of being tracked
-- through the derivation.
--
-- How.  Not by induction on the derivation: by COMPLETENESS of the exact
-- presentation (Clifford.Qupit.Presentation's `injective`).  It is
-- enough that the two sides have the same denotation, and denotations
-- are pairs compared componentwise:
--
--   gates    u and ε • v, equal mod scalars by hypothesis;
--   scalars  scal u ≈ ω^Φu = ω^(c + Φv) ≈ ω^c • ω^Φv ≈ ω^c • scal v,
--            the middle step being the transport ℤ/pℤ → ⟨ω⟩
--            multiplicative (Cyclic.Scalars.emb-∙).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford+MinusOne.Qupit.ExactLift
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_ ; wmap)
import Presentation.Base as PB
open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)

-- The transport ℤ/pℤ → ⟨ω⟩, k ↦ ω ^ toℕ k.
import Examples.Groups.Cyclic.Scalars as Sc
private
  module Sp = Sc p-2

import Examples.Groups.Clifford+MinusOne.Qupit.Syntactics
  p-3 p-prime g* g-gen as N
import Examples.Groups.Clifford+MinusOne.Qupit.Translation
  p-3 p-prime g* g-gen as T
open import Examples.Groups.Clifford+MinusOne.Qupit.Semantics
  p-3 p-prime g* g-gen
  using (Exact-group ; module Exact-Reading)

-- The phase Φ, and the scalar it computes.
import Examples.Groups.Clifford.Qupit.SemRealises
  p-3 p-prime g* g-gen as RL

------------------------------------------------------------------------
-- In the exact rule set

exact-lift : ∀ n {a b : N.Circuit n} → PB._≈_ (N.CR._QRel,_===_ n) a b →
             ∀ (c : ℤ ₚ) → RL.Width.Φ n a ≡ c + RL.Width.Φ n b →
             PB._≈_ (n N.Exact,_===_) [ a ]ᵣ ([ N.ω ^ toℕ c ]ₗ • [ b ]ᵣ)
exact-lift n {a} {b} p c e =
  R.injective
    (R.emb-r-pair a R.⟨G⟩ pair R.⟨G⟩ R.G-sym (R.val (N.ω ^ toℕ c) b))
  where
  module R  = Exact-Reading n
  module W  = RL.Width n
  module G  = Group (Exact-group n)
  module KB = PB N.Scalar-relation
  module QB = PB (N.CR._QRel,_===_ n)

  -- The scalar parts: both are ω to their phase, and the phases differ
  -- by c.
  scalar : KB._≈_ (R.Ev.scal a) ((N.ω ^ toℕ c • R.Ev.scal b) • ε)
  scalar =
    KB.trans (W.scal≈ a)
      (KB.trans (Sp.emb-cong e)
        (KB.trans (Sp.emb-∙ c (W.Φ b))
          (KB.trans (KB.cong KB.refl (KB.sym (W.scal≈ b)))
                    (KB.sym KB.right-unit))))

  -- The gate parts are the hypothesis.
  pair : G._≈_ (R.Ev.scal a , a) ((N.ω ^ toℕ c • R.Ev.scal b) • ε , ε • b)
  pair = scalar , QB.trans p (QB.sym QB.left-unit)

------------------------------------------------------------------------
-- In the rule set with -1
--
-- Along the left embedding, where the twice-embedded ω ^ k is the power
-- ω± ^ k on the nose.

exact-lift± : ∀ n {a b : N.Circuit n} → PB._≈_ (N.CR._QRel,_===_ n) a b →
              ∀ (c : ℤ ₚ) → RL.Width.Φ n a ≡ c + RL.Width.Φ n b →
              N.⌜ a ⌝ T.≈± (N.ω± ^ toℕ c • N.⌜ b ⌝)
exact-lift± n p c e =
  A.trans (A.lefts (exact-lift n p c e)) (A.cong (A.refl' omega) A.refl)
  where
  module A = T.Algebra n

  omega : [ [ N.ω ^ toℕ c ]ₗ ]ₗ ≡ N.ω± {n} ^ toℕ c
  omega = Eq.trans (Eq.cong (wmap inj₁) (T.wmap-^ inj₁ N.ω (toℕ c)))
                   (T.wmap-^ inj₁ [ inj₁ tt ]ʷ (toℕ c))
