------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the qubit Clifford group,
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ Clifford n ─→ 1,
--
-- as an ordinary extension.
--
-- The total group is the group Selinger's Figure 8 presents: Clifford
-- words modulo the *exact* congruence, which unlike ≈ᶜ still sees the
-- global scalar.  So this mirrors layer 1 (Qubit.CliffordGroup), where
-- the total group is Clifford words modulo the P4-action — and, as
-- there, the extension record is assembled by hand rather than through a
-- product construction.
--
-- Taking the total group this way makes proj the *identity on words*,
-- which is what one wants downstream, and makes the three residual
-- obligations recognisable as Selinger's theorems rather than as
-- bookkeeping:
--
--   sound      — Figure 8 is sound for the P4-action, so the identity on
--                words descends to Clifford n;
--   scalars    — a word acting trivially on P4 is a power of ω
--                (completeness, restricted to the scalars);
--   ω-faithful — ω has order exactly 8, i.e. the scalars are not
--                collapsed by Figure 8.
--
-- Everything else — the group structure of the Figure-8 words, that
-- k ↦ ωᵏ is a homomorphism ℤ/8 → Exact n, surjectivity of proj, and that
-- proj kills the scalars — is proved here.
--
-- The last obligation is the one the P4-action cannot help with:
-- action-blind at the end shows that if ≈ᶜ implied the Figure-8
-- congruence then ω would equal ε, so ω-faithful has to come from a
-- faithful model of the exact Clifford group.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.ExactExtension where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Empty using (⊥)
open import Data.Fin using (toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat as Nat using (ℕ ; zero ; suc ; _%_ ; _/_)
open import Data.Nat.DivMod using (m%n<n ; m≡m%n+[m/n]*n)
open import Data.Product using (_,_ ; ∃ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)

open import Zp.ModularArithmetic using (ℤ ; +-0-group)

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

open import Examples.Groups.Clifford.Qubit.CliffordGroup
  using (p-2 ; p-prime ; _≈ᶜ_ ; Clifford-group ; ≈ᶜ-refl)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8 using (ω ; _CRel,_===_ ; srel ; lemma-cong↑)

open import Examples.Groups.Clifford.Qubit.Selinger.Action using (cact-ω ; cact-ω^)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The scalars ⟨ω⟩ ≅ ℤ/8
--
-- Written additively in the exponent of ω.  (+-0-group m has carrier
-- ℤ (₂₊ m), so order 8 is m = 6; the check pins it, since an off-by-one
-- here would silently change ω's order.)

Scalar-group : Group 0ℓ 0ℓ
Scalar-group = +-0-group 6

private
  scalar-order-8 : Group.Carrier Scalar-group ≡ ℤ 8
  scalar-order-8 = Eq.refl

------------------------------------------------------------------------
-- The exact Clifford group: Figure-8 words
--
-- Figure 8 is group-like — C2, C3 and C5 give each gate a left inverse,
-- and a shifted generator inherits its inverse through cong↑ — so its
-- words form a group.

infix 4 _≈ᶠ_
_≈ᶠ_ : {n : ℕ} → Word (Gen n) → Word (Gen n) → Set
_≈ᶠ_ {n} = PB._≈_ (n CRel,_===_)

grouplike-F8 : Grouplike (n CRel,_===_)
grouplike-F8 (gate₁ H-gate)  = [ gate₁ H-gate ]ʷ , PB.axiom (srel F8.c2)
grouplike-F8 (gate₂ CZ-gate) = [ gate₂ CZ-gate ]ʷ , PB.axiom (srel F8.c5)
grouplike-F8 (gate₁ S-gate)  = S' • S' • S' , claim
  where
  S' = [ gate₁ S-gate ]ʷ
  -- (S·(S·S))·S has to be rebracketed into S ^ 4 = S·(S·(S·S)).
  claim : ((S' • S' • S') • S') ≈ᶠ ε
  claim = PB.trans PB.assoc
            (PB.trans (PB.cong PB.refl PB.assoc) (PB.axiom (srel F8.c3)))
grouplike-F8 (gg ↥) with grouplike-F8 gg
... | inv , eq = inv ↑' , lemma-cong↑ (inv • [ gg ]ʷ) ε eq
  where open Symplectic using () renaming (_↑ to _↑')

-- Clifford words modulo the exact congruence.
Exact-group : (n : ℕ) → Group 0ℓ 0ℓ
Exact-group n = Group-Lemmas.•-ε-group (n CRel,_===_) (grouplike-F8 {n})

------------------------------------------------------------------------
-- Powers of the scalar
--
-- ω lives on the first wire, so the scalar layer needs at least one
-- qubit; everything below is stated at width ₁₊ n.

scalar : ℤ 8 → Word (Gen (₁₊ n))
scalar k = ω ^ toℕ k

private

  -- w ^ (1 + k) = w • w ^ k, past the special case k = 0 of _^_.
  pow-suc : (k : ℕ) → (ω {n} ^ (₁₊ k)) ≈ᶠ (ω • (ω ^ k))
  pow-suc zero    = PB.sym PB.right-unit
  pow-suc (₁₊ k) = PB.refl

  pow-+ : (a b : ℕ) → (ω {n} ^ (a Nat.+ b)) ≈ᶠ ((ω ^ a) • (ω ^ b))
  pow-+ zero    b = PB.sym PB.left-unit
  pow-+ (₁₊ a) b =
    PB.trans (pow-suc (a Nat.+ b))
      (PB.trans (PB.cong PB.refl (pow-+ a b))
        (PB.trans (PB.sym PB.assoc) (PB.cong (PB.sym (pow-suc a)) PB.refl)))

  -- ω⁸ = 1 is C1, so every multiple of 8 collapses.
  pow-8 : (q : ℕ) → (ω {n} ^ (q Nat.* 8)) ≈ᶠ ε
  pow-8 zero    = PB.refl
  pow-8 (₁₊ q) =
    PB.trans (pow-+ 8 (q Nat.* 8))
      (PB.trans (PB.cong (PB.axiom (srel F8.c1)) (pow-8 q)) PB.left-unit)

  -- Hence the exponent only matters modulo 8.
  pow-mod : (a : ℕ) → (ω {n} ^ (a % 8)) ≈ᶠ (ω ^ a)
  pow-mod a =
    PB.sym (PB.trans (PB.refl' _ (Eq.cong (ω ^_) (m≡m%n+[m/n]*n a 8)))
             (PB.trans (pow-+ (a % 8) ((a / 8) Nat.* 8))
               (PB.trans (PB.cong PB.refl (pow-8 (a / 8))) PB.right-unit)))

  -- ℤ/8 addition is ℕ addition modulo 8, on the nose.
  toℕ-+ : (j k : ℤ 8) →
          toℕ (Group._∙_ Scalar-group j k) ≡ (toℕ j Nat.+ toℕ k) % 8
  toℕ-+ j k = toℕ-fromℕ< (m%n<n (toℕ j Nat.+ toℕ k) 8)

  -- k ↦ ωᵏ turns ℤ/8 addition into concatenation.
  scalar-+ : (j k : ℤ 8) →
             (scalar {n} (Group._∙_ Scalar-group j k)) ≈ᶠ (scalar j • scalar k)
  scalar-+ j k =
    PB.trans (PB.refl' _ (Eq.cong (ω ^_) (toℕ-+ j k)))
             (PB.trans (pow-mod (toℕ j Nat.+ toℕ k)) (pow-+ (toℕ j) (toℕ k)))

------------------------------------------------------------------------
-- What the extension still takes as input
--
-- These three are Selinger's theorems, not bookkeeping.  Each says
-- something the P4-action alone cannot: `sound` that Figure 8 is not too
-- coarse for it, `scalars` and `ω-faithful` that Figure 8 is exactly
-- right on the scalars.

record ExactData (n : ℕ) : Set where
  field
    -- Soundness: Figure-8-equal words act equally on P4.
    sound      : {w v : Word (Gen (₁₊ n))} → w ≈ᶠ v → w ≈ᶜ v
    -- Completeness on the scalars: a word acting trivially on P4 is ωᵏ.
    scalars    : (w : Word (Gen (₁₊ n))) → w ≈ᶜ ε →
                 ∃ λ (k : ℤ 8) → scalar k ≈ᶠ w
    -- Faithfulness on the scalars: ω has order exactly 8.
    ω-faithful : {j k : ℤ 8} → scalar {n} j ≈ᶠ scalar k → j ≡ k

------------------------------------------------------------------------
-- The extension
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ Clifford n ─→ 1
--
-- incl is k ↦ ωᵏ and proj is the identity on words: the two groups have
-- the same carrier and differ only in how much they identify.

module _ {n : ℕ} (d : ExactData n) where

  open ExactData d

  private
    module MI = MonoidMorphisms (Group.rawMonoid Scalar-group)
                                (Group.rawMonoid (Exact-group (₁₊ n)))
    module MP = MonoidMorphisms (Group.rawMonoid (Exact-group (₁₊ n)))
                                (Group.rawMonoid (Clifford-group (₁₊ n)))

    incl-mon : MI.IsMonoidHomomorphism (scalar {n})
    incl-mon = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = λ { Eq.refl → PB.refl } }
        ; homo              = scalar-+
        }
      ; ε-homo = PB.refl
      }

    -- proj is the identity: concatenation and ε are shared, and the
    -- congruence only has to get coarser, which is `sound`.
    proj-mon : MP.IsMonoidHomomorphism (λ w → w)
    proj-mon = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = sound }
        ; homo              = λ _ _ _ → Eq.refl
        }
      ; ε-homo = λ _ → Eq.refl
      }

  Exact : Extension Scalar-group (Clifford-group (₁₊ n))
  Exact = record
    { total           = Exact-group (₁₊ n)
    ; incl            = scalar
    ; proj            = λ w → w
    ; incl-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                          Scalar-group (Exact-group (₁₊ n)) incl-mon
    ; proj-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                          (Exact-group (₁₊ n)) (Clifford-group (₁₊ n)) proj-mon
    ; incl-injective  = ω-faithful
    ; proj-surjective = λ h → h , ≈ᶜ-refl {w = h}
    ; proj-kills-incl = λ k → cact-ω^ (toℕ k)
    ; ker⊆im-incl     = scalars
    }

------------------------------------------------------------------------
-- Why ω-faithful cannot come from the action
--
-- ω acts trivially on P4 (Selinger.Action.cact-ω), so if ≈ᶜ implied the
-- Figure-8 congruence then ω = ω¹ and ε = ω⁰ would be identified, and
-- ω-faithful would force ₁ ≡ ₀.  The scalar is exactly the datum cact
-- discards; ω-faithful has to come from a faithful model of the exact
-- Clifford group — Selinger's exact normal form (Qubit.Selinger.
-- NormalForm, ExactNF n = NF n × Fin 8, uniqueness still WIP) or
-- matrices over ℤ[1/√2, i].

action-blind : ({w v : Word (Gen (₁₊ n))} → w ≈ᶜ v → w ≈ᶠ v) →
               ¬ ExactData n
action-blind conv d with ExactData.ω-faithful d {₁} {₀} (conv cact-ω)
... | ()
