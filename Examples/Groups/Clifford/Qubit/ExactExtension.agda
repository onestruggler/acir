------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the qubit Clifford group,
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ CMS n ─→ 1,
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
--                words descends to CMS n;
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
open import Word.Properties using (lemma-fʷ-w^n)

import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)

open import ForStdlib.Data.Fin.Mod using (ℤ ; +-0-group)

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.ProjectiveClifford.Qubit.CliffordGroup
  using (_≈ᶜ_ ; CMS-group ; ≈ᶜ-refl)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8 using (ω ; _CRel,_===_ ; srel ; lemma-cong↑)

-- The two sides of the sequence now live over different alphabets:
-- Figure 8 over ExactGate, the P4-action layer over SympGate.  D is the
-- translation, and it is what proj has become — it used to be the
-- identity on words, back when both sides were symplectic circuits.
open import Examples.Groups.Clifford.Qubit.Selinger.Relabel p-2 p-prime
  using (D ; E ; D∘E)

open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Action using (cact-ω ; cact-ω^)

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
_≈ᶠ_ : {n : ℕ} → F8.Circuit n → F8.Circuit n → Set
_≈ᶠ_ {n} = PB._≈_ (n CRel,_===_)

-- Group-likeness now lives with the rule set, as Figure8.grouplike.
grouplike-F8 : Grouplike (n CRel,_===_)
grouplike-F8 = F8.grouplike

-- Clifford words modulo the exact congruence.
Exact-group : (n : ℕ) → Group 0ℓ 0ℓ
Exact-group n = Group-Lemmas.•-ε-group (n CRel,_===_) (grouplike-F8 {n})

------------------------------------------------------------------------
-- Powers of the scalar
--
-- ω is a 0-ary generator, so it exists at every width; the layer is
-- still stated at ₁₊ n, because that is where its symplectic reading
-- (SH)³ has a wire to live on.

scalar : ℤ 8 → F8.Circuit (₁₊ n)
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

-- Each is now stated across the translation D, since a Figure-8 word
-- and its P4-action live over different alphabets.
record ExactData (n : ℕ) : Set where
  field
    -- Soundness: Figure-8-equal words act equally on P4.
    sound      : {w v : F8.Circuit (₁₊ n)} → w ≈ᶠ v → D w ≈ᶜ D v
    -- Completeness on the scalars: a word acting trivially on P4 is ωᵏ.
    scalars    : (w : F8.Circuit (₁₊ n)) → D w ≈ᶜ ε →
                 ∃ λ (k : ℤ 8) → scalar k ≈ᶠ w
    -- Faithfulness on the scalars: ω has order exactly 8.
    ω-faithful : {j k : ℤ 8} → scalar {n} j ≈ᶠ scalar k → j ≡ k

------------------------------------------------------------------------
-- The extension
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ CMS n ─→ 1
--
-- incl is k ↦ ωᵏ and proj is D, the translation from Figure 8's
-- alphabet to the symplectic one.  It used to be the identity on words,
-- when both groups had the same carrier and differed only in how much
-- they identified; now the scalar is a generator on one side and the
-- word (SH)³ on the other, and D is what reconciles them.

module _ {n : ℕ} (d : ExactData n) where

  open ExactData d

  private
    module MI = MonoidMorphisms (Group.rawMonoid Scalar-group)
                                (Group.rawMonoid (Exact-group (₁₊ n)))
    module MP = MonoidMorphisms (Group.rawMonoid (Exact-group (₁₊ n)))
                                (Group.rawMonoid (CMS-group (₁₊ n)))

    incl-mon : MI.IsMonoidHomomorphism (scalar {n})
    incl-mon = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = λ { Eq.refl → PB.refl } }
        ; homo              = scalar-+
        }
      ; ε-homo = PB.refl
      }

    -- D is a monoid map by construction (it is a _ʷ extension, so it
    -- distributes over concatenation and sends ε to ε definitionally),
    -- and the congruence only has to get coarser, which is `sound`.
    proj-mon : MP.IsMonoidHomomorphism D
    proj-mon = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = sound }
        ; homo              = λ _ _ _ → Eq.refl
        }
      ; ε-homo = λ _ → Eq.refl
      }

  Exact : Extension Scalar-group (CMS-group (₁₊ n))
  Exact = record
    { total           = Exact-group (₁₊ n)
    ; incl            = scalar
    ; proj            = D
    ; incl-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                          Scalar-group (Exact-group (₁₊ n)) incl-mon
    ; proj-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                          (Exact-group (₁₊ n)) (CMS-group (₁₊ n)) proj-mon
    ; incl-injective  = ω-faithful
    -- Surjectivity of D: a symplectic circuit is the translation of its
    -- own relabelling, since E never produces a scalar (Relabel.D∘E).
    ; proj-surjective = λ h →
        E h , Eq.subst (_≈ᶜ h) (Eq.sym (D∘E h)) (≈ᶜ-refl {w = h})
    -- D of ωᵏ is (SH)³ to the k, which acts trivially.  D distributes
    -- over powers because it is a _ʷ extension (Word.Properties).
    ; proj-kills-incl = λ k →
        Eq.subst (_≈ᶜ ε) (Eq.sym (lemma-fʷ-w^n (toℕ k))) (cact-ω^ (toℕ k))
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

action-blind : ({w v : F8.Circuit (₁₊ n)} → D w ≈ᶜ D v → w ≈ᶠ v) →
               ¬ ExactData n
action-blind conv d with ExactData.ω-faithful d {₁} {₀} (conv cact-ω)
... | ()
