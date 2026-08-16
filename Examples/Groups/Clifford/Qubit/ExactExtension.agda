------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the qubit Clifford group,
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ VSp n ─→ 1,
--
-- as an ordinary extension.
--
-- The quotient is taken in the STRUCTURAL model VSp n (pairs (S , φ) of
-- a symplectic map and a phase function) rather than in the syntactic
-- one CMS n (words modulo the P4-action).  The two are isomorphic —
-- Qubit.Iso2.CMS≅VSp, by the denotation ⟦_⟧ᵛ — so the action-stated
-- results this file rests on carry across by ⟦_⟧ᵛ: ⟦⟧ᵛ-cong turns
-- soundness into well-definedness of proj and ⟦⟧ᵛ-injective turns a
-- trivial VSp element back into a word acting trivially, which is what
-- `scalars` expects.
--
-- The total group is the group Selinger's Figure 8 presents: Clifford
-- words modulo the *exact* congruence, which unlike ≈ᶜ still sees the
-- global scalar.  So this mirrors layer 1 (Qubit.CliffordGroup), where
-- the total group is Clifford words modulo the P4-action — and, as
-- there, the extension record is assembled by hand rather than through a
-- product construction.
--
-- Taking the total group this way makes proj a *denotation of words*,
-- which is what one wants downstream, and makes the residual obligations
-- recognisable as Selinger's theorems rather than as bookkeeping.  There
-- were three; two are now discharged:
--
--   sound      — Figure 8 is sound for the P4-action, so the denotation
--                descends to the quotient.  PROVED, in
--                ProjectiveClifford.Qubit.Selinger.Soundness.sound, and
--                imported below rather than assumed;
--   scalars    — a word acting trivially on P4 is a power of ω
--                (completeness, restricted to the scalars).  PROVED
--                below, once the projective presentation became
--                unconditional: it is Selinger.Presentation.complete-ms
--                (trivial action ⇒ trivial mod scalars) composed with
--                Selinger.ScalarKernel.kernel-ε (trivial mod scalars ⇒ a
--                power of ω), with ED to pay for the translation;
--   ω-faithful — ω has order exactly 8, i.e. the scalars are not
--                collapsed by Figure 8.
--
-- So ExactData has shrunk to the last one.  Everything else — the group
-- structure of the Figure-8 words, that k ↦ ωᵏ is a homomorphism
-- ℤ/8 → Exact n, surjectivity of proj, and that proj kills the scalars —
-- is proved here.
--
-- What is left, and why it is a different KIND of statement.  ω-faithful
-- is the one the P4-action cannot help with at all: action-blind at the
-- end shows that if ≈ᶜ implied the Figure-8 congruence then ω would
-- equal ε.  Nor can any abelian invariant supply it — a homomorphism to
-- ℤ/8 with ω ↦ 1 would need 3(s+h) = 1 on the abelianisation, and C2 and
-- C3 force 2h = 4s = 0, so s+h is even and 3(s+h) never odd.  And the
-- coset route is circular: Reidemeister–Schreier's word-component
-- well-definedness asks for faithfulness of the left embedding, which at
-- this layer IS ω-faithful.  It has to come from a faithful MODEL of the
-- exact Clifford group — matrices over ℤ[1/√2, i], where ω is e^{iπ/4}
-- and has order 8 by computation.
--
-- That model is now built: Qubit.Model.Faithful reads an n-qubit
-- circuit as a 2ⁿ × 2ⁿ matrix over ℤ/17ℤ, where i = 4, √2 = 11 and
-- ω = 2, and 2 has order exactly 8.  So ExactData n is a THEOREM at
-- every width (Model.Faithful.exact-data), and the record below is a
-- shape the extension is built with rather than an assumption.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.ExactExtension where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
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
  using (_≈ᶜ_)

-- Soundness of Figure 8 for the P4 action: every axiom, plus the
-- structural rules, checked against `cact`.  This used to be an
-- assumption (ExactData's `sound` field); it is a theorem.
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Soundness
  using (sound)

-- The structural model of the projective Clifford group, and the
-- isomorphism CMS n ≅ VSp n that lets the action-stated results
-- discharge obligations phrased in it.
open import Examples.Groups.ProjectiveClifford.Qubit.Semantics.VSp
  using (Cliff ; _≈ᵛ_ ; εᵛ ; ⟦_⟧ᵛ ; VSp-group)
open import Examples.Groups.ProjectiveClifford.Qubit.Iso2
  using (≈ᵛ-refl ; ⟦⟧ᵛ-cong ; ⟦⟧ᵛ-injective ; ⟦⟧ᵛ-surjective)

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
  using (D ; E ; D∘E ; ex→sym ; E-↑)

-- The scalar kernel of the quotient map, and completeness of the
-- mod-scalar rule set: between them they say that a word trivial in the
-- projective group is a power of ω.
import Examples.Groups.Clifford.Qubit.Selinger.ScalarKernel p-2 p-prime as SK
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Presentation
  using (complete-ms)

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
-- ω is a 0-ary generator, so it exists at every width — and so, since
-- Figure 8 acquired its own gate set, does the whole layer.  Width 0 is
-- degenerate but true: Figure 8 there is ⟨ ω ∣ ω⁸ ⟩ ≅ ℤ/8, the quotient
-- CMS 0 is trivial (SympGate has no 0-ary gate, so Gen 0 is empty), and
-- the sequence is 1 → ℤ/8 → ℤ/8 → 1 → 1.  The one place the width still
-- shows is proj: its symplectic reading of ω is (SH)³ where there is a
-- wire for it and ε at width 0 (Relabel.ex→sym), which is the case split
-- cact-Dω^ below makes.

scalar : ℤ 8 → F8.Circuit n
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

  -- Repeating ε acts as the identity: cact of a concatenation composes
  -- and cact ε is the identity, so the whole power collapses.
  cact-ε^ : (k : ℕ) → ((ε {X = Gen n}) ^ k) ≈ᶜ ε
  cact-ε^ ₀        x = Eq.refl
  cact-ε^ (₁₊ ₀)   x = Eq.refl
  cact-ε^ (₂₊ k)   x = cact-ε^ (₁₊ k) x

  -- The symplectic reading of a scalar acts trivially at every width.
  -- ex→sym is defined by cases on the width, so this has to be too: at
  -- ₁₊ n it is Selinger.Action's cact-ω^, at 0 there is no (SH)³ and D ω
  -- is ε.
  cact-Dω^ : (k : ℕ) → ((D (ω {n})) ^ k) ≈ᶜ ε
  cact-Dω^ {₀}    k = cact-ε^ k
  cact-Dω^ {₁₊ _} k = cact-ω^ k

------------------------------------------------------------------------
-- E ∘ D is the identity modulo scalars
--
-- D reads a Figure-8 word symplectically and E reads it back, but the
-- two are not inverse: D sends the scalar to the word (SH)³ where there
-- is a wire for it and to ε at width 0.  So a letter returns either as
-- itself — the gates on the nose, ω at positive width by C4 — or as ε,
-- and every discrepancy is a power of ω.  The shift case carries its
-- discrepancy up a wire unchanged (ω^↑≈ω^), and concatenation adds the
-- two exponents, which is where centrality is spent.

private

  ED-gen : (x : F8.Gen n) → ∃ λ j → E (D [ x ]ʷ) ≈ᶠ ([ x ]ʷ • (ω ^ j))
  -- At width 0 there is no (SH)³ to come back as, so ω is lost entirely
  -- and the discrepancy is ω⁻¹ = ω⁷ — which is C1 read backwards.
  ED-gen {₀}    (F8.gate₀ F8.ω-gate) = 7 , PB.sym (PB.axiom (srel F8.c1))
  ED-gen {₁₊ _} (F8.gate₀ F8.ω-gate) =
    0 , PB.trans (PB.axiom (srel F8.c4)) (PB.sym PB.right-unit)
  ED-gen (F8.gate₁ F8.H-gate)  = 0 , PB.sym PB.right-unit
  ED-gen (F8.gate₁ F8.S-gate)  = 0 , PB.sym PB.right-unit
  ED-gen (F8.gate₂ F8.CZ-gate) = 0 , PB.sym PB.right-unit
  ED-gen (y F8.↥) with ED-gen y
  ... | j , e = j ,
    Eq.subst (λ z → z ≈ᶠ ([ y F8.↥ ]ʷ • (ω ^ j)))
      (Eq.sym (E-↑ (ex→sym y)))
      (PB.trans (lemma-cong↑ _ _ e) (PB.cong PB.refl (F8.ω^↑≈ω^ j)))

  ED : (w : F8.Circuit n) → ∃ λ j → E (D w) ≈ᶠ (w • (ω ^ j))
  ED [ x ]ʷ = ED-gen x
  ED ε      = 0 , PB.sym PB.right-unit
  ED (u • v) with ED u | ED v
  ... | j , e | k , f = j Nat.+ k ,
    PB.trans (PB.cong e f)
      (PB.trans PB.assoc
        (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
          (PB.trans (PB.cong PB.refl (PB.cong (F8.ω^-central j v) PB.refl))
            (PB.trans (PB.cong PB.refl PB.assoc)
              (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym (pow-+ j k))))
                        (PB.sym PB.assoc))))))

------------------------------------------------------------------------
-- Completeness on the scalars
--
-- A word acting trivially on P4 is a power of ω.  This used to be an
-- assumption (ExactData's `scalars` field); it is now a theorem, and the
-- three pieces it composes were each the last one standing at some
-- point:
--
--   complete-ms   trivial action ⇒ trivial MOD SCALARS.  This is
--                 Selinger.Presentation.complete-ms, i.e. the projective
--                 presentation theorem read through Selinger.Iso;
--   kernel-ε      trivial mod scalars ⇒ a power of ω, on the translated
--                 word (Selinger.ScalarKernel);
--   ED            and the translation costs only another power of ω.
--
-- The exponent lands in ℕ, so the last step is the reduction mod 8 that
-- ℤ/8 wants: k + 7j, since ω⁻¹ = ω⁷.

-- The two exponents are taken as ARGUMENTS rather than `with`-abstracted.
-- The hypothesis is an equality of P4 actions, and generalising a goal
-- over a term of that type invites Agda to normalise cact on a symbolic
-- word — which is where this layer's elaboration blows up.  Naming them
-- keeps the arithmetic first-order and the check cheap.
private
  from-exponents :
    (w : F8.Circuit n) →
    (∃ λ k → E (D w) ≈ᶠ (ω ^ k)) →
    (∃ λ j → E (D w) ≈ᶠ (w • (ω ^ j))) →
    ∃ λ (κ : ℤ 8) → scalar κ ≈ᶠ w
  from-exponents {n} w (k , e) (j , f) = fromℕ< (m%n<n m 8) , claim
    where
    m : ℕ
    m = k Nat.+ 7 Nat.* j

    -- w, with its scalar tail divided out.
    w≈ : (ω ^ m) ≈ᶠ w
    w≈ =
      PB.trans (pow-+ k (7 Nat.* j))
        (PB.trans (PB.cong (PB.trans (PB.sym e) f) PB.refl)
          (PB.trans PB.assoc
            (PB.trans (PB.cong PB.refl (SK.Ω-inv n j)) PB.right-unit)))

    claim : scalar (fromℕ< (m%n<n m 8)) ≈ᶠ w
    claim =
      PB.trans (PB.refl' _ (Eq.cong (ω ^_) (toℕ-fromℕ< (m%n<n m 8))))
               (PB.trans (pow-mod m) w≈)

scalars : (w : F8.Circuit n) → D w ≈ᶜ ε → ∃ λ (k : ℤ 8) → scalar k ≈ᶠ w
scalars {n} w h =
  from-exponents w (SK.kernel-ε (complete-ms n h)) (ED w)

------------------------------------------------------------------------
-- What the extension still takes as input
--
-- One thing: that Figure 8 is FAITHFUL on the scalars.  It is Selinger's
-- theorem, not bookkeeping, and the P4-action cannot see it — the scalar
-- is precisely what that action discards (action-blind, at the end of
-- this file).  Its two companions have both become theorems: `sound` is
-- Selinger.Soundness.sound, imported above, and `scalars` is proved
-- just above.
--
-- It is a theorem too, at every width: Qubit.Model.Faithful.exact-data.
-- The record is kept because the extension and its presentation are
-- stated with it, and because it names what the model is FOR — but
-- nothing assumes it any more, so `Exact` and everything downstream can
-- be instantiated outright.

record ExactData (n : ℕ) : Set where
  field
    -- Faithfulness on the scalars: ω has order exactly 8.
    ω-faithful : {j k : ℤ 8} → scalar {n} j ≈ᶠ scalar k → j ≡ k

------------------------------------------------------------------------
-- The sequence, with no input at all
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ VSp n ─→ 1
--
-- incl is k ↦ ωᵏ and proj is ⟦ D _ ⟧ᵛ: first D, the translation from
-- Figure 8's alphabet to the symplectic one, then the VSp denotation of
-- the resulting circuit.  proj used to be the identity on words, when
-- the two groups had the same carrier and differed only in how much
-- they identified; the scalar being a generator on one side and the
-- word (SH)³ on the other is what D reconciles, and reading the result
-- structurally rather than syntactically is what ⟦_⟧ᵛ does.
--
-- Six of the Extension record's eight fields are proved here outright.
-- They are stated separately, and named, because ExactData is now
-- exactly the other two: the extension is complete apart from EXACTNESS
-- AT THE ENDS, and each end is one of Selinger's theorems.

-- The projection: translate, then denote.
projᵛ : F8.Circuit n → Cliff n
projᵛ w = ⟦ D w ⟧ᵛ

private
  module MI (n : ℕ) = MonoidMorphisms (Group.rawMonoid Scalar-group)
                                      (Group.rawMonoid (Exact-group n))
  module MP (n : ℕ) = MonoidMorphisms (Group.rawMonoid (Exact-group n))
                                      (Group.rawMonoid (VSp-group n))

  incl-mon : MI.IsMonoidHomomorphism n (scalar {n})
  incl-mon = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ { Eq.refl → PB.refl } }
      ; homo              = scalar-+
      }
    ; ε-homo = PB.refl
    }

  -- Both halves are monoid maps by construction: D is a _ʷ extension,
  -- so it distributes over concatenation and sends ε to ε
  -- definitionally, and so does ⟦_⟧ᵛ, whose clauses for _•_ and ε are
  -- _∙ᵛ_ and εᵛ.  Well-definedness is Soundness.sound read through
  -- ⟦⟧ᵛ-cong: the congruence only has to get coarser.
  proj-mon : MP.IsMonoidHomomorphism n (projᵛ {n})
  proj-mon {n} = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = λ {w} {v} w≈v → ⟦⟧ᵛ-cong {n} {D w} {D v} (sound w≈v) }
      ; homo              = λ w v → ≈ᵛ-refl (projᵛ (w • v))
      }
    ; ε-homo = ≈ᵛ-refl (εᵛ {n})
    }

-- k ↦ ωᵏ is a group homomorphism ℤ/8 → Exact n.
incl-homo : GroupMorphisms.IsGroupHomomorphism
              (Group.rawGroup Scalar-group)
              (Group.rawGroup (Exact-group n)) scalar
incl-homo {n} = isMonoidHomomorphism⇒isGroupHomomorphism
                  Scalar-group (Exact-group n) incl-mon

-- So is ⟦ D _ ⟧ᵛ : Exact n → VSp n.
proj-homo : GroupMorphisms.IsGroupHomomorphism
              (Group.rawGroup (Exact-group n))
              (Group.rawGroup (VSp-group n)) projᵛ
proj-homo {n} = isMonoidHomomorphism⇒isGroupHomomorphism
                  (Exact-group n) (VSp-group n) proj-mon

-- Surjectivity: every VSp element is denoted by some symplectic circuit
-- (Iso2.⟦⟧ᵛ-surjective), and a symplectic circuit is the translation of
-- its own relabelling, since E never produces a scalar (Relabel.D∘E).
proj-onto : (X : Cliff n) → ∃ λ (w : F8.Circuit n) → projᵛ w ≈ᵛ X
proj-onto X =
  E (proj₁ (⟦⟧ᵛ-surjective X))
  , Eq.subst (λ □ → ⟦ □ ⟧ᵛ ≈ᵛ X)
             (Eq.sym (D∘E (proj₁ (⟦⟧ᵛ-surjective X))))
             (proj₂ (⟦⟧ᵛ-surjective X))

-- D of ωᵏ is (SH)³ to the k, which acts trivially — hence denotes εᵛ, by
-- ⟦⟧ᵛ-cong.  D distributes over powers because it is a _ʷ extension
-- (Word.Properties).
proj-kills : (k : ℤ 8) → projᵛ (scalar {n} k) ≈ᵛ εᵛ
proj-kills {n} k =
  ⟦⟧ᵛ-cong {n} {D (scalar k)} {ε}
    (Eq.subst (_≈ᶜ ε) (Eq.sym (lemma-fʷ-w^n (toℕ k))) (cact-Dω^ (toℕ k)))

------------------------------------------------------------------------
-- The extension
--
-- What ExactData contributes is precisely exactness at the two ends —
-- incl-injective is ω-faithful verbatim, and ker⊆im-incl is `scalars`
-- with a VSp element turned back into a trivial action by
-- ⟦⟧ᵛ-injective.  Nothing else in the record depends on it, so this is
-- the whole of the assumption and there is no bookkeeping left inside
-- it to remove: what remains is to prove the two.

module _ {n : ℕ} (d : ExactData n) where

  open ExactData d

  Exact : Extension Scalar-group (VSp-group n)
  Exact = record
    { total           = Exact-group n
    ; incl            = scalar
    ; proj            = projᵛ
    ; incl-homo       = incl-homo
    ; proj-homo       = proj-homo
    ; incl-injective  = ω-faithful
    ; proj-surjective = proj-onto
    ; proj-kills-incl = proj-kills
    ; ker⊆im-incl     = λ w h → scalars w (⟦⟧ᵛ-injective {n} {D w} {ε} h)
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
-- matrices over ℤ[1/√2, i].  Qubit.Model.Faithful takes the second
-- route, over ℤ/17ℤ, at every width.

-- Stated at ₁₊ n, the widths where ω has a symplectic reading to act
-- by: at width 0 D ω is ε, which is what makes ExactData 0 consistent
-- with the action being blind there.
action-blind : ({w v : F8.Circuit (₁₊ n)} → D w ≈ᶜ D v → w ≈ᶠ v) →
               ¬ ExactData (₁₊ n)
action-blind conv d with ExactData.ω-faithful d {₁} {₀} (conv cact-ω)
... | ()
