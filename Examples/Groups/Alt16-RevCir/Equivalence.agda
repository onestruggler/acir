------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules (1)–(7) present 𝔄₁₆ on four wires
--
-- The second Reidemeister–Schreier step of this folder.  Its two
-- relation sets are over the same gates: Syntactics' relation — Lafont's
-- relations read on the cycles Ω i, and one rule per gate naming its
-- word in the cycles — and the rules r1, …, r7 of Theory.  The
-- translations are the identity, so the step is that each relation
-- set's rules follow from the other's:
--
-- * t⇒s (Theory): the rules r1, …, r7 hold for functions on states,
--   for which Syntactics' relation is complete.
--
-- * s⇒t, here: every rule of Syntactics is derived from r1, …, r7.
--   The relations between the cycles are Four.Relations' (orderᵀ, …):
--   derivations on four wires found by search and replayed by the
--   engine, from rule (7) and three-wire steps, which rest on the
--   completeness of the rules on three wires (ThreeWire).  The gate
--   rules follow from them: Four.Relations has each gate on its own
--   wires as the circuit of some word in the cycles (gate-Xᵀ, …); that
--   word and Translation's have the same permutation, so they are equal
--   by Lafont's relations — his completeness — and g carries the
--   equation to the circuits, the relations between the cycles being
--   derived (to-f).
--
-- So the two congruences coincide on four wires (rules≅relations: the
-- identity is a group isomorphism), the step from Lafont's presentation
-- holds for the rules as it does for Syntactics' relation
-- (Theorem-Rules-iso-Cycles, with the same translations f and g), and
-- the circuits modulo r1, …, r7 present 𝔄₁₆ (presentationᵀ), soundly
-- and completely for the functions on states, with the canonical
-- circuits of NormalForm as unique normal forms.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Equivalence where

open import Algebra.Bundles using (Group)
import Algebra.Morphism.Construct.Composition as Compose
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
  renaming (T to True)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
import Presentation.Morphism as Morphism
import Presentation.MorphismId as MorphismId

open import Examples.Groups.Alternating.Presentation as LA using ()
open import Examples.Groups.Alternating.Semantics using (Alt-group)
import Examples.Groups.Alternating.Syntactics as L

open import Examples.Groups.Alt16-RevCir.Bridge using (f-sem ; g-sem)
import Examples.Groups.Alt16-RevCir.Iso as I
open import Examples.Groups.Alt16-RevCir.Lemmas using (module FromCycles)
import Examples.Groups.Alt16-RevCir.NormalForm as N
open import Examples.Groups.Alt16-RevCir.NormalForm using (NF ; canon ; nf)
open import Examples.Groups.Alt16-RevCir.Numbering using (enc ; dec)
import Examples.Groups.Alt16-RevCir.Presentation as S
open import Examples.Groups.Alt16-RevCir.Semantics using (⟦_⟧ ; _≐_)
open import Examples.Groups.Alt16-RevCir.Syntactics
open import Examples.Groups.Alt16-RevCir.Theory
open import Examples.Groups.Alt16-RevCir.Translation using (f ; g)
import Examples.Groups.Alt16-RevCir.Four.Relations as R

open GroupMorphisms using (IsGroupIsomorphism)

private
  variable
    n : ℕ

  module LP = _IsPresentationOf_ (LA.presentation {16})

  -- Lafont's congruence.
  infix 4 _≈ᴸ_
  _≈ᴸ_ : L.Circuit 16 → L.Circuit 16 → Set
  _≈ᴸ_ = PB._≈_ (L._VRel,_===_ 16)

  ∧-intro : {a b : Bool} → True a → True b → True (a ∧ b)
  ∧-intro {true}  _ y = y
  ∧-intro {false} ()

------------------------------------------------------------------------
-- Lafont's relations, read through g, from the rules

-- Each instance of his relation is one of the relations between the
-- cycles, which Four.Relations derives.
open FromCycles (T._VRel,_===_ 4)
  (λ i p → R.orderᵀ i (≤⇒≤ᵇ p))
  (λ i p → R.nearᵀ i (≤⇒≤ᵇ p))
  (λ i p → R.farᵀ i (≤⇒≤ᵇ p))
  (λ i j p q → R.apartᵀ i j (∧-intro (≤⇒≤ᵇ q) (≤⇒≤ᵇ p)))
  using () renaming (lemma-g-rel to lemma-g-relᵀ)

g-well-definedᵀ : ∀ {u t} → L._VRel,_===_ 16 u t →
                  4 T.⊢ (g ʷ) u ≈ (g ʷ) t
g-well-definedᵀ = lemma-g-relᵀ 0 refl

open Morphism (L._VRel,_===_ 16) (T._VRel,_===_ 4)
  using (module Star-Congruence)
open Star-Congruence g g-well-definedᵀ
  using () renaming (fʷ-cong to gʷ-congᵀ)

------------------------------------------------------------------------
-- The gates, read through f and back through g

-- A circuit that is the circuit of some word in the cycles is the
-- circuit of its own word: the two words have the same permutation,
-- that of the circuit's function on states, so they are equal by
-- Lafont's relations, and g carries the equation back.
to-f : (c : Circuit 4) (u : L.Circuit 16) → 4 T.⊢ c ≈ (g ʷ) u →
       4 T.⊢ c ≈ (g ʷ) ((f ʷ) c)
to-f c u e =
  PB.trans e (gʷ-congᵀ (LA.completeness {16} {u} {(f ʷ) c} λ i →
    Eq.trans (Eq.sym (g-sem u i))
    (Eq.trans (Eq.cong dec (Eq.sym (T-sound e (enc i))))
              (Eq.sym (f-sem c i)))))

private
  -- The gates further up, between swaps, as circuits of words in the
  -- cycles.
  uX₁ uX₂ uX₃ uCX₁ uCX₂ uCCX₁ : L.Circuit 16
  uX₁   = R.wEx₀ • R.wX • R.wEx₀
  uX₂   = R.wEx₁ • uX₁ • R.wEx₁
  uX₃   = R.wEx₂ • uX₂ • R.wEx₂
  uCX₁  = (R.wEx₀ • R.wEx₁) • R.wCX • (R.wEx₁ • R.wEx₀)
  uCX₂  = (R.wEx₁ • R.wEx₂) • uCX₁ • (R.wEx₂ • R.wEx₁)
  uCCX₁ = (R.wEx₀ • R.wEx₁ • R.wEx₂) • R.wCCX •
          ((R.wEx₂ • R.wEx₁) • R.wEx₀)

  x₁ : 4 T.⊢ X₁ ≈ (g ʷ) uX₁
  x₁ = PB.trans X↑≈ (PB.cong R.gate-Ex₀ᵀ (PB.cong R.gate-Xᵀ R.gate-Ex₀ᵀ))

  x₂ : 4 T.⊢ X₂ ≈ (g ʷ) uX₂
  x₂ = PB.trans (T.lemma-cong↑ _ _ X↑≈)
                (PB.cong R.gate-Ex₁ᵀ (PB.cong x₁ R.gate-Ex₁ᵀ))

  x₃ : 4 T.⊢ X₃ ≈ (g ʷ) uX₃
  x₃ = PB.trans (T.lemma-cong↑ _ _ (T.lemma-cong↑ _ _ X↑≈))
                (PB.cong R.gate-Ex₂ᵀ (PB.cong x₂ R.gate-Ex₂ᵀ))

  cx₁ : 4 T.⊢ CX ↑ ≈ (g ʷ) uCX₁
  cx₁ = PB.trans CX↑≈
    (PB.cong (PB.cong R.gate-Ex₀ᵀ R.gate-Ex₁ᵀ)
             (PB.cong R.gate-CXᵀ (PB.cong R.gate-Ex₁ᵀ R.gate-Ex₀ᵀ)))

  cx₂ : 4 T.⊢ CX ↑ ↑ ≈ (g ʷ) uCX₂
  cx₂ = PB.trans (T.lemma-cong↑ _ _ CX↑≈)
    (PB.cong (PB.cong R.gate-Ex₁ᵀ R.gate-Ex₂ᵀ)
             (PB.cong cx₁ (PB.cong R.gate-Ex₂ᵀ R.gate-Ex₁ᵀ)))

  ccx₁ : 4 T.⊢ CCX ↑ ≈ (g ʷ) uCCX₁
  ccx₁ = PB.trans CCX↑≈
    (PB.cong (PB.cong R.gate-Ex₀ᵀ (PB.cong R.gate-Ex₁ᵀ R.gate-Ex₂ᵀ))
             (PB.cong R.gate-CCXᵀ
                      (PB.cong (PB.cong R.gate-Ex₂ᵀ R.gate-Ex₁ᵀ)
                               R.gate-Ex₀ᵀ)))

-- Each gate is the circuit of its word in the cycles.
lemma-g-fᵀ : (x : Gen 4) → 4 T.⊢ [ x ]ʷ ≈ (g ʷ) (f x)
lemma-g-fᵀ X-gen             = to-f _ R.wX R.gate-Xᵀ
lemma-g-fᵀ CX-gen            = to-f _ R.wCX R.gate-CXᵀ
lemma-g-fᵀ Ex-gen            = to-f _ R.wEx₀ R.gate-Ex₀ᵀ
lemma-g-fᵀ CCX-gen           = to-f _ R.wCCX R.gate-CCXᵀ
lemma-g-fᵀ (X-gen ↥)         = to-f _ uX₁ x₁
lemma-g-fᵀ (CX-gen ↥)        = to-f _ uCX₁ cx₁
lemma-g-fᵀ (Ex-gen ↥)        = to-f _ R.wEx₁ R.gate-Ex₁ᵀ
lemma-g-fᵀ (CCX-gen ↥)       = to-f _ uCCX₁ ccx₁
lemma-g-fᵀ (X-gen ↥ ↥)       = to-f _ uX₂ x₂
lemma-g-fᵀ (CX-gen ↥ ↥)      = to-f _ uCX₂ cx₂
lemma-g-fᵀ (Ex-gen ↥ ↥)      = to-f _ R.wEx₂ R.gate-Ex₂ᵀ
lemma-g-fᵀ (X-gen ↥ ↥ ↥)     = to-f _ uX₃ x₃
lemma-g-fᵀ (gate₀ ())
lemma-g-fᵀ (gate₀ () ↥)
lemma-g-fᵀ (gate₀ () ↥ ↥)
lemma-g-fᵀ (gate₀ () ↥ ↥ ↥)
lemma-g-fᵀ (gate₀ () ↥ ↥ ↥ ↥)

------------------------------------------------------------------------
-- From the translated relations to the rules

private
  s⇒t-rule : {w v : Circuit n} → n SRel, w === v → n T.⊢ w ≈ v
  s⇒t-rule (order i p)     = R.orderᵀ i (≤⇒≤ᵇ p)
  s⇒t-rule (near i p)      = R.nearᵀ i (≤⇒≤ᵇ p)
  s⇒t-rule (far i p)       = R.farᵀ i (≤⇒≤ᵇ p)
  s⇒t-rule (apart i j p q) = R.apartᵀ i j (∧-intro (≤⇒≤ᵇ q) (≤⇒≤ᵇ p))
  s⇒t-rule gate-X          = lemma-g-fᵀ X-gen
  s⇒t-rule gate-CX         = lemma-g-fᵀ CX-gen
  s⇒t-rule gate-CCX        = lemma-g-fᵀ CCX-gen
  s⇒t-rule gate-Ex₀        = lemma-g-fᵀ Ex-gen
  s⇒t-rule gate-Ex₁        = lemma-g-fᵀ (Ex-gen ↥)
  s⇒t-rule gate-Ex₂        = lemma-g-fᵀ (Ex-gen ↥ ↥)

-- Each rule of Syntactics' relation is a consequence of r1, …, r7: its
-- own rules as above; the laws of the swap and the structural rules
-- are the same on both sides.
s⇒t-ax : {w v : Circuit n} → n VRel, w === v → n T.⊢ w ≈ v
s⇒t-ax (srel (srel r)) = s⇒t-rule r
s⇒t-ax (srel (σrel s)) = PB.axiom (T.srel (T.σrel s))
s⇒t-ax (cong↑ a)       = T.lemma-cong↑ _ _ (s⇒t-ax a)
s⇒t-ax (comm₁ h x)     = PB.axiom (T.comm₁ h x)
s⇒t-ax (comm₂ h x)     = PB.axiom (T.comm₂ h x)
s⇒t-ax (comm₃ h x)     = PB.axiom (T.comm₃ h x)
s⇒t-ax (ω↑=ω ())

s⇒t : {w v : Circuit n} → n ⊢ w ≈ v → n T.⊢ w ≈ v
s⇒t PB.refl         = PB.refl
s⇒t (PB.sym e)      = PB.sym (s⇒t e)
s⇒t (PB.trans e e′) = PB.trans (s⇒t e) (s⇒t e′)
s⇒t (PB.cong e e′)  = PB.cong (s⇒t e) (s⇒t e′)
s⇒t PB.assoc        = PB.assoc
s⇒t PB.left-unit    = PB.left-unit
s⇒t PB.right-unit   = PB.right-unit
s⇒t (PB.axiom a)    = s⇒t-ax a

-- And back, on four wires (Theory).
t⇒s-ax : {w v : Circuit 4} → 4 T.VRel, w === v → 4 ⊢ w ≈ v
t⇒s-ax a = t⇒s (PB.axiom a)

------------------------------------------------------------------------
-- The two relation sets generate the same congruence

-- Every gate has an inverse by the rules, as it has by Syntactics'.
grouplikeᵀ : Grouplike (T._VRel,_===_ 4)
grouplikeᵀ x =
  proj₁ (I.Theorem.grouplike x) , s⇒t (proj₂ (I.Theorem.grouplike x))

private
  module Gˢ = Group-Lemmas (4 VRel,_===_) I.Theorem.grouplike
  module Gᵀ = Group-Lemmas (T._VRel,_===_ 4) grouplikeᵀ

-- The identity is an isomorphism of the two word groups.
rules≅relations :
  IsGroupIsomorphism (Group.rawGroup Gᵀ.•-ε-group)
                     (Group.rawGroup Gˢ.•-ε-group) id
rules≅relations =
  StarGroupIsomorphism.isGroupIsomorphism t⇒s-ax s⇒t-ax
  where
  open MorphismId (T._VRel,_===_ 4) (4 VRel,_===_) using (module GroupMorphs)
  open GroupMorphs grouplikeᵀ I.Theorem.grouplike

------------------------------------------------------------------------
-- The step from Lafont's presentation, for the rules

module Theoremᵀ where

  -- f : circuits → Lafont's words.  The rules hold for functions on
  -- states, so the words of their two sides have the same permutation.
  f-well-definedᵀ : ∀ {w v} → 4 T.VRel, w === v → (f ʷ) w ≈ᴸ (f ʷ) v
  f-well-definedᵀ {w} {v} r =
    LA.completeness {16} {(f ʷ) w} {(f ʷ) v} λ i →
      Eq.trans (f-sem w i)
      (Eq.trans (Eq.cong dec (T-sound (PB.axiom r) (enc i)))
                (Eq.sym (f-sem v i)))

  -- A cycle and the word of its circuit: as for Syntactics' relation.
  f-left-inv-gen : (y : L.Gen 16) → [ y ]ʷ ≈ᴸ (f ʷ) (g y)
  f-left-inv-gen = I.Theorem.f-left-inv-gen

  g-left-inv-genᵀ : (x : Gen 4) → 4 T.⊢ [ x ]ʷ ≈ (g ʷ) (f x)
  g-left-inv-genᵀ = lemma-g-fᵀ

  open Morphism (T._VRel,_===_ 4) (L._VRel,_===_ 16)
    using (module GroupMorphism)
  open GroupMorphism grouplikeᵀ LP.gl using (module StarGroupIsomorphism)

  Theorem-Rules-iso-Cycles :
    IsGroupIsomorphism (Group.rawGroup Gᵀ.•-ε-group)
                       (Group.rawGroup LP.GL.•-ε-group) (f ʷ)
  Theorem-Rules-iso-Cycles =
    StarGroupIsomorphism.isGroupIsomorphism
      f g f-well-definedᵀ f-left-inv-gen g-well-definedᵀ g-left-inv-genᵀ

------------------------------------------------------------------------
-- The presentation

-- The circuits modulo r1, …, r7 present 𝔄₁₆, a circuit read as the
-- even permutation of its word in the cycles.
presentationᵀ : (T._VRel,_===_ 4) IsPresentationOf (Alt-group 16)
presentationᵀ = record
  { gl  = grouplikeᵀ
  ; ⟦_⟧ = S.⟦_⟧ᴬ
  ; iso = Compose.isGroupIsomorphism
            {G₁ = Group.rawGroup Gᵀ.•-ε-group}
            {G₂ = Group.rawGroup LP.GL.•-ε-group}
            {G₃ = Group.rawGroup (Alt-group 16)}
            (λ {x} {y} {z} → Group.trans (Alt-group 16) {x} {y} {z})
            {f = f ʷ} {g = LP.⟦_⟧}
            Theoremᵀ.Theorem-Rules-iso-Cycles LP.iso
  }

-- Two circuits are equal by the rules exactly when they are the same
-- function on states.
soundᵀ : {w v : Circuit 4} → 4 T.⊢ w ≈ v → ⟦ w ⟧ ≐ ⟦ v ⟧
soundᵀ = T-sound

completeᵀ : {w v : Circuit 4} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 4 T.⊢ w ≈ v
completeᵀ e = s⇒t (S.complete e)

------------------------------------------------------------------------
-- The normal form

-- Every circuit is equal by the rules to its canonical circuit, the
-- translation of Lafont's canonical form (NormalForm),
normal-formᵀ : (w : Circuit 4) → 4 T.⊢ canon (nf w) ≈ w
normal-formᵀ w = s⇒t (N.normal-form w)

-- and circuits equal by the rules have the same normal form.
nf-congᵀ : {w v : Circuit 4} → 4 T.⊢ w ≈ v → nf w ≡ nf v
nf-congᵀ e = N.nf-cong (t⇒s e)
