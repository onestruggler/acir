------------------------------------------------------------------------
-- Presentations of groups
--
-- Swap networks in real-Clifford+CH circuits: two networks with the
-- same permutation are equal
--
-- The swap Ex satisfies the relations of the circuit presentation of
-- the symmetric group: it is an involution (Figure 1 (g)), it satisfies
-- the braid relation — the swap rules (f1)–(f4) for the swap itself,
-- which is `TopWeakening.nat` at three wires — and the structural rules
-- of the two presentations are the same.  So the circuits of that
-- presentation map into QC, σ ↦ Ex (`net`), and the completeness of
-- the presentation (`Symmetric.Presentation`) carries over: **two swap
-- networks denoting the same permutation are equal in QC**
-- (`perm-≈`).
--
-- This is the topology the paper gets for free by working in a PROP:
-- wherever a derivation moves wires around, the networks it compares
-- are equal as soon as they permute the wires alike.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.PermCalc where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (ℕ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions using (module _IsPresentationOf_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (nat)
open import Examples.Groups.Real-Clifford+CH.Weakening using (weaken)

import Examples.Groups.Symmetric.Syntactics as S
import Examples.Groups.Symmetric.Presentation as SP
open import Examples.Groups.Symmetric.Semantics using (Permutation′-group)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The map

φ : S.Gen n → Circuit n
φ (S.gate₀ ())
φ (S.gate₁ ())
φ (S.gate₂ S.σ-gate) = Ex
φ (g S.↥)           = φ g ↑

-- A network: a circuit of the symmetric presentation, read in QC.
net : Word (S.Gen n) → Circuit n
net = φ ʷ

net-↑ : (w : Word (S.Gen n)) → net (w S.↑) ≡ net w ↑
net-↑ [ g ]ʷ  = Eq.refl
net-↑ ε       = Eq.refl
net-↑ (u • v) = Eq.cong₂ _•_ (net-↑ u) (net-↑ v)

------------------------------------------------------------------------
-- It respects the relations

private
  -- The braid relation for the swap: the swap rules for the swap
  -- itself (TopWeakening.nat at three wires), on the bottom wires of
  -- any wider circuit.
  braid : (₃₊ n) ⊢ Ex ↓ • Ex ↑ • Ex ↓ ≈ Ex ↑ • Ex ↓ • Ex ↑
  braid {n} = begin
    Ex ↓ • Ex ↑ • Ex ↓                ≈⟨ by-passoc (□ • □ • □) ((□ • (□ • ε)) • □) Eq.refl ⟩
    (Ex ↓ • (Ex ↑ • ε)) • Ex ↓        ≈⟨ sym (weaken n (s≤s (s≤s (s≤s z≤n))) (nat {2} Ex)) ⟩
    Ex ↑ • (Ex ↓ • (Ex ↑ • ε))        ≈⟨ by-passoc (□ • (□ • (□ • ε))) (□ • □ • □) Eq.refl ⟩
    Ex ↑ • Ex ↓ • Ex ↑ ∎
    where open Tools ((₃₊ n) VRel,_===_)

  -- A two-wire circuit at the bottom commutes with anything two wires
  -- up, letter by letter (as in TopWeakening, where it is private).
  low-comm : (u : Circuit 2) (v : Circuit n) → (₂₊ n) ⊢ (u ↓ᵏ n) • v ↑ ↑ ≈ v ↑ ↑ • (u ↓ᵏ n)
  low-comm [ gate₀ () ]ʷ v
  low-comm [ gate₀ () ↥ ]ʷ v
  low-comm [ gate₀ () ↥ ↥ ]ʷ v
  low-comm {n} [ gate₁ h ]ʷ v = sym (comm-gate₁-w↑ h (v ↑))
    where open Tools ((₂₊ n) VRel,_===_)
  low-comm {n} [ gate₂ h ]ʷ v = sym (comm-gate₂-w↑↑ h v)
    where open Tools ((₂₊ n) VRel,_===_)
  low-comm {n} [ gate₁ h ↥ ]ʷ v =
    lemma-cong↑ ([ gate₁ h ]ʷ • v ↑) (v ↑ • [ gate₁ h ]ʷ) (PB-sym (comm-gate₁-w↑ h v))
    where open Tools ((₁₊ n) VRel,_===_) renaming (sym to PB-sym)
  low-comm {n} ε v = trans left-unit (sym right-unit)
    where open Tools ((₂₊ n) VRel,_===_)
  low-comm {n} (u • t) v = begin
    ((u ↓ᵏ n) • (t ↓ᵏ n)) • v ↑ ↑   ≈⟨ assoc ⟩
    (u ↓ᵏ n) • ((t ↓ᵏ n) • v ↑ ↑)   ≈⟨ back _ (low-comm t v) ⟩
    (u ↓ᵏ n) • (v ↑ ↑ • (t ↓ᵏ n))   ≈⟨ sym assoc ⟩
    ((u ↓ᵏ n) • v ↑ ↑) • (t ↓ᵏ n)   ≈⟨ front _ (low-comm u v) ⟩
    (v ↑ ↑ • (u ↓ᵏ n)) • (t ↓ᵏ n)   ≈⟨ assoc ⟩
    v ↑ ↑ • (u ↓ᵏ n) • (t ↓ᵏ n) ∎
    where open Tools ((₂₊ n) VRel,_===_)

φ-ax : ∀ {u v : Word (S.Gen n)} → S._VRel,_===_ n u v → n ⊢ net u ≈ net v
φ-ax (S.srel S.order)                = Ex²
φ-ax {₃₊ n} (S.srel S.yang-baxter)   = braid
φ-ax {₁₊ n} (S.cong↑ {w = w} {v = v} r) =
  Eq.subst₂ (λ a b → (₁₊ n) ⊢ a ≈ b) (Eq.sym (net-↑ w)) (Eq.sym (net-↑ v))
            (lemma-cong↑ (net w) (net v) (φ-ax r))
φ-ax (S.comm₁ () g)
φ-ax {₂₊ n} (S.comm₂ S.σ-gate g) = sym (low-comm (Ex {0}) (φ g))
  where open Tools ((₂₊ n) VRel,_===_)
φ-ax (S.ω↑=ω ())

private
  module Cong {n : ℕ} = PP.StarCongruence (S._VRel,_===_ n) (_VRel,_===_ n) φ φ-ax

net-cong : ∀ {u v : Word (S.Gen n)} → PB._≈_ (S._VRel,_===_ n) u v → n ⊢ net u ≈ net v
net-cong = Cong.fʷ-cong

------------------------------------------------------------------------
-- Two networks with the same permutation are equal

module _ {n : ℕ} where
  private
    module SPn = _IsPresentationOf_ (SP.presentation {n})
    open GroupMorphisms (Group.rawGroup SPn.GL.•-ε-group)
                        (Group.rawGroup (Permutation′-group n))

  -- The permutation a network denotes.
  perm : Word (S.Gen n) → Group.Carrier (Permutation′-group n)
  perm = SPn.⟦_⟧

  perm-≈ : ∀ {u v : Word (S.Gen n)} →
           Group._≈_ (Permutation′-group n) (perm u) (perm v) → n ⊢ net u ≈ net v
  perm-≈ {u} {v} e =
    net-cong (IsGroupMonomorphism.injective
                (IsGroupIsomorphism.isGroupMonomorphism SPn.iso) {u} {v} e)
