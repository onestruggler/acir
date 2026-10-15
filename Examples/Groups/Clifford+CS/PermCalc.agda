------------------------------------------------------------------------
-- Presentations of groups
--
-- Swap networks in Clifford+CS circuits: two networks with the same
-- permutation are equal
--
-- Real-Clifford+CH.PermCalc for the Clifford+CS gates.  The swap is an
-- involution and satisfies the braid relation (one evaluation on three
-- wires), and the structural rules of the symmetric group's circuit
-- presentation are among ours, so its circuits map into Clifford+CS
-- circuits, σ ↦ Swap (`net`), and its completeness
-- (`Symmetric.Presentation`) carries over: two swap networks denoting
-- the same permutation are equal (`perm-≈`).  This is the PROP
-- structure the joint paper uses implicitly whenever it places an
-- equation on other wires.  A network's inverse is its reverse
-- (`net-inv`, `perm-inv`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.PermCalc where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Fin using (Fin) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions using (module _IsPresentationOf_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Swaps using (Swap²)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
import Examples.Groups.Clifford+CS.ThreeQubit as ThreeQubit

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
φ (S.gate₂ S.σ-gate) = Swap
φ (g S.↥)           = φ g ↑

-- A network: a circuit of the symmetric presentation, read here.
net : Word (S.Gen n) → Circuit n
net = φ ʷ

net-↑ : (w : Word (S.Gen n)) → net (w S.↑) ≡ net w ↑
net-↑ [ g ]ʷ  = Eq.refl
net-↑ ε       = Eq.refl
net-↑ (u • v) = Eq.cong₂ _•_ (net-↑ u) (net-↑ v)

------------------------------------------------------------------------
-- It respects the relations

private
  module S₃ = Below 3 ThreeQubit.complete

  braid : (₃₊ n) ⊢ Swap • Swap ↑ • Swap ≈ Swap ↑ • Swap • Swap ↑
  braid = S₃.by-sem (Swap • Swap ↑ • Swap) (Swap ↑ • Swap • Swap ↑) Eq.refl

φ-ax : ∀ {u v : Word (S.Gen n)} → S._VRel,_===_ n u v → n ⊢ net u ≈ net v
φ-ax (S.srel S.order)                = Swap²
φ-ax {₃₊ n} (S.srel S.yang-baxter)   = braid
φ-ax {₁₊ n} (S.cong↑ {w = w} {v = v} r) =
  Eq.subst₂ (λ a b → (₁₊ n) ⊢ a ≈ b) (Eq.sym (net-↑ w)) (Eq.sym (net-↑ v))
            (lemma-cong↑ (net w) (net v) (φ-ax r))
φ-ax (S.comm₁ () g)
φ-ax {₂₊ n} (S.comm₂ S.σ-gate g) = sym (low-comm (Swap {0}) (φ g))
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

------------------------------------------------------------------------
-- The reverse of a network is its inverse

revS : Word (S.Gen n) → Word (S.Gen n)
revS [ g ]ʷ  = [ g ]ʷ
revS ε       = ε
revS (u • v) = revS v • revS u

revS-↑ : (w : Word (S.Gen n)) → revS (w S.↑) ≡ revS w S.↑
revS-↑ [ g ]ʷ  = Eq.refl
revS-↑ ε       = Eq.refl
revS-↑ (u • v) = Eq.cong₂ _•_ (revS-↑ v) (revS-↑ u)

revS² : (w : Word (S.Gen n)) → revS (revS w) ≡ w
revS² [ g ]ʷ  = Eq.refl
revS² ε       = Eq.refl
revS² (u • v) = Eq.cong₂ _•_ (revS² u) (revS² v)

private
  gen² : (g : S.Gen n) → n ⊢ φ g • φ g ≈ ε
  gen² (S.gate₀ ())
  gen² (S.gate₁ ())
  gen² (S.gate₂ S.σ-gate) = Swap²
  gen² (g S.↥)            = lemma-cong↑ (φ g • φ g) ε (gen² g)

net-inv : (u : Word (S.Gen n)) → n ⊢ net u • net (revS u) ≈ ε
net-inv {n} [ g ]ʷ  = gen² g
net-inv {n} ε       = left-unit
  where open Tools (n VRel,_===_)
net-inv {n} (u • v) = begin
  (net u • net v) • (net (revS v) • net (revS u))
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  net u • (net v • net (revS v)) • net (revS u)
    ≈⟨ back _ (trans (front _ (net-inv v)) left-unit) ⟩
  net u • net (revS u)
    ≈⟨ net-inv u ⟩
  ε ∎
  where open Tools (n VRel,_===_)

net-inv′ : (u : Word (S.Gen n)) → n ⊢ net (revS u) • net u ≈ ε
net-inv′ {n} [ g ]ʷ  = gen² g
net-inv′ {n} ε       = left-unit
  where open Tools (n VRel,_===_)
net-inv′ {n} (u • v) = begin
  (net (revS v) • net (revS u)) • (net u • net v)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  net (revS v) • (net (revS u) • net u) • net v
    ≈⟨ back _ (trans (front _ (net-inv′ u)) left-unit) ⟩
  net (revS v) • net v
    ≈⟨ net-inv′ v ⟩
  ε ∎
  where open Tools (n VRel,_===_)

private
  perm-gen² : (g : S.Gen n) (k : Fin n) → perm [ g ]ʷ ⟨$⟩ʳ (perm [ g ]ʷ ⟨$⟩ʳ k) ≡ k
  perm-gen² (S.gate₀ ())
  perm-gen² (S.gate₁ ())
  perm-gen² (S.gate₂ S.σ-gate) 0F           = Eq.refl
  perm-gen² (S.gate₂ S.σ-gate) (sF 0F)      = Eq.refl
  perm-gen² (S.gate₂ S.σ-gate) (sF (sF k))  = Eq.refl
  perm-gen² (g S.↥)            0F           = Eq.refl
  perm-gen² (g S.↥)            (sF k)       = Eq.cong sF (perm-gen² g k)

perm-inv : (u : Word (S.Gen n)) (k : Fin n) → perm (revS u) ⟨$⟩ʳ (perm u ⟨$⟩ʳ k) ≡ k
perm-inv [ g ]ʷ  k = perm-gen² g k
perm-inv ε       k = Eq.refl
perm-inv (u • v) k =
  Eq.trans (Eq.cong (perm (revS u) ⟨$⟩ʳ_) (perm-inv v (perm u ⟨$⟩ʳ k))) (perm-inv u k)

-- A permutation is injective.
perm-inj : (u : Word (S.Gen n)) {j k : Fin n} → perm u ⟨$⟩ʳ j ≡ perm u ⟨$⟩ʳ k → j ≡ k
perm-inj u {j} {k} e =
  Eq.trans (Eq.sym (perm-inv u j)) (Eq.trans (Eq.cong (perm (revS u) ⟨$⟩ʳ_) e) (perm-inv u k))
