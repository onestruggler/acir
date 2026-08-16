------------------------------------------------------------------------
-- Presentations of groups
--
-- The two descriptions of the qubit Clifford group modulo scalars agree
-- (p = 2):
--
--     CMS n  ≅  K ×_f Q.
--
-- CMS n (Qubit.CliffordGroup) is the group of Clifford words over H, S,
-- CZ quotiented by equality of their sign-tracking action on the phased
-- Pauli group P4 n.  K ×_f Q (Qubit.Semantics.Sem3, `Twisted`) is the
-- twisted product of the two PRESENTED groups — Pauli words K and
-- simplified symplectic words Q — along the factor set γ that Sem3
-- builds.  So this file says that the cocycle Sem3 computes really does
-- reassemble the Clifford group, and not merely some extension with the
-- same kernel and quotient.
--
-- The isomorphism is the obvious pair-splitting.  In one direction
--
--     Φ (a , u) = incl ⟦ a ⟧ · secn u,
--
-- the Pauli part read into CMS times the chosen lift of the symplectic
-- part; in the other,
--
--     Ψ w = (kerpart w , w),
--
-- where kerpart w names the Pauli by which w and the lift of its own
-- symplectic image differ.  Everything about Ψ is derived from Φ: once Φ
-- is an injective homomorphism and Φ ∘ Ψ is the identity, the
-- homomorphism laws for Ψ follow by cancelling Φ, and each map is the
-- other's surjectivity witness.
--
-- Φ is a homomorphism for exactly the two reasons Sem3 proves γ is a
-- factor set: the defect of the lifting IS the factor set
-- (incl-sem-defect), and conjugating a Pauli by a lift is acting on it
-- (CliffordGroup.conj-incl).  Its injectivity is the two presentations'
-- completeness — the simplified symplectic rule set for the second
-- component, Presentation-Alt for the first — with a cancellation in
-- CMS in between.  Surjectivity is the kernel witness: once the lift of
-- w's symplectic image is divided out, what is left acts trivially on
-- phaseless Paulis, so it is a Pauli.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Semantics.Iso-CMS-Tw where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures
  using (module GroupMorphisms ; module MonoidMorphisms)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; ε ; _•_)

import Algebra.Properties.Group as GroupProperties
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Presentation.Base as PB

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Construct.FactorSetExtension using (FactorSet)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

-- Qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic ; _≈ˢ_ ; _⁻¹ˢ ; εˢ ; module Interpretation)
import Examples.Groups.ProjectivePauli.Presentation-Alt p-2 p-prime as PA
open import Examples.Groups.ProjectiveClifford.Qubit.CliffordAction using (cact)
import Examples.Groups.ProjectiveClifford.Qubit.CliffordGroup as CLG
import Examples.Groups.ProjectiveClifford.Qubit.Semantics.Sem3 as S3

open Symplectic using (ap ; ap⁻¹ ; invʳ)
open Interpretation using (⟦_⟧)
open CLG using (_≈ᶜ_ ; _⁻¹ᶜ)
open S3 using (PGen ; SGen ; ΓK ; ΓQ)

module _ (n : ℕ) where

  private
    module T  = Group (S3.Twisted n)
    module C  = Group (CLG.CMS-group n)
    module KB = PB (ΓK n)
    module QB = PB (ΓQ n)
    module BK = PA.Build n

    -- The two morphism namespaces, one per direction.
    module MC = MonoidMorphisms (Group.rawMonoid (CLG.CMS-group n))
                                (Group.rawMonoid (S3.Twisted n))
    module GC = GroupMorphisms (Group.rawGroup (CLG.CMS-group n))
                               (Group.rawGroup (S3.Twisted n))
    module MT = MonoidMorphisms (Group.rawMonoid (S3.Twisted n))
                                (Group.rawMonoid (CLG.CMS-group n))
    module GT = GroupMorphisms (Group.rawGroup (S3.Twisted n))
                               (Group.rawGroup (CLG.CMS-group n))

    -- The factor set of the twisted product, named.
    f : Word (SGen n) → Word (SGen n) → Word (PGen n)
    f = FactorSet.f (S3.γ n)

  ----------------------------------------------------------------------
  -- A Pauli word, read into the Clifford group
  --
  -- It is a group homomorphism K → CMS n: `sem` is one by computation,
  -- `incl` by incl-∙ / incl-ε.

  IS : Word (PGen n) → Word (SGen n)
  IS w = CLG.incl (PA.sem w)

  private
    IS-cong : {w w' : Word (PGen n)} → KB._≈_ w w' → IS w ≈ᶜ IS w'
    IS-cong e = C.reflexive (Eq.cong CLG.incl (BK.sound e))

    IS-∙ : (w w' : Word (PGen n)) → IS (w • w') ≈ᶜ (IS w • IS w')
    IS-∙ w w' = CLG.incl-∙ (PA.sem w) (PA.sem w')

    -- Acting on a Pauli word is conjugating its image by the lift: this
    -- is CliffordGroup.conj-incl, with ⟦ secn u ⟧ traded for ⟦ u ⟧.
    IS-act : (u : Word (SGen n)) (w : Word (PGen n)) →
             IS (S3.act u w) ≈ᶜ ((S3.secn n u • IS w) • (S3.secn n u) ⁻¹ᶜ)
    IS-act u w =
      C.trans {i = IS (S3.act u w)}
              {j = CLG.incl (ap ⟦ S3.secn n u ⟧ (PA.sem w))}
              {k = (S3.secn n u • IS w) • (S3.secn n u) ⁻¹ᶜ}
        (C.reflexive (Eq.cong CLG.incl
          (Eq.trans (S3.actw-sem u w)
                    (Eq.sym (S3.denote-eq (S3.secn-≈ n u) (PA.sem w))))))
        (C.sym {x = (S3.secn n u • IS w) • (S3.secn n u) ⁻¹ᶜ}
               {y = CLG.incl (ap ⟦ S3.secn n u ⟧ (PA.sem w))}
          (CLG.conj-incl (S3.secn n u) (PA.sem w)))

    -- The defining property of the defect: it is what the two lifts
    -- overshoot the lift of the product by.
    defect-· : (u v : Word (SGen n)) →
               (S3.defect n u v • S3.secn n (u • v))
                 ≈ᶜ (S3.secn n u • S3.secn n v)
    defect-· u v x =
      Eq.cong (λ z → cact (S3.secn n u) (cact (S3.secn n v) z))
              (CLG.invˡ-lemma (S3.secn n (u • v)) x)

  ----------------------------------------------------------------------
  -- Φ: from the twisted product into the Clifford group
  --
  -- The Pauli part, read in, times the chosen lift of the symplectic
  -- part.

  Φ : T.Carrier → Word (SGen n)
  Φ (a , u) = IS a • S3.secn n u

  Φ-cong : {x y : T.Carrier} → x T.≈ y → Φ x ≈ᶜ Φ y
  Φ-cong {a , u} {b , v} (ea , eu) =
    CLG.∙-congᶜ {w = IS a} {w' = IS b} {v = S3.secn n u} {v' = S3.secn n v}
      (IS-cong ea) (C.reflexive (S3.secn-cong n eu))

  -- The unit lifts to the unit, and the identity Pauli conjugates
  -- trivially.
  Φ-ε : Φ T.ε ≈ᶜ ε
  Φ-ε = C.trans {i = Φ T.ε} {j = IS ε} {k = ε} patch CLG.incl-ε
    where
    patch : Φ T.ε ≈ᶜ IS ε
    patch x = Eq.cong (λ z → cact (IS ε) (cact z x)) (S3.secn-ε n)

  -- Multiplicativity.  The factor-set term is the defect of the lifting
  -- (incl-sem-defect), so it cancels against the two lifts; the acted-on
  -- Pauli is a conjugate (IS-act), so its two copies of the lift cancel
  -- as well, leaving the two factors side by side.
  Φ-homo : (x y : T.Carrier) → Φ (x T.∙ y) ≈ᶜ (Φ x • Φ y)
  Φ-homo (a , u) (b , v) = begin
    IS ((a • S3.act u b) • f u v) • W
      ≈⟨ (λ x → IS-∙ (a • S3.act u b) (f u v) (cact W x)) ⟩
    (IS (a • S3.act u b) • IS (f u v)) • W
      ≈⟨ (λ x → IS-∙ a (S3.act u b) (cact (IS (f u v)) (cact W x))) ⟩
    ((A • IS (S3.act u b)) • IS (f u v)) • W
      ≈⟨ (λ x → Eq.cong (λ z → cact A (cact (IS (S3.act u b)) z))
                        (S3.incl-sem-defect n u v (cact W x))) ⟩
    ((A • IS (S3.act u b)) • D) • W
      ≈⟨ (λ x → Eq.cong (λ z → cact A (cact (IS (S3.act u b)) z))
                        (defect-· u v x)) ⟩
    (A • IS (S3.act u b)) • (U • V)
      ≈⟨ (λ x → Eq.cong (cact A) (IS-act u b (cact U (cact V x)))) ⟩
    (A • ((U • B) • U ⁻¹ᶜ)) • (U • V)
      ≈⟨ (λ x → Eq.cong (λ z → cact A (cact U (cact B z)))
                        (CLG.invˡ-lemma U (cact V x))) ⟩
    (A • U) • (B • V) ∎
    where
    open ≈-Reasoning C.setoid
    A = IS a
    B = IS b
    U = S3.secn n u
    V = S3.secn n v
    W = S3.secn n (u • v)
    D = S3.defect n u v

  ----------------------------------------------------------------------
  -- Φ is injective
  --
  -- The Pauli part is invisible to proj, so the symplectic components
  -- must already agree; then the two lifts are the SAME word, and
  -- cancelling one leaves the Pauli parts, which incl separates.

  private
    proj-Φ : (a : Word (PGen n)) (u : Word (SGen n)) →
             CLG.proj (Φ (a , u)) ≈ˢ ⟦ u ⟧
    proj-Φ a u x = begin
      ap ⟦ IS a ⟧ (ap ⟦ S3.secn n u ⟧ x)
        ≡⟨ CLG.proj-kills-incl (PA.sem a) (ap ⟦ S3.secn n u ⟧ x) ⟩
      ap ⟦ S3.secn n u ⟧ x
        ≡⟨ S3.denote-eq (S3.secn-≈ n u) x ⟩
      ap ⟦ u ⟧ x ∎
      where open Eq.≡-Reasoning

  Φ-injective : {x y : T.Carrier} → Φ x ≈ᶜ Φ y → x T.≈ y
  Φ-injective {a , u} {b , v} e = pauli-eq , symp-eq
    where
    open ≈-Reasoning C.setoid
    open GroupProperties (CLG.CMS-group n) using (∙-cancelʳ)

    -- The symplectic components denote the same transformation, and the
    -- simplified rule set is complete.
    symp-eq : QB._≈_ u v
    symp-eq = S3.denote-injective (λ x →
      Eq.trans (Eq.sym (proj-Φ a u x))
               (Eq.trans (CLG.proj-cong {w = Φ (a , u)} {v = Φ (b , v)} e x)
                         (proj-Φ b v x)))

    -- So the section picks the same word on both sides.
    lift-eq : S3.secn n u ≡ S3.secn n v
    lift-eq = S3.secn-cong n symp-eq

    cancel : IS a ≈ᶜ IS b
    cancel = ∙-cancelʳ (S3.secn n v) (IS a) (IS b) (begin
      IS a • S3.secn n v  ≈⟨ C.reflexive (Eq.cong (IS a •_) (Eq.sym lift-eq)) ⟩
      IS a • S3.secn n u  ≈⟨ e ⟩
      IS b • S3.secn n v  ∎)

    pauli-eq : KB._≈_ a b
    pauli-eq = BK.complete
      (CLG.incl-injective {P = PA.sem a} {P' = PA.sem b} cancel)

  ----------------------------------------------------------------------
  -- Ψ: from the Clifford group into the twisted product
  --
  -- Divide out the lift of w's own symplectic image.  What is left
  -- projects to the identity, so the kernel witness reads it as a Pauli.

  private
    proj-⁻¹ᶜ : (w : Word (SGen n)) → CLG.proj (w ⁻¹ᶜ) ≈ˢ (CLG.proj w ⁻¹ˢ)
    proj-⁻¹ᶜ = GroupMorphisms.IsGroupHomomorphism.⁻¹-homo
                 (Extension.proj-homo (CLG.CMS-extension n))

    lift-triv : (w : Word (SGen n)) →
                CLG.proj (w • (S3.secn n w) ⁻¹ᶜ) ≈ˢ εˢ
    lift-triv w x = begin
      ap ⟦ w ⟧ (ap ⟦ (S3.secn n w) ⁻¹ᶜ ⟧ x)
        ≡⟨ Eq.cong (ap ⟦ w ⟧) (proj-⁻¹ᶜ (S3.secn n w) x) ⟩
      ap ⟦ w ⟧ (ap⁻¹ ⟦ S3.secn n w ⟧ x)
        ≡⟨ S3.denote-eq (S3.secn-≈ n w) (ap⁻¹ ⟦ S3.secn n w ⟧ x) ⟨
      ap ⟦ S3.secn n w ⟧ (ap⁻¹ ⟦ S3.secn n w ⟧ x)
        ≡⟨ invʳ ⟦ S3.secn n w ⟧ x ⟩
      x ∎
      where open Eq.≡-Reasoning

  -- The Pauli part of a Clifford word.
  kerpart : Word (SGen n) → Word (PGen n)
  kerpart w =
    PA.inv-nf (CLG.ker-witness (w • (S3.secn n w) ⁻¹ᶜ) (lift-triv w))

  Ψ : Word (SGen n) → T.Carrier
  Ψ w = kerpart w , w

  -- Φ undoes Ψ: putting the Pauli part back and multiplying by the lift
  -- rebuilds the word.
  Φ∘Ψ : (w : Word (SGen n)) → Φ (Ψ w) ≈ᶜ w
  Φ∘Ψ w = begin
    IS (kerpart w) • U
      ≈⟨ (λ x → Eq.cong (λ z → cact z (cact U x))
                        (Eq.cong CLG.incl (PA.sem-inv KW))) ⟩
    CLG.incl KW • U
      ≈⟨ (λ x → CLG.ker-witness-correct (w • U ⁻¹ᶜ) (lift-triv w) (cact U x)) ⟩
    (w • U ⁻¹ᶜ) • U
      ≈⟨ (λ x → Eq.cong (cact w) (CLG.invˡ-lemma U x)) ⟩
    w ∎
    where
    open ≈-Reasoning C.setoid
    U  = S3.secn n w
    KW = CLG.ker-witness (w • U ⁻¹ᶜ) (lift-triv w)

  ----------------------------------------------------------------------
  -- Ψ is a homomorphism
  --
  -- Nothing here is new: each law is its Φ-counterpart with Φ cancelled
  -- off the front, which Φ-injective allows.

  Ψ-cong : {w v : Word (SGen n)} → w ≈ᶜ v → Ψ w T.≈ Ψ v
  Ψ-cong {w} {v} e = Φ-injective {Ψ w} {Ψ v} (begin
    Φ (Ψ w)  ≈⟨ Φ∘Ψ w ⟩
    w        ≈⟨ e ⟩
    v        ≈⟨ Φ∘Ψ v ⟨
    Φ (Ψ v)  ∎)
    where open ≈-Reasoning C.setoid

  Ψ-homo : (w v : Word (SGen n)) → Ψ (w • v) T.≈ (Ψ w T.∙ Ψ v)
  Ψ-homo w v = Φ-injective {Ψ (w • v)} {Ψ w T.∙ Ψ v} (begin
    Φ (Ψ (w • v))      ≈⟨ Φ∘Ψ (w • v) ⟩
    w • v              ≈⟨ CLG.∙-congᶜ {w = Φ (Ψ w)} {w' = w}
                                      {v = Φ (Ψ v)} {v' = v}
                            (Φ∘Ψ w) (Φ∘Ψ v) ⟨
    Φ (Ψ w) • Φ (Ψ v)  ≈⟨ Φ-homo (Ψ w) (Ψ v) ⟨
    Φ (Ψ w T.∙ Ψ v)    ∎)
    where open ≈-Reasoning C.setoid

  Ψ-ε : Ψ ε T.≈ T.ε
  Ψ-ε = Φ-injective {Ψ ε} {T.ε} (begin
    Φ (Ψ ε)  ≈⟨ Φ∘Ψ ε ⟩
    ε        ≈⟨ Φ-ε ⟨
    Φ T.ε    ∎)
    where open ≈-Reasoning C.setoid

  Ψ-injective : {w v : Word (SGen n)} → Ψ w T.≈ Ψ v → w ≈ᶜ v
  Ψ-injective {w} {v} e = begin
    w        ≈⟨ Φ∘Ψ w ⟨
    Φ (Ψ w)  ≈⟨ Φ-cong {Ψ w} {Ψ v} e ⟩
    Φ (Ψ v)  ≈⟨ Φ∘Ψ v ⟩
    v        ∎
    where open ≈-Reasoning C.setoid

  ----------------------------------------------------------------------
  -- The isomorphism
  --
  -- Each map is the other's surjectivity witness.

  Ψ-isMonoidHomomorphism : MC.IsMonoidHomomorphism Ψ
  Ψ-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ {w} {v} → Ψ-cong {w} {v} }
      ; homo              = Ψ-homo
      }
    ; ε-homo = Ψ-ε
    }

  CMS≅Twisted : GC.IsGroupIsomorphism Ψ
  CMS≅Twisted = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
          (CLG.CMS-group n) (S3.Twisted n) Ψ-isMonoidHomomorphism
      ; injective = λ {w} {v} → Ψ-injective {w} {v}
      }
    ; surjective = λ x → Φ x , λ {z} e → Φ-injective {Ψ z} {x} (begin
        Φ (Ψ z)  ≈⟨ Φ∘Ψ z ⟩
        z        ≈⟨ e ⟩
        Φ x      ∎)
    }
    where open ≈-Reasoning C.setoid

  -- The same isomorphism the other way round, which the work above has
  -- already proved.

  Φ-isMonoidHomomorphism : MT.IsMonoidHomomorphism Φ
  Φ-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ {x} {y} → Φ-cong {x} {y} }
      ; homo              = Φ-homo
      }
    ; ε-homo = Φ-ε
    }

  Twisted≅CMS : GT.IsGroupIsomorphism Φ
  Twisted≅CMS = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
          (S3.Twisted n) (CLG.CMS-group n) Φ-isMonoidHomomorphism
      ; injective = λ {x} {y} → Φ-injective {x} {y}
      }
    ; surjective = λ w → Ψ w , λ {z} e → begin
        Φ z      ≈⟨ Φ-cong {z} {Ψ w} e ⟩
        Φ (Ψ w)  ≈⟨ Φ∘Ψ w ⟩
        w        ∎
    }
    where open ≈-Reasoning C.setoid
