------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the symplectic normal form, via Circuit.Uniqueness
--
-- An alternative route to Normalization.Uniqueness's unique-nf: rather
-- than appealing to NF-Inj's bespoke argument, this module supplies
-- Circuit.Uniqueness's interface and lets the generic machinery
-- produce the theorem.
--
-- Unlike the Sₙ instantiation, the towers here agree on the nose.
-- Taking C n := ML (₁₊ n) and [_]ᶜ := [_]ᵐˡ makes Circuit.CosetNF's
--
--   NF 0 = ⊤       NF (₁₊ n) = NF n × C n
--   [ nf , c ] = [ nf ] ↑ • [ c ]ᶜ
--
-- literally Section's NF and [_], so the theorem obtained is about the
-- real symplectic normal form.
--
-- States are Paulis, one per wire: Ob is Pauli1 and the distinguished
-- object is the identity Pauli, so the probe state is pI ∷ pIₙ.  The
-- action is by ap⁻¹ rather than ap — that is what makes it a RIGHT
-- action, since ap of a composite applies its right factor first.
--
-- WHAT IS NOT DISCHARGED.  c-inj is a parameter of module Uniqueness
-- below, not a theorem.  Circuit.Uniqueness only ever probes states
-- h ∷ pIₙ: pinning the tail is what makes lifted prefixes vanish, and
-- that is what its coset step relies on.  But an ML (₁₊ n) box carries
-- a B and a D column, one entry per wire, and recovering those needs
-- probes at every wire -- which is exactly what LMHeadInj does, with
-- inputs pI ∷ ⋯ ∷ probe at wire j ∷ pIₙ.  So c-inj asks for strictly
-- more than lemma-lm-head-inj (whose hypothesis ranges over all of
-- Pauli (₁₊ n), not just the p² states with pIₙ tails), and it is
-- likely false for n ≥ 2.  Discharging it would need Circuit.Uniqueness
-- reworked along NF-Inj's lines: recover the coset from agreement on
-- ALL states, then descend a wire by surjectivity of the coset action
-- rather than by a vanishing prefix.  Everything else below is proved.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)

open import Notations

module Examples.Groups.Symplectic.Normalization.Uniqueness2
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Algebra.Bundles using (Group ; Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁)
open import Data.Vec.Base as Vec using (Vec ; _∷_ ; [])
import Data.Vec.Relation.Binary.Equality.Setoid as VecEq
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise-≡⇒≡ ; ≡⇒Pointwise-≡)
open import ForStdlib.Algebra.IndexedAction using (IndexedRightAction)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP

import Circuit.CosetNF as CosetNF
import Circuit.Uniqueness as CU
import Normalization.NormalForm.Uniqueness.Propositional as NFU

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pI ; pIₙ ; _*ₚ_)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using ( _≈ˢ_ ; εˢ ; _∘ˢ_ ; _⁻¹ˢ ; Sp-group ; lift₀ˢ ; Sp-embedding
        ; module Interpretation )
  renaming (Symplectic to Sym)
open Sym using (ap ; ap⁻¹ ; invˡ ; invʳ ; linear-*)
open Interpretation using (⟦_⟧)
open import Examples.Groups.Symplectic.Normalization.NF p-2 p-prime
  using (ML ; A)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using ([_]ᵐˡ)
open import Examples.Groups.Symplectic.Transport p-2 p-prime
  using (sound-ax)

private variable n : ℕ


------------------------------------------------------------------------
-- Soundness

-- The congruence closure of sound-ax.  ⟦_⟧ takes ε and _•_ to the unit
-- and composition of Symplectic on the nose, so every structural case
-- is refl or a transitivity.

sound : {w v : Circuit n} → PB._≈_ (n QRel,_===_) w v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
sound {n} = go
  where
  open PB (n QRel,_===_)

  go : {w v : Circuit n} → w ≈ v → ⟦ w ⟧ ≈ˢ ⟦ v ⟧
  go PB.refl        p = Eq.refl
  go (PB.sym e)     p = Eq.sym (go e p)
  go (PB.trans e f) p = Eq.trans (go e p) (go f p)
  go (PB.cong {w} {w'} {v} {v'} e f) p =
    Eq.trans (Eq.cong (ap ⟦ w ⟧) (go f p)) (go e (ap ⟦ v' ⟧ p))
  go PB.assoc       p = Eq.refl
  go PB.left-unit   p = Eq.refl
  go PB.right-unit  p = Eq.refl
  go (PB.axiom x)   p = sound-ax x p

-- ⟦_⟧ is a monoid homomorphism out of the word monoid; only the
-- congruence has content.
mhomo : ∀ n → MonoidMorphisms.IsMonoidHomomorphism
                (Monoid.rawMonoid (PP.•-ε-monoid (n QRel,_===_)))
                (Group.rawMonoid (Sp-group n))
                (⟦_⟧ {n})
mhomo n = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism =
        record { cong = λ {w} {v} → sound {n} {w} {v} }
    ; homo = λ _ _ _ → Eq.refl
    }
  ; ε-homo = λ _ → Eq.refl
  }


------------------------------------------------------------------------
-- Symplectic transformations acting on Paulis

-- ap is a LEFT action of _∘ˢ_ (ap (S ∘ˢ T) = ap S ∘ ap T applies T
-- first), so the right action is by the inverse: ap⁻¹ of a composite
-- applies the inverse of its left factor first, which is exactly the
-- law ◁-compose asks for.  Both ◁-identity and ◁-compose then hold
-- definitionally.

infixl 7 _◁_
_◁_ : Pauli n → Sym n → Pauli n
xs ◁ S = ap⁻¹ S xs

private
  -- Transformations that agree agree on inverses too.
  ap⁻¹-cong : (S T : Sym n) → S ≈ˢ T → ∀ p → ap⁻¹ S p ≡ ap⁻¹ T p
  ap⁻¹-cong S T e p =
    Eq.trans (Eq.sym (invˡ T (ap⁻¹ S p)))
             (Eq.cong (ap⁻¹ T)
               (Eq.trans (Eq.sym (e (ap⁻¹ S p))) (invʳ S p)))

Ob : Setoid 0ℓ 0ℓ
Ob = Eq.setoid Pauli1

act : IndexedRightAction (λ n → Group.rawMonoid (Sp-group n)) Ob
act = record
  { _◁_        = _◁_
  ; ◁-cong     = λ {_} {xs} {ys} {S} {T} xs≋ys S≈T →
                   ≡⇒Pointwise-≡
                     (Eq.trans (Eq.cong (ap⁻¹ S) (Pointwise-≡⇒≡ xs≋ys))
                               (ap⁻¹-cong S T S≈T ys))
  ; ◁-identity = λ xs → ≡⇒Pointwise-≡ Eq.refl
  ; ◁-compose  = λ xs S T → ≡⇒Pointwise-≡ Eq.refl
  }

open VecEq Ob using (_≋_)


------------------------------------------------------------------------
-- Lifting, and the identity Pauli

-- A lifted circuit acts as the identity on wire 0 and as the unlifted
-- circuit on the rest: the generator action is head-preserving cons
-- (actg⁻¹ (g ↥) (x ∷ ps) = x ∷ actg⁻¹ g ps), and composition threads
-- that through.  This is SemInj's lift-act for ap⁻¹ and for _↑ rather
-- than the word-lift; SemInj's version is private and states the other
-- two, so it is redone here.

lift-act⁻¹ : (w : Circuit n) (x : Pauli1) (ps : Pauli n) →
             ap⁻¹ ⟦ w ↑ ⟧ (x ∷ ps) ≡ x ∷ ap⁻¹ ⟦ w ⟧ ps
lift-act⁻¹ [ g ]ʷ  x ps = Eq.refl
lift-act⁻¹ ε x ps = Eq.refl
lift-act⁻¹ (w • v) x ps =
  Eq.trans (Eq.cong (ap⁻¹ ⟦ v ↑ ⟧) (lift-act⁻¹ w x ps))
           (lift-act⁻¹ v x (ap⁻¹ ⟦ w ⟧ ps))

lift-act : (w : Circuit n) (x : Pauli1) (ps : Pauli n) →
           ap ⟦ w ↑ ⟧ (x ∷ ps) ≡ x ∷ ap ⟦ w ⟧ ps
lift-act [ g ]ʷ  x ps = Eq.refl
lift-act ε x ps = Eq.refl
lift-act (w • v) x ps =
  Eq.trans (Eq.cong (ap ⟦ w ↑ ⟧) (lift-act v x ps))
           (lift-act w x (ap ⟦ v ⟧ ps))

head-fix : (h : Pauli1) (t : Pauli n) (w : Circuit n) →
           ((h ∷ t) ◁ ⟦ w ↑ ⟧) ≋ (h ∷ (t ◁ ⟦ w ⟧))
head-fix h t w = ≡⇒Pointwise-≡ (lift-act⁻¹ w h t)

-- Lifting a circuit by a wire is the embedding of Sp(2n) into
-- Sp(2(1+n)): both act as the identity on wire 0 and as ⟦ w ⟧ on the
-- rest, and every Pauli (₁₊ n) splits as x ∷ ps.
compat : (w : Circuit n) → ⟦ w ↑ ⟧ ≈ˢ lift₀ˢ ⟦ w ⟧
compat w (x ∷ ps) = lift-act w x ps

private
  -- Scaling a Pauli by ₀ gives the identity Pauli ...
  zero-*ₚ : (p : Pauli n) → ₀ *ₚ p ≡ pIₙ
  zero-*ₚ []            = Eq.refl
  zero-*ₚ ((a , b) ∷ p) =
    Eq.cong₂ _∷_ (Eq.cong₂ _,_ (*-zeroˡ a) (*-zeroˡ b)) (zero-*ₚ p)

  -- ... so linearity makes every symplectic transformation fix it.
  fix-pIₙ : (S : Sym n) → ap S pIₙ ≡ pIₙ
  fix-pIₙ {n} S = Eq.trans
    (Eq.trans (Eq.cong (ap S) (Eq.sym (zero-*ₚ (pIₙ {n}))))
              (linear-* S ₀ pIₙ))
    (zero-*ₚ (ap S pIₙ))

  replicate-pI : ∀ n → Vec.replicate n pI ≡ pIₙ {n}
  replicate-pI ₀      = Eq.refl
  replicate-pI (₁₊ n) = Eq.cong ((₀ , ₀) ∷_) (replicate-pI n)

zz-fix : (w : Circuit n) →
         (Vec.replicate n pI ◁ ⟦ w ⟧) ≋ Vec.replicate n pI
zz-fix {n} w = ≡⇒Pointwise-≡ (Eq.trans
  (Eq.trans (Eq.cong (ap⁻¹ ⟦ w ⟧) (replicate-pI n))
            (fix-pIₙ (⟦ w ⟧ ⁻¹ˢ)))
  (Eq.sym (replicate-pI n)))


------------------------------------------------------------------------
-- The identity coset

-- Circuit.CosetNF wants a distinguished coset for its normalizer.  The
-- uniqueness proof never looks at it; this is Normalization.Iᶜ, copied
-- so as not to depend on that module.
Ic : ML (₁₊ n)
Ic {₀}    = ([] , ₀) , ([] , Ia)
  where Ia = (₀ , ₁) , λ ()
Ic {₁₊ m} = inj₁ ((Vec.replicate (₁₊ m) (₀ , ₀) , ₀)
                 , (Vec.replicate (₁₊ m) (₀ , ₀) , Ia))
  where Ia = (₀ , ₁) , λ ()


------------------------------------------------------------------------
-- Uniqueness of the normal form

-- The one obligation this architecture cannot discharge; see the
-- header.  It says a coset representative is determined by how it acts
-- on the states pI ∷ pIₙ alone.
module Uniqueness
  (c-inj : ∀ {n} {c1 c2 : ML (₁₊ n)} →
           (∀ (h : Pauli1) → let t = Vec.replicate n pI in
              ((h ∷ t) ◁ ⟦ [ c1 ]ᵐˡ ⟧) ≋ ((h ∷ t) ◁ ⟦ [ c2 ]ᵐˡ ⟧)) →
           c1 ≡ c2)
  where

  module Uniq =
    CU (λ n → ML (₁₊ n)) (λ {n} → Ic {n}) SympGate [_]ᵐˡ
       Sp-group Sp-embedding
       Base._SRel,_===_ ⟦_⟧ mhomo (λ {n} {w} → compat {n} w)
       Ob act head-fix pI zz-fix (λ {n} {c1} {c2} → c-inj {n} {c1} {c2})

  open CosetNF (λ n → ML (₁₊ n)) (λ {n} → Ic {n}) SympGate [_]ᵐˡ
    using (NF ; inv-nf)

  unique-nf : ∀ n →
              let open NFU (n QRel,_===_) (NF n)
                           (Group.setoid (Sp-group n)) (⟦_⟧ {n})
              in UniqueNormalForm (inv-nf {n})
  unique-nf = Uniq.unique-nf
