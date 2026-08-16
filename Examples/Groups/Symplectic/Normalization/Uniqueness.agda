------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of the symplectic normal form, via Circuit.Uniqueness
--
-- An alternative route to Normalization.Uniqueness's unique-nf: rather
-- than appealing to NF-Inj's argument directly, this module supplies
-- Circuit.Uniqueness's interface and lets the generic machinery
-- produce the theorem.  Circuit.Uniqueness is in fact NF-Inj's
-- argument made generic -- its act-nf, lemma-act-nf and nf-injective
-- are the abstract forms of NF-Inj's -- so the two coset obligations
-- are met by NF-Inj's own lemmas, unchanged:
--
--   c-inj  = lemma-lm-head-inj   (the completeness crux)
--   c-surj = lemma-lm-tail-surj
--
-- The towers agree on the nose.  Taking C n := ML (₁₊ n) and
-- [_]ᶜ := [_]ᵐˡ makes Circuit.CosetNF's
--
--   NF 0 = ⊤       NF (₁₊ n) = NF n × C n
--   [ nf , c ] = [ nf ] ↑ • [ c ]ᶜ
--
-- literally Section's NF and [_], so the theorem obtained is about the
-- real symplectic normal form.
--
-- States are Paulis, one per wire: Ob is Pauli1.  The action is ap,
-- which is a LEFT action, since ap of a composite applies its right
-- factor first -- so the coset factor of a normal form is the one
-- next to the input, which is what lets the coset be recovered from
-- every state rather than from states of a restricted shape.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)

open import Notations

module Examples.Groups.Symplectic.Normalization.Uniqueness
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Algebra.Bundles using (Group ; Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Product using (Σ-syntax ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (≡×≡⇒≡)
open import Data.Sum using (inj₁)
open import Data.Vec.Base as Vec using (Vec ; _∷_ ; [] ; head ; tail)
import Data.Vec.Relation.Binary.Equality.Setoid as VecEq
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise-≡⇒≡ ; ≡⇒Pointwise-≡)
open import ForStdlib.Algebra.IndexedAction using (IndexedLeftAction)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP

import Circuit.CosetNF as CosetNF
import Circuit.Uniqueness as CU
import Normalization.NormalForm.Uniqueness.Propositional as NFU

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (_≈ˢ_ ; εˢ ; _∘ˢ_ ; Sp-group ; module Interpretation)
  renaming (Symplectic to Sym)
open Sym using (ap)
open Interpretation using (⟦_⟧)
open import Examples.Groups.Symplectic.Normalization.Boxes p-2 p-prime
  using (ML)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using ([_]ᵐˡ) renaming (NF to NFˢ ; [_] to [_]ˢ)
open import Examples.Groups.Symplectic.Normalization.NF-Inj p-2 p-prime
  using (act ; lemma-lm-head-inj ; lemma-lm-tail-surj)
open import Examples.Groups.Symplectic.SoundnessDirect p-2 p-prime
  using (sound-ax)

private variable n : ℕ


------------------------------------------------------------------------
-- Soundness

-- The congruence closure of sound-ax.  ⟦_⟧ takes ε and _•_ to the unit
-- and composition of Sym on the nose, so every structural case is refl
-- or a transitivity.

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
                (Monoid.rawMonoid (Group.monoid (Sp-group n)))
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

-- ap is a LEFT action of _∘ˢ_: ap (S ∘ˢ T) = ap S ∘ ap T applies T
-- first, which is exactly ▷-compose.  Both ▷-identity and ▷-compose
-- hold definitionally.

Ob : Setoid 0ℓ 0ℓ
Ob = Eq.setoid Pauli1

act′ : IndexedLeftAction
         (λ n → Monoid.rawMonoid (Group.monoid (Sp-group n))) Ob
act′ = record
  { _▷_        = ap
  ; ▷-cong     = λ {_} {S} {T} {xs} {ys} S≈T xs≋ys →
                   ≡⇒Pointwise-≡
                     (Eq.trans (Eq.cong (ap S) (Pointwise-≡⇒≡ xs≋ys))
                               (S≈T ys))
  ; ▷-identity = λ xs → ≡⇒Pointwise-≡ Eq.refl
  ; ▷-compose  = λ S T xs → ≡⇒Pointwise-≡ Eq.refl
  }

open VecEq Ob using (_≋_ ; ≋-refl)


------------------------------------------------------------------------
-- Lifting

-- A lifted circuit acts as the identity on wire 0 and as the unlifted
-- circuit on the rest: the generator action is head-preserving cons
-- (actg (g ↥) (x ∷ ps) = x ∷ actg g ps), and composition threads that
-- through.  This is SemInj's lift-act stated for _↑ rather than the
-- word-lift; SemInj's is private, so it is redone here.

head-fix : (h : Pauli1) (t : Pauli n) (w : Circuit n) →
           (ap ⟦ w ↑ ⟧ (h ∷ t)) ≋ (h ∷ ap ⟦ w ⟧ t)
head-fix h t [ g ]ʷ  = ≋-refl
head-fix h t ε       = ≋-refl
head-fix h t (w • v) = ≡⇒Pointwise-≡
  (Eq.trans (Eq.cong (ap ⟦ w ↑ ⟧) (Pointwise-≡⇒≡ (head-fix h t v)))
            (Pointwise-≡⇒≡ (head-fix h (ap ⟦ v ⟧ t) w)))


------------------------------------------------------------------------
-- The two coset obligations

-- Both are NF-Inj's lemmas verbatim: the coset is determined by the
-- head of its action on every state, and every tail arises as the
-- tail of its action, the action being a bijection.

c-inj : {c1 c2 : ML (₁₊ n)} →
        (∀ (ps : Pauli (₁₊ n)) →
           head (ap ⟦ [ c1 ]ᵐˡ ⟧ ps) ≡ head (ap ⟦ [ c2 ]ᵐˡ ⟧ ps)) →
        c1 ≡ c2
c-inj {n} {c1} {c2} = lemma-lm-head-inj c1 c2

c-surj : (c : ML (₁₊ n)) (qs : Pauli n) →
         Σ[ ps ∈ Pauli (₁₊ n) ] (tail (ap ⟦ [ c ]ᵐˡ ⟧ ps)) ≋ qs
c-surj c qs = proj₁ s , ≡⇒Pointwise-≡ (proj₂ s)
  where s = lemma-lm-tail-surj c qs


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

module Uniq =
  CU (λ n → ML (₁₊ n)) (λ {n} → Ic {n}) SympGate [_]ᵐˡ
     (λ n → Group.monoid (Sp-group n)) Symplectic.Base._SRel,_===_
     ⟦_⟧ mhomo Ob act′ head-fix
     (λ {n} {c1} {c2} → c-inj {n} {c1} {c2}) c-surj

open CosetNF (λ n → ML (₁₊ n)) (λ {n} → Ic {n}) SympGate [_]ᵐˡ
  using (NF ; inv-nf)

-- Semantic injectivity of the section, unpackaged.
open Uniq public using (⟦inv-nf⟧-injective)


------------------------------------------------------------------------
-- Transporting to Section's tower

-- Circuit.CosetNF's tower and Section's are the same recursion, but at
-- a VARIABLE width neither reduces, so the two are interchangeable
-- only propositionally.  toNF is the evident isomorphism, and it
-- commutes with the two sections, which carries the theorem over to
-- the NF the rest of the development uses.

toNF : ∀ {n} → NFˢ n → NF n
toNF {₀}    _       = _
toNF {₁₊ n} (u , c) = toNF u , c

private
  toNF-injective : ∀ {n} {u v : NFˢ n} → toNF u ≡ toNF v → u ≡ v
  toNF-injective {₀}    {_}     {_}      _  = Eq.refl
  toNF-injective {₁₊ n} {u , c} {v , c'} eq =
    ≡×≡⇒≡ (toNF-injective (Eq.cong proj₁ eq) , Eq.cong proj₂ eq)

  toNF-section : ∀ {n} (u : NFˢ n) → inv-nf (toNF u) ≡ [ u ]ˢ
  toNF-section {₀}    _       = Eq.refl
  toNF-section {₁₊ n} (u , c) =
    Eq.cong (λ w → w ↑ • [ c ]ᵐˡ) (toNF-section u)

-- Distinct normal forms denote distinct symplectic transformations —
-- the statement NF-Inj proves as ⟦[]⟧-injective, obtained here from
-- the generic machinery instead.
⟦[]⟧-injective : ∀ n {u v : NFˢ n} → ⟦ [ u ]ˢ ⟧ ≈ˢ ⟦ [ v ]ˢ ⟧ → u ≡ v
⟦[]⟧-injective n {u} {v} eq =
  toNF-injective (⟦inv-nf⟧-injective n claim)
  where
  claim : ⟦ inv-nf (toNF u) ⟧ ≈ˢ ⟦ inv-nf (toNF v) ⟧
  claim rewrite toNF-section u | toNF-section v = eq

-- Normal forms with equal denotations are equal.
unique-nf : ∀ n → let Sem = Group.setoid (Sp-group n) in

  NFU.UniqueNormalForm (n QRel,_===_) (NF n) Sem ⟦_⟧ (inv-nf {n})
  
unique-nf = Uniq.unique-nf
