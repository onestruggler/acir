------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical forms for three-wire circuits: an even signed permutation
-- followed by one of the 135 frame representatives.  The normalization
-- produces derivations in the 1185-equation circuit theory.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.NormalForm where

open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_ ; _ʷ)
open import Presentation.GroupLike using (module Group-Lemmas)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH.Syntactics using (Circuit)
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Derived {8} as Source
import Examples.Groups.CCX+HH.ThreeQubit.Presentation as P
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerNormalForm as B
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerPresentation as Base
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerFaithfulness as Faithful
import Examples.Groups.CCX+HH.ThreeQubit.Compact.Presentation as Compact
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (b)
open import Examples.Groups.CCX+HH.ThreeQubit.Cosets using (Coset ; c000 ; rep)
open import Examples.Groups.CCX+HH.ThreeQubit.Separation using (separate)

private
  module R = PB P._===_
  module A = PB (T._===_ {8})
  module G = Group-Lemmas (T._===_ {8}) Source.grouplike

NF : Set
NF = B.NF × Coset

section : NF → Circuit 3
section (q , c) = P.Theory.decode (B.section q) • rep c

nf : Circuit 3 → NF
nf w = Base.nf (P.Theory.output c000 w) , P.Theory.state c000 w

normalize : ∀ w → w R.≈ section (nf w)
normalize w = R.trans (P.normalization w)
  (R.cong (P.Theory.base-lift
    (Compact.derive (Base.normalize (P.Theory.output c000 w)))) R.refl)

private
  source-section : ∀ q c → E.encode (section (q , c)) A.≈
    (b ʷ) (B.section q) • E.encode (rep c)
  source-section q c = A.cong (P.Theory.decode-correct (B.section q)) A.refl

unique : ∀ {x y} → section x R.≈ section y → x ≡ y
unique {q , c} {r , d} eq = Eq.cong₂ _,_ base-eq state-eq
  where
  expanded : (b ʷ) (B.section q) • E.encode (rep c) A.≈
             (b ʷ) (B.section r) • E.encode (rep d)
  expanded = A.trans (A.sym (source-section q c))
    (A.trans (P.Theory.encode-cong eq) (source-section r d))

  state-eq : c ≡ d
  state-eq = separate c d (B.section q) (B.section r) expanded

  base-eq : q ≡ r
  base-eq = Faithful.separate (G.•-cancelʳ
    (A.trans expanded (A.cong A.refl
      (A.refl' (Eq.cong (λ s → E.encode (rep s)) (Eq.sym state-eq))))))

nf-section : ∀ x → nf (section x) ≡ x
nf-section x = Eq.sym (unique (normalize (section x)))

nf-cong : ∀ {u v} → u R.≈ v → nf u ≡ nf v
nf-cong {u} {v} eq = unique
  (R.trans (R.sym (normalize u)) (R.trans eq (normalize v)))

nf-complete : ∀ {u v} → nf u ≡ nf v → u R.≈ v
nf-complete {u} {v} eq = R.trans (normalize u)
  (R.trans (R.refl' (Eq.cong section eq)) (R.sym (normalize v)))

semantic-unique : ∀ {x y} → C.interpret (section x) ≡ C.interpret (section y) → x ≡ y
semantic-unique {x} {y} eq = unique {x} {y}
  (P.completeness {u = section x} {v = section y} eq)
