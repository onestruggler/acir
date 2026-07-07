------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Normalization where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
open import Relation.Nullary.Decidable using (yes ; no)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Base as NFBase
open NFBase using (NormalFormWithoutInverse ; NormalForm)
import Normalization.CosetNF as CosetNF

open import Notations

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.Cosets

private variable
  n : ℕ

------------------------------------------------------------------------
-- Right coset action

-- The right action of a generator on a coset: ract c b returns the
-- residual circuit b' and the coset c' reached from c by b, so that
-- [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ (see ract-sound below).
ract : C (₁₊ n) → Gen (₂₊ n) → Circuit (₁₊ n) × C (₁₊ n)
ract {n}     ε         σ-gen       = ε , σ• ε
ract {n}     (σ• ε)    σ-gen       = ε , ε
ract {₁₊ n}  (σ• σ• c) σ-gen       = (σ {n = n}) , σ• σ• c
ract {n}     ε         (g ↥)       = [ g ]ʷ , ε
ract {0}     (σ• ε)    (gate₁ () ↥)
ract {0}     (σ• ε)    ((() ↥) ↥)
ract {₁₊ n}  (σ• c)    (g ↥)   = proj₁ (ract {n} c g) ↑ , σ• (proj₂ (ract {n} c g))

-- Extension of ract to whole circuits: the stateful fold _** threads
-- the coset through the word.
racts : C (₁₊ n) → Circuit (₂₊ n) → Circuit (₁₊ n) × C (₁₊ n)
racts {n} = ract {n} **

------------------------------------------------------------------------
-- Soundness of the coset action

-- ract-sound certifies the coset-table transition: for
-- (b' , c') = ract c b we have [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ.
ract-sound : ∀ {n} c b →
  let
    open PB ((₂₊ n) VRel,_===_)
    (b' , c') = ract {n} c b
  in

    [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ

ract-sound {n} ε σ-gen = cong refl (sym right-unit)
  where
  P = _VRel,_===_ (₂₊ n)
  open PB P
ract-sound {n} (σ• ε) σ-gen =
  trans (cong right-unit refl)
        (trans (axiom (srel order)) (sym right-unit))
  where
  P = _VRel,_===_ (₂₊ n)
  open PB P
  open PP P
ract-sound {n} ε (g ↥) =
  trans left-unit (sym right-unit)
  where
  P = _VRel,_===_ (₂₊ n)
  open PB P
ract-sound {₁₊ n} (σ• σ• c) σ-gen = begin
  [ σ• σ• c ]ᶜ • σ ≈⟨ assoc ⟩
  σ • [ σ• c ]ᶜ ↑ • σ ≡⟨ Eq.refl ⟩
  σ • (σ ↑ • [ c ]ᶜ ↑ ↑) • σ ≈⟨ cong refl assoc ⟩
  σ • σ ↑ • [ c ]ᶜ ↑ ↑ • σ ≈⟨ cong refl (cong refl (lemma-comm ([ c ]ᶜ))) ⟩
  σ • σ ↑ • σ • [ c ]ᶜ ↑ ↑ ≈⟨ sym (cong refl assoc) ⟩
  σ • (σ ↑ • σ) • [ c ]ᶜ ↑ ↑ ≈⟨ sym assoc ⟩
  (σ • (σ ↑ • σ)) • [ c ]ᶜ ↑ ↑ ≈⟨ cong (axiom (srel yang-baxter)) refl ⟩
  (σ ↑ • σ • σ ↑) • [ c ]ᶜ ↑ ↑ ≈⟨ trans assoc (cong refl assoc) ⟩
  σ ↑ • σ • σ ↑ • [ c ]ᶜ ↑ ↑ ≡⟨ Eq.refl ⟩
  σ ↑ • σ • [ σ• c ]ᶜ ↑ ∎
  where
  P = (₃₊ n) VRel,_===_
  open PB P
  open PP P
  open SR word-setoid
ract-sound {0} (σ• c) ((gate₁ ()) ↥)
ract-sound {0} (σ• c) (((() ↥)) ↥)
ract-sound {₁₊ n} (σ• ε) (b@σ-gen ↥) = begin
  [ σ• ε ]ᶜ • [ b ↥ ]ʷ ≈⟨ assoc ⟩
  σ • (ε • [ b ]ʷ) ↑ ≈⟨ cright (lemma-cong↑ (ε • [ b ]ʷ) (b0 ↑ • [ c0 ]ᶜ) ih) ⟩
  σ • (b0 ↑ • [ c0 ]ᶜ) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [ c0 ]ᶜ ↑) ≈⟨ sym assoc ⟩
  (σ • b0 ↑ ↑) • [ c0 ]ᶜ ↑ ≈⟨ cong (sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [ c0 ]ᶜ ↑ ≈⟨ assoc ⟩
  b0 ↑ ↑ • [ σ• c0 ]ᶜ ∎
  where
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} ε b)
  c0 = proj₂ (ract {n} ε b)
  ih = ract-sound {n} ε b
ract-sound {₁₊ n} (σ• ε) (b@(b' ↥) ↥) = begin
  [ σ• ε ]ᶜ • [ b ↥ ]ʷ ≈⟨ assoc ⟩
  σ • (ε • [ b ]ʷ) ↑ ≈⟨ cong refl (lemma-cong↑ (ε • [ b ]ʷ) (b0 ↑ • [ c0 ]ᶜ) ih) ⟩
  σ • (b0 ↑ • [ c0 ]ᶜ) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [ c0 ]ᶜ ↑) ≈⟨ sym assoc ⟩
  (σ • b0 ↑ ↑) • [ c0 ]ᶜ ↑ ≈⟨ cong (sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [ c0 ]ᶜ ↑ ≈⟨ assoc ⟩
  b0 ↑ ↑ • [ σ• c0 ]ᶜ ∎
  where
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} ε b)
  c0 = proj₂ (ract {n} ε b)
  ih = ract-sound {n} ε b

ract-sound {₁₊ n} (σ• σ• c) (b@σ-gen ↥) = begin
  [ σ• σ• c ]ᶜ • [ b ↥ ]ʷ ≈⟨ assoc ⟩
  σ • ([ σ• c ]ᶜ • [ b ]ʷ) ↑ ≈⟨ cong refl (lemma-cong↑ _ _ ih) ⟩
  σ • (b0 ↑ • [ c0 ]ᶜ) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [ c0 ]ᶜ ↑) ≈⟨ sym assoc ⟩
  (σ • b0 ↑ ↑) • [ c0 ]ᶜ ↑ ≈⟨ cong (sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [ c0 ]ᶜ ↑ ≈⟨ assoc ⟩
  b0 ↑ ↑ • [ σ• c0 ]ᶜ ∎
  where
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} (σ• c) b)
  c0 = proj₂ (ract {n} (σ• c) b)
  ih = ract-sound {n} (σ• c) b
ract-sound {₁₊ n} (σ• σ• c) (b@(bb ↥) ↥) = begin
  [ σ• σ• c ]ᶜ • [ b ↥ ]ʷ ≈⟨ assoc ⟩
  σ • ([ σ• c ]ᶜ • [ b ]ʷ) ↑ ≈⟨ cong refl (lemma-cong↑ _ _ ih) ⟩
  σ • (b0 ↑ • [ c0 ]ᶜ) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [ c0 ]ᶜ ↑) ≈⟨ sym assoc ⟩
  (σ • b0 ↑ ↑) • [ c0 ]ᶜ ↑ ≈⟨ cong (sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [ c0 ]ᶜ ↑ ≈⟨ assoc ⟩
  b0 ↑ ↑ • [ σ• c0 ]ᶜ ∎
  where
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} (σ• c) b)
  c0 = proj₂ (ract {n} (σ• c) b)
  ih = ract-sound {n} (σ• c) b

------------------------------------------------------------------------
-- Soundness of the coset action on words

-- racts-sound extends ract-sound from generators to circuits.
racts-sound : ∀ {n} c bs →
  let
    open PB ((₂₊ n) VRel,_===_)
    (bs' , c') = racts {n} c bs
  in
    [ c ]ᶜ • bs ≈ bs' ↑ • [ c' ]ᶜ

racts-sound {n} c [ x ]ʷ = ract-sound c x
racts-sound {n} c ε = trans right-unit (sym left-unit)
  where
  P = _VRel,_===_ (₂₊ n)
  open PB P
racts-sound {n} c (bs • as) with racts c bs | racts-sound c bs
... | (bs' , c') | ih1 with racts c' as | racts-sound c' as
... | (as' , c'') | ih2 = begin
  [ c ]ᶜ • (bs • as) ≈⟨ sym assoc ⟩
  ([ c ]ᶜ • bs) • as ≈⟨ cong ih1 refl ⟩
  (bs' ↑ • [ c' ]ᶜ) • as ≈⟨ assoc ⟩
  bs' ↑ • [ c' ]ᶜ • as ≈⟨ cong refl ih2 ⟩
  bs' ↑ • as' ↑ • [ c'' ]ᶜ ≈⟨ sym assoc ⟩
  (bs' • as') ↑ • [ c'' ]ᶜ ∎
  where
  P = (₂₊ n) VRel,_===_
  open PB P
  open PP P
  open SR word-setoid

------------------------------------------------------------------------
-- Pointwise relation on action results

-- Presentation equivalence on the circuit component, propositional
-- equality on the coset component.
infix 4 _≋_
_≋_ : Rel (Circuit (₁₊ n) × C (₁₊ n)) 0ℓ
_≋_ {n} = let _≈₀_ = PB._≈_ ((₁₊ n) VRel,_===_)
          in Pointwise _≈₀_ (_≡_ {A = C (₁₊ n)})

------------------------------------------------------------------------
-- Inverse of the generator embedding

-- Acting on the trivial coset by an embedded generator recovers the
-- generator itself.
⁻¹[⇑]-gen' : let _⊛_ = ract ** in ∀ (x : Gen (₁₊ n)) →
  ([ x ]ʷ , ε) ≋ ε ⊛ [ x ↥ ]ʷ
⁻¹[⇑]-gen' {n} x = PB.refl , Eq.refl

------------------------------------------------------------------------
-- Auxiliary computation lemmas for the coset action

-- Acting on the trivial coset by a lifted circuit strips one lift and
-- leaves the coset fixed.
ract-suc' : ∀ {n} w → (ract {n} **) ε (w ↑) ≡ (w , ε)
ract-suc' {n} [ x ]ʷ = Eq.refl
ract-suc' {n} ε       = Eq.refl
ract-suc' {n} (w • v) with ract-suc' {n} w
... | ih with ract-suc' {n} v
... | ih' with racts ε (w ↑)
... | (w' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih
                       | Eq.cong proj₁ ih' | Eq.cong proj₂ ih'
              with racts ε (v ↑)
... | (v' , ev) = begin w • v , ε ≡⟨ Eq.refl ⟩ (w • v , ε) ∎
  where open ≡-Reasoning

-- Acting on the coset σ• ε by a triply lifted circuit strips one lift
-- and leaves the coset fixed.  The recursive sub-computation is
-- racts ε (w ↑ ↑) rather than racts ε (w ↑): on a coset σ• c the
-- action peels only the outermost lift before recursing, so each
-- generator still carries two lifts when it reaches the trivial coset.
ract-suc''' : ∀ {n} (w : Circuit n) →
  (ract {₁₊ n} **) (σ• ε) (w ↑ ↑ ↑) ≡ (w ↑ ↑ , σ• ε)
ract-suc''' {n} [ x ]ʷ = Eq.refl
ract-suc''' {n} ε       = Eq.refl
ract-suc''' {n} (w • v) with ract-suc''' {n} w
... | ih with ract-suc''' {n} v
... | ih' with racts ε (w ↑ ↑)
... | (w'' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih
                        | Eq.cong proj₁ ih' | Eq.cong proj₂ ih'
               with racts ε (v ↑ ↑)
... | (v'' , ev) = begin w ↑ ↑ • v ↑ ↑ , σ• ε ≡⟨ Eq.refl ⟩ (w ↑ ↑ • v ↑ ↑ , σ• ε) ∎
  where open ≡-Reasoning

-- The generator σ passes through any coset of the form σ• σ• c
-- unchanged, leaving the coset fixed.
ract-σ•σ•σ : ∀ {n} (c : C n) →
  racts (σ• σ• c) σ ≡ (σ , σ• σ• c)
ract-σ•σ•σ {n} c = Eq.refl

-- Acting on σ• c by a lifted generator lifts the result of acting on
-- c by the generator itself.
ract-σ•1 : ∀ {n} (c : C (₁₊ n)) (g : Gen (₂₊ n)) →
  let (b' , c') = ract {n} c g
  in ract (σ• c) (g ↥) ≡ (b' ↑ , σ• c')
ract-σ•1 {n} ε       σ-gen   = Eq.refl
ract-σ•1 {n} ε       (g' ↥)  = Eq.refl
ract-σ•1 {n} (σ• c') σ-gen   = Eq.refl
ract-σ•1 {n} (σ• c') (g' ↥)  = Eq.refl

-- Word version of ract-σ•1: acting on σ• c by a lifted circuit
-- lifts the result of acting on c.
ract-σ•1s : ∀ {n} (c : C (₁₊ n)) w →
  let (w' , c') = (ract {n} **) c w
  in (ract {₁₊ n} **) (σ• c) (w ↑) ≡ (w' ↑ , σ• c')
ract-σ•1s {n} c [ x ]ʷ = ract-σ•1 c x
ract-σ•1s {n} c ε       = Eq.refl
ract-σ•1s {n} c (w • v)
  with ract-σ•1s c w | (ract **) c w | inspect ((ract **) c) w
... | ih1 | w' , c0 | [ eq1 ]ₑ rewrite ih1 | eq1
  with ract-σ•1s c0 v | (ract **) c0 v | inspect ((ract **) c0) v
... | ih2 | v' , c1 | [ eq2 ]ₑ rewrite eq2 | Eq.cong proj₁ ih2 | Eq.cong proj₂ ih2 = Eq.refl

-- A doubly lifted generator passes through the coset σ• ε unchanged.
-- The n = 0 case is vacuous since Gen 0 is empty; for n ≥ 1 the
-- equation holds by definition.
ract-σ•ε-gg↥ : ∀ {n} (g : Gen n) →
  ract {n} (σ• ε) (g ↥ ↥) ≡ ([ g ↥ ]ʷ , σ• ε)
ract-σ•ε-gg↥ {zero}  ()
ract-σ•ε-gg↥ {₁₊ n} g = Eq.refl

------------------------------------------------------------------------
-- Well-definedness of the coset action

-- The coset action respects the raw relations: acting on a coset by
-- two axiom-related circuits yields ≋-related results.
⁻¹[⇑]-wd'' : ∀ {n} →
  let _⊛_ = ract ** in
  let _===_ = (₂₊ n) VRel,_===_ in
  ∀ (c : C (₁₊ n)){u t : Circuit (₂₊ n)} →

    u === t → c ⊛ u ≋ c ⊛ t

-- ε coset
⁻¹[⇑]-wd'' {n} ε (srel order)
  = PB.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} ε (comm₂ σ-gate g)
  rewrite ract-σ•ε-gg↥ g
  = PB.trans PB.right-unit (PB.sym PB.left-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} ε (srel yang-baxter)
  = PB.trans PB.left-unit
      (PB.trans PB.left-unit
        (PB.trans (PB.sym PB.right-unit)
          (PB.cong PB.refl (PB.sym PB.left-unit))))
  , Eq.refl
⁻¹[⇑]-wd'' {n} ε (cong↑ {w = w} {v} eq)
  rewrite ract-suc' {n} w | ract-suc' {n} v
  = PB.axiom eq , Eq.refl

-- σ• ε coset
⁻¹[⇑]-wd'' {n} (σ• ε) (srel order)
  = PB.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (comm₂ σ-gate g)
  rewrite ract-σ•ε-gg↥ g
  = PB.trans PB.right-unit (PB.sym PB.left-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (srel yang-baxter)
  = PB.refl , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (srel order))
  = PB.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (comm₂ σ-gate g))
  rewrite ract-σ•ε-gg↥ g
  = PB.trans PB.right-unit (PB.sym PB.left-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (srel yang-baxter))
  = PB.trans PB.left-unit
      (PB.trans PB.left-unit
        (PB.trans (PB.sym PB.right-unit)
          (PB.cong PB.refl (PB.sym PB.left-unit))))
  , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (srel order)))
  rewrite ract-σ•1 {₁₊ n} ε σ-gen
  = PB.axiom (cong↑ (srel order)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (comm₂ σ-gate g)))
  = PB.axiom (cong↑ (comm₂ σ-gate g)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (srel yang-baxter)))
  rewrite ract-σ•1 {₁₊ n} ε σ-gen
  = PB.axiom (cong↑ (srel yang-baxter)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (cong↑ {w = w} {v} eq)))
  rewrite ract-suc''' w | ract-suc''' v
  = PB.axiom (cong↑ (cong↑ eq)) , Eq.refl

-- σ• σ• c coset
⁻¹[⇑]-wd'' {n} (σ• σ• c) (srel order)
  = PB.axiom (srel order) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• σ•_ {n₁} ε) (srel yang-baxter)
  = PB.trans (PB.cong PB.refl PB.right-unit)
      (PB.trans PB.right-unit
        (PB.trans (PB.sym PB.left-unit)
          (PB.cong PB.refl (PB.sym PB.left-unit))))
  , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• σ•_ {n₁} (σ• c)) (srel yang-baxter)
  = PB.axiom (srel yang-baxter) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• σ•_ {zero}   c) (comm₂ σ-gate (gate₁ ()))
⁻¹[⇑]-wd'' {n} (σ• σ•_ {zero}   c) (comm₂ σ-gate (() ↥))
⁻¹[⇑]-wd'' {n} (σ• σ•_ {₁₊ m} c) (comm₂ σ-gate g)
  rewrite ract-σ•1 c g
  = lemma-comm (proj₁ (ract c g)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• σ•_ {n₁} c) (cong↑ {w = w} {v} eq)
  with ⁻¹[⇑]-wd'' (σ• c) eq
... | (wv , eq0)
  rewrite ract-σ•1s (σ• c) w | ract-σ•1s (σ• c) v
  = lemma-cong↑ _ _ wv , Eq.cong σ•_ eq0

------------------------------------------------------------------------
-- Tower instantiation (via Normalization.CosetNF.CosetTower)
--
-- Sₙ is built by iterating the single-level coset extension: level
-- (₂₊ k) extends level (₁₊ k) by the cosets C (₁₊ k), with right
-- action ract.  Below we package that single-level data as an
-- Extension and fold it up the tower.

module T = CosetNF.CosetTower
  (λ k → Gen (₁₊ k)) (λ k → _VRel,_===_ (₁₊ k)) (λ k → C (₁₊ k))

ext : ∀ k → T.Extension k
ext k = record
  { I         = ε
  ; f         = [_]ʷ ∘ _↥
  ; h         = ract
  ; [_]       = [_]ᶜ
  ; h=⁻¹f-gen = ⁻¹[⇑]-gen'
  ; h-wd-ax   = ⁻¹[⇑]-wd''
  ; f-wd-ax   = λ x → Eq.subst₂ _≈_ (Eq.sym (wconcatmap-[f]ʷ _)) (Eq.sym (wconcatmap-[f]ʷ _))
                                (PB.axiom (cong↑ x))
  ; [I]≈ε     = _≈_.refl
  ; h=ract    = λ c b →
      Eq.subst (λ x → _≈_ ([ c ]ᶜ • [ b ]ʷ) (x • [ ract c b .proj₂ ]ᶜ))
               (Eq.sym (wconcatmap-[f]ʷ (ract c b .proj₁)))
               (ract-sound c b)
  }
  where
  open PB (_VRel,_===_ (₂₊ k))
  open PP (_VRel,_===_ (₂₊ k))

-- S₀ is trivial: Gen 0 is empty, so ⊤ is the normal form and
-- singleton collapses every word to ε.
base0' : NormalForm (_VRel,_===_ 0)
base0' = record
  { NF           = ⊤
  ; nf           = λ _ → tt
  ; nf-cong      = λ _ → Eq.refl
  ; inv-nf       = λ _ → ε
  ; inv-nf∘nf=id = λ {w} → sym (singleton {w})
  }
  where
  open PB (_VRel,_===_ 0)
  singleton : ∀ {a} → a ≈ ε
  singleton {ε}      = PB.refl
  singleton {a • a₁} = PB.trans (PB.cong singleton singleton) PB.left-unit

-- S₁ is trivial as well: Gen 1 has no inhabitants, so every word
-- again collapses to ε.
base1' : NormalForm (_VRel,_===_ 1)
base1' = record
  { NF           = ⊤
  ; nf           = λ _ → tt
  ; nf-cong      = λ _ → Eq.refl
  ; inv-nf       = λ _ → ε
  ; inv-nf∘nf=id = λ {w} → sym (singleton {w})
  }
  where
  open PB (_VRel,_===_ 1)
  singleton : ∀ {a} → a ≈ ε
  singleton {[ gate₁ () ]ʷ}
  singleton {[ () ↥ ]ʷ}
  singleton {ε}      = PB.refl
  singleton {a • a₁} = PB.trans (PB.cong singleton singleton) PB.left-unit

-- The main construction: a normal form for every Sₙ, obtained by
-- folding the Extension up the coset tower from the trivial base
-- cases.
nfp'-t : ∀ n → NormalForm (_VRel,_===_ n)
nfp'-t 0       = base0'
nfp'-t (suc k) = T.nfp'-tower ext base1' k

------------------------------------------------------------------------
-- Normal form, its inverse, and the NormalFormWithoutInverse witnesses
--
-- nf-of, inv-nf and NF are the coset tower's canonical normal-form
-- data.  Note inv-nf uses the word-lift (f *) rather than _↑; the two
-- agree up to Word.Properties.wconcatmap-[f]ʷ.

NF : ℕ → Set
NF n = NormalForm.NF (nfp'-t n)

nf-of : Circuit n → NF n
nf-of {n} = NormalForm.nf (nfp'-t n)

inv-nf : NF n → Circuit n
inv-nf {n} = NormalForm.inv-nf (nfp'-t n)

nfp : (n : ℕ) → NormalFormWithoutInverse (_VRel,_===_ n)
nfp n = NormalForm.hasNormalFormWithoutInverse (nfp'-t n)

nf-cong : ∀ {n} → let _≈_ = PB._≈_ (_VRel,_===_ n) in
  Homomorphic₂ _≈_ _≡_ (nf-of {n})
nf-cong {n} = NormalForm.nf-cong (nfp'-t n)

inv-nf∘nf≈id : (n : ℕ) → let _≈_ = PB._≈_ (_VRel,_===_ n) in {w : Circuit n} →
  inv-nf {n} (nf-of w) ≈ w
inv-nf∘nf≈id n = NormalForm.inv-nf∘nf=id (nfp'-t n)

------------------------------------------------------------------------
-- Decidable equality on normal forms

deceq : DecidableEquality (NF n)
deceq {zero}    tt      tt       = yes Eq.refl
deceq {₁₊ zero} tt      tt       = yes Eq.refl
deceq {₂₊ n}   (a , b) (a' , b') with deceq {₁₊ n} a a' | deceqC b b'
... | yes p1 | yes p2 = yes (≡×≡⇒≡ (p1 , p2))
... | yes p1 | no  p2 = no (λ { x → p2 (proj₂ (≡⇒≡×≡ x)) })
... | no  p1 | yes p2 = no (λ { x → p1 (proj₁ (≡⇒≡×≡ x)) })
... | no  p1 | no  p2 = no (λ { x → p2 (proj₂ (≡⇒≡×≡ x)) })
