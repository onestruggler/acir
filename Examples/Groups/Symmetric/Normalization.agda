------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Level using (0ℓ)

open import Relation.Binary using (Rel ; Setoid)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)

open import Function using (_∘_)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Unit using (⊤ ; tt)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open PP using (NormalFormWithoutInverse ; NormalForm)

import Presentation.CosetNF as CA
import Presentation.Reidemeister-Schreier as RS
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full
open import Presentation.GroupLike

open import Notations
import Presentation.Vertical-Syntactics

module Examples.Groups.Symmetric.Normalization where

private variable
  n :  ℕ
  
open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.Cosets

------------------------------------------------------------------------
-- Right coset action
--
-- ract : C (₁₊ n) → Gen (₂₊ n) → Circuit (₁₊ n) × C (₁₊ n)

ract : C (₁₊ n) → Gen (₂₊ n) → Circuit (₁₊ n) × C (₁₊ n)
ract {n}     ε         σ-gen       = ε , σ• ε
ract {n}     (σ• ε)    σ-gen       = ε , ε
ract {₁₊ n}  (σ• σ• c) σ-gen       = (σ {n = n}) , σ• σ• c
ract {n}     ε         (g ↥)       = [ g ]ʷ , ε
ract {0}     (σ• ε)    (gate₁ () ↥)
ract {0}     (σ• ε)    ((() ↥) ↥)
ract {₁₊ n}  (σ• c)    (g ↥)   = proj₁ (ract {n} c g) ↑ , σ• (proj₂ (ract {n} c g))

racts : C (₁₊ n) → Circuit (₂₊ n) → Circuit (₁₊ n) × C (₁₊ n)
racts {n} = ract {n} **

------------------------------------------------------------------------
-- lemma-ract: [c]ᶜ • [b]ʷ ≈ b' ↑ • [c']ᶜ  where (b', c') = ract c b

lemma-ract : ∀ {n} c b →
  let
    open PB ((₂₊ n) VRel,_===_)
    (b' , c') = ract {n} c b
  in
  
    [ c ]ᶜ • [ b ]ʷ ≈ b' ↑ • [ c' ]ᶜ
    
lemma-ract {n} ε σ-gen = cong refl (sym right-unit)
  where P = _VRel,_===_ (₂₊ n) ; open PB P
lemma-ract {n} (σ• ε) σ-gen =
  trans (cong right-unit refl)
               (trans (axiom (srel order)) (sym right-unit))
  where P = _VRel,_===_ (₂₊ n) ; open PB P ; open PP P
lemma-ract {n} ε (g ↥) =
  trans left-unit (sym right-unit)
  where P = _VRel,_===_ (₂₊ n) ; open PB P
lemma-ract {₁₊ n} (σ• σ• c) σ-gen = begin
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
lemma-ract {0} (σ• c) ((gate₁ ()) ↥)
lemma-ract {0} (σ• c) (((() ↥)) ↥)
lemma-ract {₁₊ n} (σ• ε) (b@σ-gen ↥) = begin
  [ σ• ε ]ᶜ • [ b ↥ ]ʷ ≈⟨ assoc ⟩
  σ • (ε • [ b ]ʷ) ↑ ≈⟨ cright (lemma-cong↑ (ε • [ b ]ʷ) (b0 ↑ • [ c0 ]ᶜ) ih) ⟩
  σ • (b0 ↑ • [ c0 ]ᶜ) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [ c0 ]ᶜ ↑) ≈⟨ sym assoc ⟩
  (σ • b0 ↑ ↑) • [ c0 ]ᶜ ↑ ≈⟨ cong (sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [ c0 ]ᶜ ↑ ≈⟨ assoc ⟩
  b0 ↑ ↑ • [ σ• c0 ]ᶜ ∎
  where
  P0 = _VRel,_===_ (₂₊ n)
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} ε b)
  c0 = proj₂ (ract {n} ε b)
  ih = lemma-ract {n} ε b
lemma-ract {₁₊ n} (σ• ε) (b@(b' ↥) ↥) = begin
  [ σ• ε ]ᶜ • [ b ↥ ]ʷ ≈⟨ assoc ⟩
  σ • (ε • [ b ]ʷ) ↑ ≈⟨ cong refl (lemma-cong↑ (ε • [ b ]ʷ) (b0 ↑ • [ c0 ]ᶜ) ih) ⟩
  σ • (b0 ↑ • [ c0 ]ᶜ) ↑ ≡⟨ Eq.refl ⟩
  σ • (b0 ↑ ↑ • [ c0 ]ᶜ ↑) ≈⟨ sym assoc ⟩
  (σ • b0 ↑ ↑) • [ c0 ]ᶜ ↑ ≈⟨ cong (sym (lemma-comm b0)) refl ⟩
  (b0 ↑ ↑ • σ) • [ c0 ]ᶜ ↑ ≈⟨ assoc ⟩
  b0 ↑ ↑ • [ σ• c0 ]ᶜ ∎
  where
  P0 = _VRel,_===_ (₂₊ n)
  P  = _VRel,_===_ (₃₊ n)
  open PB P
  open PP P
  open SR word-setoid
  b0 = proj₁ (ract {n} ε b)
  c0 = proj₂ (ract {n} ε b)
  ih = lemma-ract {n} ε b
  
lemma-ract {₁₊ n} (σ• σ• c) (b@σ-gen ↥) = begin
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
  ih = lemma-ract {n} (σ• c) b
lemma-ract {₁₊ n} (σ• σ• c) (b@(bb ↥) ↥) = begin
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
  ih = lemma-ract {n} (σ• c) b

------------------------------------------------------------------------
-- lemma-racts: extends lemma-ract to words

lemma-racts : ∀ {n} c bs →
  let
    open PB ((₂₊ n) VRel,_===_)
    (bs' , c') = racts {n} c bs
  in
    [ c ]ᶜ • bs ≈ bs' ↑ • [ c' ]ᶜ
    
lemma-racts {n} c [ x ]ʷ = lemma-ract c x
lemma-racts {n} c ε = trans right-unit (sym left-unit)
  where P = _VRel,_===_ (₂₊ n) ; open PB P
lemma-racts {n} c (bs • as) with racts c bs | lemma-racts c bs
... | (bs' , c') | ih1 with racts c' as | lemma-racts c' as
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
-- ≋  : pointwise relation on (Circuit (₁₊ n) × C (₁₊ n))

infix 4 _≋_
_≋_ : Rel (Circuit (₁₊ n) × C (₁₊ n)) 0ℓ
_≋_ {n} = let _≈₀_ = PB._≈_ ((₁₊ n) VRel,_===_) in Pointwise _≈₀_ (_≡_ {A = C (₁₊ n)})

------------------------------------------------------------------------
-- ⁻¹[⇑]-gen': inverse of the generator embedding

⁻¹[⇑]-gen' : let _⊛_ = ract ** in ∀ (x : Gen (₁₊ n)) →
  ([ x ]ʷ , ε) ≋ ε ⊛ [ x ↥ ]ʷ
⁻¹[⇑]-gen' {n} x = PB.refl , Eq.refl

------------------------------------------------------------------------
-- Auxiliary ract-computation lemmas (all Eq.refl by definition)

lemma-ract-suc : ∀ {n} w → racts {n} ε (w ↑) ≡ (w , ε)
lemma-ract-suc {n} [ x ]ʷ = Eq.refl
lemma-ract-suc {n} ε       = Eq.refl
lemma-ract-suc {n} (w • v) with lemma-ract-suc {n} w
... | ih with lemma-ract-suc {n} v
... | ih' with racts ε (w ↑)
... | (w' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih
                       | Eq.cong proj₁ ih' | Eq.cong proj₂ ih'
              with racts ε (v ↑)
... | (v' , ev) = begin w • v , ε ≡⟨ Eq.refl ⟩ (w • v , ε) ∎
  where open ≡-Reasoning

lemma-ract-suc' : ∀ {n} w → (ract {n} **) ε (w ↑) ≡ (w , ε)
lemma-ract-suc' {n} [ x ]ʷ = Eq.refl
lemma-ract-suc' {n} ε       = Eq.refl
lemma-ract-suc' {n} (w • v) with lemma-ract-suc' {n} w
... | ih with lemma-ract-suc' {n} v
... | ih' with racts ε (w ↑)
... | (w' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih
                       | Eq.cong proj₁ ih' | Eq.cong proj₂ ih'
              with racts ε (v ↑)
... | (v' , ev) = begin w • v , ε ≡⟨ Eq.refl ⟩ (w • v , ε) ∎
  where open ≡-Reasoning

-- The auxiliary sub-computation is racts ε (w ↑ ↑) rather than racts ε
-- (w ↑) because case 7 contributes ract {n} ε (x ↥ ↥), not ract {n} ε
-- (x ↥), when the outer implicit is ₁₊ n.
lemma-ract-suc''' : ∀ {n} (w : Circuit n) → (ract {₁₊ n} **) (σ• ε) (w ↑ ↑ ↑) ≡ (w ↑ ↑ , σ• ε)
lemma-ract-suc''' {n} [ x ]ʷ = Eq.refl
lemma-ract-suc''' {n} ε       = Eq.refl
lemma-ract-suc''' {n} (w • v) with lemma-ract-suc''' {n} w
... | ih with lemma-ract-suc''' {n} v
... | ih' with racts ε (w ↑ ↑)
... | (w'' , ew) rewrite Eq.cong proj₁ ih | Eq.cong proj₂ ih
                        | Eq.cong proj₁ ih' | Eq.cong proj₂ ih'
               with racts ε (v ↑ ↑)
... | (v'' , ev) = begin w ↑ ↑ • v ↑ ↑ , σ• ε ≡⟨ Eq.refl ⟩ (w ↑ ↑ • v ↑ ↑ , σ• ε) ∎
  where open ≡-Reasoning

lemma-ract-σ•σ•σ : ∀ {n} (c : C n) →
  racts (σ• σ• c) σ ≡ (σ , σ• σ• c)
lemma-ract-σ•σ•σ {n} c = Eq.refl

lemma-ract-σ•1 : ∀ {n} (c : C (₁₊ n)) (g : Gen (₂₊ n)) →
  let (b' , c') = ract {n} c g
  in ract (σ• c) (g ↥) ≡ (b' ↑ , σ• c')
lemma-ract-σ•1 {n} ε       σ-gen   = Eq.refl
lemma-ract-σ•1 {n} ε       (g' ↥)  = Eq.refl
lemma-ract-σ•1 {n} (σ• c') σ-gen   = Eq.refl
lemma-ract-σ•1 {n} (σ• c') (g' ↥)  = Eq.refl

lemma-ract-σ•1s : ∀ {n} (c : C (₁₊ n)) w →
  let (w' , c') = (ract {n} **) c w
  in (ract {₁₊ n} **) (σ• c) (w ↑) ≡ (w' ↑ , σ• c')
lemma-ract-σ•1s {n} c [ x ]ʷ = lemma-ract-σ•1 c x
lemma-ract-σ•1s {n} c ε       = Eq.refl
lemma-ract-σ•1s {n} c (w • v)
  with lemma-ract-σ•1s c w | (ract **) c w | inspect ((ract **) c) w
... | ih1 | w' , c0 | [ eq1 ]ₑ rewrite ih1 | eq1
  with lemma-ract-σ•1s c0 v | (ract **) c0 v | inspect ((ract **) c0) v
... | ih2 | v' , c1 | [ eq2 ]ₑ rewrite eq2 | Eq.cong proj₁ ih2 | Eq.cong proj₂ ih2 = Eq.refl
  where open ≡-Reasoning

-- ract {n} (σ• ε) ((g ↥) ↥) ≡ ([g ↥]ʷ , σ• ε)
-- Case 7 needs implicit ≥ 1; n=0 is vacuous since Gen 0 = ∅
lemma-ract-σ•ε-gg↥ : ∀ {n} (g : Gen n) → ract {n} (σ• ε) (g ↥ ↥) ≡ ([ g ↥ ]ʷ , σ• ε)
lemma-ract-σ•ε-gg↥ {zero}  ()
lemma-ract-σ•ε-gg↥ {₁₊ n} g = Eq.refl

------------------------------------------------------------------------
-- ⁻¹[⇑]-wd'': coset action respects raw relations

⁻¹[⇑]-wd'' : ∀ {n} →
  let _⊛_ = ract ** in
  let _===_ = (₂₊ n) VRel,_===_ in
  ∀ (c : C (₁₊ n)){u t : Circuit (₂₊ n)} →
  
    u === t → c ⊛ u ≋ c ⊛ t

-- ε coset
⁻¹[⇑]-wd'' {n} ε (srel order)
  = PB.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} ε (comm₂ σ-gate g)
  rewrite lemma-ract-σ•ε-gg↥ g
  = PB.trans PB.right-unit (PB.sym PB.left-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} ε (srel yang-baxter)
  = PB.trans PB.left-unit
      (PB.trans PB.left-unit
        (PB.trans (PB.sym PB.right-unit)
          (PB.cong PB.refl (PB.sym PB.left-unit))))
  , Eq.refl
⁻¹[⇑]-wd'' {n} ε (cong↑ {w = w} {v} eq)
  rewrite lemma-ract-suc' {n} w | lemma-ract-suc' {n} v
  = PB.axiom eq , Eq.refl

-- σ• ε coset
⁻¹[⇑]-wd'' {n} (σ• ε) (srel order)
  = PB.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (comm₂ σ-gate g)
  rewrite lemma-ract-σ•ε-gg↥ g
  = PB.trans PB.right-unit (PB.sym PB.left-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (srel yang-baxter)
  = PB.refl , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (srel order))
  = PB.left-unit , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (comm₂ σ-gate g))
  rewrite lemma-ract-σ•ε-gg↥ g
  = PB.trans PB.right-unit (PB.sym PB.left-unit) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (srel yang-baxter))
  = PB.trans PB.left-unit
      (PB.trans PB.left-unit
        (PB.trans (PB.sym PB.right-unit)
          (PB.cong PB.refl (PB.sym PB.left-unit))))
  , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (srel order)))
  rewrite lemma-ract-σ•1 {₁₊ n} ε σ-gen
  = PB.axiom (cong↑ (srel order)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (comm₂ σ-gate g)))
  = PB.axiom (cong↑ (comm₂ σ-gate g)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (srel yang-baxter)))
  rewrite lemma-ract-σ•1 {₁₊ n} ε σ-gen
  = PB.axiom (cong↑ (srel yang-baxter)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• ε) (cong↑ (cong↑ (cong↑ {w = w} {v} eq)))
  rewrite lemma-ract-suc''' w | lemma-ract-suc''' v
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
  rewrite lemma-ract-σ•σ•σ c | lemma-ract-σ•1 (σ• c) (g ↥) | lemma-ract-σ•1 c g
  = lemma-comm (proj₁ (ract c g)) , Eq.refl
⁻¹[⇑]-wd'' {n} (σ• σ•_ {n₁} c) (cong↑ {w = w} {v} eq)
  with ⁻¹[⇑]-wd'' (σ• c) eq
... | (wv , eq0)
  rewrite lemma-ract-σ•1s (σ• c) w | lemma-ract-σ•1s (σ• c) v
  = lemma-cong↑ _ _ wv , Eq.cong σ•_ eq0

------------------------------------------------------------------------
-- Tower instantiation (via Presentation.CosetNF.CosetTower)
--
-- Sₙ is built by iterating the single-level coset extension: level
-- (₂₊ k) extends level (₁₊ k) by the cosets C (₁₊ k), with right
-- action ract.  Below we package that single-level data as an
-- Extension and fold it up the tower.

module T = CA.CosetTower (λ k → Gen (₁₊ k)) (λ k → _VRel,_===_ (₁₊ k)) (λ k → C (₁₊ k))

ext : ∀ k → T.Extension k
ext k = record
  { I         = ε
  ; f         = [_]ʷ ∘ _↥
  ; h         = ract
  ; [_]       = [_]ᶜ
  ; h=⁻¹f-gen = ⁻¹[⇑]-gen'
  ; h-wd-ax   = ⁻¹[⇑]-wd''
  ; f-wd-ax   = λ x → Eq.subst₂ _≈_ (Eq.sym (lemma-* _)) (Eq.sym (lemma-* _))
                                (PB.axiom (cong↑ x))
  ; [I]≈ε     = _≈_.refl
  ; h=ract    = λ c b →
      Eq.subst (λ x → _≈_ ([ c ]ᶜ • [ b ]ʷ) (x • [ ract c b .proj₂ ]ᶜ))
               (Eq.sym (lemma-* (ract c b .proj₁)))
               (lemma-ract c b)
  }
  where
  open PB (_VRel,_===_ (₂₊ k))
  open PP (_VRel,_===_ (₂₊ k))

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

nfp'-t : ∀ n → NormalForm (_VRel,_===_ n)
nfp'-t 0       = base0'
nfp'-t (suc k) = T.nfp'-tower ext base1' k

------------------------------------------------------------------------
-- Normal form, its inverse, and the NormalFormWithoutInverse witnesses
--
-- nf-of, inv-nf and NF are the coset tower's canonical normal-form
-- data.  Note inv-nf uses the word-lift (f *) rather than _↑; the two
-- agree up to Word.Properties.lemma-*.

NF : ℕ → Set
NF n = NormalForm.NF (nfp'-t n)

nf-of : Circuit n → NF n
nf-of {n} = NormalForm.nf (nfp'-t n)

inv-nf : NF n → Circuit n
inv-nf {n} = NormalForm.inv-nf (nfp'-t n)

nfp : (n : ℕ) → NormalFormWithoutInverse (_VRel,_===_ n)
nfp n = NormalForm.hasNormalFormWithoutInverse (nfp'-t n)

lemma-nf-cong : ∀ {n} → let _≈_ = PB._≈_ (_VRel,_===_ n) in
  Homomorphic₂ _≈_ _≡_ (nf-of {n})
lemma-nf-cong {n} = NormalForm.nf-cong (nfp'-t n)

lemma-inv-nf : (n : ℕ) → let _≈_ = PB._≈_ (_VRel,_===_ n) in {w : Circuit n} →
  inv-nf {n} (nf-of w) ≈ w
lemma-inv-nf n = NormalForm.inv-nf∘nf=id (nfp'-t n)

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
