------------------------------------------------------------------------
-- Presentations of groups
--
-- The multi-qudit symplectic Clifford group and its normal form via
-- coset enumeration (Reidemeister–Schreier), built on the coset action
-- of Normalization.Pushing.PushML.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

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
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
open NFBase using (NormalFormInjective ; NormalForm)
import Normalization.CosetNF as CosetNF

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Data.Sum
open import Data.Vec using (Vec ; [] ; _∷_ ; replicate)

import Examples.Groups.Symplectic.Normalization.Pushing.PushML p-2 p-prime as PushML
open import Examples.Groups.Symplectic.Normalization.Pushing.DH p-2 p-prime using (aux-mc1ε)
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime using (lemma-order-Ex-n)
open import Algebra.Properties.Ring (+-*-ring p-2) using (-0#≈0#)

private variable
  n : ℕ

C = ML

------------------------------------------------------------------------
-- Right coset action (proved in PushML)

-- The right action of a generator on a coset: ract c g returns the
-- residual circuit b' and the coset c' reached, so that
-- [ c ]ᶜ • [ g ]ʷ ≈ b' ↑ • [ c' ]ᶜ.
ract : ∀ {n} → C (₁₊ n) → Gen (₁₊ n) → Circuit n × C (₁₊ n)
ract = PushML.ract

[_]ᶜ : ∀ {n} → C (₁₊ n) → Circuit (₁₊ n)
[_]ᶜ = [_]ᵐˡ

ract-sound : ∀ {n} c g →
  let open PB ((₁₊ n) QRel,_===_)
      (b' , c') = ract {n} c g
  in [ c ]ᶜ • [ g ]ʷ ≈ b' ↑ • [ c' ]ᶜ
ract-sound = PushML.ract-sound

------------------------------------------------------------------------
-- Pointwise relation on action results
--
-- Presentation equivalence on the residual circuit component,
-- propositional equality on the coset component.
infix 4 _≋_
_≋_ : Rel (Circuit n × C (₁₊ n)) 0ℓ
_≋_ {n} = let _≈₀_ = PB._≈_ (n QRel,_===_)
          in Pointwise _≈₀_ (_≡_ {A = C (₁₊ n)})

------------------------------------------------------------------------
-- The identity coset and the two Extension obligations that are NOT
-- generic (well-definedness on the axioms is the completeness content).
--
-- SCAFFOLD: I, [I]≈ε, the generator-inverse property, and the axiom
-- well-definedness are stated with their final types and left as holes
-- to be discharged.

-- The identity coset: the ML box interpreting to ε.
-- (Boxes are Fin 3 × Fin 3 / Fin 3.  The all-zero box + identity A box is
-- a PLACEHOLDER value — the actual identity representative is pinned down
-- when discharging [I]≈ε' below.)
Ia : A
Ia = (₀ , ₁) , λ ()

Iᶜ : ∀ {n} → C (₁₊ n)
Iᶜ {zero}  = ([] , ₀) , ([] , Ia)
Iᶜ {suc m} = inj₁ ((replicate (₁₊ m) (₀ , ₀) , ₀) , (replicate (₁₊ m) (₀ , ₀) , Ia))

-- The identity A box interprets to ε: [ Ia ]ᵃ = M ((₁,λ())⁻¹) • ⟦ε⟧ₕₛ,
-- and (₁,λ())⁻¹ has value ₁ (inv-₁), so aux-MM + aux-mc1ε finish.
[Ia]≈ε : ∀ {n} → let open PB ((₁₊ n) QRel,_===_) in [ Ia ]ᵃ ≈ ε
[Ia]≈ε {n} = trans (cong (aux-MM (((₁ , λ ()) ⁻¹) .proj₂) (λ ()) inv-₁) refl) aux-mc1ε
  where open PB ((₁₊ n) QRel,_===_) ; open Lemmas0 n

-- Zero boxes reduce to ε / Ex (the CZ^/CX'^/S^ powers vanish; -0 ≡ 0).
[₀]ᵉ≈ε : ∀ {n} → let open PB ((₁₊ n) QRel,_===_) in [_]ᵉ {n} ₀ ≈ ε
[₀]ᵉ≈ε {n} = refl' (Eq.cong S^ -0#≈0#)
  where open PB ((₁₊ n) QRel,_===_)

[₀]ᵈ≈Ex : ∀ {n} → let open PB ((₂₊ n) QRel,_===_) in [_]ᵈ {n} (₀ , ₀) ≈ Ex
[₀]ᵈ≈Ex {n} = trans (cright (refl' (Eq.cong CZ^ -0#≈0#))) right-unit
  where open PB ((₂₊ n) QRel,_===_)

[₀]ᵇ≈Ex : ∀ {n} → let open PB ((₂₊ n) QRel,_===_) in [_]ᵇ {n} (₀ , ₀) ≈ Ex
[₀]ᵇ≈Ex {n} = trans (cright (cright left-unit)) (trans (cright H3H≈ε) right-unit)
  where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_)
  H3H≈ε : H ^ 3 • H ≈ ε
  H3H≈ε = trans (sym (^-+ H 3 1)) (axiom order-H)

-- All-zero M column · all-zero B vector telescopes to ε: at each level a
-- D-box Ex pairs with a B-box Ex (Ex² ≈ ε), leaving the shorter product.
aux-MB : ∀ {k} → let open PB ((₁₊ k) QRel,_===_) in
  [ (replicate k (₀ , ₀) , ₀) ]ᵐ • [ replicate k (₀ , ₀) ]ᵛᵇ ≈ ε
aux-MB {zero} = trans right-unit [₀]ᵉ≈ε
  where open PB (1 QRel,_===_)
aux-MB {suc m} = begin
  ([ (₀ , ₀) ]ᵈ • [ (dv , ₀) ]ᵐ ↑) • ([ dv ]ᵛᵇ ↑ • [ (₀ , ₀) ]ᵇ)
    ≈⟨ cong refl (cright [₀]ᵇ≈Ex) ⟩
  ([ (₀ , ₀) ]ᵈ • [ (dv , ₀) ]ᵐ ↑) • ([ dv ]ᵛᵇ ↑ • Ex)
    ≈⟨ cong (cleft [₀]ᵈ≈Ex) refl ⟩
  (Ex • [ (dv , ₀) ]ᵐ ↑) • ([ dv ]ᵛᵇ ↑ • Ex)              ≈⟨ assoc ⟩
  Ex • ([ (dv , ₀) ]ᵐ ↑ • ([ dv ]ᵛᵇ ↑ • Ex))             ≈⟨ cright (sym assoc) ⟩
  Ex • (([ (dv , ₀) ]ᵐ ↑ • [ dv ]ᵛᵇ ↑) • Ex)
    ≈⟨ cright (cleft (lemma-cong↑ _ _ (aux-MB {m}))) ⟩
  Ex • (ε • Ex)                                           ≈⟨ cright left-unit ⟩
  Ex • Ex                                                 ≈⟨ lemma-order-Ex-n ⟩
  ε ∎
  where
  open PB ((₂₊ m) QRel,_===_) ; open PP ((₂₊ m) QRel,_===_) ; open SR word-setoid
  dv = replicate m (₀ , ₀)

-- Its interpretation is the identity word.
[I]≈ε' : ∀ {n} → let open PB ((₁₊ n) QRel,_===_) in [ Iᶜ {n} ]ᶜ ≈ ε
[I]≈ε' {zero}  = trans (sym assoc) (trans (cleft aux-MB) (trans left-unit [Ia]≈ε))
  where open PB (1 QRel,_===_) ; open PP (1 QRel,_===_)
[I]≈ε' {suc m} = trans (sym assoc) (trans (cleft aux-MB) (trans left-unit [Ia]≈ε))
  where open PB ((₂₊ m) QRel,_===_) ; open PP ((₂₊ m) QRel,_===_)

-- Acting on the identity coset by an embedded generator recovers the
-- generator itself.
⁻¹[⇑]-gen' : ∀ {n} (x : Gen n) →
  _≋_ {n} ([ x ]ʷ , Iᶜ {n}) ((ract {n} ᵗ) (Iᶜ {n}) ([ x ↥ ]ʷ))
⁻¹[⇑]-gen' {n} x = {!!}

-- Well-definedness: the coset action respects the raw relations.  This
-- is the Reidemeister–Schreier completeness obligation for the
-- symplectic presentation (order-{S,H,SH,CZ}, comm-HHS, M-mul,
-- semi-{MS,M↑CZ,M↓CZ}, comm-CZ-S{↓,↑}, selinger-c10..c15, and the
-- structural cong↑/comm₁/comm₂).  Discharged case-by-case below.
⁻¹[⇑]-wd'' : ∀ {n} →
  let _===_ = (₁₊ n) QRel,_===_ in
  ∀ (c : C (₁₊ n)) {u t : Circuit (₁₊ n)} →
    u === t → (ract {n} ᵗ) c u ≋ (ract {n} ᵗ) c t
⁻¹[⇑]-wd'' {n} c eq = {!!}

------------------------------------------------------------------------
-- Tower instantiation (via Normalization.CosetNF.CosetTower)
--
-- Spₙ is built by iterating the single-level coset extension: level
-- (₁₊ k) extends level k by the cosets C (₁₊ k) = ML (₁₊ k), with right
-- action ract.  The alphabet at level k is Gen k, so the tower starts
-- from the empty Gen 0.

module T = CosetNF.CosetTower
  (λ k → Gen k) (λ k → k QRel,_===_) (λ k → C (₁₊ k))

ext : ∀ k → T.Extension k
ext k = record
  { I         = Iᶜ {k}
  ; f         = [_]ʷ ∘ _↥
  ; h         = ract
  ; [_]       = [_]ᶜ
  ; h=⁻¹f-gen = ⁻¹[⇑]-gen'
  ; h-wd-ax   = ⁻¹[⇑]-wd''
  ; f-wd-ax   = λ x → Eq.subst₂ _≈_ (Eq.sym (wconcatmap-[f]ʷ _)) (Eq.sym (wconcatmap-[f]ʷ _))
                                (PB.axiom (cong↑ x))
  ; [I]≈ε     = [I]≈ε'
  ; h=ract    = λ c b →
      Eq.subst (λ x → _≈_ ([ c ]ᶜ • [ b ]ʷ) (x • [ ract c b .proj₂ ]ᶜ))
               (Eq.sym (wconcatmap-[f]ʷ (ract c b .proj₁)))
               (ract-sound c b)
  }
  where
  open PB ((₁₊ k) QRel,_===_)
  open PP ((₁₊ k) QRel,_===_)

-- Sp₀ is trivial: Gen 0 is empty, so ⊤ is the normal form and every
-- word collapses to ε.
base0' : NormalForm (0 QRel,_===_) ⊤
base0' = record
  { rightInverse = record
      { to        = λ _ → tt
      ; from      = λ _ → ε
      ; to-cong   = λ _ → Eq.refl
      ; from-cong = λ { Eq.refl → refl }
      ; inverseʳ  = λ { Eq.refl → sym singleton }
      }
  }
  where
  open PB (0 QRel,_===_)
  singleton : ∀ {a} → a ≈ ε
  singleton {[ () ]ʷ}
  singleton {ε}      = PB.refl
  singleton {a • a₁} = PB.trans (PB.cong singleton singleton) PB.left-unit

-- The main construction: a normal form for every Spₙ, obtained by
-- folding the Extension up the coset tower from the trivial base.
NFᵗ : ℕ → Set
NFᵗ n = T.tower-carrier ⊤ n

nfp'-t : ∀ n → NormalForm (n QRel,_===_) (NFᵗ n)
nfp'-t n = T.nfp'-tower ext base0' n

------------------------------------------------------------------------
-- Normal form, its inverse, and the NormalFormInjective witnesses

nf-of : Circuit n → NFᵗ n
nf-of {n} = SNF.NormalForm.nf (nfp'-t n)

inv-nf : NFᵗ n → Circuit n
inv-nf {n} = SNF.NormalForm.inv-nf (nfp'-t n)

nfp : (n : ℕ) → NormalFormInjective (n QRel,_===_) (NFᵗ n)
nfp n = SNF.NormalForm.normalFormInjective (nfp'-t n)

nf-cong : ∀ {n} → let _≈_ = PB._≈_ (n QRel,_===_) in
  Homomorphic₂ _≈_ _≡_ (nf-of {n})
nf-cong {n} = SNF.NormalForm.nf-cong (nfp'-t n)

inv-nf∘nf≈id : (n : ℕ) → let _≈_ = PB._≈_ (n QRel,_===_) in {w : Circuit n} →
  inv-nf {n} (nf-of w) ≈ w
inv-nf∘nf≈id n = SNF.NormalForm.inv-nf∘nf=id (nfp'-t n)
