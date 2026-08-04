-- Part of the Examples.Groups.Symplectic.ExtendedGate.NF-Inj split (memory-reduced typechecking).
-- --safe omitted while the 4 head-injectivity lemmas remain postulated.
-- (call-by-need: --call-by-name omitted; these proof-heavy modules typecheck
--  far faster and with less memory under the default sharing strategy.)
{-# OPTIONS --cubical-compatible --termination-depth=4 #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (no)


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW using (≡×≡⇒≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Maybe hiding (zipWith ; map)
open import Data.Sum using (inj₁ ; inj₂ ; [_,_] ; [_,_]′)
open import Data.Unit using (tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Data.Fin using (toℕ ; zero)
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting using ()
open import Data.Nat.Primality



module Examples.Groups.Symplectic.ExtendedGate.NF-Inj-Base (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
open Symplectic-Derived-Gen renaming (M to ZM)
open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.BoxAction p-2 p-prime
open Normal-Form1

private
  variable
    n : ℕ
    
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.ExtendedGate.NF2 p-2 p-prime
open LM2
open ≡-Reasoning
open Eq hiding ([_])

-- head/tail reconstruction (local copy of Examples.Groups.Symplectic.NF.lemma-aux-vec).
lemma-aux-vec : ∀ {A : Set} n (v : Vec A (₁₊ n)) → head v ∷ tail v ≡ v
lemma-aux-vec {A} ₀ (x ∷ v) = auto
lemma-aux-vec {A} (₁₊ n) (x ∷ v) = auto

-- act fixes pIₙ (local copy of Examples.Groups.Symplectic.NF.lemma-actw-pIₙ).
lemma-actw-pIₙ : ∀ {n} w → act w pIₙ ≡ pIₙ {n}
lemma-actw-pIₙ {n} [ gate₁ (H-gen ₀) ]ʷ = auto
lemma-actw-pIₙ {n} [ gate₁ (H-gen ₁) ]ʷ = Eq.cong₂ _∷_ (≡×≡⇒≡ (-0#≈0# , auto)) auto
lemma-actw-pIₙ {n} [ gate₁ (H-gen ₂) ]ʷ = Eq.cong₂ _∷_ (≡×≡⇒≡ (-0#≈0# , -0#≈0#)) auto
lemma-actw-pIₙ {n} [ gate₁ (H-gen ₃) ]ʷ = Eq.cong₂ _∷_ (≡×≡⇒≡ (auto , -0#≈0#)) auto
lemma-actw-pIₙ {n} [ gate₁ (S-gen k) ]ʷ = auto
lemma-actw-pIₙ {n} [ gate₂ (CZ-gen k) ]ʷ = auto
lemma-actw-pIₙ {n} [ x ↥ ]ʷ = Eq.cong₂ _∷_ auto (lemma-actw-pIₙ [ x ]ʷ)
lemma-actw-pIₙ {n} ε = auto
lemma-actw-pIₙ {n} (w • w₁) = begin
  act w (act w₁ pIₙ) ≡⟨ Eq.cong (act w) (lemma-actw-pIₙ w₁) ⟩
  act w (pIₙ) ≡⟨ lemma-actw-pIₙ w ⟩
  pIₙ ∎
  where
  open ≡-Reasoning

-- Sub-postulates for lemma-lm-head-inj.
postulate
  -- n=2: ML 2 elements are distinguished by head of Pauli action.
  lemma-cosets2-head-inj : ∀ (lm₁ lm₂ : ML 2) →
    (∀ (ps : Pauli 2) → head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)) → lm₁ ≡ lm₂

  -- The M×L' branch (inj₁) and D×LM branch (inj₂) produce distinct head outputs.
  lemma-lm-inj₁≁inj₂ : ∀ {n} (m : M (₃₊ n)) (l : L' (₃₊ n)) (d : D) (lm' : ML (₂₊ n)) →
    (∀ ps → head (act ([ m ]ᵐ • [ l ]ˡ') ps) ≡ head (act ([ d ]ᵈ • [ lm' ]ᵐˡ ↑) ps)) → ⊥

  -- M×L' action is head-injective.
  lemma-ml-head-inj : ∀ {n} (m₁ m₂ : M (₃₊ n)) (l₁ l₂ : L' (₃₊ n)) →
    (∀ ps → head (act ([ m₁ ]ᵐ • [ l₁ ]ˡ') ps) ≡ head (act ([ m₂ ]ᵐ • [ l₂ ]ˡ') ps)) →
    m₁ ≡ m₂ × l₁ ≡ l₂

-- D-box pZ-prefix, pI second entry. (Vector-level proof: head only at the end,
-- to avoid forcing full act-normalization of the M-box word.)
lemma-dbox-pZ-pI : ∀ {n} (d : D) (t : Pauli n) →
  head (act [ d ]ᵈ (pZ ∷ pI ∷ t)) ≡ (₀ , d .proj₁)
lemma-dbox-pZ-pI {n} (₀ , dv) t = Eq.cong head (begin
  act [ ₀ , dv ]ᵈ (pZ ∷ pI ∷ t) ≡⟨ auto ⟩
  act Ex ((₀ , ₁ + ₀ * (- dv)) ∷ (₀ , ₀ + ₀ * (- dv)) ∷ t)
    ≡⟨ Eq.cong (act Ex) auxP ⟩
  act Ex ((₀ , ₁) ∷ (₀ , ₀) ∷ t) ≡⟨ lemma-act-Ex (₀ , ₁) (₀ , ₀) t ⟩
  (₀ , ₀) ∷ (₀ , ₁) ∷ t ∎)
  where
  auxP : ((₀ , ₁ + ₀ * (- dv)) ∷ (₀ , ₀ + ₀ * (- dv)) ∷ t) ≡ ((₀ , ₁) ∷ (₀ , ₀) ∷ t)
  auxP = Eq.cong₂ (λ s1 s2 → (₀ , s1) ∷ (₀ , s2) ∷ t)
           (Eq.trans (Eq.cong (₁ +_) (*-zeroˡ (- dv))) (+-identityʳ ₁))
           (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ (- dv))) (+-identityʳ ₀))
lemma-dbox-pZ-pI {n} (c@(₁₊ c') , dv) t = Eq.cong head (begin
  act [ c , dv ]ᵈ (pZ ∷ pI ∷ t) ≡⟨ auto ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ , HS^ -dv/c ⟧ₘ₊) (pZ ∷ pI ∷ t)
    ≡⟨ Eq.cong (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ)) (lemma-HS-x -dv/c ₀ ₁ (pI ∷ t)) ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- (₁ + ₀ * -dv/c) , ₀) ∷ pI ∷ t)
    ≡⟨ Eq.cong (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ)) auxA ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- ₁ , ₀) ∷ pI ∷ t)
    ≡⟨ Eq.cong (act [ ₀ , ₁ ]ᵈ) (lemma-M (- ₁) ₀ (pI ∷ t) ((c , λ ()) ⁻¹)) ⟩
  act [ ₀ , ₁ ]ᵈ ((- ₁ * c⁻¹⁻¹ , ₀ * c⁻¹) ∷ pI ∷ t)
    ≡⟨ Eq.cong (act [ ₀ , ₁ ]ᵈ) auxB ⟩
  act [ ₀ , ₁ ]ᵈ ((- c , ₀) ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
  act Ex ((- c , ₀ + ₀ * (- ₁)) ∷ (₀ , ₀ + (- c) * (- ₁)) ∷ t)
    ≡⟨ Eq.cong (act Ex) auxC ⟩
  act Ex ((- c , ₀) ∷ (₀ , c) ∷ t) ≡⟨ lemma-act-Ex (- c , ₀) (₀ , c) t ⟩
  (₀ , c) ∷ (- c , ₀) ∷ t ∎)
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  c⁻¹⁻¹ = (((c , λ ()) ⁻¹) ⁻¹) .proj₁
  -dv/c = - dv * c⁻¹
  auxA : ((- (₁ + ₀ * -dv/c) , ₀) ∷ pI ∷ t) ≡ ((- ₁ , ₀) ∷ pI ∷ t)
  auxA = Eq.cong (λ s → (s , ₀) ∷ pI ∷ t)
           (Eq.cong -_ (Eq.trans (Eq.cong (₁ +_) (*-zeroˡ -dv/c)) (+-identityʳ ₁)))
  auxB : ((- ₁ * c⁻¹⁻¹ , ₀ * c⁻¹) ∷ pI ∷ t) ≡ ((- c , ₀) ∷ (₀ , ₀) ∷ t)
  auxB = Eq.cong (λ q → q ∷ pI ∷ t)
           (≡×≡⇒≡ (Eq.trans (-1*x≈-x c⁻¹⁻¹) (Eq.cong -_ (inv-involutive (c , λ ()))) , *-zeroˡ c⁻¹))
  auxC : ((- c , ₀ + ₀ * (- ₁)) ∷ (₀ , ₀ + (- c) * (- ₁)) ∷ t) ≡ ((- c , ₀) ∷ (₀ , c) ∷ t)
  auxC = Eq.cong₂ (λ s1 s2 → (- c , s1) ∷ (₀ , s2) ∷ t)
           (Eq.trans (Eq.cong (₀ +_) (*-zeroˡ (- ₁))) (+-identityʳ ₀))
           (Eq.trans (+-identityˡ ((- c) * (- ₁))) (Eq.trans (*-comm (- c) (- ₁)) (Eq.trans (-1*x≈-x (- c)) (-‿involutive c))))

-- D-box pX-prefix, pI second entry.
lemma-dbox-pX-pI : ∀ {n} (d : D) (t : Pauli n) →
  head (act [ d ]ᵈ (pX ∷ pI ∷ t)) ≡ (₀ , - d .proj₂)
lemma-dbox-pX-pI {n} (₀ , dv) t = Eq.cong head (begin
  act [ ₀ , dv ]ᵈ (pX ∷ pI ∷ t) ≡⟨ auto ⟩
  act Ex ((₁ , ₀ + ₀ * (- dv)) ∷ (₀ , ₀ + ₁ * (- dv)) ∷ t)
    ≡⟨ lemma-act-Ex (₁ , ₀ + ₀ * (- dv)) (₀ , ₀ + ₁ * (- dv)) t ⟩
  (₀ , ₀ + ₁ * (- dv)) ∷ (₁ , ₀ + ₀ * (- dv)) ∷ t
    ≡⟨ Eq.cong (λ s → (₀ , s) ∷ (₁ , ₀ + ₀ * (- dv)) ∷ t) (Eq.trans (+-identityˡ (₁ * (- dv))) (*-identityˡ (- dv))) ⟩
  (₀ , - dv) ∷ (₁ , ₀ + ₀ * (- dv)) ∷ t ∎)
lemma-dbox-pX-pI {n} (c@(₁₊ c') , dv) t = Eq.cong head (begin
  act [ c , dv ]ᵈ (pX ∷ pI ∷ t) ≡⟨ auto ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ , HS^ -dv/c ⟧ₘ₊) (pX ∷ pI ∷ t)
    ≡⟨ Eq.cong (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ)) (lemma-HS-x -dv/c ₁ ₀ (pI ∷ t)) ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- (₀ + ₁ * -dv/c) , ₁) ∷ pI ∷ t)
    ≡⟨ Eq.cong (act [ ₀ , ₁ ]ᵈ) (lemma-M (- (₀ + ₁ * -dv/c)) ₁ (pI ∷ t) ((c , λ ()) ⁻¹)) ⟩
  act [ ₀ , ₁ ]ᵈ ((- (₀ + ₁ * -dv/c) * c⁻¹⁻¹ , ₁ * c⁻¹) ∷ pI ∷ t)
    ≡⟨ Eq.cong (act [ ₀ , ₁ ]ᵈ) auxB ⟩
  act [ ₀ , ₁ ]ᵈ ((dv , c⁻¹) ∷ (₀ , ₀) ∷ t) ≡⟨ auto ⟩
  act Ex ((dv , c⁻¹ + ₀ * (- ₁)) ∷ (₀ , ₀ + dv * (- ₁)) ∷ t)
    ≡⟨ Eq.cong (act Ex) auxC ⟩
  act Ex ((dv , c⁻¹) ∷ (₀ , - dv) ∷ t) ≡⟨ lemma-act-Ex (dv , c⁻¹) (₀ , - dv) t ⟩
  (₀ , - dv) ∷ (dv , c⁻¹) ∷ t ∎)
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  c⁻¹⁻¹ = (((c , λ ()) ⁻¹) ⁻¹) .proj₁
  -dv/c = - dv * c⁻¹
  eqA : - (₀ + ₁ * -dv/c) * c⁻¹⁻¹ ≡ dv
  eqA = Eq.trans (Eq.cong (λ w → - w * c⁻¹⁻¹) (Eq.trans (+-identityˡ (₁ * -dv/c)) (*-identityˡ -dv/c)))
        (Eq.trans (Eq.cong (_* c⁻¹⁻¹) (Eq.trans (Eq.cong -_ (Eq.sym (-‿distribˡ-* dv c⁻¹))) (-‿involutive (dv * c⁻¹))))
        (Eq.trans (Eq.cong (dv * c⁻¹ *_) (inv-involutive (c , λ ())))
        (Eq.trans (*-assoc dv c⁻¹ c)
        (Eq.trans (Eq.cong (dv *_) (Eq.trans (*-comm c⁻¹ c) (lemma-⁻¹ʳ c {{nztoℕ {y = c} {neq0 = λ ()}}})))
        (*-identityʳ dv)))))
  auxB : ((- (₀ + ₁ * -dv/c) * c⁻¹⁻¹ , ₁ * c⁻¹) ∷ pI ∷ t) ≡ ((dv , c⁻¹) ∷ (₀ , ₀) ∷ t)
  auxB = Eq.cong (λ q → q ∷ pI ∷ t) (≡×≡⇒≡ (eqA , *-identityˡ c⁻¹))
  auxC : ((dv , c⁻¹ + ₀ * (- ₁)) ∷ (₀ , ₀ + dv * (- ₁)) ∷ t) ≡ ((dv , c⁻¹) ∷ (₀ , - dv) ∷ t)
  auxC = Eq.cong₂ (λ s1 s2 → (dv , s1) ∷ (₀ , s2) ∷ t)
           (Eq.trans (Eq.cong (c⁻¹ +_) (*-zeroˡ (- ₁))) (+-identityʳ c⁻¹))
           (Eq.trans (+-identityˡ (dv * (- ₁))) (Eq.trans (*-comm dv (- ₁)) (-1*x≈-x dv)))

-- D-box pZ-transparency.
lemma-dbox-pZ-head : ∀ {n} (d : D) (q : Pauli1) (t : Pauli n) →
  head (act [ d ]ᵈ (pZ ∷ q ∷ t)) ≡ q +₁ (₀ , d .proj₁)
lemma-dbox-pZ-head {n} (₀ , dv) (qa , qb) t = Eq.cong head (begin
  act [ ₀ , dv ]ᵈ (pZ ∷ (qa , qb) ∷ t) ≡⟨ auto ⟩
  act Ex ((₀ , ₁ + qa * (- dv)) ∷ (qa , qb + ₀ * (- dv)) ∷ t)
    ≡⟨ lemma-act-Ex (₀ , ₁ + qa * (- dv)) (qa , qb + ₀ * (- dv)) t ⟩
  (qa , qb + ₀ * (- dv)) ∷ (₀ , ₁ + qa * (- dv)) ∷ t
    ≡⟨ Eq.cong (λ p → p ∷ (₀ , ₁ + qa * (- dv)) ∷ t) (≡×≡⇒≡ (Eq.sym (+-identityʳ qa) , Eq.cong (qb +_) (*-zeroˡ (- dv)))) ⟩
  (qa + ₀ , qb + ₀) ∷ (₀ , ₁ + qa * (- dv)) ∷ t ∎)
lemma-dbox-pZ-head {n} (c@(₁₊ c') , dv) (qa , qb) t = Eq.cong head (begin
  act [ c , dv ]ᵈ (pZ ∷ (qa , qb) ∷ t) ≡⟨ auto ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ , HS^ -dv/c ⟧ₘ₊) (pZ ∷ (qa , qb) ∷ t)
    ≡⟨ Eq.cong (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ)) (lemma-HS-x -dv/c ₀ ₁ ((qa , qb) ∷ t)) ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- (₁ + ₀ * -dv/c) , ₀) ∷ (qa , qb) ∷ t)
    ≡⟨ Eq.cong (act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ)) auxA ⟩
  act ([ ₀ , ₁ ]ᵈ • ⟦ (c , λ ()) ⁻¹ ⟧ₘ) ((- ₁ , ₀) ∷ (qa , qb) ∷ t)
    ≡⟨ Eq.cong (act [ ₀ , ₁ ]ᵈ) (lemma-M (- ₁) ₀ ((qa , qb) ∷ t) ((c , λ ()) ⁻¹)) ⟩
  act [ ₀ , ₁ ]ᵈ ((- ₁ * c⁻¹⁻¹ , ₀ * c⁻¹) ∷ (qa , qb) ∷ t)
    ≡⟨ Eq.cong (act [ ₀ , ₁ ]ᵈ) auxB ⟩
  act [ ₀ , ₁ ]ᵈ ((- c , ₀) ∷ (qa , qb) ∷ t) ≡⟨ auto ⟩
  act Ex ((- c , ₀ + qa * (- ₁)) ∷ (qa , qb + (- c) * (- ₁)) ∷ t)
    ≡⟨ lemma-act-Ex (- c , ₀ + qa * (- ₁)) (qa , qb + (- c) * (- ₁)) t ⟩
  (qa , qb + (- c) * (- ₁)) ∷ (- c , ₀ + qa * (- ₁)) ∷ t
    ≡⟨ Eq.cong (λ p → p ∷ (- c , ₀ + qa * (- ₁)) ∷ t) (≡×≡⇒≡ (Eq.sym (+-identityʳ qa) , Eq.cong (qb +_) eq3)) ⟩
  (qa + ₀ , qb + c) ∷ (- c , ₀ + qa * (- ₁)) ∷ t ∎)
  where
  c⁻¹ = ((c , λ ()) ⁻¹) .proj₁
  c⁻¹⁻¹ = (((c , λ ()) ⁻¹) ⁻¹) .proj₁
  -dv/c = - dv * c⁻¹
  auxA : ((- (₁ + ₀ * -dv/c) , ₀) ∷ (qa , qb) ∷ t) ≡ ((- ₁ , ₀) ∷ (qa , qb) ∷ t)
  auxA = Eq.cong (λ s → (s , ₀) ∷ (qa , qb) ∷ t)
           (Eq.cong -_ (Eq.trans (Eq.cong (₁ +_) (*-zeroˡ -dv/c)) (+-identityʳ ₁)))
  auxB : ((- ₁ * c⁻¹⁻¹ , ₀ * c⁻¹) ∷ (qa , qb) ∷ t) ≡ ((- c , ₀) ∷ (qa , qb) ∷ t)
  auxB = Eq.cong (λ p → p ∷ (qa , qb) ∷ t)
           (≡×≡⇒≡ (Eq.trans (-1*x≈-x c⁻¹⁻¹) (Eq.cong -_ (inv-involutive (c , λ ()))) , *-zeroˡ c⁻¹))
  eq3 : (- c) * (- ₁) ≡ c
  eq3 = Eq.trans (*-comm (- c) (- ₁)) (Eq.trans (-1*x≈-x (- c)) (-‿involutive c))

-- Right cancellation for componentwise addition on Pauli1.
+₁-cancelʳ : ∀ (x y c : Pauli1) → x +₁ c ≡ y +₁ c → x ≡ y
+₁-cancelʳ (a₁ , b₁) (a₂ , b₂) (c₁ , c₂) eq =
  ≡×≡⇒≡ (aux (cong proj₁ eq) , aux (cong proj₂ eq))
  where
  aux : ∀ {a b c : ℤ ₚ} → a + c ≡ b + c → a ≡ b
  aux {a} {b} {c} h = begin
    a             ≡⟨ sym (+-identityʳ a) ⟩
    a + ₀         ≡⟨ cong (a +_) (sym (+-inverseʳ c)) ⟩
    a + (c + - c) ≡⟨ sym (+-assoc a c (- c)) ⟩
    (a + c) + - c ≡⟨ cong (_+ - c) h ⟩
    (b + c) + - c ≡⟨ +-assoc b c (- c) ⟩
    b + (c + - c) ≡⟨ cong (b +_) (+-inverseʳ c) ⟩
    b + ₀         ≡⟨ +-identityʳ b ⟩
    b             ∎

-- Negation is injective: -a ≡ -b → a ≡ b.  (public: used by Examples.Groups.Symplectic.NF-Inj-LM)
neg-inj : ∀ (a b : ℤ ₚ) → - a ≡ - b → a ≡ b
neg-inj a b h = begin
  a     ≡⟨ sym (-‿involutive a) ⟩
  - - a ≡⟨ cong -_ h ⟩
  - - b ≡⟨ -‿involutive b ⟩
  b     ∎

------------------------------------------------------------------------
-- Helpers for the n=1 (ML 1) head-injectivity proof.

-- The A witness (a proof of ≢ (₀,₀)) is proof-irrelevant: functions into ⊥
-- are definitionally equal, so A-equality is determined by the first projection.
A-≡ : ∀ (a₁ a₂ : A) → a₁ .proj₁ ≡ a₂ .proj₁ → a₁ ≡ a₂
A-≡ (_ , _) (_ , _) refl = refl

-- Left multiplicative cancellation by a nonzero scalar.
*-cancelˡ-nz : ∀ (a x y : ℤ ₚ) (nz : a ≢ ₀) → a * x ≡ a * y → x ≡ y
*-cancelˡ-nz a x y nz eq = begin
  x               ≡⟨ sym (*-identityˡ x) ⟩
  ₁ * x           ≡⟨ cong (_* x) (sym (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = nz}}})) ⟩
  ainv * a * x    ≡⟨ *-assoc ainv a x ⟩
  ainv * (a * x)  ≡⟨ cong (ainv *_) eq ⟩
  ainv * (a * y)  ≡⟨ sym (*-assoc ainv a y) ⟩
  ainv * a * y    ≡⟨ cong (_* y) (lemma-⁻¹ˡ a {{nztoℕ {y = a} {neq0 = nz}}}) ⟩
  ₁ * y           ≡⟨ *-identityˡ y ⟩
  y ∎
  where
  ainv = ((a , nz) ⁻¹) .proj₁

-- act [ lm ]ᵐˡ for lm : ML 1 is a single-qudit map; its head is the whole entry.
-- Four evaluations pin the map down at pZ and pX for the two A-shapes.

-- x = ₀ branch (a = (₀ , ₁₊ y')).
hdZ0 : ∀ e y' (pr : (₀ , ₁₊ y') ≢ (₀ , ₀)) →
  head (act [ (([] , e) , ([] , ((₀ , ₁₊ y') , pr))) ]ᵐˡ (pZ ∷ [])) ≡ (₀ , ((₁₊ y' , λ ()) ⁻¹) .proj₁)
hdZ0 e y' pr = cong head (begin
  act [ (([] , e) , ([] , ((₀ , ₁₊ y') , pr))) ]ᵐˡ (pZ ∷ [])
    ≡⟨ auto ⟩
  act (S^ (- e)) (act (ZM inv) ((₀ , ₁) ∷ []))
    ≡⟨ cong (act (S^ (- e))) (lemma-M ₀ ₁ [] inv) ⟩
  act (S^ (- e)) ((₀ * inv⁻¹ , ₁ * xI) ∷ [])
    ≡⟨ auto ⟩
  ((₀ * inv⁻¹ , ₁ * xI + ₀ * inv⁻¹ * (- e)) ∷ [])
    ≡⟨ cong (_∷ []) (≡×≡⇒≡ (*-zeroˡ inv⁻¹ , simp)) ⟩
  ((₀ , xI) ∷ []) ∎)
  where
  inv = (₁₊ y' , λ ()) ⁻¹
  xI = inv .proj₁
  inv⁻¹ = (inv ⁻¹) .proj₁
  simp : ₁ * xI + ₀ * inv⁻¹ * (- e) ≡ xI
  simp = trans (cong₂ _+_ (*-identityˡ xI)
                          (trans (cong (_* (- e)) (*-zeroˡ inv⁻¹)) (*-zeroˡ (- e))))
               (+-identityʳ xI)

hdX0 : ∀ e y' (pr : (₀ , ₁₊ y') ≢ (₀ , ₀)) →
  head (act [ (([] , e) , ([] , ((₀ , ₁₊ y') , pr))) ]ᵐˡ (pX ∷ [])) ≡ (₁₊ y' , (₁₊ y') * (- e))
hdX0 e y' pr = cong head (begin
  act [ (([] , e) , ([] , ((₀ , ₁₊ y') , pr))) ]ᵐˡ (pX ∷ [])
    ≡⟨ auto ⟩
  act (S^ (- e)) (act (ZM inv) ((₁ , ₀) ∷ []))
    ≡⟨ cong (act (S^ (- e))) (lemma-M ₁ ₀ [] inv) ⟩
  act (S^ (- e)) ((₁ * inv⁻¹ , ₀ * xI) ∷ [])
    ≡⟨ auto ⟩
  ((₁ * inv⁻¹ , ₀ * xI + ₁ * inv⁻¹ * (- e)) ∷ [])
    ≡⟨ cong (_∷ []) (≡×≡⇒≡ (p1 , p2)) ⟩
  ((₁₊ y' , (₁₊ y') * (- e)) ∷ []) ∎)
  where
  inv = (₁₊ y' , λ ()) ⁻¹
  xI = inv .proj₁
  inv⁻¹ = (inv ⁻¹) .proj₁
  ii : inv⁻¹ ≡ ₁₊ y'
  ii = inv-involutive (₁₊ y' , λ ())
  p1 : ₁ * inv⁻¹ ≡ ₁₊ y'
  p1 = trans (*-identityˡ inv⁻¹) ii
  p2 : ₀ * xI + ₁ * inv⁻¹ * (- e) ≡ (₁₊ y') * (- e)
  p2 = trans (cong₂ _+_ (*-zeroˡ xI) (cong (_* (- e)) p1)) (+-identityˡ ((₁₊ y') * (- e)))

-- x ≠ ₀ branch (a = (₁₊ x' , y)).
hdZ1 : ∀ e x' y (pr : (₁₊ x' , y) ≢ (₀ , ₀)) →
  head (act [ (([] , e) , ([] , ((₁₊ x' , y) , pr))) ]ᵐˡ (pZ ∷ [])) ≡ (- (₁₊ x') , (₁₊ x') * e)
hdZ1 e x' y pr = cong head (begin
  act [ (([] , e) , ([] , ((₁₊ x' , y) , pr))) ]ᵐˡ (pZ ∷ [])
    ≡⟨ auto ⟩
  act (S^ (- e)) (act (ZM inv) (act (H • S^ k) ((₀ , ₁) ∷ [])))
    ≡⟨ cong (λ v → act (S^ (- e)) (act (ZM inv) v)) (lemma-HS-x k ₀ ₁ []) ⟩
  act (S^ (- e)) (act (ZM inv) ((- (₁ + ₀ * k) , ₀) ∷ []))
    ≡⟨ cong (act (S^ (- e))) (lemma-M (- (₁ + ₀ * k)) ₀ [] inv) ⟩
  act (S^ (- e)) ((- (₁ + ₀ * k) * inv⁻¹ , ₀ * xI) ∷ [])
    ≡⟨ auto ⟩
  ((- (₁ + ₀ * k) * inv⁻¹ , ₀ * xI + - (₁ + ₀ * k) * inv⁻¹ * (- e)) ∷ [])
    ≡⟨ cong (_∷ []) (≡×≡⇒≡ (q1 , q2)) ⟩
  ((- (₁₊ x') , (₁₊ x') * e) ∷ []) ∎)
  where
  inv = (₁₊ x' , λ ()) ⁻¹
  xI = inv .proj₁
  inv⁻¹ = (inv ⁻¹) .proj₁
  k = - y * xI
  ii : inv⁻¹ ≡ ₁₊ x'
  ii = inv-involutive (₁₊ x' , λ ())
  q1 : - (₁ + ₀ * k) * inv⁻¹ ≡ - (₁₊ x')
  q1 = trans (cong (λ z → - z * inv⁻¹) (trans (cong (₁ +_) (*-zeroˡ k)) (+-identityʳ ₁)))
             (trans (-1*x≈-x inv⁻¹) (cong -_ ii))
  q2 : ₀ * xI + - (₁ + ₀ * k) * inv⁻¹ * (- e) ≡ (₁₊ x') * e
  q2 = trans (cong₂ _+_ (*-zeroˡ xI) (cong (_* (- e)) q1))
             (trans (+-identityˡ (- (₁₊ x') * (- e)))
                    (trans (sym (-‿distribˡ-* (₁₊ x') (- e)))
                    (trans (cong -_ (sym (-‿distribʳ-* (₁₊ x') e)))
                           (-‿involutive ((₁₊ x') * e)))))

hdX1 : ∀ e x' y (pr : (₁₊ x' , y) ≢ (₀ , ₀)) →
  head (act [ (([] , e) , ([] , ((₁₊ x' , y) , pr))) ]ᵐˡ (pX ∷ [])) .proj₁ ≡ y
hdX1 e x' y pr = cong proj₁ (cong head (begin
  act [ (([] , e) , ([] , ((₁₊ x' , y) , pr))) ]ᵐˡ (pX ∷ [])
    ≡⟨ auto ⟩
  act (S^ (- e)) (act (ZM inv) (act (H • S^ k) ((₁ , ₀) ∷ [])))
    ≡⟨ cong (λ v → act (S^ (- e)) (act (ZM inv) v)) (lemma-HS-x k ₁ ₀ []) ⟩
  act (S^ (- e)) (act (ZM inv) ((- (₀ + ₁ * k) , ₁) ∷ []))
    ≡⟨ cong (act (S^ (- e))) (lemma-M (- (₀ + ₁ * k)) ₁ [] inv) ⟩
  act (S^ (- e)) ((- (₀ + ₁ * k) * inv⁻¹ , ₁ * xI) ∷ [])
    ≡⟨ auto ⟩
  ((- (₀ + ₁ * k) * inv⁻¹ , ₁ * xI + - (₀ + ₁ * k) * inv⁻¹ * (- e)) ∷ [])
    ≡⟨ cong (λ z → (z , ₁ * xI + - (₀ + ₁ * k) * inv⁻¹ * (- e)) ∷ []) r1 ⟩
  ((y , ₁ * xI + - (₀ + ₁ * k) * inv⁻¹ * (- e)) ∷ []) ∎))
  where
  inv = (₁₊ x' , λ ()) ⁻¹
  xI = inv .proj₁
  inv⁻¹ = (inv ⁻¹) .proj₁
  k = - y * xI
  ii : inv⁻¹ ≡ ₁₊ x'
  ii = inv-involutive (₁₊ x' , λ ())
  -- - (₀ + ₁ * k) * inv⁻¹ = - k * inv⁻¹ = (y * xI) * inv⁻¹ = y * (xI * inv⁻¹) = y
  r1 : - (₀ + ₁ * k) * inv⁻¹ ≡ y
  r1 = begin
    - (₀ + ₁ * k) * inv⁻¹        ≡⟨ cong (λ z → - z * inv⁻¹) (trans (+-identityˡ (₁ * k)) (*-identityˡ k)) ⟩
    - k * inv⁻¹                  ≡⟨ cong (_* inv⁻¹) (trans (-‿distribˡ-* (- y) xI) (cong (_* xI) (-‿involutive y))) ⟩
    y * xI * inv⁻¹               ≡⟨ *-assoc y xI inv⁻¹ ⟩
    y * (xI * inv⁻¹)             ≡⟨ cong (λ z → y * (xI * z)) ii ⟩
    y * (xI * (₁₊ x'))           ≡⟨ cong (y *_) (lemma-⁻¹ˡ (₁₊ x') {{nztoℕ {y = ₁₊ x'} {neq0 = λ ()}}}) ⟩
    y * ₁                        ≡⟨ *-identityʳ y ⟩
    y ∎

------------------------------------------------------------------------
-- n=1 head-injectivity: ML 1 elements are distinguished by the head of
-- their Pauli action.  Recover the A-shape (x = ₀ vs x ≠ ₀) from the
-- pZ head, then the remaining data from the pZ/pX heads.
lemma-nf1-head-inj : ∀ (lm₁ lm₂ : ML 1) →
  (∀ (ps : Pauli 1) → head (act [ lm₁ ]ᵐˡ ps) ≡ head (act [ lm₂ ]ᵐˡ ps)) → lm₁ ≡ lm₂
-- Absurd A = (₀ , ₀) cases.
lemma-nf1-head-inj (([] , _) , ([] , ((₀ , ₀) , pr₁))) _ _ = ⊥-elim (pr₁ refl)
lemma-nf1-head-inj (([] , _) , ([] , ((₁₊ _ , _) , _))) (([] , _) , ([] , ((₀ , ₀) , pr₂))) _ = ⊥-elim (pr₂ refl)
lemma-nf1-head-inj (([] , _) , ([] , ((₀ , ₁₊ _) , _))) (([] , _) , ([] , ((₀ , ₀) , pr₂))) _ = ⊥-elim (pr₂ refl)
-- x₁ = ₀ , x₂ = ₀.
lemma-nf1-head-inj (([] , e₁) , ([] , ((₀ , ₁₊ y₁') , pr₁))) (([] , e₂) , ([] , ((₀ , ₁₊ y₂') , pr₂))) h =
  ≡×≡⇒≡ (cong ([] ,_) e-eq , cong ([] ,_) a-eq)
  where
  X0eq : (₁₊ y₁' , (₁₊ y₁') * (- e₁)) ≡ (₁₊ y₂' , (₁₊ y₂') * (- e₂))
  X0eq = trans (sym (hdX0 e₁ y₁' pr₁)) (trans (h (pX ∷ [])) (hdX0 e₂ y₂' pr₂))
  y-eq : ₁₊ y₁' ≡ ₁₊ y₂'
  y-eq = cong proj₁ X0eq
  a-eq : ((₀ , ₁₊ y₁') , pr₁) ≡ ((₀ , ₁₊ y₂') , pr₂)
  a-eq = A-≡ _ _ (cong (₀ ,_) y-eq)
  coeff-eq : (₁₊ y₁') * (- e₁) ≡ (₁₊ y₁') * (- e₂)
  coeff-eq = trans (cong proj₂ X0eq) (cong (_* (- e₂)) (sym y-eq))
  e-eq : e₁ ≡ e₂
  e-eq = neg-inj e₁ e₂ (*-cancelˡ-nz (₁₊ y₁') (- e₁) (- e₂) (λ ()) coeff-eq)
-- x₁ = ₀ , x₂ ≠ ₀ : contradictory pZ heads.
lemma-nf1-head-inj (([] , e₁) , ([] , ((₀ , ₁₊ y₁') , pr₁))) (([] , e₂) , ([] , ((₁₊ x₂' , y₂) , pr₂))) h =
  ⊥-elim ((-' (₁₊ x₂' , λ ())) .proj₂ (sym peq))
  where
  Zeq : (₀ , ((₁₊ y₁' , λ ()) ⁻¹) .proj₁) ≡ (- (₁₊ x₂') , (₁₊ x₂') * e₂)
  Zeq = trans (sym (hdZ0 e₁ y₁' pr₁)) (trans (h (pZ ∷ [])) (hdZ1 e₂ x₂' y₂ pr₂))
  peq : ₀ ≡ - (₁₊ x₂')
  peq = cong proj₁ Zeq
-- x₁ ≠ ₀ , x₂ = ₀ : contradictory pZ heads.
lemma-nf1-head-inj (([] , e₁) , ([] , ((₁₊ x₁' , y₁) , pr₁))) (([] , e₂) , ([] , ((₀ , ₁₊ y₂') , pr₂))) h =
  ⊥-elim ((-' (₁₊ x₁' , λ ())) .proj₂ peq)
  where
  Zeq : (- (₁₊ x₁') , (₁₊ x₁') * e₁) ≡ (₀ , ((₁₊ y₂' , λ ()) ⁻¹) .proj₁)
  Zeq = trans (sym (hdZ1 e₁ x₁' y₁ pr₁)) (trans (h (pZ ∷ [])) (hdZ0 e₂ y₂' pr₂))
  peq : - (₁₊ x₁') ≡ ₀
  peq = cong proj₁ Zeq
-- x₁ ≠ ₀ , x₂ ≠ ₀.
lemma-nf1-head-inj (([] , e₁) , ([] , ((₁₊ x₁' , y₁) , pr₁))) (([] , e₂) , ([] , ((₁₊ x₂' , y₂) , pr₂))) h =
  ≡×≡⇒≡ (cong ([] ,_) e-eq , cong ([] ,_) a-eq)
  where
  Zeq : (- (₁₊ x₁') , (₁₊ x₁') * e₁) ≡ (- (₁₊ x₂') , (₁₊ x₂') * e₂)
  Zeq = trans (sym (hdZ1 e₁ x₁' y₁ pr₁)) (trans (h (pZ ∷ [])) (hdZ1 e₂ x₂' y₂ pr₂))
  x-eq : ₁₊ x₁' ≡ ₁₊ x₂'
  x-eq = neg-inj (₁₊ x₁') (₁₊ x₂') (cong proj₁ Zeq)
  y-eq : y₁ ≡ y₂
  y-eq = trans (sym (hdX1 e₁ x₁' y₁ pr₁)) (trans (cong proj₁ (h (pX ∷ []))) (hdX1 e₂ x₂' y₂ pr₂))
  a-eq : ((₁₊ x₁' , y₁) , pr₁) ≡ ((₁₊ x₂' , y₂) , pr₂)
  a-eq = A-≡ _ _ (≡×≡⇒≡ (x-eq , y-eq))
  coeff-eq : (₁₊ x₁') * e₁ ≡ (₁₊ x₁') * e₂
  coeff-eq = trans (cong proj₂ Zeq) (cong (_* e₂) (sym x-eq))
  e-eq : e₁ ≡ e₂
  e-eq = *-cancelˡ-nz (₁₊ x₁') e₁ e₂ (λ ()) coeff-eq

