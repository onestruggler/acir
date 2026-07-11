{-# OPTIONS  --safe #-}
{-# OPTIONS --termination-depth=2 #-}
{-# OPTIONS  --call-by-name #-}


open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using ([_,_] ; [_,_]′)
open import Data.Unit using (tt)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Derived2 (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Zp.Mod-Lemmas p-2 p-prime
open import Examples.Groups.Symplectic.Symplectic p-2 p-prime
open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime


open Symplectic
open Symplectic-GroupLike

private
  variable
    n : ℕ


open import Algebra.Properties.Ring (+-*-ring p-2)


lemma-nf1*nf1' : let open PB ((₁₊ n) QRel,_===_) in ∀ (s s' x' : ℤ ₚ) (m m' : ℤ* ₚ) -> (neq : s' ≢ ₀) ->
  let
  m'f = m' .proj₁ 
  mf = m .proj₁ 
  y* = m *' m' ⁻¹
  m'⁻¹ = (m' ⁻¹) .proj₁
  y = y* .proj₁
  ss'* : ℤ* ₚ
  ss'* = (s' , neq)
  [ss'*]⁻¹ = (ss'* ⁻¹) .proj₁
  k* = ss'* *' (m' ⁻¹ *' m' ⁻¹)
  k = k* .proj₁
  k⁻¹ = (k* ⁻¹) .proj₁
  -k⁻¹ = - k⁻¹
  -y/k' = ((y* *' k* ⁻¹) *' -'₁)
  -y/k = -y/k' .proj₁
  yy = (mf * mf) * (m'⁻¹ * m'⁻¹)
  in
  
  S^ s • M m • H • ⟦ (s' , m' , HS^ x') ⟧₁ ≈ S^ (s + - [ss'*]⁻¹ * m ^2 ) • M -y/k' • H • S^ (-k⁻¹ + x')

lemma-nf1*nf1' {n} s s' x' m m' neq  = begin
  S^ s • M m • H • ⟦ (s' , m' , HS^ x') ⟧₁ ≈⟨ (cright cright cright sym assoc) ⟩
  S^ s • M m • H • (S^ s' • M m') • H • S^ x' ≈⟨ by-passoc (□ • □ • □ • □) (□ ^ 3 • □) auto ⟩
  (S^ s • M m • H) • (S^ s' • M m') • H • S^ x' ≈⟨ (cright cleft lemma-S^kM (m' .proj₁) s' (m' .proj₂)) ⟩
  (S^ s • M m • H) • (M m' • S^ ((s') * (m' ⁻¹) ^2)) • H • S^ x'  ≈⟨ by-passoc (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
  (S^ s • M m) • (H • M m') • S^ ((s') * (m' ⁻¹) ^2) • H • S^ x'  ≈⟨ ((cright (cleft semi-HM m'))) ⟩
  (S^ s • M m) • (M (m' ⁻¹) • H) • S^ ((s') * (m' ⁻¹) ^2) • H • S^ x'  ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 2) auto ⟩
  S^ s • (M m • M (m' ⁻¹)) • H • S^ ((s') * (m' ⁻¹) ^2) • H • S^ x'  ≈⟨ ((cright cleft axiom (M-mul m (m' ⁻¹)))) ⟩
  S^ s • M (m *' m' ⁻¹) • H • S^ ((s') * (m' ⁻¹) ^2) • H • S^ x'  ≈⟨ (cright by-passoc (□ ^ 5) (□ ^ 4 • □) auto) ⟩
  S^ s • (M (m *' m' ⁻¹) • H • S^ ((s') * (m' ⁻¹) ^2) • H) • S^ x'  ≈⟨ (cright cleft derived-7 k y (k* .proj₂) (y* .proj₂)) ⟩
  S^ s • (S^ (-k⁻¹ * (y * y)) • M -y/k' • (H • S^ -k⁻¹)) • S^ x'  ≈⟨ by-passoc (□ • □ ^ 4 • □) (□ ^ 2 • □ • □ • □ ^ 2) auto ⟩
  (S^ s • S^ (-k⁻¹ * (y * y))) • M -y/k' • H • S^ -k⁻¹ • S^ x'  ≈⟨ cong (lemma-S^k+l s (-k⁻¹ * (y * y))) (cright (cright lemma-S^k+l -k⁻¹ x' )) ⟩
  S^ (s + -k⁻¹ * (y * y)) • M -y/k' • H • S^ (-k⁻¹ + x')  ≈⟨ (cleft aux) ⟩
  S^ (s + - [ss'*]⁻¹ * m ^2 ) • M -y/k' • H • S^ (-k⁻¹ + x')  ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open Lemmas0 n
  m'f = m' .proj₁ 
  mf = m .proj₁ 
  y* = m *' m' ⁻¹
  m'⁻¹ = (m' ⁻¹) .proj₁
  y = y* .proj₁
  ss'* : ℤ* ₚ
  ss'* = (s' , neq)
  [ss'*]⁻¹ = (ss'* ⁻¹) .proj₁
  k* = ss'* *' (m' ⁻¹ *' m' ⁻¹)
  k = k* .proj₁
  k⁻¹ = (k* ⁻¹) .proj₁
  -k⁻¹ = - k⁻¹
  -y/k' = ((y* *' k* ⁻¹) *' -'₁)
  -y/k = -y/k' .proj₁
  yy = (mf * mf) * (m'⁻¹ * m'⁻¹)

  aux0 : y * y ≡ yy
  aux0 = Eq.trans (*-assoc mf m'⁻¹ y) (Eq.trans (Eq.cong (mf *_) (Eq.sym (*-assoc m'⁻¹ mf m'⁻¹))) (Eq.trans (Eq.cong (\ xx -> mf * (xx * m'⁻¹)) (*-comm m'⁻¹ mf)) (Eq.trans (Eq.cong (mf *_) (*-assoc mf m'⁻¹ m'⁻¹)) (Eq.sym (*-assoc mf mf (m'⁻¹ * m'⁻¹))))))
  aux : S^ (s + -k⁻¹ * (y * y)) ≈ S^ (s + - [ss'*]⁻¹ * m ^2 )
  aux = begin
    S^ (s + -k⁻¹ * (y * y)) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) auto)) ⟩
    S^ (s + - ((ss'* *' (m' ⁻¹ *' m' ⁻¹)) ⁻¹) .proj₁ * (y * y)) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.cong ( _* (y * y)) (Eq.cong -_ (inv-distrib ss'* (m' ⁻¹ *' m' ⁻¹)))))) ⟩
    S^ (s + - ((ss'* ⁻¹ *' (m' ⁻¹ *' m' ⁻¹) ⁻¹)) .proj₁ * (y * y)) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.cong ( _* (y * y)) (Eq.cong -_ (Eq.cong ([ss'*]⁻¹ *_) (inv-distrib (m' ⁻¹) (m' ⁻¹))))))) ⟩
    S^ (s + - ((ss'* ⁻¹ *' (m' ⁻¹ ⁻¹ *' m' ⁻¹ ⁻¹))) .proj₁ * (y * y)) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.cong ( _* (y * y)) (Eq.cong -_ (Eq.cong ([ss'*]⁻¹ *_) (Eq.cong₂ _*_ (inv-involutive m') (inv-involutive m') )))))) ⟩
    S^ (s + - (([ss'*]⁻¹ * (m' .proj₁ * m' .proj₁)))  * (y * y)) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.sym (-‿distribˡ-* ((([ss'*]⁻¹ * (m' .proj₁ * m' .proj₁)))) (y * y))))) ⟩
    S^ (s + - ((([ss'*]⁻¹ * (m'f * m'f))) * (y * y))) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.cong -_ (*-assoc [ss'*]⁻¹ (m'f * m'f) (y * y))))) ⟩
    S^ (s + - ([ss'*]⁻¹ * ((m'f * m'f) * (y * y)))) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.cong -_  (Eq.cong ([ss'*]⁻¹ *_) (*-comm (m'f * m'f) (y * y)))))) ⟩
    S^ (s + - ([ss'*]⁻¹ * ((y * y) * (m'f * m'f) ))) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.cong -_  (Eq.cong ([ss'*]⁻¹ *_) (Eq.cong (_* (m'f * m'f)) aux0))))) ⟩
    S^ (s + - ([ss'*]⁻¹ * (yy * (m'f * m'f) ))) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.cong -_  (Eq.cong ([ss'*]⁻¹ *_) (*-assoc (mf * mf) (m'⁻¹ * m'⁻¹) (m'f * m'f)))))) ⟩
    S^ (s + - ([ss'*]⁻¹ * ((mf * mf) * ((m'⁻¹ * m'⁻¹) * (m'f * m'f)) ))) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.cong -_  (Eq.cong ([ss'*]⁻¹ *_) (Eq.cong ((mf * mf) *_) (aux-xxxx m')))))) ⟩
    S^ (s + - ([ss'*]⁻¹ * ((mf * mf) * ₁ ))) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (Eq.cong -_  (Eq.cong ([ss'*]⁻¹ *_) (*-identityʳ (mf * mf)))))) ⟩
    S^ (s + - ([ss'*]⁻¹ * (mf * mf))) ≈⟨ refl' (Eq.cong S^ (Eq.cong (s +_) (-‿distribˡ-* [ss'*]⁻¹ (mf * mf)))) ⟩
    S^ (s + - [ss'*]⁻¹ * m ^2 ) ∎




