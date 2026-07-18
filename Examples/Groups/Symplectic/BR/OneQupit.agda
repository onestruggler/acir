{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS  --call-by-name #-}
{-# OPTIONS --termination-depth=4 #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Vec as V
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Maybe
open import Data.Sum using ([_,_] ; [_,_]′)
open import Data.Unit using (tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Data.Fin using (zero)
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting using ()
open import Data.Nat.Primality



module Examples.Groups.Symplectic.BR.OneQupit (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    




open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.ExtendedGate.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.Properties p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Symplectic.ExtendedGate.NF2-Sym p-2 p-prime
open LM2


open import Zp.ModularArithmetic
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.NF2-Sym p-2 p-prime
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym5 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime

open import Examples.Groups.Symplectic.Lemmas.Lemma-Comm-n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to Cp1)
open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import Examples.Groups.Symplectic.Lemmas.Completeness1-Sym p-2 p-prime renaming (module Completeness to CP1) using ()
open import Examples.Groups.Symplectic.Lemmas.Coset2-Update-Sym p-2 p-prime using ()
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.DH p-2 p-prime
open import Examples.Groups.Symplectic.BR.Calculations p-2 p-prime


open PB (1 QRel,_===_)
open PP (1 QRel,_===_)
open SR word-setoid
open Pattern-Assoc
open Lemmas0 0

fig-24-1 : ∀ (b* : ℤ* ₚ) ->
  let
  b = b* .proj₁
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b (b* .proj₂)
  nz' : (b , ₀) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 b ₀ (b* .proj₂)
  in
  
  [ (₀ , b) , nz ]ᵃ • H ≈ [ (b , ₀) , nz' ]ᵃ
  
fig-24-1 b*@(₀ , nzb) = ⊥-elim (nzb auto)
fig-24-1 b*@(b@(₁₊ b-1) , nzb) = begin
  ⟦ (b , λ ()) ⁻¹ , ε ⟧ₘ₊ • H ≈⟨ cleft right-unit ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • H ≈⟨ cright sym right-unit ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • H • ε ≈⟨ refl ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • H • S^ ₀ ≈⟨ cright cright refl' (Eq.cong S^ (Eq.sym (Eq.trans (Eq.cong (_* b⁻¹) -0#≈0#) (*-zeroˡ b⁻¹)))) ⟩
  ⟦ (b , λ ()) ⁻¹ ⟧ₘ • H • S^ (- ₀ * b⁻¹) ≈⟨ refl ⟩
  [ (b , ₀) , aux-a≠0⇒ab≠0 b ₀ nzb  ]ᵃ ∎
  where
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b (b* .proj₂)
  b⁻¹ = (b* ⁻¹).proj₁
  


fig-24-2 : ∀ (a* : ℤ* ₚ) ->
  let
  a = a* .proj₁
  nz : (a , ₀) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a ₀ (a* .proj₂)
  nz' : (₀ , - a ) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' a*) .proj₂)
  in
  
  [ (a , ₀) , nz ]ᵃ • H ≈ [ (₀ , - a) , nz' ]ᵃ
  
fig-24-2 a*@(₀ , nza) = ⊥-elim (nza auto)
fig-24-2 a*@(a@(₁₊ a-1) , nza) = begin
  [ (a , ₀) , nz ]ᵃ • H ≈⟨ refl ⟩
  ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ • H ≈⟨ cleft cright cright  refl' (Eq.cong S^ ( (Eq.trans (Eq.cong (_* a⁻¹) -0#≈0#) (*-zeroˡ a⁻¹)))) ⟩
  (⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • S^ ₀ ) • H ≈⟨ cleft cright right-unit ⟩
  (⟦ (a , λ ()) ⁻¹ ⟧ₘ • H) • H ≈⟨ assoc ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • H ≈⟨ cright lemma-HH-M-1  ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • ZM (-'₁) ≈⟨ axiom (M-mul ((a , λ ()) ⁻¹) -'₁) ⟩
  ⟦ (a , λ ()) ⁻¹ *' -'₁ ⟧ₘ  ≈⟨ aux-MM (((a , λ ()) ⁻¹ *' -'₁) .proj₂) (( -'₁ *' (a , λ ()) ⁻¹) .proj₂) (*-comm a⁻¹ (- ₁)) ⟩
  ⟦  -'₁ *' (a , λ ()) ⁻¹  ⟧ₘ  ≈⟨ aux-MM  ((-'₁ *' (a , λ ()) ⁻¹) .proj₂) ((-' (a , λ ()) ⁻¹).proj₂) (-1*x≈-x a⁻¹) ⟩
  ⟦  -' (a , λ ()) ⁻¹  ⟧ₘ  ≈⟨ aux-MM  ((-' (a , λ ()) ⁻¹) .proj₂) (( (-' (a , λ ())) ⁻¹) .proj₂) (Eq.sym (inv-neg-comm ((a , λ ())))) ⟩
  ⟦  (-' (a , λ ())) ⁻¹  ⟧ₘ  ≈⟨ refl ⟩
  ⟦  (- a , ((-' a*) .proj₂)) ⁻¹  ⟧ₘ  ≈⟨ sym (aux-abox-nzb (- a) (((-' a*) .proj₂))) ⟩
  [ (₀ , - a) , nz' ]ᵃ ∎
  where
  nz : (a , ₀) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a ₀ (a* .proj₂)
  nz' : (₀ , - a ) ≢ (₀ , ₀)
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' a*) .proj₂)

  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - ₀ * a⁻¹



fig-24-3 : ∀ (a* b* : ℤ* ₚ) ->
  let
  a = a* .proj₁
  b = b* .proj₁
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b (a* .proj₂)
  nz' : (b , - a ) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 b (- a) (b* .proj₂)
  [ab]⁻¹* = ( a* *' b*) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁
  in
  
  [ (a , b) , nz ]ᵃ • H ≈ S^ [ab]⁻¹ • [ (b , - a) , nz' ]ᵃ
  
fig-24-3 a*@(₀ , nza) b* = ⊥-elim (nza auto)
fig-24-3 a*@(a@(₁₊ a-1) , nza) b*@(b , nzb) = begin
  [ (a , b) , nz ]ᵃ • H ≈⟨ refl ⟩
  ⟦ (a , λ ()) ⁻¹ , HS^ -b/a ⟧ₘ₊ • H ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
  ⟦ (a , λ ()) ⁻¹ ⟧ₘ • H • S^ -b/a • H ≈⟨ derived-7  x y nzx nzy ⟩
  S^ (-x⁻¹ * (y * y)) • ZM -y/x' • (H • S^ -x⁻¹) ≈⟨ cong (refl' (Eq.cong S^ (cal .proj₁))) (cong (aux-MM  (-y/x' .proj₂) ((b* ⁻¹) .proj₂) (cal .proj₂ .proj₁)) (cright refl' (Eq.cong S^ (cal .proj₂ .proj₂)))) ⟩
  S^ [ab]⁻¹ • ZM (b* ⁻¹) • (H • S^ (- - a * b⁻¹)) ≈⟨ sym (cright aux-abox-nza b (- a) nzb) ⟩
  S^ [ab]⁻¹ • [ (b , - a) , nz' ]ᵃ ∎
  where
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b (a* .proj₂)
  nz' : (b , - a ) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 b (- a) (b* .proj₂)
  b⁻¹ = (b* ⁻¹) .proj₁

  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  y = a⁻¹
  nzy = ((a , λ ()) ⁻¹) .proj₂
  x = -b/a
  nzx = (-' b* *' a* ⁻¹).proj₂
  
  x⁻¹ = ((x , nzx) ⁻¹) .proj₁
  x⁻¹⁻¹ = (((x , nzx) ⁻¹) ⁻¹) .proj₁
  -x⁻¹ = - x⁻¹
  -y/x' = (((y , nzy) *' ((x , nzx) ⁻¹)) *' -'₁)
  -y/x = -y/x' .proj₁

  [ab]⁻¹* = (  (a , λ ()) *' (b , nzb)  ) ⁻¹
  [ab]⁻¹ = [ab]⁻¹* .proj₁

  cal = fig-24-3-cal-1 a* b*



fig-25-1 : ∀ (b*@(b , nzb) : ℤ* ₚ) ->
  let
  b⁻¹ = (b* ⁻¹) .proj₁
  b⁻² = b⁻¹ * b⁻¹
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  in
  
  [(₀ , b) , nz ]ᵃ • S ≈ S^ b⁻² • [(₀ , b) , nz ]ᵃ

fig-25-1 b*@(b , nzb) = begin
  [(₀ , b) , nz ]ᵃ • S ≈⟨ cleft aux-abox-nzb b nzb ⟩
  ⟦ (b , nzb) ⁻¹ ⟧ₘ • S ≈⟨ axiom (semi-MS ((b , nzb) ⁻¹)) ⟩
  S^ b⁻² • ⟦ (b , nzb) ⁻¹ ⟧ₘ ≈⟨ cright sym (aux-abox-nzb b nzb) ⟩
  S^ b⁻² • [(₀ , b) , nz ]ᵃ ∎
  where
  b⁻¹ = (b* ⁻¹) .proj₁
  b⁻² = b⁻¹ * b⁻¹
  nz : (₀ , b) ≢ (₀ , ₀)
  nz = aux-b≠0⇒ab≠0 ₀ b nzb
  

fig-25-2 : ∀ (a*@(a , nza) : ℤ* ₚ) (b : ℤ ₚ) ->
  let
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  a⁻¹ = ((a , nza) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  nz' : (a , b + - a) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 a (b + - a) nza
  in
  
  [(a , b) , nz ]ᵃ • S ≈ [(a , b + - a) , nz' ]ᵃ

fig-25-2 a*@(a , nza) b = begin
  [(a , b) , nz ]ᵃ • S ≈⟨ cleft aux-abox-nza a b nza ⟩
  ⟦ (a , nza) ⁻¹ , HS^ -b/a ⟧ₘ₊ • S ≈⟨  (  by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto) ⟩
  ((ZM (a* ⁻¹) • H) • S^ -b/a • S) ≈⟨ (  cright lemma-S^k+l  -b/a ₁) ⟩
  ((ZM (a* ⁻¹) • H) • S^ (-b/a + ₁)) ≈⟨ ( ( assoc)) ⟩
  (ZM (a* ⁻¹) • H • S^ (-b/a + ₁)) ≈⟨ cright cright refl' (Eq.cong S^ (fig-25-2-cal a* b))  ⟩
  (ZM (a* ⁻¹) • H • S^ (- (b + - a) * a⁻¹)) ≈⟨ sym (aux-abox-nza a (b + - a) nza) ⟩
  ([ (a , (b + - a)) , nz' ]ᵃ) ≈⟨ refl ⟩
  ([ (a , b + - a) , nz' ]ᵃ)  ∎
  where
  nz : (a , b) ≢ (₀ , ₀)
  nz = aux-a≠0⇒ab≠0 a b nza
  a⁻¹ = ((a , nza) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  nz' : (a , b + - a) ≢ (₀ , ₀)
  nz' = aux-a≠0⇒ab≠0 a (b + - a) nza
  


dir-and-A'-of : A -> Gen 1 -> Word (Gen 1) × A
dir-and-A'-of x@((a@₀ , b@₀) , nz) _ = ⊥-elim (nz auto)
dir-and-A'-of x@((a@₀ , b@(₁₊ _)) , nz) H-gen          =     ε          ,     (b , ₀) , λ ()
dir-and-A'-of x@((a@(₁₊ _) , b@₀) , nz) H-gen          =     ε          ,     (₀ , - a) , nz'
  where
  nz' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
dir-and-A'-of x@((a@(₁₊ _) , b@(₁₊ _)) , nz) H-gen     =     S^ [ab]⁻¹  ,     (b , - a) , nz'
  where
  nz' = aux-a≠0⇒ab≠0 b (- a) λ ()
  [ab]⁻¹ = ((  (a , λ ()) *' (b , λ ())  ) ⁻¹) .proj₁
dir-and-A'-of x@((a@₀ , b@(₁₊ _)) , nz) S-gen          =     S^ b⁻²     ,     (₀ , b) , nz
  where
  b* = (b , λ ())
  b⁻² = ((b* ⁻¹) .proj₁) * ((b* ⁻¹) .proj₁)
dir-and-A'-of x@((a@(₁₊ _) , b) , nz) S-gen            =      ε         ,     (a , b + - a) , nz'
  where
  nz' = aux-a≠0⇒ab≠0 a (b + - a) λ ()


lemma-single-qupit-br-A : ∀ (x : A) (g : Gen 1) ->
  let (dir , x') = dir-and-A'-of x g in
  
  [ x ]ᵃ • [ g ]ʷ ≈ dir • [ x' ]ᵃ

lemma-single-qupit-br-A x@((a@₀ , b@₀) , nz) _ = ⊥-elim (nz auto)
lemma-single-qupit-br-A x@((a@₀ , b@(₁₊ _)) , nz) S-gen = fig-25-1 (b , (λ ()))
lemma-single-qupit-br-A x@((a@(₁₊ _) , b@₀) , nz) S-gen = trans (fig-25-2 (a , (λ ())) b) (sym left-unit)
lemma-single-qupit-br-A x@((a@(₁₊ _) , b@(₁₊ _)) , nz) S-gen = trans (fig-25-2 (a , (λ ())) b) (sym left-unit)
lemma-single-qupit-br-A x@((a@₀ , b@(₁₊ _)) , nz) H-gen = trans (fig-24-1 (b , (λ ()))) (sym left-unit)
lemma-single-qupit-br-A x@((a@(₁₊ _) , b@₀) , nz) H-gen = trans (fig-24-2 (a , (λ ()))) (sym left-unit)
lemma-single-qupit-br-A x@((a@(₁₊ _) , b@(₁₊ _)) , nz) H-gen = fig-24-3 (a , (λ ())) (b , λ ()) 


lemma-single-qupit-br-E : ∀ (b : ℤ ₚ) ->

  [ b ]ᵉ • S ≈ [ b + - ₁ ]ᵉ
  
lemma-single-qupit-br-E b = begin
  [ b ]ᵉ • S ≈⟨ refl ⟩
  S^ (- b) • S ≈⟨ lemma-S^k+l (- b) ₁ ⟩
  S^ (- b + ₁) ≡⟨ Eq.cong S^ (Eq.cong (- b +_) (Eq.sym (-‿involutive ₁))) ⟩
  S^ (- b + - - ₁) ≡⟨ Eq.cong S^ (-‿+-comm b (- ₁)) ⟩
  S^ (- (b + - ₁)) ≈⟨ refl ⟩
  [ b + - ₁ ]ᵉ ∎


 
