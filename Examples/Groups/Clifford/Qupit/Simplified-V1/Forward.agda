{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (no)


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁ ; ∃)

open import Data.Nat hiding (_^_ ; _*_ ; _+_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Fin hiding (_+_ ; _≤_)
open import Data.Bool hiding (_≤_)
open import Data.List hiding ([_])

open import Data.Maybe
open import Data.Sum using (inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_)
import Presentation.Construct.Properties.SemiDirectProduct2 as SDP2
open import Presentation.Tactic.Rewriting hiding ([_])

open import Presentation.GroupLike
open import Data.Nat.Primality

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem


module Examples.Groups.Clifford.Qupit.Simplified-V1.Forward
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


open import Examples.Groups.Clifford.Qupit.SemiDirect.Syntactics p-3 p-prime g* g-gen
open import Examples.Groups.Clifford.Qupit.Simplified-V1.LemmasCZ p-3 p-prime g* g-gen hiding (module CL ; module CLb)

import Examples.Groups.ProjectivePauli.Presentation-Alt p-2 p-prime as XZ

module Iso (n : ℕ) where

  open import Examples.Groups.Clifford.Qupit.Simplified-V1.Syntactics
    p-3 p-prime g* g-gen as Cli
  open import Examples.Groups.Clifford.Qupit.Simplified-V1.Lemmas
    p-3 p-prime g* g-gen
    using (module Lemmas1)
  open import Examples.Groups.Clifford.Qupit.Simplified-V1.LemmasXZ
    p-3 p-prime g* g-gen
    using (module Lemmas1b)

  module Clifford = Clifford-Relations


  f : ∀ {n} -> SemiDirect.Gen n -> Word (Gen n)
  f SemiDirect.X-gen = Clifford.X
  f SemiDirect.Z-gen = Clifford.Z
  f SemiDirect.H-gen = Cli.H
  f SemiDirect.S-gen = Clifford.R
  f SemiDirect.CZ-gen = Cli.CZ
  f {₁₊ n} (inj₁ (x XZ.↥)) = f (inj₁ x) ↑
  f {₁₊ n} (inj₂ (y Sym.↥)) = f (inj₂ y) ↑

  h : ∀ {n} -> Cli.Gen n -> Word (SemiDirect.Gen n)
  h Cli.H-gen = SemiDirect.H
  h Cli.S-gen = SemiDirect.Z^ -1/2 • SemiDirect.S
  h Cli.CZ-gen = SemiDirect.CZ
  h (x Cli.↥) = (h x) SemiDirect.↑


  module SD = SemiDirect
  module CL = Lemmas1
  module CLb = Lemmas1b


  f-M : ∀ {n} x -> (f ʷ) (SD.M {n = n} x) ≡ Clifford.M x
  f-M {n} x' = begin
    (f ʷ) (SD.S^ x • SD.H • SD.S^ x⁻¹ • SD.H • SD.S^ x • SD.H) ≡⟨ Eq.cong₂ _•_ (lemma-fʷ-w^n (toℕ x)) (Eq.cong₂ _•_ auto (Eq.cong₂ _•_ (lemma-fʷ-w^n (toℕ x⁻¹)) (Eq.cong₂ _•_ auto (Eq.cong₂ _•_ (lemma-fʷ-w^n (toℕ x)) auto)))) ⟩
    Clifford.R^ x • Cli.H • Clifford.R^ x⁻¹ • Cli.H • Clifford.R^ x • Cli.H ≡⟨ auto ⟩
    Clifford.M x' ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  f-M' : ∀ {n} x -> (f ʷ) [  Sym.M {n = n} x ]ᵣ ≡ Clifford.M x
  f-M' {n} x' = begin
    (f ʷ) [ Sym.M x' ]ᵣ ≡⟨ Eq.cong (\ z -> (f ʷ) (z • [ Sym.H • Sym.S^ x⁻¹ • Sym.H • Sym.S^ x • Sym.H ]ᵣ)) (lemma-[w^n]ᵣ=[w]ᵣ^n Sym.S (toℕ x)) ⟩
    (f ʷ) (SD.S^ x • [ Sym.H • Sym.S^ x⁻¹ • Sym.H • Sym.S^ x • Sym.H ]ᵣ) ≡⟨  auto ⟩
    (f ʷ) (SD.S^ x • SD.H • [ Sym.S^ x⁻¹ • Sym.H • Sym.S^ x • Sym.H ]ᵣ) ≡⟨ Eq.cong
                                                                            (λ z → (f ʷ) (SD.S^ x • SD.H • z • [ Sym.H • Sym.S^ x • Sym.H ]ᵣ))
                                                                            (lemma-[w^n]ᵣ=[w]ᵣ^n Sym.S (toℕ x⁻¹)) ⟩
    (f ʷ) (SD.S^ x • SD.H • SD.S^ x⁻¹ • [ Sym.H • Sym.S^ x • Sym.H ]ᵣ) ≡⟨ Eq.cong (\ z -> (f ʷ) (SD.S^ x • SD.H • SD.S^ x⁻¹ • SD.H • z • SD.H)) (lemma-[w^n]ᵣ=[w]ᵣ^n Sym.S (toℕ x)) ⟩
    (f ʷ) (SD.S^ x • SD.H • SD.S^ x⁻¹ • SD.H • SD.S^ x • SD.H) ≡⟨ f-M x' ⟩
    Clifford.M x' ∎
    where
    open ≡-Reasoning
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )


  lemma-f*-[w]ᵣ : ∀ {n} {w : Word (Sym.Gen n)} -> (f ʷ) [ w Sym.↑ ]ᵣ ≡ (f ʷ) [ w ]ᵣ ↑
  lemma-f*-[w]ᵣ {n} {[ x ]ʷ} = auto
  lemma-f*-[w]ᵣ {n} {ε} = auto
  lemma-f*-[w]ᵣ {n} {w • w₁} rewrite lemma-f*-[w]ᵣ {w = w} | lemma-f*-[w]ᵣ {w = w₁} = auto

  lemma-[]ₗ-↑' : ∀ {n} (w : Word (XZ.Gen n)) -> SD._↑ {n} ([_]ₗ {B = Sym.Gen n} w) ≡ [_]ₗ {B = Sym.Gen (₁₊ n)} (w XZ.↑)
  lemma-[]ₗ-↑' {n} [ x ]ʷ = auto
  lemma-[]ₗ-↑' {n} ε = auto
  lemma-[]ₗ-↑' {n} (w • w₁) rewrite lemma-[]ₗ-↑' w | lemma-[]ₗ-↑' w₁ = auto

  lemma-f*-SD↑ : ∀ {n} (w : Word (SemiDirect.Gen n)) -> (f ʷ) (SD._↑ {n} w) ≡ ((f ʷ) w) ↑
  lemma-f*-SD↑ {n} [ inj₁ x ]ʷ = auto
  lemma-f*-SD↑ {n} [ inj₂ y ]ʷ = auto
  lemma-f*-SD↑ {n} ε = auto
  lemma-f*-SD↑ {n} (w • w₁) rewrite lemma-f*-SD↑ w | lemma-f*-SD↑ w₁ = auto

  lemma-f*-^ᵣ : ∀ {n} (w : Word (Sym.Gen n)) k -> (f ʷ) ([ w ^ k ]ᵣ) ≡ ((f ʷ) [ w ]ᵣ) ^ k
  lemma-f*-^ᵣ w k = Eq.trans (Eq.cong (f ʷ) (lemma-[w^n]ᵣ=[w]ᵣ^n w k)) (lemma-fʷ-w^n k)

  lemma-f*-^ₗ : ∀ {n} (w : Word (XZ.Gen n)) k -> (f ʷ) ([ w ^ k ]ₗ) ≡ ((f ʷ) [ w ]ₗ) ^ k
  lemma-f*-^ₗ w k = Eq.trans (Eq.cong (f ʷ) (lemma-[w^n]ₗ=[w]ₗ^n w k)) (lemma-fʷ-w^n k)


  lemma-f*-S⁻¹↑ : ∀ {n} -> (f ʷ) ([ (S {n} ^ p-1) Sym.↑ ]ᵣ) ≡ Clifford.R ↑ ^ p-1
  lemma-f*-S⁻¹↑ {n} = begin
    (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) ≡⟨ lemma-f*-[w]ᵣ {w = S ^ p-1} ⟩
    (f ʷ) ([ S ^ p-1 ]ᵣ) ↑ ≡⟨ Eq.cong _↑ (lemma-f*-^ᵣ S p-1) ⟩
    (Clifford.R ^ p-1) ↑ ≡⟨ Lemmas-Clifford.lemma-↑^ p-1 Clifford.R ⟩
    Clifford.R ↑ ^ p-1 ∎
    where open ≡-Reasoning


  f-well-defined : ∀ {n w v} ->
    let
      open PB (n SemiDirect.QRel,_===_) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
      open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using ()
    in
    w ===₁ v -> (f ʷ) w ≈₂ (f ʷ) v

  f-well-defined {n@(₁₊ n')} (SD.order-X) = begin
    (f ʷ) ([ XZ.X ^ p ]ₗ) ≡⟨ Eq.cong (f ʷ) (lemma-[w^n]ₗ=[w]ₗ^n XZ.X p) ⟩
    (f ʷ) ([ XZ.X ]ₗ ^ p) ≡⟨ lemma-fʷ-w^n p ⟩
    ((f ʷ) [ XZ.X ]ₗ) ^ p ≈⟨ CL.lemma-order-X n' ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid

  f-well-defined {n@(₁₊ n')} (SD.order-Z) = begin
    (f ʷ) ([ XZ.Z ^ p ]ₗ) ≡⟨ Eq.cong (f ʷ) (lemma-[w^n]ₗ=[w]ₗ^n XZ.Z p) ⟩
    (f ʷ) ([ XZ.Z ]ₗ ^ p) ≡⟨ lemma-fʷ-w^n p ⟩
    ((f ʷ) [ XZ.Z ]ₗ) ^ p ≈⟨ CL.lemma-order-Z n' ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined (SD.comm-Z-X) = PB.sym (Lemmas1b.lemma-comm-X-Z _)
  -- At width ₁ the shifted generator is a Gen ₀, which gate₀ inhabits;
  -- neither gate set has a 0-ary gate, so the split goes one deeper.
  f-well-defined {₁₊ ₀} (left (XZ.comm₁ XZ.X-gate (XZ.gate₀ ())))
  f-well-defined {₁₊ ₀} (left (XZ.comm₁ XZ.Z-gate (XZ.gate₀ ())))
  f-well-defined {n@(₂₊ n2)} (left (XZ.comm₁ XZ.X-gate g)) = begin
    (f ʷ) ([ [ g XZ.↥ ]ʷ • XZ.X ]ₗ) ≡⟨ auto ⟩
    (f ʷ) ([ [ g XZ.↥ ]ʷ ]ₗ) • (f ʷ) ([ XZ.X ]ₗ) ≡⟨ auto ⟩
    (f ʷ) ([ [ g XZ.↥ ]ʷ ]ₗ) • Clifford.X ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-X-w↑ (f (inj₁ g))) ⟩
    Clifford.X • (f ʷ) ([ [ g XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    (f ʷ) ([ XZ.X • [ g XZ.↥ ]ʷ ]ₗ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₂₊ n2)} (left (XZ.comm₁ XZ.Z-gate g)) = begin
    (f ʷ) ([ [ g XZ.↥ ]ʷ • XZ.Z ]ₗ) ≡⟨ auto ⟩
    (f ʷ) ([ [ g XZ.↥ ]ʷ ]ₗ) • (f ʷ) ([ XZ.Z ]ₗ) ≡⟨ auto ⟩
    (f ʷ) ([ [ g XZ.↥ ]ʷ ]ₗ) • Clifford.Z ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-Z-w↑ (f (inj₁ g))) ⟩
    Clifford.Z • (f ʷ) ([ [ g XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    (f ʷ) ([ XZ.Z • [ g XZ.↥ ]ʷ ]ₗ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  -- cong↑ from width ₀: the Pauli relation there is empty, exactly as
  -- the symplectic one is below.  It needs saying now that XZ is a
  -- Lift-Relation, since the emptiness is no longer visible in the
  -- shape of a datatype.
  f-well-defined {₁₊ ₀} (left (XZ.cong↑ (XZ.srel ())))
  f-well-defined {n@(suc (n'@(₁₊ n'')))} (left (XZ.cong↑ {w = w} {v} x)) = begin
    (f ʷ) ([ w XZ.↑ ]ₗ) ≡⟨ lemma-f*-[w]ₗ {w = w} ⟩
    (f ʷ) ([ w ]ₗ) ↑ ≈⟨ Clifford-Relations.lemma-cong↑ ((f ʷ) ([ w ]ₗ)) ((f ʷ) ([ v ]ₗ)) (f-well-defined (left x)) ⟩
    (f ʷ) ([ v ]ₗ) ↑ ≡⟨ Eq.sym (lemma-f*-[w]ₗ {w = v}) ⟩
    (f ʷ) ([ v XZ.↑ ]ₗ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid

    lemma-f*-[w]ₗ : ∀ {n} {w : Word (XZ.Gen (n))} -> (f ʷ) [ w XZ.↑ ]ₗ ≡ (f ʷ) [ w ]ₗ ↑
    lemma-f*-[w]ₗ {n} {[ x ]ʷ} = auto
    lemma-f*-[w]ₗ {n} {ε} = auto
    lemma-f*-[w]ₗ {n} {w • w₁} rewrite lemma-f*-[w]ₗ {w = w} | lemma-f*-[w]ₗ {w = w₁} = auto

  f-well-defined {n@(₁₊ n')} (right (Sim.srel Sim.order-S)) = begin
    (f ʷ) ([ S ^ p ]ᵣ) ≡⟨ Eq.cong (f ʷ) (lemma-[w^n]ᵣ=[w]ᵣ^n S p) ⟩
    (f ʷ) ([ S ]ᵣ ^ p) ≡⟨ lemma-fʷ-w^n p ⟩
    ((f ʷ) [ S ]ᵣ) ^ p ≈⟨ CL.lemma-order-R n' ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  
  f-well-defined {n@(₁₊ n')} (right (Sim.srel Sim.order-H)) = begin
    (f ʷ) ([ H ^ 2 ]ᵣ) ≡⟨ auto ⟩
    Cli.H ^ 2 ≈⟨ _≈₂_.axiom Clifford.order-H ⟩
    Clifford.M₋₁ ≡⟨ Eq.sym (f-M' -'₁) ⟩
    (f ʷ) [ Sim.M₋₁ ]ᵣ ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
 
  f-well-defined {n@(₁₊ n')} (right (Sim.srel (Sim.M-power k))) =  begin
    (f ʷ) ([ Sim.Mg^ k ]ᵣ) ≡⟨ Eq.cong (f ʷ) (lemma-[w^n]ᵣ=[w]ᵣ^n Sim.Mg (toℕ k)) ⟩
    (f ʷ) ([ Sim.Mg ]ᵣ ^ toℕ k) ≡⟨ lemma-fʷ-w^n (toℕ k) ⟩
    (f ʷ) [ Sim.Mg ]ᵣ ^ toℕ k ≡⟨ Eq.cong (_^ toℕ k) (f-M' g*) ⟩
    Clifford.M g* ^ toℕ k ≈⟨ _≈₂_.axiom (Clifford.M-power k) ⟩
    Clifford.M (g^ k) ≡⟨ Eq.sym (f-M' (g^ k)) ⟩
    (f ʷ) [ Sym.M (g^ k) ]ᵣ ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
    open Primitive-Root-Modp' g* g-gen
    
  f-well-defined {n@(₁₊ n')} (right (Sim.srel Sim.semi-MS)) = begin
    (f ʷ) ([ Sim.Mg • S ]ᵣ) ≡⟨ auto ⟩
    (f ʷ) [ Sim.Mg ]ᵣ • (f ʷ) [ S ]ᵣ ≡⟨ Eq.cong (_• (f ʷ) [ S ]ᵣ) (f-M' g*) ⟩
    Clifford.M g* • (f ʷ) [ S ]ᵣ ≈⟨ _≈₂_.axiom Clifford.semi-MR ⟩
    Clifford.R^ (g * g) • Clifford.M g* ≡⟨ Eq.cong (Clifford.R^ (g * g) •_) (Eq.sym (f-M' g*)) ⟩
    Clifford.R^ (g * g) • (f ʷ) [ Sim.Mg ]ᵣ ≡⟨ Eq.cong (_• (f ʷ) [ Sim.Mg ]ᵣ) (Eq.sym (lemma-f*-^ᵣ S (toℕ (g * g)))) ⟩
    (f ʷ) ([ S ^ toℕ (g * g) ]ᵣ) • (f ʷ) [ Sim.Mg ]ᵣ ≡⟨ auto ⟩
    (f ʷ) ([ S^ (g * g) • Sim.Mg ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid

  f-well-defined {n@(suc (n'@(₁₊ n'')))} (right (Sim.srel Sim.semi-M↑CZ)) = begin
    (f ʷ) ([ Sim.Mg ↑ • CZ ]ᵣ) ≡⟨ auto ⟩
    (f ʷ) [ Sim.Mg ↑ ]ᵣ • Cli.CZ ≡⟨ Eq.cong (_• Cli.CZ) (lemma-f*-[w]ᵣ {w = Sim.Mg}) ⟩
    (f ʷ) [ Sim.Mg ]ᵣ ↑ • Cli.CZ ≡⟨ Eq.cong (\ x -> x ↑ • Cli.CZ) (f-M' g*) ⟩
    Clifford.M g* ↑ • Cli.CZ ≈⟨ _≈₂_.axiom Clifford.semi-M↑CZ ⟩
    CZ^ g • Clifford.M g* ↑ ≡⟨ Eq.cong (\ x -> CZ^ g • x ↑) (Eq.sym (f-M' g*)) ⟩
    CZ^ g • (f ʷ) [ Sim.Mg ]ᵣ ↑ ≡⟨ Eq.cong (CZ^ g •_) (Eq.sym (lemma-f*-[w]ᵣ {w = Sim.Mg})) ⟩
    CZ^ g • (f ʷ) [ Sim.Mg ↑ ]ᵣ ≡⟨ Eq.cong (_• (f ʷ) [ Sim.Mg ↑ ]ᵣ) (Eq.sym (lemma-f*-^ᵣ CZ (toℕ g))) ⟩
    (f ʷ) ([ CZ ^ toℕ g ]ᵣ) • (f ʷ) [ Sim.Mg ↑ ]ᵣ ≡⟨ auto ⟩
    (f ʷ) ([ CZ^ g • Sim.Mg ↑ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid

  f-well-defined {n@(suc (n'@(₁₊ n'')))} (right (Sim.srel Sim.semi-M↓CZ)) = begin
    (f ʷ) ([ Sim.Mg • CZ ]ᵣ) ≡⟨ auto ⟩
    (f ʷ) [ Sim.Mg ]ᵣ • Cli.CZ ≡⟨ Eq.cong (_• Cli.CZ) (f-M' g*) ⟩
    Clifford.M g* • Cli.CZ ≈⟨ _≈₂_.axiom Clifford.semi-M↓CZ ⟩
    CZ^ g • Clifford.M g* ≡⟨ Eq.cong (CZ^ g •_) (Eq.sym (f-M' g*)) ⟩
    CZ^ g • (f ʷ) [ Sim.Mg ]ᵣ ≡⟨ Eq.cong (_• (f ʷ) [ Sim.Mg ]ᵣ) (Eq.sym (lemma-f*-^ᵣ CZ (toℕ g))) ⟩
    (f ʷ) ([ CZ ^ toℕ g ]ᵣ) • (f ʷ) [ Sim.Mg ]ᵣ ≡⟨ auto ⟩
    (f ʷ) ([ CZ^ g • Sim.Mg ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(suc (n'@(₁₊ n'')))} (right (Sim.srel Sim.order-CZ)) = begin
    (f ʷ) ([ CZ ^ p ]ᵣ) ≡⟨ Eq.cong (f ʷ) (lemma-[w^n]ᵣ=[w]ᵣ^n CZ p) ⟩
    (f ʷ) ([ CZ ]ᵣ ^ p) ≡⟨ lemma-fʷ-w^n p ⟩
    ((f ʷ) [ CZ ]ᵣ) ^ p ≈⟨ _≈₂_.axiom Clifford.order-CZ ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.srel Sim.comm-CZ-S↓)) = begin
    (f ʷ) ([ CZ • S ]ᵣ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.R ≈⟨ sym₂ lemma-comm-R-CZ ⟩
    Clifford.R • Cli.CZ ≡⟨ auto ⟩
    (f ʷ) ([ S • CZ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.srel Sim.comm-CZ-S↑)) = begin
    (f ʷ) ([ CZ • S Sym.↑ ]ᵣ) ≡⟨ Eq.cong (\ x -> Cli.CZ • x) (lemma-f*-[w]ᵣ {w = S}) ⟩
    Cli.CZ • Clifford.R ↑ ≈⟨ sym₂ lemma-comm-R↑-CZ ⟩
    Clifford.R ↑ • Cli.CZ ≡⟨ Eq.cong (\ x -> x • Cli.CZ) (Eq.sym (lemma-f*-[w]ᵣ {w = S})) ⟩
    (f ʷ) ([ S Sym.↑ • CZ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.srel Sim.selinger-c10)) = begin
    (f ʷ) ([ CZ • H Sym.↑ • CZ ]ᵣ) ≡⟨ auto ⟩
    Cli.CZ • Cli.H ↑ • Cli.CZ ≈⟨ _≈₂_.axiom Clifford.selinger-c10 ⟩
    Clifford.R ↑ ^ p-1 • Cli.H ↑ • Clifford.R ↑ ^ p-1 • Cli.CZ • Cli.H ↑ • Clifford.R ↑ ^ p-1 • Clifford.R ^ p-1
      ≡⟨ Eq.cong (\ x -> x • Cli.H ↑ • Clifford.R ↑ ^ p-1 • Cli.CZ • Cli.H ↑ • Clifford.R ↑ ^ p-1 • Clifford.R ^ p-1) (Eq.sym lemma-f*-S⁻¹↑) ⟩
    (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • Clifford.R ↑ ^ p-1 • Cli.CZ • Cli.H ↑ • Clifford.R ↑ ^ p-1 • Clifford.R ^ p-1
      ≡⟨ Eq.cong (\ x -> (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • x • Cli.CZ • Cli.H ↑ • Clifford.R ↑ ^ p-1 • Clifford.R ^ p-1) (Eq.sym lemma-f*-S⁻¹↑) ⟩
    (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • Clifford.R ↑ ^ p-1 • Clifford.R ^ p-1
      ≡⟨ Eq.cong (\ x -> (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • x • Clifford.R ^ p-1) (Eq.sym lemma-f*-S⁻¹↑) ⟩
    (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Clifford.R ^ p-1
      ≡⟨ Eq.cong (\ x -> (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • x) (Eq.sym (lemma-f*-^ᵣ S p-1)) ⟩
    (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.H ↑ • (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • Cli.CZ • Cli.H ↑ • (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ) • (f ʷ) ([ S ^ p-1 ]ᵣ)
      ≡⟨ auto ⟩
    (f ʷ) ([ (S ^ p-1) Sym.↑ • H Sym.↑ • (S ^ p-1) Sym.↑ • CZ • H Sym.↑ • (S ^ p-1) Sym.↑ • S ^ p-1 ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.srel Sim.selinger-c11)) = begin
    (f ʷ) ([ CZ • H • CZ ]ᵣ) ≡⟨ auto ⟩
    Cli.CZ • Cli.H • Cli.CZ ≈⟨ _≈₂_.axiom Clifford.selinger-c11 ⟩
    Clifford.R ^ p-1 • Cli.H • Clifford.R ^ p-1 • Cli.CZ • Cli.H • Clifford.R ^ p-1 • Clifford.R ↑ ^ p-1
      ≡⟨ Eq.cong (\ x -> x • Cli.H • Clifford.R ^ p-1 • Cli.CZ • Cli.H • Clifford.R ^ p-1 • Clifford.R ↑ ^ p-1) (Eq.sym (lemma-f*-^ᵣ S p-1)) ⟩
    (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.H • Clifford.R ^ p-1 • Cli.CZ • Cli.H • Clifford.R ^ p-1 • Clifford.R ↑ ^ p-1
      ≡⟨ Eq.cong (\ x -> (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.H • x • Cli.CZ • Cli.H • Clifford.R ^ p-1 • Clifford.R ↑ ^ p-1) (Eq.sym (lemma-f*-^ᵣ S p-1)) ⟩
    (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.H • (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • Clifford.R ^ p-1 • Clifford.R ↑ ^ p-1
      ≡⟨ Eq.cong (\ x -> (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.H • (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • x • Clifford.R ↑ ^ p-1) (Eq.sym (lemma-f*-^ᵣ S p-1)) ⟩
    (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.H • (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • (f ʷ) ([ S ^ p-1 ]ᵣ) • Clifford.R ↑ ^ p-1
      ≡⟨ Eq.cong (\ x -> (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.H • (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • (f ʷ) ([ S ^ p-1 ]ᵣ) • x) (Eq.sym lemma-f*-S⁻¹↑) ⟩
    (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.H • (f ʷ) ([ S ^ p-1 ]ᵣ) • Cli.CZ • Cli.H • (f ʷ) ([ S ^ p-1 ]ᵣ) • (f ʷ) ([ (S ^ p-1) Sym.↑ ]ᵣ)
      ≡⟨ auto ⟩
    (f ʷ) ([ S ^ p-1 • H • S ^ p-1 • CZ • H • S ^ p-1 • (S ^ p-1) Sym.↑ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.srel Sim.selinger-c12)) = begin
    (f ʷ) ([ CZ ↑ • CZ ]ᵣ) ≡⟨ auto ⟩
    Cli.CZ ↑ • Cli.CZ ≈⟨ _≈₂_.axiom Clifford.selinger-c12 ⟩
    Cli.CZ • Cli.CZ ↑ ≡⟨ auto ⟩
    (f ʷ) ([ CZ • CZ ↑ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.srel Sim.selinger-c13)) = begin
    (f ʷ) ([ ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ ]ᵣ) ≡⟨ auto ⟩
    Cli.⊤⊥ ↑ • Cli.CZ ↓ • Cli.⊥⊤ ↑ ≈⟨ _≈₂_.axiom Clifford.selinger-c13 ⟩
    Cli.⊥⊤ ↓ • Cli.CZ ↑ • Cli.⊤⊥ ↓ ≡⟨ auto ⟩
    (f ʷ) ([ ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.srel Sim.selinger-c14)) = begin
    (f ʷ) ([ (⊤⊥ ↑ • CZ ↓) ^ 3 ]ᵣ) ≡⟨ auto ⟩
    (Cli.⊤⊥ ↑ • Cli.CZ ↓) ^ 3 ≈⟨ _≈₂_.axiom Clifford.selinger-c14 ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n} (right (Sim.srel Sim.selinger-c15)) = begin
    (f ʷ) ([ (⊥⊤ ↓ • CZ ↑) ^ 3 ]ᵣ) ≡⟨ auto ⟩
    (Cli.⊥⊤ ↓ • Cli.CZ ↑) ^ 3 ≈⟨ _≈₂_.axiom Clifford.selinger-c15 ⟩
    ε ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  -- comm₁/comm₂ carry a generator one (resp. two) wires below the gate, and
  -- the Clifford commutation lemmas are stated at ₂₊/₃₊, so the real work
  -- starts one wire higher; at the minimal width the generator is a Gen ₀,
  -- of which there is none.
  -- (Gen ₀ is inhabited only by gate₀, and SympGate has no 0-ary gate,
  -- so the split has to go one constructor deeper than a bare `()`.)
  f-well-defined {₁₊ ₀} (right (Sim.comm₁ Sym.H-gate (Sym.gate₀ ())))
  f-well-defined {n@(₂₊ n')} (right (Sim.comm₁ Sym.H-gate x)) = begin
    (f ʷ) ([ [ x Sym.↥ ]ʷ • H ]ᵣ) ≡⟨ auto ⟩
    (f (inj₂ x)) ↑ • Cli.H ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-H-w↑ (f (inj₂ x))) ⟩
    Cli.H • (f (inj₂ x)) ↑ ≡⟨ auto ⟩
    (f ʷ) ([ H • [ x Sym.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {₁₊ ₀} (right (Sim.comm₁ Sym.S-gate (Sym.gate₀ ())))
  f-well-defined {n@(₂₊ n')} (right (Sim.comm₁ Sym.S-gate x)) = begin
    (f ʷ) ([ [ x Sym.↥ ]ʷ • S ]ᵣ) ≡⟨ auto ⟩
    (f (inj₂ x)) ↑ • Clifford.R ≈⟨ sym₂ (lemma-comm-R-w↑ (f (inj₂ x))) ⟩
    Clifford.R • (f (inj₂ x)) ↑ ≡⟨ auto ⟩
    (f ʷ) ([ S • [ x Sym.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {₂₊ ₀} (right (Sim.comm₂ Sym.CZ-gate (Sym.gate₀ ())))
  f-well-defined {n@(₃₊ n')} (right (Sim.comm₂ Sym.CZ-gate x)) = begin
    (f ʷ) ([ [ x Sym.↥ Sym.↥ ]ʷ • CZ ]ᵣ) ≡⟨ auto ⟩
    (f (inj₂ x)) ↑ ↑ • Cli.CZ ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-CZ-w↑ (f (inj₂ x))) ⟩
    Cli.CZ • (f (inj₂ x)) ↑ ↑ ≡⟨ auto ⟩
    (f ʷ) ([ CZ • [ x Sym.↥ Sym.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  -- cong↑ from width ₀: the symplectic relation there is empty.
  f-well-defined {₁₊ ₀} (right (Sim.cong↑ (Sim.srel ())))
  f-well-defined {n@(suc (n'@(₁₊ n'')))} (right (Sim.cong↑ {w = w} {v} x)) = begin
    (f ʷ) ([ w Sym.↑ ]ᵣ) ≡⟨ lemma-f*-[w]ᵣ {w = w} ⟩
    (f ʷ) ([ w ]ᵣ) ↑ ≈⟨ Clifford-Relations.lemma-cong↑ ((f ʷ) ([ w ]ᵣ)) ((f ʷ) ([ v ]ᵣ)) (f-well-defined (right x)) ⟩
    (f ʷ) ([ v ]ᵣ) ↑ ≡⟨ Eq.sym (lemma-f*-[w]ᵣ {w = v}) ⟩
    (f ʷ) ([ v Sym.↑ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid


  -- Neither factor has a 0-ary gate, so a gate₀ on either side of the
  -- commutation is absurd.  One clause per shape Agda splits into: the
  -- absurd pattern has to sit where the case tree actually branches.
  f-well-defined (mid (comm (XZ.gate₀ ()) _))
  f-well-defined (mid (comm ((XZ.gate₀ ()) XZ.↥) _))
  f-well-defined (mid (comm (((XZ.gate₀ ()) XZ.↥) XZ.↥) _))
  f-well-defined (mid (comm XZ.X-gen (Sym.gate₀ ())))
  f-well-defined (mid (comm XZ.Z-gen (Sym.gate₀ ())))
  f-well-defined (mid (comm (n₁ XZ.↥) (Sym.gate₀ ())))
  -- STILL INCOMPLETE: two `mid (comm n h)` cases remain, both fallout
  -- from gate₀ inhabiting Gen ₀.  They need Agda's own case split to
  -- locate; the absurd pattern has to sit exactly where the case tree
  -- branches, and the clauses above cover every position I could find
  -- by hand.
  f-well-defined {n@(₁₊ n')} (mid (comm XZ.X-gen Sym.H-gen)) = begin
    (f ʷ) ([ [ Sym.H-gen ]ʷ ]ᵣ • [ [ XZ.X-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.H • Clifford.X ≈⟨ CLb.conj-H-X n' ⟩
    Clifford.Z • Cli.H ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.H-gen XZ.X-gen ]ₗ • [ [ Sym.H-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₁₊ n')} (mid (comm XZ.X-gen Sym.S-gen)) = begin
    (f ʷ) ([ [ Sym.S-gen ]ʷ ]ᵣ • [ [ XZ.X-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Clifford.R • Clifford.X ≈⟨ lemma-conj-R-X ⟩
    (Clifford.X • Clifford.Z) • Clifford.R ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.S-gen XZ.X-gen ]ₗ • [ [ Sym.S-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₂₊ n')} (mid (comm XZ.X-gen Sym.CZ-gen)) = begin
    (f ʷ) ([ [ Sym.CZ-gen ]ʷ ]ᵣ • [ [ XZ.X-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.X ≈⟨ _≈₂_.axiom Clifford.rel-X↓-CZ ⟩
    Clifford.X • Clifford.Z ↑ • Cli.CZ ≈⟨ sym₂ assoc₂ ⟩
    (Clifford.X • Clifford.Z ↑) • Cli.CZ ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.CZ-gen XZ.X-gen ]ₗ • [ [ Sym.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂ ; assoc to assoc₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₂₊ n')} (mid (comm XZ.X-gen (h₁ Sym.↥))) = begin
    (f ʷ) ([ [ h₁ Sym.↥ ]ʷ ]ᵣ • [ [ XZ.X-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    (f (inj₂ h₁)) ↑ • Clifford.X ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-X-w↑ (f (inj₂ h₁))) ⟩
    Clifford.X • (f (inj₂ h₁)) ↑ ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj (h₁ Sym.↥) XZ.X-gen ]ₗ • [ [ h₁ Sym.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₁₊ n')} (mid (comm XZ.Z-gen Sym.H-gen)) = begin
    (f ʷ) ([ [ Sym.H-gen ]ʷ ]ᵣ • [ [ XZ.Z-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.H • Clifford.Z ≈⟨ CLb.conj-H-Z n' ⟩
    Clifford.X^ (- ₁) • Cli.H ≡⟨ Eq.cong (\ x -> Clifford.X ^ x • Cli.H) lemma-toℕ-1ₚ ⟩
    Clifford.X ^ p-1 • Cli.H ≡⟨ Eq.cong (_• Cli.H) (Eq.sym (lemma-f*-^ₗ XZ.X p-1)) ⟩
    (f ʷ) ([ XZ.X ^ p-1 ]ₗ) • Cli.H ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.H-gen XZ.Z-gen ]ₗ • [ [ Sym.H-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₁₊ n')} (mid (comm XZ.Z-gen Sym.S-gen)) = begin
    (f ʷ) ([ [ Sym.S-gen ]ʷ ]ᵣ • [ [ XZ.Z-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Clifford.R • Clifford.Z ≈⟨ lemma-comm-R-Z ⟩
    Clifford.Z • Clifford.R ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.S-gen XZ.Z-gen ]ₗ • [ [ Sym.S-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₂₊ n')} (mid (comm XZ.Z-gen Sym.CZ-gen)) = begin
    (f ʷ) ([ [ Sym.CZ-gen ]ʷ ]ᵣ • [ [ XZ.Z-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.Z ≈⟨ sym₂ lemma-comm-Z-CZ ⟩
    Clifford.Z • Cli.CZ ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.CZ-gen XZ.Z-gen ]ₗ • [ [ Sym.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₂₊ n')} (mid (comm XZ.Z-gen (h₁ Sym.↥))) = begin
    (f ʷ) ([ [ h₁ Sym.↥ ]ʷ ]ᵣ • [ [ XZ.Z-gen ]ʷ ]ₗ) ≡⟨ auto ⟩
    (f (inj₂ h₁)) ↑ • Clifford.Z ≈⟨ sym₂ (Lemmas-Clifford.lemma-comm-Z-w↑ (f (inj₂ h₁))) ⟩
    Clifford.Z • (f (inj₂ h₁)) ↑ ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj (h₁ Sym.↥) XZ.Z-gen ]ₗ • [ [ h₁ Sym.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₂₊ n')} (mid (comm (n₁ XZ.↥) Sym.H-gen)) = begin
    (f ʷ) ([ [ Sym.H-gen ]ʷ ]ᵣ • [ [ n₁ XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.H • (f (inj₁ n₁)) ↑ ≈⟨ Lemmas-Clifford.lemma-comm-H-w↑ (f (inj₁ n₁)) ⟩
    (f (inj₁ n₁)) ↑ • Cli.H ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.H-gen (n₁ XZ.↥) ]ₗ • [ [ Sym.H-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₂₊ n')} (mid (comm (n₁ XZ.↥) Sym.S-gen)) = begin
    (f ʷ) ([ [ Sym.S-gen ]ʷ ]ᵣ • [ [ n₁ XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Clifford.R • (f (inj₁ n₁)) ↑ ≈⟨ lemma-comm-R-w↑ (f (inj₁ n₁)) ⟩
    (f (inj₁ n₁)) ↑ • Clifford.R ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.S-gen (n₁ XZ.↥) ]ₗ • [ [ Sym.S-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₂₊ n')} (mid (comm (XZ.X-gen XZ.↥) Sym.CZ-gen)) = begin
    (f ʷ) ([ [ Sym.CZ-gen ]ʷ ]ᵣ • [ [ XZ.X-gen XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.X ↑ ≈⟨ _≈₂_.axiom Clifford.rel-X↑-CZ ⟩
    Clifford.X ↑ • Clifford.Z • Cli.CZ ≈⟨ sym₂ assoc₂ ⟩
    (Clifford.X ↑ • Clifford.Z) • Cli.CZ ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.CZ-gen (XZ.X-gen XZ.↥) ]ₗ • [ [ Sym.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂ ; assoc to assoc₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₂₊ n')} (mid (comm (XZ.Z-gen XZ.↥) Sym.CZ-gen)) = begin
    (f ʷ) ([ [ Sym.CZ-gen ]ʷ ]ᵣ • [ [ XZ.Z-gen XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • Clifford.Z ↑ ≈⟨ sym₂ lemma-comm-Z↑-CZ ⟩
    Clifford.Z ↑ • Cli.CZ ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.CZ-gen (XZ.Z-gen XZ.↥) ]ₗ • [ [ Sym.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_ ; sym to sym₂) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₃₊ n')} (mid (comm ((m XZ.↥) XZ.↥) Sym.CZ-gen)) = begin
    (f ʷ) ([ [ Sym.CZ-gen ]ʷ ]ᵣ • [ [ (m XZ.↥) XZ.↥ ]ʷ ]ₗ) ≡⟨ auto ⟩
    Cli.CZ • (f (inj₁ m)) ↑ ↑ ≈⟨ Lemmas-Clifford.lemma-comm-CZ-w↑ (f (inj₁ m)) ⟩
    (f (inj₁ m)) ↑ ↑ • Cli.CZ ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj Sym.CZ-gen ((m XZ.↥) XZ.↥) ]ₗ • [ [ Sym.CZ-gen ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    open SR word-setoid
  f-well-defined {n@(₁₊ n')} (mid (comm (n₁ XZ.↥) (h₁ Sym.↥))) = begin
    (f ʷ) ([ [ h₁ Sym.↥ ]ʷ ]ᵣ • [ [ n₁ XZ.↥ ]ʷ ]ₗ) ≡⟨ Eq.sym (lemma-f*-SD↑ ([ [ h₁ ]ʷ ]ᵣ • [ [ n₁ ]ʷ ]ₗ)) ⟩
    (f ʷ) ([ [ h₁ ]ʷ ]ᵣ • [ [ n₁ ]ʷ ]ₗ) ↑ ≈⟨ Clifford-Relations.lemma-cong↑ _ _ (f-well-defined (mid (comm n₁ h₁))) ⟩
    (f ʷ) ([ SemiDirect.conj h₁ n₁ ]ₗ • [ [ h₁ ]ʷ ]ᵣ) ↑ ≡⟨ Eq.sym (lemma-f*-SD↑ ([ SemiDirect.conj h₁ n₁ ]ₗ • [ [ h₁ ]ʷ ]ᵣ)) ⟩
    (f ʷ) (SD._↑ {n'} ([ SemiDirect.conj h₁ n₁ ]ₗ • [ [ h₁ ]ʷ ]ᵣ)) ≡⟨ auto ⟩
    (f ʷ) (SD._↑ {n'} ([_]ₗ {B = Sym.Gen n'} (SemiDirect.conj h₁ n₁)) • [ [ h₁ Sym.↥ ]ʷ ]ᵣ) ≡⟨ Eq.cong (\ x -> (f ʷ) (x • [ [ h₁ Sym.↥ ]ʷ ]ᵣ)) bridge ⟩
    (f ʷ) ([_]ₗ {B = Sym.Gen (₁₊ n')} (SemiDirect.conj h₁ n₁ XZ.↑) • [ [ h₁ Sym.↥ ]ʷ ]ᵣ) ≡⟨ auto ⟩
    (f ʷ) ([ SemiDirect.conj (h₁ Sym.↥) (n₁ XZ.↥) ]ₗ • [ [ h₁ Sym.↥ ]ʷ ]ᵣ) ∎
    where
    open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using (refl')
    open PP (n Clifford.QRel,_===_)
    bridge : SD._↑ {n'} ([_]ₗ {B = Sym.Gen n'} (SemiDirect.conj h₁ n₁)) ≡ [_]ₗ {B = Sym.Gen (₁₊ n')} (SemiDirect.conj h₁ n₁ XZ.↑)
    bridge = lemma-[]ₗ-↑' (SemiDirect.conj h₁ n₁)
    open SR word-setoid
