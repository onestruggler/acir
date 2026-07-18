------------------------------------------------------------------------
-- Presentations of groups
--
-- The action on Simplified circuits, via the Sim ≅ Derived isomorphism
------------------------------------------------------------------------

{-# OPTIONS --safe --termination-depth=2 #-}

open import Data.Fin using (toℕ ; fromℕ<)
open import Data.Fin.Properties using (fromℕ<-cong ; fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ<n)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.Nat.DivMod
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; proj₁ ; ∃)
open import Function using (_∘_ ; id)
open import Notations
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.Rewriting hiding ([_])
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR
open import Word.Base hiding (wfoldl)
open import Zp.Fermats-little-theorem
open import Zp.ModularArithmetic
module Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.Action-Sym
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime hiding (act))
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where
open Primitive-Root-Modp' g* g-gen

private
  variable
    n : ℕ

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime as SD
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
open import Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit p-2 p-prime
open Lemmas-2Q 2 hiding (lemma-CZ^k-%)
open Symplectic
open Simplified-Relations

open import Examples.Groups.Pauli.Semantics p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Iso-Sym-Derived p-2 p-prime hiding (module G1 ; module G2)
open Iso

open SymDerived renaming (Gen to Gen₃ ; _QRel,_===_ to _QRel,_===₃_) using ()

der : Word (Gen₂ n) -> Word (Gen₃ n)
der {n} = ((f'* {n}) ∘ id)

open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.Properties p-2 p-prime renaming (act to dact) using ()
act : ∀ {n} → Word (Gen n) → Pauli n → Pauli n
act {n} w ps = dact (der w) ps


module D = SymDerived


lemma-der' : let open PB ((₁₊ n) QRel,_===₃_) in
  ∀ k -> der (S ^ k) ≈ D.S ^ k
lemma-der' ₀ = PB.refl
lemma-der' ₁ = PB.refl
lemma-der' (₂₊ k) = PB.cong PB.refl (lemma-der' (₁₊ k))


lemma-der'' : ∀ k ->
  let
  open PB ((₁₊ n) QRel,_===₃_)
  k' = fromℕ< (m%n<n k p)
  in
  der (S ^ k) ≈ D.S^ k'
lemma-der'' {n} k = begin
  der (S ^ k) ≈⟨ lemma-der' k ⟩
  D.S ^ k ≈⟨ lemma-S^k-% k ⟩
  D.S ^ (k Nat.% p) ≈⟨ refl' (Eq.cong (D.S ^_) (Eq.sym ( toℕ-fromℕ< (m%n<n k p)))) ⟩
  D.S ^ toℕ k' ≈⟨ sym (axiom (D.srel (D.derived-S k'))) ⟩
  D.S^ k' ∎
  where
  open PB ((₁₊ n) QRel,_===₃_)
  open PP ((₁₊ n) QRel,_===₃_)
  open SR word-setoid
  k' = fromℕ< (m%n<n k p)
  open SD.Lemmas0 n

lemma-der : let open PB ((₁₊ n) QRel,_===₃_) in
  ∀ k -> der (S^ k) ≈ D.S^ k
lemma-der {n} k = begin
  der (S^ k) ≈⟨ refl ⟩
  der (S ^ toℕ k) ≈⟨ lemma-der'' (toℕ k) ⟩
  D.S^ k' ≈⟨ refl' (Eq.cong D.S^ (fromℕ<-cong (toℕ k Nat.% p) (toℕ k) (m<n⇒m%n≡m (toℕ<n k)) (m%n<n (toℕ k) p) (toℕ<n k))) ⟩
  D.S^ k'' ≈⟨ refl' (Eq.cong D.S^ (fromℕ<-toℕ k (toℕ<n k))) ⟩
  D.S^ k ∎
  where
  open PB ((₁₊ n) QRel,_===₃_)
  open PP ((₁₊ n) QRel,_===₃_)
  open SR word-setoid
  k'' : ℤ ₚ
  k'' = fromℕ< (toℕ<n k)
  k' = fromℕ< (m%n<n (toℕ k) p)
  open SD.Lemmas0 n




lemma-derH : ∀ k ->
  let
  open PB ((₁₊ n) QRel,_===₃_)
  in
  der (H^ k) ≈ D.H^ k
lemma-derH {n} ₀ = PB.sym (PB.axiom (D.srel (D.derived-H ₀)))
lemma-derH {n} ₁ = PB.refl
lemma-derH {n} ₂ = PB.sym (PB.axiom (D.srel (D.derived-H ₂)))
lemma-derH {n} ₃ = PB.sym (PB.axiom (D.srel (D.derived-H ₃)))



lemma-derM : let open PB ((₁₊ n) QRel,_===₃_) in
  ∀ k -> der (M k) ≈ D.M k
lemma-derM {n} k*@(k , nz) = cong (lemma-der k) (cong (lemma-derH ₁) (cong (lemma-der k⁻¹) (cong (lemma-derH ₁) (cong (lemma-der k) refl))))
  where
  open PB ((₁₊ n) QRel,_===₃_)
  open PP ((₁₊ n) QRel,_===₃_)
  open SR word-setoid
  k⁻¹ = (k* ⁻¹) .proj₁


lemma-derCZ' : let open PB ((₂₊ n) QRel,_===₃_) in
  ∀ k -> der (CZ ^ k) ≈ D.CZ ^ k
lemma-derCZ' ₀ = PB.refl
lemma-derCZ' ₁ = PB.refl
lemma-derCZ' (₂₊ k) = PB.cong PB.refl (lemma-derCZ' (₁₊ k))


lemma-derCZ'' : ∀ k ->
  let
  open PB ((₂₊ n) QRel,_===₃_)
  k' = fromℕ< (m%n<n k p)
  in
  der (CZ ^ k) ≈ D.CZ^ k'
lemma-derCZ'' {n} k = begin
  der (CZ ^ k) ≈⟨ lemma-derCZ' k ⟩
  D.CZ ^ k ≈⟨ lemma-CZ^k-% k ⟩
  D.CZ ^ (k Nat.% p) ≈⟨ refl' (Eq.cong (D.CZ ^_) (Eq.sym ( toℕ-fromℕ< (m%n<n k p)))) ⟩
  D.CZ ^ toℕ k' ≈⟨ sym (axiom (D.srel (D.derived-CZ k'))) ⟩
  D.CZ^ k' ∎
  where
  open PB ((₂₊ n) QRel,_===₃_)
  open PP ((₂₊ n) QRel,_===₃_)
  open SR word-setoid
  k' = fromℕ< (m%n<n k p)
  open SD.Lemmas-1 n

lemma-derCZ : let open PB ((₂₊ n) QRel,_===₃_) in
  ∀ k -> der (CZ^ k) ≈ D.CZ^ k
lemma-derCZ {n} k = begin
  der (CZ^ k) ≈⟨ refl ⟩
  der (CZ ^ toℕ k) ≈⟨ lemma-derCZ'' (toℕ k) ⟩
  D.CZ^ k' ≈⟨ refl' (Eq.cong D.CZ^ (fromℕ<-cong (toℕ k Nat.% p) (toℕ k) (m<n⇒m%n≡m (toℕ<n k)) (m%n<n (toℕ k) p) (toℕ<n k))) ⟩
  D.CZ^ k'' ≈⟨ refl' (Eq.cong D.CZ^ (fromℕ<-toℕ k (toℕ<n k))) ⟩
  D.CZ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===₃_)
  open PP ((₂₊ n) QRel,_===₃_)
  open SR word-setoid
  k'' : ℤ ₚ
  k'' = fromℕ< (toℕ<n k)
  k' = fromℕ< (m%n<n (toℕ k) p)
  open SD.Lemmas0 n
