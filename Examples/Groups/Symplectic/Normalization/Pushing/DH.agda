{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq


open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)

open import Data.Empty using (⊥-elim)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


open import Data.Nat.Primality


module Examples.Groups.Symplectic.Normalization.Pushing.DH (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where

private
  variable
    n : ℕ
    

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open import Examples.Groups.Symplectic.NF1-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime

open import Examples.Groups.Symplectic.NF2-Sym p-2 p-prime
open LM2


--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime

open Lemmas0a
open Lemmas0a1
open Lemmas0b
open Lemmas0c
open Lemmas-Sym
open Duality

open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime


aux-mc1ε : let open PB ((₁₊ n) QRel,_===_) in ⟦ ₁* , ε ⟧ₘ₊ ≈ ε
aux-mc1ε {n} = PB.trans (PB.cong (PB.sym lemma-M1) PB.refl) PB.left-unit
  where
  open Lemmas0 n


aux-b≠0⇒ab≠0 : ∀ (a b : ℤ ₚ) (nz : b ≢ ₀) → _≢_ {A = ℤ ₚ × ℤ ₚ} (a , b) (₀ , ₀)
aux-b≠0⇒ab≠0 a b nz eq0 = ⊥-elim (nz (Eq.cong proj₂ eq0))

aux-abox-nza : let open PB ((₁₊ n) QRel,_===_) in ∀ a b → (nz : a ≢ ₀) →
  let
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹
  in
  [ (a , b) , aux-a≠0⇒ab≠0 a b nz ]ᵃ ≈  ⟦ (a , nz) ⁻¹ , HS^ -b/a ⟧ₘ₊
aux-abox-nza {n} a@₀ b nz = ⊥-elim (nz auto)
-- [_]ᵃ is built from XM; the ⟦_⟧ₘ₊ form on the right is the ZM one, and
-- the two are exchanged by inversion.
aux-abox-nza {n} a@(₁₊ a-1) b nz =
  refl' (Eq.cong (_• (H • S^ -b/a)) (XM≡ZM⁻¹ (a , nz)))
  where
  open PB ((₁₊ n) QRel,_===_)
  a⁻¹ = ((a , nz) ⁻¹) .proj₁
  -b/a = - b * a⁻¹


aux-abox-nzb : let open PB ((₁₊ n) QRel,_===_) in ∀ b → (nz : b ≢ ₀) →
  [ (₀ , b) , aux-b≠0⇒ab≠0 ₀ b nz ]ᵃ ≈  ⟦ (b , nz) ⁻¹ ⟧ₘ
aux-abox-nzb {n} b@₀ nz = ⊥-elim (nz auto)
aux-abox-nzb {n} b@(₁₊ b-1) nz = refl' (XM≡ZM⁻¹ (b , nz))
  where
  open PB ((₁₊ n) QRel,_===_)
