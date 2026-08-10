{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq



open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)


open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Notations



open import Data.Fin using (toℕ)
open import Presentation.GroupLike
open import Data.Nat.Primality



module Examples.Groups.Symplectic.BR.Two.Lemmas3 (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

n : ℕ
n = 0
    




open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic



open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
--open Lemmas-2Q 2

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym4 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime

open Lemmas-Sym



open PB ((₂₊ n) QRel,_===_)
open PP ((₂₊ n) QRel,_===_)
open SR word-setoid
open Pattern-Assoc
sa = by-passoc
open Lemmas0 n
module L01 = Lemmas0 (₁₊ n)
open Lemmas-2Q n
open Sym0-Rewriting (₁₊ n)
open Symplectic-GroupLike
open Basis-Change _ ((₂₊ n) QRel,_===_) grouplike

open Rewriting-Swap 1
open Commuting-Symplectic 0


⌶ : ∀ {n} → Word (Gen (₂₊ n))
⌶ = H ↓ • H ↑ • CZ • H ↓ • H ↑


aux-hEx-4 : H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex ≈ H ↓ • H ↑ • CZ • H ↓ • H ↑
aux-hEx-4 = bbc (H ↑ ^ 2) (Ex • H ^ 2) claim
  where
  claim : H ↑ ^ 2 • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex) • (Ex • H ^ 2) ≈ H ↑ ^ 2 • (H ↓ • H ↑ • CZ • H ↓ • H ↑) • (Ex • H ^ 2)
  claim = begin
    H ↑ ^ 2 • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex) • (Ex • H ^ 2) ≈⟨ rewrite-swap 100 auto ⟩
    CZ • H • H ↑ • CZ ≈⟨ aux-hEx'' ⟩
    H ↑ • H ↓ • (CZ⁻¹) • H ↑ • H ↓ • Ex ≈⟨ cright cright cleft sym right-unit ⟩
    H ↑ • H ↓ • (CZ⁻¹ • ε) • H ↑ • H ↓ • Ex ≈⟨ cright cright cleft (cong (refl' (Eq.cong (CZ ^_) (Eq.sym lemma-toℕ₋₁))) (rewrite-sym0 100 auto)) ⟩
    H ↑ • H ↓ • (CZ^ ₋₁ • H ↑ ^ 2 • H ↑ ^ 2) • H ↑ • H ↓ • Ex ≈⟨ cright cright cleft sym assoc ⟩
    H ↑ • H ↓ • ((CZ^ ₋₁ • H ↑ ^ 2) • H ↑ ^ 2) • H ↑ • H ↓ • Ex ≈⟨ cright cright cleft cleft sym lemma-semi-HH↑-CZ ⟩
    H ↑ • H ↓ • ((H ↑ ^ 2 • CZ) • H ↑ ^ 2) • H ↑ • H ↓ • Ex ≈⟨ general-comm auto ⟩
    H ↑ ^ 2 • (H ↓ • H ↑ • CZ • H ↓ • H ↑) • (H ↑ ^ 2 • Ex) ≈⟨ cright cright rewrite-swap 100 auto ⟩
    H ↑ ^ 2 • (H ↓ • H ↑ • CZ • H ↓ • H ↑) • (Ex • H ^ 2) ∎

y≠1⇒1-y≠0 : ∀ (y : ℤ ₚ) -> y ≢ ₁ -> ₁ + - y ≢ ₀
y≠1⇒1-y≠0 y neq1 eq0 = neq1 ((Eq.trans (Eq.trans (Eq.sym (+-identityˡ y)) (Eq.cong (_+ y) (Eq.sym eq0))) (Eq.trans (+-assoc ₁ (- y ) y) (Eq.trans (Eq.cong (₁ +_) (+-inverseˡ y)) (+-identityʳ ₁)))))

aux-M|| : ∀ (y*@(y , nz) : ℤ* ₚ) -> M (y* ⁻¹) ↑ • CZ^ y • H • H ↑ • CZ • M (y* ⁻¹) ↑ ≈ CZ • H • H ↑ • CZ^ y
aux-M|| y*@(y , nz) = begin
  M (y* ⁻¹) ↑ • CZ^ y • H • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ sym assoc ⟩
  (M (y* ⁻¹) ↑ • CZ^ y) • H • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ cleft lemma-M↑CZ^k y⁻¹ y ((y* ⁻¹) .proj₂) ⟩
  (CZ^ (y * y⁻¹) • M (y* ⁻¹) ↑) • H • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  CZ^ (y * y⁻¹) • (M (y* ⁻¹) ↑ • H) • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ cong (refl' (Eq.cong CZ^ (lemma-⁻¹ʳ y {{nztoℕ {y = y} {neq0 = nz}}}))) (sym (cleft lemma-comm-H-w↑ (M (y* ⁻¹)))) ⟩
  CZ • (H • M (y* ⁻¹) ↑) • H ↑ • CZ • M (y* ⁻¹) ↑ ≈⟨ cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  CZ • H • (M (y* ⁻¹) ↑ • H ↑) • CZ • M (y* ⁻¹) ↑ ≈⟨ cright cright cleft sym (lemma-cong↑ _ _ (semi-HM y*)) ⟩
  CZ • H • (H ↑ • M y* ↑) • CZ • M (y* ⁻¹) ↑ ≈⟨ cright cright sa (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
  CZ • H • H ↑ • (M y* ↑ • CZ) • M (y* ⁻¹) ↑ ≈⟨ cright cright cright cleft axiom (semi-M↑CZ y*) ⟩
  CZ • H • H ↑ • (CZ^ y • M y* ↑) • M (y* ⁻¹) ↑ ≈⟨ cright cright cright assoc ⟩
  CZ • H • H ↑ • CZ^ y • M y* ↑ • M (y* ⁻¹) ↑ ≈⟨ cright cright cright (cright lemma-cong↑ _ _ (aux-M-mul y*)) ⟩
  CZ • H • H ↑ • CZ^ y • ε ≈⟨ cright cright (cright right-unit) ⟩
  CZ • H • H ↑ • CZ^ y ∎
  where
  y⁻¹ = (y* ⁻¹) .proj₁

lemma-⌶-CZ^y : ∀ (y*@(y , nz) : ℤ* ₚ) (neq1 : y ≢ ₁) ->
  let
  nzm : ₁ + - y ≢ ₀
  nzm = y≠1⇒1-y≠0 y neq1
  ₁-y : ℤ* ₚ
  ₁-y = (₁ + - y , nzm)
  in
  ⌶ • CZ^ y ≈ M (₁-y ⁻¹) ↑ • CZ^ y • ⌶ • M (₁-y ⁻¹)
lemma-⌶-CZ^y y*@(y , nz) neq1 = begin
  ⌶ • CZ^ y ≈⟨ refl ⟩
  (H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ^ y ≈⟨ cleft sym aux-hEx-4 ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex) • CZ^ y ≈⟨ sa (□ ^ 7 • □) (□ ^ 6 • □ ^ 2) auto ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2) • Ex • CZ^ y ≈⟨ cright comm⇒pow-comm 1 (toℕ y) (sym lemma-comm-Ex-CZ-n) ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2) • CZ^ y • Ex ≈⟨ sa (□ ^ 6 • □ ^ 2) (□ ^ 5 • □ ^ 2 • □) auto ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ) • (H ^ 2 • CZ^ y) • Ex ≈⟨ cright cleft lemma-semi-HH↓-CZ^k' y ⟩
  (H ↑ ^ 2 • CZ • H • H ↑ • CZ) • (CZ^ (- y) • H ^ 2) • Ex ≈⟨ sa (□ ^ 5 • □ ^ 2 • □) (□ ^ 4 • □ ^ 2 • □ ^ 2) auto ⟩
  (H ↑ ^ 2 • CZ • H • H ↑) • (CZ • CZ^ (- y)) • H ^ 2 • Ex ≈⟨ cright cleft lemma-CZ^k+l ₁ (- y) ⟩
  (H ↑ ^ 2 • CZ • H • H ↑) • CZ^ (₁ + - y) • H ^ 2 • Ex ≈⟨ sa (□ ^ 4 • □ ^ 3) (□ • □ ^ 4 • □ ^ 2) auto ⟩
  H ↑ ^ 2 • (CZ • H • H ↑ • CZ^ (₁ + - y)) • H ^ 2 • Ex ≈⟨ cright cleft sym (aux-M|| ₁-y) ⟩
  H ↑ ^ 2 • (M (₁-y ⁻¹) ↑ • CZ^ (₁ + - y) • H • H ↑ • CZ • M (₁-y ⁻¹) ↑) • H ^ 2 • Ex ≈⟨ sa (□ • □ ^ 6 • □ ^ 2) (□ ^ 2 • □ • □ ^ 3 • □ ^ 2 • □) auto ⟩
  (H ↑ ^ 2 • M (₁-y ⁻¹) ↑) • CZ^ (₁ + - y) • (H • H ↑ • CZ) • (M (₁-y ⁻¹) ↑ • H ^ 2) • Ex ≈⟨ cright cong (refl' (Eq.cong CZ^ (+-comm ₁ (- y)))) (cright cleft sym (lemma-comm-Hᵏ-w↑ 2 (M (₁-y ⁻¹)))) ⟩
  (H ↑ ^ 2 • M (₁-y ⁻¹) ↑) • CZ^ (- y + ₁) • (H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ cong (lemma-cong↑ _ _ (aux-comm-HHM (₁-y ⁻¹))) (cleft sym (lemma-CZ^k+l (- y) ₁)) ⟩
  (M (₁-y ⁻¹) ↑ • H ↑ ^ 2) • (CZ^ (- y) • CZ) • (H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ sa (□ ^ 2 • □ ^ 2 • □ ^ 3 • □ ^ 2 • □) (□ • □ ^ 2 • □ ^ 4 • □ ^ 2 • □) auto ⟩
  M (₁-y ⁻¹) ↑ • (H ↑ ^ 2 • CZ^ (- y)) • (CZ • H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ cright cleft lemma-semi-HH↑-CZ^k'' y ⟩
  M (₁-y ⁻¹) ↑ • (CZ^ y • H ↑ ^ 2) • (CZ • H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ sa (□ • □ ^ 2 • □ ^ 2) (□ • □ • □ ^ 2 • □) auto ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • (H ↑ ^ 2 • CZ • H • H ↑ • CZ) • (H ^ 2 • M (₁-y ⁻¹) ↑) • Ex ≈⟨ cright cright sa (□ ^ 5 • □ ^ 2 • □) (□ ^ 6 • □ ^ 2) auto ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2) • M (₁-y ⁻¹) ↑ • Ex ≈⟨ cright cright cright sym (lemma-Ex-M (₁-y ⁻¹)) ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2) • Ex • M (₁-y ⁻¹) ≈⟨ cright cright sa (□ ^ 6 • □ ^ 2) (□ ^ 7 • □) auto ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • (H ↑ ^ 2 • CZ • H • H ↑ • CZ • H ^ 2 • Ex) • M (₁-y ⁻¹) ≈⟨ cright cright cleft aux-hEx-4 ⟩
  M (₁-y ⁻¹) ↑ • CZ^ y • ⌶ • M (₁-y ⁻¹) ∎
  where
  nzm : ₁ + - y ≢ ₀
  nzm = y≠1⇒1-y≠0 y neq1
  ₁-y : ℤ* ₚ
  ₁-y = (₁ + - y , nzm)

  
