{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- General-width CZ ↑ push through a B-vector.
--
-- Generalises BR.Three.BB-CZ.lemma-dir-and-vb' from `Vec B 2` to
-- `Vec B (₂₊ n)`.  CZ ↑ (wires 1,2) interacts only with the bottom two
-- B boxes; the residual `dir ⇣` lands on wires 0,1 and commutes past the
-- wire-≥2 tail (aux-comm-w⇣-v↑↑), leaving the tail boxes unchanged.  The
-- bottom-two interaction is BB-CZ (width 3) widened by CongDownK.cong↓ᵏ.
------------------------------------------------------------------------

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as ℕ
open import Data.Vec using (Vec ; [] ; _∷_)

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Nat.Primality
open import Notations

module Examples.Groups.Symplectic.BR.Three.BB-CZ-n (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open Lemmas-Sym
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n p-2 p-prime using (lemma-comm-CZ-w↑↑)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
import Examples.Groups.Symplectic.BR.Three.BB-CZ p-2 p-prime as TBB
open TBB using (_⇣)

------------------------------------------------------------------------
-- ⇣ (the width-2→3 embedding used by BB-CZ) agrees with ↓ᵏ 1.

⇣≡↓ᵏ1 : ∀ (w : Word (Gen 2)) → w ⇣ ≡ w ↓ᵏ 1
⇣≡↓ᵏ1 [ gate₁ H-gate ]ʷ     = Eq.refl
⇣≡↓ᵏ1 [ gate₁ S-gate ]ʷ     = Eq.refl
⇣≡↓ᵏ1 [ gate₂ CZ-gate ]ʷ    = Eq.refl
⇣≡↓ᵏ1 [ gate₁ H-gate ↥ ]ʷ   = Eq.refl
⇣≡↓ᵏ1 [ gate₁ S-gate ↥ ]ʷ   = Eq.refl
⇣≡↓ᵏ1 [ gate₀ () ↥ ↥ ]ʷ
⇣≡↓ᵏ1 ε                     = Eq.refl
⇣≡↓ᵏ1 (w • v)               = Eq.cong₂ _•_ (⇣≡↓ᵏ1 w) (⇣≡↓ᵏ1 v)

------------------------------------------------------------------------
-- Box widening at an arbitrary base width.

CX'^-↓ᵏ : ∀ {m} (b : ℤ ₚ) (k : ℕ) → (CX'^ {m} b) ↓ᵏ k ≡ CX'^ b
CX'^-↓ᵏ b k = Eq.cong₂ _•_ (pow-↓ᵏ H 3 k) (Eq.cong₂ _•_ (CZ^-↓ᵏ b k) Eq.refl)

S^↑-↓ᵏ : ∀ {m} (j : ℤ ₚ) (k : ℕ) → (S^ {m} j ↑) ↓ᵏ k ≡ S^ j ↑
S^↑-↓ᵏ j k = Eq.trans (↑↓ᵏ-comm (S^ j) k) (Eq.cong _↑ (S^-↓ᵏ j k))

b-↓ᵏ : ∀ {m} (b : B) (k : ℕ) → [_]ᵇ {m} b ↓ᵏ k ≡ [_]ᵇ {m ℕ.+ k} b
b-↓ᵏ (₀ , b) k = Eq.cong₂ _•_ Eq.refl (CX'^-↓ᵏ b k)
b-↓ᵏ (a@(₁₊ _) , b) k =
  Eq.cong₂ _•_ Eq.refl
    (Eq.cong₂ _•_ (CX'^-↓ᵏ a k)
      (Eq.cong₂ _•_ Eq.refl (S^↑-↓ᵏ -b/a k)))
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

b↑-↓ᵏ : ∀ (b : B) (k : ℕ) → ([_]ᵇ {0} b ↑) ↓ᵏ k ≡ [_]ᵇ {k} b ↑
b↑-↓ᵏ b k = Eq.trans (↑↓ᵏ-comm ([_]ᵇ {0} b) k) (Eq.cong _↑ (b-↓ᵏ {0} b k))

↓ᵏ-↓ᵏ-2 : ∀ (w : Circuit 2) (k : ℕ) → (w ↓ᵏ 1) ↓ᵏ k ≡ w ↓ᵏ (₁₊ k)
↓ᵏ-↓ᵏ-2 [ gate₁ y ]ʷ  k = Eq.refl
↓ᵏ-↓ᵏ-2 [ gate₂ y ]ʷ  k = Eq.refl
↓ᵏ-↓ᵏ-2 [ g ↥ ]ʷ      k =
  Eq.trans (Eq.cong (_↓ᵏ k) (↑↓ᵏ-comm ([ g ]ʷ) 1))
    (Eq.trans (↑↓ᵏ-comm ([ g ]ʷ ↓ᵏ 1) k)
      (Eq.trans (Eq.cong _↑ (↓ᵏ-↓ᵏ-1 ([ g ]ʷ) k))
        (Eq.sym (↑↓ᵏ-comm ([ g ]ʷ) (₁₊ k)))))
↓ᵏ-↓ᵏ-2 ε             k = Eq.refl
↓ᵏ-↓ᵏ-2 (w • v)       k = Eq.cong₂ _•_ (↓ᵏ-↓ᵏ-2 w k) (↓ᵏ-↓ᵏ-2 v k)

CZ↑-↓ᵏ : ∀ {m} (k : ℕ) → (CZ {m} ↑) ↓ᵏ k ≡ CZ ↑
CZ↑-↓ᵏ k = Eq.trans (↑↓ᵏ-comm CZ k) Eq.refl

------------------------------------------------------------------------
-- vb'-of / dir-of at general width: only the bottom two entries change.

gen-vb'-of : ∀ {n} → Vec B (₂₊ n) → Vec B (₂₊ n)
gen-vb'-of ((a , b) ∷ (c , d) ∷ bs) = (a , b + - c) ∷ (c , d + - a) ∷ bs

gen-dir-b : ∀ {n} → Vec B (₂₊ n) → Word (Gen 2)
gen-dir-b (b₁ ∷ b₂ ∷ bs) = TBB.dir-of (b₁ ∷ b₂ ∷ [])

------------------------------------------------------------------------
-- A width-2 word padded onto wires 0,1 commutes past a wire-≥2 word.

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

  comm-↓ᵏ2-w↑↑ : ∀ (u : Word (Gen 2)) (w : Word (Gen (₁₊ n))) →
    (u ↓ᵏ (₁₊ n)) • (w ↑ ↑) ≈ (w ↑ ↑) • (u ↓ᵏ (₁₊ n))
  comm-↓ᵏ2-w↑↑ [ gate₁ H-gate ]ʷ   w = lemma-comm-H-w↑ (w ↑)
  comm-↓ᵏ2-w↑↑ [ gate₁ S-gate ]ʷ   w = lemma-comm-S-w↑ (w ↑)
  comm-↓ᵏ2-w↑↑ [ gate₂ CZ-gate ]ʷ  w = lemma-comm-CZ-w↑↑ w
  comm-↓ᵏ2-w↑↑ [ gate₁ H-gate ↥ ]ʷ w = lemma-cong↑ _ _ (lemma-comm-H-w↑ w)
  comm-↓ᵏ2-w↑↑ [ gate₁ S-gate ↥ ]ʷ w = lemma-cong↑ _ _ (lemma-comm-S-w↑ w)
  comm-↓ᵏ2-w↑↑ [ gate₀ () ↥ ↥ ]ʷ w
  comm-↓ᵏ2-w↑↑ ε                   w = trans left-unit (sym right-unit)
  comm-↓ᵏ2-w↑↑ (u • v)             w = begin
    ((u ↓ᵏ (₁₊ n)) • (v ↓ᵏ (₁₊ n))) • (w ↑ ↑)   ≈⟨ assoc ⟩
    (u ↓ᵏ (₁₊ n)) • ((v ↓ᵏ (₁₊ n)) • (w ↑ ↑))   ≈⟨ cright (comm-↓ᵏ2-w↑↑ v w) ⟩
    (u ↓ᵏ (₁₊ n)) • ((w ↑ ↑) • (v ↓ᵏ (₁₊ n)))   ≈⟨ sym assoc ⟩
    ((u ↓ᵏ (₁₊ n)) • (w ↑ ↑)) • (v ↓ᵏ (₁₊ n))   ≈⟨ cleft (comm-↓ᵏ2-w↑↑ u w) ⟩
    ((w ↑ ↑) • (u ↓ᵏ (₁₊ n))) • (v ↓ᵏ (₁₊ n))   ≈⟨ assoc ⟩
    (w ↑ ↑) • ((u ↓ᵏ (₁₊ n)) • (v ↓ᵏ (₁₊ n)))   ∎

  open Pattern-Assoc renaming (by-passoc to sa)

  ----------------------------------------------------------------------
  -- The general-width CZ ↑ push.

  gen-bb-cz : ∀ (vb : Vec B (₂₊ n)) →
    [ vb ]ᵛᵇ • CZ ↑ ≈ (gen-dir-b vb ↓ᵏ (₁₊ n)) • [ gen-vb'-of vb ]ᵛᵇ
  gen-bb-cz (b₁ ∷ b₂ ∷ bs) = begin
    ((T • B2) • B1) • G           ≈⟨ sa (((□ • □) • □) • □) (□ • ((□ • □) • □)) auto ⟩
    T • ((B2 • B1) • G)           ≈⟨ cright widened-BBCZ ⟩
    T • (Res • Bot')              ≈⟨ sym assoc ⟩
    (T • Res) • Bot'              ≈⟨ cleft (sym (comm-↓ᵏ2-w↑↑ (gen-dir-b (b₁ ∷ b₂ ∷ bs)) [ bs ]ᵛᵇ)) ⟩
    (Res • T) • Bot'              ≈⟨ sa ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) auto ⟩
    Res • ((T • B2') • B1')       ∎
    where
    T   = [ bs ]ᵛᵇ ↑ ↑
    B2  = [ b₂ ]ᵇ ↑
    B1  = [ b₁ ]ᵇ
    G   = CZ ↑
    dir = TBB.dir-of (b₁ ∷ b₂ ∷ [])
    Res = dir ↓ᵏ (₁₊ n)
    b₁' = proj₁ b₁ , proj₂ b₁ + - proj₁ b₂
    b₂' = proj₁ b₂ , proj₂ b₂ + - proj₁ b₁
    B2' = [ b₂' ]ᵇ ↑
    B1' = [ b₁' ]ᵇ
    Bot' = B2' • B1'

    dir⇣↓ᵏn≡Res : (dir ⇣) ↓ᵏ n ≡ Res
    dir⇣↓ᵏn≡Res = Eq.trans (Eq.cong (_↓ᵏ n) (⇣≡↓ᵏ1 dir)) (↓ᵏ-↓ᵏ-2 dir n)

    eqL : ([ b₁ ∷ b₂ ∷ [] ]ᵛᵇ • CZ ↑) ↓ᵏ n ≡ ((ε • B2) • B1) • G
    eqL = Eq.cong₂ _•_
            (Eq.cong₂ _•_ (Eq.cong₂ _•_ Eq.refl (b↑-↓ᵏ b₂ n)) (b-↓ᵏ {1} b₁ n))
            (CZ↑-↓ᵏ n)

    eqR : (dir ⇣ • [ b₁' ∷ b₂' ∷ [] ]ᵛᵇ) ↓ᵏ n ≡ Res • ((ε • B2') • B1')
    eqR = Eq.cong₂ _•_ dir⇣↓ᵏn≡Res
            (Eq.cong₂ _•_ (Eq.cong₂ _•_ Eq.refl (b↑-↓ᵏ b₂' n)) (b-↓ᵏ {1} b₁' n))

    widened-BBCZ : (B2 • B1) • G ≈ Res • Bot'
    widened-BBCZ = begin
      (B2 • B1) • G                                          ≈⟨ sym (trans (refl' eqL) (cleft (cleft left-unit))) ⟩
      ([ b₁ ∷ b₂ ∷ [] ]ᵛᵇ • CZ ↑) ↓ᵏ n                       ≈⟨ cong↓ᵏ n _ _ (TBB.lemma-dir-and-vb' (b₁ ∷ b₂ ∷ [])) ⟩
      (dir ⇣ • [ b₁' ∷ b₂' ∷ [] ]ᵛᵇ) ↓ᵏ n                    ≈⟨ trans (refl' eqR) (cright (cleft left-unit)) ⟩
      Res • Bot'                                             ∎
