------------------------------------------------------------------------
-- Presentations of groups
--
-- Phase gates: T conjugated by a linear circuit
--
-- For a nonzero row ℓ, the phase gate
--
--     P ℓ = (r ℓ)⁻¹ • T • r ℓ
--
-- multiplies |x⟩ by ω^(ℓ·x), since r ℓ writes the parity ℓ·x on wire
-- 0, where T reads it.  Two facts make these gates the building blocks
-- of every diagonal circuit:
--
--   phase-conj  T conjugated by ANY linear circuit M is the phase gate
--               of the parity M writes on wire 0: in the normal form
--               W ↑ • s₁ u • r ℓ of M, T commutes with the upper part
--               and with the column part, which keep wire 0;
--   P-comm      phase gates commute.  Conjugating one by the other's
--               representative gives a phase gate again, and T commutes
--               with every phase gate: P e₀ is T, P (sw ℓ) lives on the
--               upper wires, and P (cx ℓ) is U conjugated by an upper
--               circuit, U commuting with T (Diagonal.LocalT).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.Phase where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Evaluation using (_⁻¹ ; module Inv)
open import Examples.Groups.CNOT+Dihedral.Linear.Local using (CX01)
open import Examples.Groups.CNOT+Dihedral.Linear.Base
open import Examples.Groups.CNOT+Dihedral.Linear.Steps
open import Examples.Groups.CNOT+Dihedral.Diagonal.LocalT

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The representatives as linear words, and reversal

infixl 9 _↑ₗ
_↑ₗ : Word (LGen n) → Word (LGen (₁₊ n))
_↑ₗ = wmap _↥ₗ

⌊⌋-↑ : (w : Word (LGen n)) → ⌊ w ↑ₗ ⌋ ≡ ⌊ w ⌋ ↑
⌊⌋-↑ [ y ]ʷ   = Eq.refl
⌊⌋-↑ ε        = Eq.refl
⌊⌋-↑ (w • v)  = Eq.cong₂ _•_ (⌊⌋-↑ w) (⌊⌋-↑ v)

rL : NZ n → Word (LGen n)
rL e₀     = ε
rL (cx ℓ) = [ cnot ]ʷ • rL ℓ ↑ₗ
rL (sw ℓ) = [ swap ]ʷ • rL ℓ ↑ₗ

r-⌊⌋ : (ℓ : NZ n) → r ℓ ≡ ⌊ rL ℓ ⌋
r-⌊⌋ e₀     = Eq.refl
r-⌊⌋ (cx ℓ) = Eq.cong (CNOT •_) (Eq.trans (Eq.cong _↑ (r-⌊⌋ ℓ)) (Eq.sym (⌊⌋-↑ (rL ℓ))))
r-⌊⌋ (sw ℓ) = Eq.cong (SWAP •_) (Eq.trans (Eq.cong _↑ (r-⌊⌋ ℓ)) (Eq.sym (⌊⌋-↑ (rL ℓ))))

revL : Word (LGen n) → Word (LGen n)
revL [ y ]ʷ  = [ y ]ʷ
revL ε       = ε
revL (w • v) = revL v • revL w

ι-invol : (y : LGen n) → n ⊢ [ ι y ]ʷ • [ ι y ]ʷ ≈ ε
ι-invol cnot     = ax R₄
ι-invol swap     = ax swap-order
ι-invol (y ↥ₗ)   = lift (ι-invol y)

rev-right : (L : Word (LGen n)) → n ⊢ ⌊ L ⌋ • ⌊ revL L ⌋ ≈ ε
rev-right [ y ]ʷ = ι-invol y
rev-right {n} ε  = left-unit
  where open Width n
rev-right {n} (w • v) = begin
  (⌊ w ⌋ • ⌊ v ⌋) • ⌊ revL v ⌋ • ⌊ revL w ⌋
    ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  ⌊ w ⌋ • (⌊ v ⌋ • ⌊ revL v ⌋) • ⌊ revL w ⌋
    ≈⟨ back _ (front _ (rev-right v)) ⟩
  ⌊ w ⌋ • ε • ⌊ revL w ⌋
    ≈⟨ back _ left-unit ⟩
  ⌊ w ⌋ • ⌊ revL w ⌋
    ≈⟨ rev-right w ⟩
  ε ∎
  where open Width n

rev-⁻¹ : (L : Word (LGen n)) → n ⊢ ⌊ revL L ⌋ ≈ ⌊ L ⌋ ⁻¹
rev-⁻¹ {n} L = Inv.inverseʳ-unique n (rev-right L)

-- The inverse of a word one wire up.
⁻¹-↑ : (w : Circuit n) → (w ↑) ⁻¹ ≡ (w ⁻¹) ↑
⁻¹-↑ [ g ]ʷ   = Eq.refl
⁻¹-↑ ε        = Eq.refl
⁻¹-↑ (w • v)  = Eq.cong₂ _•_ (⁻¹-↑ v) (⁻¹-↑ w)

------------------------------------------------------------------------
-- Phase gates

P : NZ (₁₊ n) → Circuit (₁₊ n)
P ℓ = r ℓ ⁻¹ • T • r ℓ

-- T commutes with whatever lies above wire 0, and with the column
-- part of a normal form.
T-↑ : (w : Circuit n) → (₁₊ n) ⊢ T • w ↑ ≈ w ↑ • T
T-↑ {n} w = Width.sym (comm-gate₁-w↑ T-gate w)

T-s₁ : (u : SOne (₁₊ n)) → (₁₊ n) ⊢ T • s₁ u ≈ s₁ u • T
T-s₁ {n} one₀    = Width.slide-ε (₁₊ n)
T-s₁ {n} (one u) = Width.slide (₁₊ n) T-CX01 (T-↑ (s u))

-- T conjugated by a linear circuit.
phase-conj : (M : Word (LGen (₁₊ n))) →
             (₁₊ n) ⊢ ⌊ M ⌋ ⁻¹ • T • ⌊ M ⌋ ≈ P (LNF.row (lnf M))
phase-conj {n} M = begin
  ⌊ M ⌋ ⁻¹ • T • ⌊ M ⌋
    ≈⟨ cong (Inv.⁻¹-cong (₁₊ n) d) (back T d) ⟩
  (W ↑ • s₁ u • r ℓ) ⁻¹ • T • W ↑ • s₁ u • r ℓ
    ≈⟨ by-passoc (((□ • □) • □) • □ • □ • □ • □) (□ • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
  r ℓ ⁻¹ • s₁ u ⁻¹ • ((W ↑) ⁻¹ • T • W ↑) • s₁ u • r ℓ
    ≈⟨ back _ (back _ (front _ cancel-W)) ⟩
  r ℓ ⁻¹ • s₁ u ⁻¹ • T • s₁ u • r ℓ
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (T-s₁ u)) assoc))) ⟩
  r ℓ ⁻¹ • s₁ u ⁻¹ • s₁ u • T • r ℓ
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (Inv.inverseˡ (₁₊ n))) left-unit)) ⟩
  r ℓ ⁻¹ • T • r ℓ ∎
  where
  open Width (₁₊ n)
  N = lnf M
  W = LNF.upper N
  u = LNF.col N
  ℓ = LNF.row N
  d : (₁₊ n) ⊢ ⌊ M ⌋ ≈ W ↑ • s₁ u • r ℓ
  d = decompose M
  cancel-W : (₁₊ n) ⊢ (W ↑) ⁻¹ • T • W ↑ ≈ T
  cancel-W = begin
    (W ↑) ⁻¹ • T • W ↑     ≈⟨ back _ (T-↑ W) ⟩
    (W ↑) ⁻¹ • W ↑ • T     ≈⟨ sym assoc ⟩
    ((W ↑) ⁻¹ • W ↑) • T   ≈⟨ front _ (Inv.inverseˡ (₁₊ n)) ⟩
    ε • T                  ≈⟨ left-unit ⟩
    T                      ∎

------------------------------------------------------------------------
-- T commutes with every phase gate

-- The two shapes of a phase gate with a gadget.
P-sw : (ℓ : NZ (₁₊ n)) → (₂₊ n) ⊢ P (sw ℓ) ≈ (r ℓ ⁻¹) ↑ • T ↑ • r ℓ ↑
P-sw {n} ℓ = begin
  ((r ℓ ↑) ⁻¹ • SWAP) • T • SWAP • r ℓ ↑
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  (r ℓ ↑) ⁻¹ • (SWAP • T • SWAP) • r ℓ ↑
    ≈⟨ back _ (front _ SWAP-T-SWAP) ⟩
  (r ℓ ↑) ⁻¹ • T ↑ • r ℓ ↑
    ≈⟨ front _ (refl' (⁻¹-↑ (r ℓ))) ⟩
  (r ℓ ⁻¹) ↑ • T ↑ • r ℓ ↑ ∎
  where open Width (₂₊ n)

P-cx : (ℓ : NZ (₁₊ n)) → (₂₊ n) ⊢ P (cx ℓ) ≈ (r ℓ ⁻¹) ↑ • U • r ℓ ↑
P-cx {n} ℓ = begin
  ((r ℓ ↑) ⁻¹ • CNOT) • T • CNOT • r ℓ ↑
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  (r ℓ ↑) ⁻¹ • U • r ℓ ↑
    ≈⟨ front _ (refl' (⁻¹-↑ (r ℓ))) ⟩
  (r ℓ ⁻¹) ↑ • U • r ℓ ↑ ∎
  where open Width (₂₊ n)

private
  -- T past A ↑ • C • B ↑, given T past C.
  T-sandwich : (A B : Circuit n) (C : Circuit (₁₊ n)) →
               (₁₊ n) ⊢ T • C ≈ C • T →
               (₁₊ n) ⊢ T • A ↑ • C • B ↑ ≈ (A ↑ • C • B ↑) • T
  T-sandwich {n} A B C e =
    Width.slide (₁₊ n) (T-↑ A) (Width.slide (₁₊ n) e (T-↑ B))

  T-past : ∀ {X Y : Circuit (₁₊ n)} → (₁₊ n) ⊢ X ≈ Y →
           (₁₊ n) ⊢ T • Y ≈ Y • T → (₁₊ n) ⊢ T • X ≈ X • T
  T-past {n} e c = trans (back T e) (trans c (front T (sym e)))
    where open Width (₁₊ n)

T-P : (ℓ : NZ (₁₊ n)) → (₁₊ n) ⊢ T • P ℓ ≈ P ℓ • T
T-P {n} e₀ = by-assoc Eq.refl
  where open Width (₁₊ n)
T-P (sw ℓ) =
  T-past (P-sw ℓ) (T-sandwich (r ℓ ⁻¹) (r ℓ) (T ↑) (Width.sym (ax' (comm₁ T-gate T-gen))))
T-P (cx ℓ) = T-past (P-cx ℓ) (T-sandwich (r ℓ ⁻¹) (r ℓ) U T-U)

------------------------------------------------------------------------
-- Phase gates commute

private
  -- A word commuting with a conjugate, conjugated back.
  conj-comm : ∀ {m} (g ρ X : Circuit m) →
              m ⊢ g • (ρ • X • ρ ⁻¹) ≈ (ρ • X • ρ ⁻¹) • g →
              m ⊢ (ρ ⁻¹ • g • ρ) • X ≈ X • (ρ ⁻¹ • g • ρ)
  conj-comm {m} g ρ X c = begin
    (ρ ⁻¹ • g • ρ) • X
      ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    ρ ⁻¹ • g • ρ • X
      ≈⟨ back _ (back _ (sym (cancelʳ' (ρ • X)))) ⟩
    ρ ⁻¹ • g • (ρ • X) • ρ ⁻¹ • ρ
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • (□ • (□ • □ • □)) • □) Eq.refl ⟩
    ρ ⁻¹ • (g • (ρ • X • ρ ⁻¹)) • ρ
      ≈⟨ back _ (front _ c) ⟩
    ρ ⁻¹ • ((ρ • X • ρ ⁻¹) • g) • ρ
      ≈⟨ by-passoc (□ • ((□ • □ • □) • □) • □) ((□ • □) • □ • □ • □ • □) Eq.refl ⟩
    (ρ ⁻¹ • ρ) • X • ρ ⁻¹ • g • ρ
      ≈⟨ front _ (Inv.inverseˡ m) ⟩
    ε • X • ρ ⁻¹ • g • ρ
      ≈⟨ left-unit ⟩
    X • ρ ⁻¹ • g • ρ ∎
    where
    open Width m
    cancelʳ' : (t : Circuit m) → m ⊢ t • ρ ⁻¹ • ρ ≈ t
    cancelʳ' t = trans (back t (Inv.inverseˡ m)) right-unit

P-comm : (ℓ ℓ' : NZ (₁₊ n)) → (₁₊ n) ⊢ P ℓ • P ℓ' ≈ P ℓ' • P ℓ
P-comm {n} ℓ ℓ' = conj-comm T (r ℓ) (P ℓ') (T-past Q≈ (T-P ℓ''))
  where
  open Width (₁₊ n)
  M : Word (LGen (₁₊ n))
  M = rL ℓ' • revL (rL ℓ)
  ℓ'' = LNF.row (lnf M)
  -- ⌊ M ⌋ is r ℓ' • (r ℓ)⁻¹.
  M≈ : (₁₊ n) ⊢ ⌊ M ⌋ ≈ r ℓ' • r ℓ ⁻¹
  M≈ = trans (refl' (Eq.cong₂ _•_ (Eq.sym (r-⌊⌋ ℓ')) Eq.refl))
         (back _ (trans (rev-⁻¹ (rL ℓ)) (refl' (Eq.cong _⁻¹ (Eq.sym (r-⌊⌋ ℓ))))))
  M⁻¹≈ : (₁₊ n) ⊢ ⌊ M ⌋ ⁻¹ ≈ r ℓ • r ℓ' ⁻¹
  M⁻¹≈ = trans (Inv.⁻¹-cong (₁₊ n) M≈) (front _ (Inv.⁻¹-involutive (₁₊ n)))
  Q≈ : (₁₊ n) ⊢ r ℓ • P ℓ' • r ℓ ⁻¹ ≈ P ℓ''
  Q≈ = begin
    r ℓ • (r ℓ' ⁻¹ • T • r ℓ') • r ℓ ⁻¹
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
    (r ℓ • r ℓ' ⁻¹) • T • r ℓ' • r ℓ ⁻¹
      ≈⟨ cong (sym M⁻¹≈) (back T (sym M≈)) ⟩
    ⌊ M ⌋ ⁻¹ • T • ⌊ M ⌋
      ≈⟨ phase-conj M ⟩
    P ℓ'' ∎
