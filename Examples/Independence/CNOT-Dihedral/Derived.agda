------------------------------------------------------------------------
-- Presentations of groups
--
-- The axioms of Amy, Chen and Ross that CNOTdihe₂ omits, derived in it
--
-- Appendix H of Blake's paper: (R2), (R3), (R5), (R8) and (R11), and
-- (R4), CNOT CNOT = ε, "by the same rewriting used in the section for
-- Clifford+T" (Derivation D.5: insert T T⁷, conjugate T by the CNOT
-- drawn upside down, and let (B) exchange the two CNOTs).  Each is
-- stated on the bottom wires of a circuit of any width; the other
-- axioms of Amy, Chen and Ross are axioms of CNOTdihe₂ as they stand.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.CNOT-Dihedral.Derived where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊)

import Presentation.Base as PB

open import Examples.Independence.CNOT-Dihedral.Syntactics
open import Examples.Independence.Reasoning Gate
open Theory _SRel,_===_

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The axioms used, on the bottom wires of any circuit

private
  X²₀ : (₁₊ n) ⊢ X • X ≈ ε
  X²₀ {n} = ax-at X² n

  X²₁ : (₂₊ n) ⊢ X ↑ • X ↑ ≈ ε
  X²₁ = lift X²₀

  T⁸₀ : (₁₊ n) ⊢ T • T ^ 7 ≈ ε
  T⁸₀ {n} = ax-at T⁸ n

  TX′ : (₁₊ n) ⊢ ω • T† • X ≈ X • T
  TX′ {n} = ax-at TX n

  XC′ : (₂₊ n) ⊢ CX • X ≈ X ↑ • CX • X ↑
  XC′ {n} = ax-at XC n

  B′ : (₂₊ n) ⊢ CX • CX↓ ≈ σ • CX
  B′ {n} = ax-at B n

  ZC′ : (₂₊ n) ⊢ CX • Z ↑ ≈ Z • CX • Z
  ZC′ {n} = ax-at ZC n

  CPh′ : (₂₊ n) ⊢ CX • T ↑ • CX ≈ T ↑
  CPh′ {n} = ax-at CPh n

  σσ : (₂₊ n) ⊢ σ • σ ≈ ε
  σσ = sym-rule σ-inv

  Tσ : (₂₊ n) ⊢ T • σ ≈ σ • T ↑
  Tσ = sym-rule (σ-nat₁ ⌈ T-gate ⌉)

  X↑X : (₂₊ n) ⊢ X ↑ • X ≈ X • X ↑
  X↑X = PB.axiom (comm₁ ⌈ X-gate ⌉ (gate₁ ⌈ X-gate ⌉))

------------------------------------------------------------------------
-- The swap, and the CNOT drawn upside down

σTσ : (₂₊ n) ⊢ σ • T • σ ≈ T ↑
σTσ {n} = begin
  σ • T • σ          ≈⟨ back σ Tσ ⟩
  σ • σ • T ↑        ≈⟨ by-assoc Eq.refl ⟩
  (σ • σ) • T ↑      ≈⟨ front (T ↑) σσ ⟩
  ε • T ↑            ≈⟨ left-unit ⟩
  T ↑                ∎
  where open Width (₂₊ n)

σT↑σ : (₂₊ n) ⊢ σ • T ↑ • σ ≈ T
σT↑σ {n} = begin
  σ • T ↑ • σ                ≈⟨ back σ (front σ (sym σTσ)) ⟩
  σ • (σ • T • σ) • σ        ≈⟨ by-assoc Eq.refl ⟩
  (σ • σ) • T • (σ • σ)      ≈⟨ cong σσ (back T σσ) ⟩
  ε • T • ε                  ≈⟨ trans left-unit right-unit ⟩
  T                          ∎
  where open Width (₂₊ n)

-- (CPh) for the CNOT whose control is wire 0.
CPh↓ : (₂₊ n) ⊢ CX↓ • T • CX↓ ≈ T
CPh↓ {n} = begin
  CX↓ • T • CX↓                ≈⟨ by-assoc Eq.refl ⟩
  σ • CX • (σ • T • σ) • CX • σ ≈⟨ back σ (back CX (front (CX • σ) σTσ)) ⟩
  σ • CX • T ↑ • CX • σ        ≈⟨ by-assoc Eq.refl ⟩
  σ • (CX • T ↑ • CX) • σ      ≈⟨ back σ (front σ CPh′) ⟩
  σ • T ↑ • σ                  ≈⟨ σT↑σ ⟩
  T                            ∎
  where open Width (₂₊ n)

σCX : (₂₊ n) ⊢ σ • CX ≈ CX↓ • σ
σCX {n} = sym (begin
  CX↓ • σ               ≈⟨ by-assoc Eq.refl ⟩
  σ • CX • (σ • σ)      ≈⟨ back σ (back CX σσ) ⟩
  σ • CX • ε            ≈⟨ back σ right-unit ⟩
  σ • CX                ∎)
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- (R4): CNOT CNOT = ε  (Derivation D.5)

R₄ : (₂₊ n) ⊢ CX • CX ≈ ε
R₄ {n} = begin
  CX • CX                                ≈⟨ back CX (sym right-unit) ⟩
  CX • CX • ε                            ≈⟨ back CX (back CX (sym T⁸₀)) ⟩
  CX • CX • (T • T ^ 7)                  ≈⟨ back CX (back CX (front (T ^ 7) (sym CPh↓))) ⟩
  CX • CX • ((CX↓ • T • CX↓) • T ^ 7)    ≈⟨ by-assoc Eq.refl ⟩
  CX • (CX • CX↓) • T • CX↓ • T ^ 7      ≈⟨ back CX (front _ B′) ⟩
  CX • (σ • CX) • T • CX↓ • T ^ 7        ≈⟨ back CX (front _ σCX) ⟩
  CX • (CX↓ • σ) • T • CX↓ • T ^ 7       ≈⟨ by-assoc Eq.refl ⟩
  (CX • CX↓) • σ • T • CX↓ • T ^ 7       ≈⟨ front _ B′ ⟩
  (σ • CX) • σ • T • CX↓ • T ^ 7         ≈⟨ by-assoc Eq.refl ⟩
  (CX↓ • T • CX↓) • T ^ 7                ≈⟨ front (T ^ 7) CPh↓ ⟩
  T • T ^ 7                              ≈⟨ T⁸₀ ⟩
  ε                                      ∎
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- X past the CNOT

X↑CX : (₂₊ n) ⊢ X ↑ • CX ≈ CX • X • X ↑
X↑CX {n} = begin
  X ↑ • CX                       ≈⟨ back (X ↑) (sym right-unit) ⟩
  X ↑ • CX • ε                   ≈⟨ back (X ↑) (back CX (sym X²₁)) ⟩
  X ↑ • CX • (X ↑ • X ↑)         ≈⟨ by-assoc Eq.refl ⟩
  (X ↑ • CX • X ↑) • X ↑         ≈⟨ front (X ↑) (sym XC′) ⟩
  (CX • X) • X ↑                 ≈⟨ assoc ⟩
  CX • X • X ↑                   ∎
  where open Width (₂₊ n)

-- (R3)  (Derivation H.2)
R₃ : (₂₊ n) ⊢ CX • X ↑ • CX ≈ X ↑ • X
R₃ {n} = begin
  CX • X ↑ • CX          ≈⟨ back CX X↑CX ⟩
  CX • CX • X • X ↑      ≈⟨ by-assoc Eq.refl ⟩
  (CX • CX) • X • X ↑    ≈⟨ front _ R₄ ⟩
  ε • X • X ↑            ≈⟨ left-unit ⟩
  X • X ↑                ≈⟨ sym X↑X ⟩
  X ↑ • X                ∎
  where open Width (₂₊ n)

-- (R2)  (Derivation H.1)
R₂ : (₂₊ n) ⊢ CX • X • CX ≈ X
R₂ {n} = begin
  CX • X • CX                    ≈⟨ sym assoc ⟩
  (CX • X) • CX                  ≈⟨ front CX XC′ ⟩
  (X ↑ • CX • X ↑) • CX          ≈⟨ by-assoc Eq.refl ⟩
  X ↑ • CX • (X ↑ • CX)          ≈⟨ back (X ↑) (back CX X↑CX) ⟩
  X ↑ • CX • (CX • X • X ↑)      ≈⟨ by-assoc Eq.refl ⟩
  X ↑ • (CX • CX) • X • X ↑      ≈⟨ back (X ↑) (front _ R₄) ⟩
  X ↑ • ε • X • X ↑              ≈⟨ back (X ↑) left-unit ⟩
  X ↑ • X • X ↑                  ≈⟨ sym assoc ⟩
  (X ↑ • X) • X ↑                ≈⟨ front (X ↑) X↑X ⟩
  (X • X ↑) • X ↑                ≈⟨ assoc ⟩
  X • X ↑ • X ↑                  ≈⟨ back X X²₁ ⟩
  X • ε                          ≈⟨ right-unit ⟩
  X                              ∎
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- (R5)  (Derivation H.3)

R₅ : (₂₊ n) ⊢ σ ≈ CX • σ • CX • σ • CX
R₅ {n} = sym (begin
  CX • σ • CX • σ • CX       ≈⟨ by-assoc Eq.refl ⟩
  (CX • CX↓) • CX            ≈⟨ front CX B′ ⟩
  (σ • CX) • CX              ≈⟨ assoc ⟩
  σ • CX • CX                ≈⟨ back σ R₄ ⟩
  σ • ε                      ≈⟨ right-unit ⟩
  σ                          ∎)
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- (R8)  (Derivation H.4)

-- A word on wire 0 passes a word shifted past it.
private
  pass : (w : Circuit (₁₊ n)) (k : ℕ) → (₂₊ n) ⊢ w ↑ • T ^ k ≈ T ^ k • w ↑
  pass {n} w zero          = trans right-unit (sym left-unit)
    where open Width (₂₊ n)
  pass {n} w (suc zero)    = comm-gate₁-w↑ ⌈ T-gate ⌉ w
  pass {n} w (suc (suc k)) = begin
    w ↑ • T • T ^ suc k        ≈⟨ sym assoc ⟩
    (w ↑ • T) • T ^ suc k      ≈⟨ front _ (comm-gate₁-w↑ ⌈ T-gate ⌉ w) ⟩
    (T • w ↑) • T ^ suc k      ≈⟨ assoc ⟩
    T • w ↑ • T ^ suc k        ≈⟨ back T (pass w (suc k)) ⟩
    T • T ^ suc k • w ↑        ≈⟨ sym assoc ⟩
    (T • T ^ suc k) • w ↑      ∎
    where open Width (₂₊ n)

  -- The CNOT conjugates products factor by factor.
  conj-• : (a b : Circuit (₂₊ n)) →
           (₂₊ n) ⊢ (CX • a • CX) • (CX • b • CX) ≈ CX • (a • b) • CX
  conj-• {n} a b = begin
    (CX • a • CX) • (CX • b • CX)      ≈⟨ assoc ⟩
    CX • (a • CX) • (CX • b • CX)      ≈⟨ back CX assoc ⟩
    CX • a • CX • (CX • b • CX)        ≈⟨ back CX (back a (sym assoc)) ⟩
    CX • a • (CX • CX) • b • CX        ≈⟨ back CX (back a (front _ R₄)) ⟩
    CX • a • ε • b • CX                ≈⟨ back CX (back a left-unit) ⟩
    CX • a • b • CX                    ≈⟨ back CX (sym assoc) ⟩
    CX • (a • b) • CX                  ∎
    where open Width (₂₊ n)

  Z²₀ : (₂₊ n) ⊢ Z • Z ≈ ε
  Z²₀ {n} = trans (by-assoc Eq.refl) (ax-at T⁸ (suc n))
    where open Width (₂₊ n)

R₈ : (₂₊ n) ⊢ CT ^ 4 ≈ T ^ 4 • (T ↑) ^ 4
R₈ {n} = begin
  CT • CT • CT • CT                      ≈⟨ back CT (back CT (conj-• T T)) ⟩
  CT • CT • (CX • (T • T) • CX)          ≈⟨ back CT (conj-• T (T • T)) ⟩
  CT • (CX • (T • T • T) • CX)           ≈⟨ conj-• T (T • T • T) ⟩
  CX • (T • T • T • T) • CX              ≈⟨ by-assoc Eq.refl ⟩
  CX • Z • CX                            ≈⟨ back CX (back Z (sym right-unit)) ⟩
  CX • Z • CX • ε                        ≈⟨ back CX (back Z (back CX (sym Z²₀))) ⟩
  CX • Z • CX • (Z • Z)                  ≈⟨ by-assoc Eq.refl ⟩
  CX • (Z • CX • Z) • Z                  ≈⟨ back CX (front Z (sym ZC′)) ⟩
  CX • (CX • Z ↑) • Z                    ≈⟨ by-assoc Eq.refl ⟩
  (CX • CX) • Z ↑ • Z                    ≈⟨ front _ R₄ ⟩
  ε • Z ↑ • Z                            ≈⟨ left-unit ⟩
  Z ↑ • Z                                ≈⟨ by-assoc Eq.refl ⟩
  Z ↑ • T ^ 4                            ≈⟨ pass Z 4 ⟩
  T ^ 4 • Z ↑                            ≈⟨ by-assoc Eq.refl ⟩
  T ^ 4 • (T ↑) ^ 4                      ∎
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- (R11)  (Derivation H.5)

R₁₁ : (₁₊ n) ⊢ X • T • X ≈ ω • T ^ 7
R₁₁ {n} = begin
  X • T • X              ≈⟨ sym assoc ⟩
  (X • T) • X            ≈⟨ front X (sym TX′) ⟩
  (ω • T† • X) • X       ≈⟨ by-assoc Eq.refl ⟩
  ω • T† • (X • X)       ≈⟨ back ω (back T† X²₀) ⟩
  ω • T† • ε             ≈⟨ back ω right-unit ⟩
  ω • T ^ 7              ∎
  where open Width (₁₊ n)
