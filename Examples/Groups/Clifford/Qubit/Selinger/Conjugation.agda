------------------------------------------------------------------------
-- Presentations of groups
--
-- fwd-conj: the conjugation axioms of the Clifford extension presentation
-- hold among the derived Figure-8 words.
--
-- The extension presentation of Qubit.Presentation carries one axiom per
-- (gate, Pauli generator) pair,
--
--     x · y  =  conj x y · x       (ConjRelʷ.comm y x),
--
-- where conj is read off the symplectic action actg.  Translating it with
-- f (Qubit.Selinger.Translation) turns it into an equation between gate
-- words, which this module derives in Selinger's Figure 8 mod scalars.
--
-- The case analysis follows the wire the Pauli generator sits on:
--
--   * wire 0, gate on wire 0     — C2, C3, C4 (via PauliWords.XZ);
--   * wires 0-1, gate = CZ       — C5-C9;
--   * disjoint wires             — the structural rules comm₁, comm₂.
--
-- Everything about the vector/word dictionary is in Selinger.PauliVec.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.Conjugation where

open import Data.Nat using (ℕ ; zero)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _ʷ)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic
  using (Gen ; SympGate ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥
        ; S ; H ; CZ ; _↑)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z ; _CRel,_===_ ; srel ; comm₂ ; lemma-cong↑)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; conj ; genToVec ; vecToWord)
open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pI ; pX ; pZ ; pIₙ)
import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg)

open import Examples.Groups.Clifford.Qubit.Selinger.Translation
  using (f ; pauliGen→word ; Pw ; fₗ≡Pw ; X-gen ; Z-gen)
open import Examples.Groups.Clifford.Qubit.Selinger.PauliWords using (module XZ ; module ↑Comm)
open import Examples.Groups.Clifford.Qubit.Selinger.PauliVec

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Conjugating the wire-0 Paulis by a wire-0 gate
--
-- H swaps X and Z; S sends X to XZ and fixes Z.  Only the S/X case needs
-- C4: it is the one that holds solely modulo the scalar.

module Wire0 (m : ℕ) where

  private Γ = (₁₊ m) CRel,_===_
  open PB Γ
  open PP Γ using (by-assoc ; word-setoid)
  open SR word-setoid

  -- X = H Z H, so H X = Z H by C2.
  HX : (H • X) ≈ (Z • H)
  HX = trans (sym assoc) (trans (cleft (axiom (srel MS.c2))) left-unit)

  -- The same equation read the other way round.
  HZ : (H • Z) ≈ (X • H)
  HZ = sym (trans assoc
             (trans (cright assoc)
               (trans (cright (cright (axiom (srel MS.c2))))
                      (cright right-unit))))

  -- S X S⁻¹ = X Z.  XZ.step5 (X = S³ X S³) is where C4 enters.
  SX : (S • X) ≈ ((X • Z) • S)
  SX = begin
    S • X                                 ≈⟨ cright XZ.step5 m ⟩
    S • ((S • S • S) • X • (S • S • S))   ≈⟨ by-assoc auto ⟩
    (S ^ 4) • (X • (S • S • S))           ≈⟨ cleft (axiom (srel MS.c3)) ⟩
    ε • (X • (S • S • S))                 ≈⟨ left-unit ⟩
    X • (S • S • S)                       ≈⟨ by-assoc auto ⟩
    (X • Z) • S                           ∎

  -- Z is a power of S.
  SZ : (S • Z) ≈ (Z • S)
  SZ = by-assoc auto

------------------------------------------------------------------------
-- Conjugating by CZ
--
-- C8 and C9 give the two nontrivial conjugates; C6 and C7 say the S's,
-- hence the Z's, pass through.  Each is turned round with C5 (CZ² = ε).

module Wire01 (m : ℕ) where

  private Γ = (₂₊ m) CRel,_===_
  open PB Γ
  open PP Γ using (by-assoc ; word-setoid)
  open SR word-setoid

  CZ-X : (CZ • X) ≈ ((X • Z ↑) • CZ)
  CZ-X = begin
    CZ • X                        ≈⟨ sym right-unit ⟩
    (CZ • X) • ε                  ≈⟨ cright (sym (axiom (srel MS.c5))) ⟩
    (CZ • X) • (CZ • CZ)          ≈⟨ by-assoc auto ⟩
    (CZ • (X • CZ)) • CZ          ≈⟨ cleft (cright (axiom (srel MS.c8))) ⟩
    (CZ • (CZ • (X • Z ↑))) • CZ  ≈⟨ cleft (sym assoc) ⟩
    ((CZ • CZ) • (X • Z ↑)) • CZ  ≈⟨ cleft (cleft (axiom (srel MS.c5))) ⟩
    (ε • (X • Z ↑)) • CZ          ≈⟨ cleft left-unit ⟩
    (X • Z ↑) • CZ                ∎

  CZ-X↑ : (CZ • X ↑) ≈ ((Z • X ↑) • CZ)
  CZ-X↑ = begin
    CZ • X ↑                      ≈⟨ sym right-unit ⟩
    (CZ • X ↑) • ε                ≈⟨ cright (sym (axiom (srel MS.c5))) ⟩
    (CZ • X ↑) • (CZ • CZ)        ≈⟨ by-assoc auto ⟩
    (CZ • (X ↑ • CZ)) • CZ        ≈⟨ cleft (cright (axiom (srel MS.c9))) ⟩
    -- C9 lists the acted Pauli first (X↑ then Z), as C8 does; the shape
    -- this lemma feeds downstream wants them the other way round, and
    -- they are on disjoint wires, so ↑-comm-Z swaps them.
    (CZ • (CZ • (X ↑ • Z))) • CZ  ≈⟨ cleft (cright (cright (↑Comm.↑-comm-Z (₁₊ m) X))) ⟩
    (CZ • (CZ • (Z • X ↑))) • CZ  ≈⟨ cleft (sym assoc) ⟩
    ((CZ • CZ) • (Z • X ↑)) • CZ  ≈⟨ cleft (cleft (axiom (srel MS.c5))) ⟩
    (ε • (Z • X ↑)) • CZ          ≈⟨ cleft left-unit ⟩
    (Z • X ↑) • CZ                ∎

  CZ-Z : (CZ • Z) ≈ (Z • CZ)
  CZ-Z = begin
    CZ • (S • S)  ≈⟨ sym assoc ⟩
    (CZ • S) • S  ≈⟨ cleft (sym (axiom (srel MS.c6))) ⟩
    (S • CZ) • S  ≈⟨ assoc ⟩
    S • (CZ • S)  ≈⟨ cright (sym (axiom (srel MS.c6))) ⟩
    S • (S • CZ)  ≈⟨ sym assoc ⟩
    (S • S) • CZ  ∎

  CZ-Z↑ : (CZ • Z ↑) ≈ (Z ↑ • CZ)
  CZ-Z↑ = begin
    CZ • (S ↑ • S ↑)  ≈⟨ sym assoc ⟩
    (CZ • S ↑) • S ↑  ≈⟨ cleft (sym (axiom (srel MS.c7))) ⟩
    (S ↑ • CZ) • S ↑  ≈⟨ assoc ⟩
    S ↑ • (CZ • S ↑)  ≈⟨ cright (sym (axiom (srel MS.c7))) ⟩
    S ↑ • (S ↑ • CZ)  ≈⟨ sym assoc ⟩
    (S ↑ • S ↑) • CZ  ∎

  -- Anything on wires 2 and above commutes with CZ, by comm₂.
  CZ-comm : (w : Word (Gen m)) → (CZ • (w ↑ ↑)) ≈ ((w ↑ ↑) • CZ)
  CZ-comm [ g ]ʷ  = sym (axiom (comm₂ CZ-gate g))
  CZ-comm ε       = trans right-unit (sym left-unit)
  CZ-comm (u • v) =
    trans (sym assoc)
      (trans (cleft (CZ-comm u))
        (trans assoc (trans (cright (CZ-comm v)) (sym assoc))))

------------------------------------------------------------------------
-- The conjugation axioms, translated

private

  -- Rewrite the two Pauli words of a conjugation equation.
  via : {a u u' v v' : Word (Gen n)} →
        PB._≈_ (n CRel,_===_) u u' →
        PB._≈_ (n CRel,_===_) v v' →
        PB._≈_ (n CRel,_===_) (a • u') (v' • a) →
        PB._≈_ (n CRel,_===_) (a • u) (v • a)
  via pu pv h =
    PB.trans (PB.cong PB.refl pu)
             (PB.trans h (PB.cong (PB.sym pv) PB.refl))

  -- conj at a wire-0 generator, with genToVec unfolded.
  conj-X : (x : Gen (₁₊ m)) →
           conj x (X-gen {m}) ≡ vecToWord (actg x (pX ∷ pIₙ {m}))
  conj-X x = Eq.cong (λ □ → vecToWord (actg x □)) genToVec-X

  conj-Z : (x : Gen (₁₊ m)) →
           conj x (Z-gen {m}) ≡ vecToWord (actg x (pZ ∷ pIₙ {m}))
  conj-Z x = Eq.cong (λ □ → vecToWord (actg x □)) genToVec-Z

  -- A Pauli generator above wire 0, translated after the action of a
  -- gate that fixes the wire-0 slot.
  above : (ps : Pauli (₁₊ m)) (y : PauliGen (₁₊ m)) →
          PB._≈_ ((₁₊ m) CRel,_===_) (Pw (vecToWord ps)) (pauliGen→word y) →
          PB._≈_ ((₂₊ m) CRel,_===_)
                 (Pw (vecToWord (pI ∷ ps))) (pauliGen→word y ↑)
  above ps y eq =
    PB.trans (Pw-cons pI ps)
             (PB.trans (PB.cong Pq-I (lemma-cong↑ _ _ eq)) PB.left-unit)

-- The translated conjugation equation, generator by generator.
conj-word : (x : Gen n) (y : PauliGen n) →
            PB._≈_ (n CRel,_===_)
                   ([ x ]ʷ • pauliGen→word y) (Pw (conj x y) • [ x ]ʷ)

conj-word {₁₊ m} (gate₁ H-gate) y with pview {m} y
... | vX =
  via (PB.refl' _ P-X)
      (PB.trans (PB.refl' _ (Eq.cong Pw (conj-X (gate₁ H-gate))))
                (PB.trans (Pw-basis pZ) Pq-Z))
      (Wire0.HX _)
... | vZ =
  via (PB.refl' _ P-Z)
      (PB.trans (PB.refl' _ (Eq.cong Pw (conj-Z (gate₁ H-gate))))
                (PB.trans (Pw-basis pX) Pq-X))
      (Wire0.HZ _)
... | v↑ y' =
  via PB.refl (above (genToVec y') y' (Pw-genToVec y'))
      (PB.sym (↑Comm.↑-comm-gen _ (pauliGen→word y') H-gate))

conj-word {₁₊ m} (gate₁ S-gate) y with pview {m} y
... | vX =
  via (PB.refl' _ P-X)
      (PB.trans (PB.refl' _ (Eq.cong Pw (conj-X (gate₁ S-gate))))
                (PB.trans (Pw-basis (₁ , ₁)) Pq-XZ))
      (Wire0.SX _)
... | vZ =
  via (PB.refl' _ P-Z)
      (PB.trans (PB.refl' _ (Eq.cong Pw (conj-Z (gate₁ S-gate))))
                (PB.trans (Pw-basis pZ) Pq-Z))
      (Wire0.SZ _)
... | v↑ y' =
  via PB.refl (above (genToVec y') y' (Pw-genToVec y'))
      (PB.sym (↑Comm.↑-comm-gen _ (pauliGen→word y') S-gate))

conj-word {₂₊ m} (gate₂ CZ-gate) y with pview {₁₊ m} y
... | vX =
  via (PB.refl' _ P-X)
      (PB.trans (PB.refl' _ (Eq.cong Pw (conj-X (gate₂ CZ-gate))))
                (PB.trans (Pw-basis₂ pX pZ)
                          (PB.cong Pq-X (lemma-cong↑ _ _ Pq-Z))))
      (Wire01.CZ-X _)
... | vZ =
  via (PB.refl' _ P-Z)
      (PB.trans (PB.refl' _ (Eq.cong Pw (conj-Z (gate₂ CZ-gate))))
                (PB.trans (Pw-basis₂ pZ pI)
                          (PB.trans (PB.cong Pq-Z (lemma-cong↑ _ _ Pq-I))
                                    PB.right-unit)))
      (Wire01.CZ-Z _)
... | v↑ y' with pview {m} y'
... | vX =
  via (PB.refl' _ (Eq.cong _↑ P-X))
      (PB.trans (PB.refl' _
                  (Eq.cong (λ □ → Pw (vecToWord (actg (gate₂ CZ-gate) (pI ∷ □))))
                           genToVec-X))
                (PB.trans (Pw-basis₂ pZ pX)
                          (PB.cong Pq-Z (lemma-cong↑ _ _ Pq-X))))
      (Wire01.CZ-X↑ _)
... | vZ =
  via (PB.refl' _ (Eq.cong _↑ P-Z))
      (PB.trans (PB.refl' _
                  (Eq.cong (λ □ → Pw (vecToWord (actg (gate₂ CZ-gate) (pI ∷ □))))
                           genToVec-Z))
                (PB.trans (Pw-basis₂ pI pZ)
                          (PB.trans (PB.cong Pq-I (lemma-cong↑ _ _ Pq-Z))
                                    PB.left-unit)))
      (Wire01.CZ-Z↑ _)
... | v↑ y'' =
  via PB.refl
      (above (pI ∷ genToVec y'') (inj₂ y'')
             (above (genToVec y'') y'' (Pw-genToVec y'')))
      (Wire01.CZ-comm _ (pauliGen→word y''))

conj-word {₁₊ m} (g ↥) y with pview {m} y
... | vX =
  via (PB.refl' _ P-X)
      (PB.trans (PB.refl' _
                  (Eq.cong Pw
                    (Eq.trans (conj-X (g ↥))
                              (Eq.cong (λ □ → vecToWord (pX ∷ □)) (act-pI g)))))
                (PB.trans (Pw-basis pX) Pq-X))
      (↑Comm.↑-comm-X _ [ g ]ʷ)
... | vZ =
  via (PB.refl' _ P-Z)
      (PB.trans (PB.refl' _
                  (Eq.cong Pw
                    (Eq.trans (conj-Z (g ↥))
                              (Eq.cong (λ □ → vecToWord (pZ ∷ □)) (act-pI g)))))
                (PB.trans (Pw-basis pZ) Pq-Z))
      (↑Comm.↑-comm-Z _ [ g ]ʷ)
... | v↑ y' =
  via PB.refl
      (PB.trans (Pw-cons pI (actg g (genToVec y')))
                (PB.trans (PB.cong Pq-I PB.refl) PB.left-unit))
      (lemma-cong↑ _ _ (conj-word g y'))

------------------------------------------------------------------------
-- fwd-conj, in the shape Qubit.Selinger.Iso's F-WD asks for

fwd-conj : (y : PauliGen n) (x : Gen n) →
           PB._≈_ (n CRel,_===_)
                  ((f ʷ) ([ [ x ]ʷ ]ᵣ • [ [ y ]ʷ ]ₗ))
                  ((f ʷ) ([ conj x y ]ₗ • [ [ x ]ʷ ]ᵣ))
fwd-conj {n} y x =
  Eq.subst (λ □ → PB._≈_ (n CRel,_===_)
                         ([ x ]ʷ • pauliGen→word y) (□ • [ x ]ʷ))
           (Eq.sym (fₗ≡Pw (conj x y))) (conj-word x y)
