------------------------------------------------------------------------
-- Presentations of groups
--
-- The mixed Schreier atom M_a X_bc K_abcd is built from a disjoint
-- pair of K blocks and a sign pair.  This is the Table 1 identity
-- behind the physical decoder: (K_A K_B)(M_a M_e), squared, equals
-- the mixed atom whenever the spare block B and level e are disjoint.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+H.GeneralN.MixedAtom {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_)
open import Word.Base using (Word ; ε ; _•_)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Derived as D
import Examples.Groups.CCX+H.GeneralN.Factorization as Factorization
open import Presentation.Base (U._===_ {n}) hiding (_===_)
open import Presentation.Properties (U._===_ {n}) using (word-setoid ; by-assoc)
open import Relation.Binary.Reasoning.Setoid word-setoid

private
  module F = Factorization (U._===_ {n}) D.grouplike
  open F using (comm-product ; product-comm)

  cancel-square : ∀ P C → C • P ≈ P • C → C • C ≈ ε →
    (P • C) • (P • C) ≈ P • P
  cancel-square P C cp cc = begin
    (P • C) • (P • C) ≈⟨ trans assoc (cong refl (sym assoc)) ⟩
    P • ((C • P) • C) ≈⟨ cong refl (cong cp refl) ⟩
    P • ((P • C) • C) ≈⟨ trans (cong refl assoc) (sym assoc) ⟩
    (P • P) • (C • C) ≈⟨ cong refl cc ⟩
    (P • P) • ε ≈⟨ right-unit ⟩
    P • P ∎

module Block
  (a b c d e f g h i : Fin n)
  .(ab : a < b) .(bc : b < c) .(cd : c < d)
  .(fg : f < g) .(gh : g < h) .(hi : h < i)
  (af : a ≢ f) (ag : a ≢ g) (ah : a ≢ h) (ai : a ≢ i)
  (bf : b ≢ f) (bg : b ≢ g) (bh : b ≢ h) (bi : b ≢ i)
  (cf : c ≢ f) (cg : c ≢ g) (ch : c ≢ h) (ci : c ≢ i)
  (df : d ≢ f) (dg : d ≢ g) (dh : d ≢ h) (di : d ≢ i)
  (ea : e ≢ a) (eb : e ≢ b) (ec : e ≢ c) (ed : e ≢ d)
  (ef : e ≢ f) (eg : e ≢ g) (eh : e ≢ h) (ei : e ≢ i)
  where

  A B Q S J : Word (U.Gen n)
  A = U.K a b c d ab bc cd
  B = U.K f g h i fg gh hi
  Q = A • B
  S = U.M a • U.M e
  J = (U.M a • U.X b c bc) • A

  private
    m = U.M a
    t = U.M e
    P = A • m
    C = B • t

    AB : A • B ≈ B • A
    AB = axiom (U.r2f ab bc cd fg gh hi
      af ag ah ai bf bg bh bi cf cg ch ci df dg dh di)

    mB : m • B ≈ B • m
    mB = axiom (U.r2e fg gh hi af ag ah ai)

    tA : t • A ≈ A • t
    tA = axiom (U.r2e ab bc cd ea eb ec ed)

    tB : t • B ≈ B • t
    tB = axiom (U.r2e fg gh hi ef eg eh ei)

    tm : t • m ≈ m • t
    tm = axiom (U.r2d ea)

    PC : C • P ≈ P • C
    PC = product-comm (comm-product (sym AB) (sym mB))
      (comm-product tA tm)

    CC : C • C ≈ ε
    CC = trans (cancel-square B t tB (axiom U.r1b))
      (axiom (U.r1c fg gh hi))

    QS : Q • S ≈ P • C
    QS = begin
      (A • B) • (m • t) ≈⟨ by-assoc Eq.refl ⟩
      A • ((B • m) • t) ≈⟨ cong refl (cong (sym mB) refl) ⟩
      A • ((m • B) • t) ≈⟨ by-assoc Eq.refl ⟩
      (A • m) • (B • t) ∎

  reflection : J ≈ P • P
  reflection = begin
    (m • U.X b c bc) • A ≈⟨ assoc ⟩
    m • (U.X b c bc • A) ≈⟨ cong refl (axiom (U.r4b ab bc cd)) ⟩
    m • (m • A • m • A • m) ≈⟨ by-assoc Eq.refl ⟩
    (m • m) • ((A • m) • (A • m)) ≈⟨ cong (axiom U.r1b) refl ⟩
    ε • ((A • m) • (A • m)) ≈⟨ left-unit ⟩
    P • P ∎

  mixed : (Q • S) • (Q • S) ≈ J
  mixed = trans (cong QS QS)
    (trans (cancel-square P C PC CC) (sym reflection))
