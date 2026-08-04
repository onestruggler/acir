------------------------------------------------------------------------
-- Presentations of groups
--
-- Transporting the c10 residual word identities to c11 by Ex-conjugation.
--
-- The three open c11 word identities (SrelWDSel11i/j/k's *-Goal) are the
-- wire-0↔1 mirrors of the proven c10 identities (SrelWDSel10l.idβα,
-- SrelWDSel10k.idαβ, SrelWDSel10n.idββ).  The coset-level duality died
-- (Ex acts only on doubly-inj₂ cosets), but at the WORD level the swap
-- is simply conjugation by Ex, and conjugation is a congruence — no
-- axiom-preservation argument needed.
--
-- Machinery: a sliding relation  Sl A B = A • Ex ≈ Ex • B, closed under
-- concatenation and powers, with base slides from the live Ex-Sym*
-- lemma family (all at general width):
--     lemma-comm-Ex-H-n  : H ↑ • Ex ≈ Ex • H
--     lemma-comm-Ex-CZ-n : CZ • Ex ≈ Ex • CZ
--     lemma-order-Ex-n   : Ex ^ 2 ≈ ε
--     lemma-Ex-S^ᵏ       : Ex • S^ k ≈ S^ k ↑ • Ex     (symbolic power!)
--     lemma-Ex-M         : Ex • ZM x ≈ ZM x ↑ • Ex
-- Directions are completed by sl-flip, which conjugates a slide by
-- Ex • Ex ≈ ε.  Then  conj-eq : Sl A A' → Sl B B' → A' ≈ B' → A ≈ B
-- (prove upstairs, cancel Ex on the right via Group-Lemmas.•-cancelʳ)
-- turns each c10 identity instance into its c11 mirror.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.ExTransport
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Fin using (Fin ; toℕ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Symplectic-GroupLike using (grouplike)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime
  using (lemma-comm-Ex-H-n ; lemma-comm-Ex-CZ-n ; lemma-order-Ex-n ;
         lemma-Ex-S↑-n)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime using (C)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (hpad)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10l
  p-2 p-prime using (module BAValues ; idβα)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10k
  p-2 p-prime using (idαβ)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10n
  p-2 p-prime using (idββ)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10f
  p-2 p-prime using (padSA)
import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11i
  p-2 p-prime as S11i
import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11j
  p-2 p-prime as S11j
import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11k
  p-2 p-prime as S11k

------------------------------------------------------------------------
-- The sliding kit.

module Slide {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open Group-Lemmas ((₂₊ m) QRel,_===_) (grouplike {₂₊ m})
    using (•-cancelʳ)
  open Lemmas-Sym using (lemma-comm-H-w↑ ; lemma-comm-S-w↑)
  open SR word-setoid

  -- A • Ex ≈ Ex • B : sliding Ex leftward through A leaves B.
  Sl : Word (Gen (₂₊ m)) → Word (Gen (₂₊ m)) → Set
  Sl A B = A • Ex ≈ Ex • B

  -- The Ex-Sym2n lemmas arrive by-emb'd from width 2, so their words are
  -- flattened right-nested letter chains rather than Ex-shaped; by-assoc
  -- (associativity only, concrete letters) bridges the bracketing.
  E2 : Ex • Ex ≈ ε
  E2 = trans (by-assoc auto) lemma-order-Ex-n

  sl-flip : ∀ {A B} → Sl A B → Sl B A
  sl-flip {A} {B} s = begin
    B • Ex                ≈⟨ sym left-unit ⟩
    ε • (B • Ex)          ≈⟨ cleft (sym E2) ⟩
    (Ex • Ex) • (B • Ex)  ≈⟨ assoc ⟩
    Ex • (Ex • (B • Ex))  ≈⟨ cright (sym assoc) ⟩
    Ex • ((Ex • B) • Ex)  ≈⟨ cright (cleft (sym s)) ⟩
    Ex • ((A • Ex) • Ex)  ≈⟨ cright assoc ⟩
    Ex • (A • (Ex • Ex))  ≈⟨ cright (cright E2) ⟩
    Ex • (A • ε)          ≈⟨ cright right-unit ⟩
    Ex • A ∎

  sl-• : ∀ {A A' B B'} → Sl A A' → Sl B B' → Sl (A • B) (A' • B')
  sl-• {A} {A'} {B} {B'} sA sB = begin
    (A • B) • Ex    ≈⟨ assoc ⟩
    A • (B • Ex)    ≈⟨ cright sB ⟩
    A • (Ex • B')   ≈⟨ sym assoc ⟩
    (A • Ex) • B'   ≈⟨ cleft sA ⟩
    (Ex • A') • B'  ≈⟨ assoc ⟩
    Ex • (A' • B') ∎

  sl-ε : Sl ε ε
  sl-ε = trans left-unit (sym right-unit)

  sl-H↑ : Sl (H ↑) H
  sl-H↑ = trans (by-assoc auto) (trans lemma-comm-Ex-H-n (by-assoc auto))

  sl-H : Sl H (H ↑)
  sl-H = sl-flip sl-H↑

  sl-CZ : Sl CZ CZ
  sl-CZ = trans (by-assoc auto) (trans lemma-comm-Ex-CZ-n (by-assoc auto))

  sl-S : Sl S (S ↑)
  sl-S = trans (by-assoc auto) (trans (sym lemma-Ex-S↑-n) (by-assoc auto))

  sl-S↑ : Sl (S ↑) S
  sl-S↑ = sl-flip sl-S

  -- ℕ-indexed powers slide factorwise.
  sl-pow : ∀ {A A'} → Sl A A' → ∀ j → Sl (A ^ j) (A' ^ j)
  sl-pow s zero          = sl-ε
  sl-pow s (suc zero)    = s
  sl-pow s (suc (suc j)) = sl-• s (sl-pow s (suc j))

  -- Symbolic S-powers: S^ k = S ^ toℕ k, and _↑ = wmap distributes over
  -- • definitionally, so (S ^ j) ↑ needs only the power-lift bridge.
  ↑-pow : ∀ (w : Circuit (₁₊ m)) j → (w ^ j) ↑ ≡ (w ↑) ^ j
  ↑-pow w zero          = Eq.refl
  ↑-pow w (suc zero)    = Eq.refl
  ↑-pow w (suc (suc j)) = Eq.cong ((w ↑) •_) (↑-pow w (suc j))

  sl-castR : ∀ {A B B'} → Sl A B → B ≡ B' → Sl A B'
  sl-castR s eq = trans s (cright (refl' eq))

  sl-S^ : ∀ (k : ℤ ₚ) → Sl (S^ k) (S^ k ↑)
  sl-S^ k = sl-castR (sl-pow sl-S (toℕ k)) (Eq.sym (↑-pow S (toℕ k)))

  sl-S^↑ : ∀ (k : ℤ ₚ) → Sl (S^ k ↑) (S^ k)
  sl-S^↑ k = sl-flip (sl-S^ k)

  -- ZM x = S^ x • H • S^ x⁻¹ • H • S^ x • H, and wmap distributes, so
  -- the composite slide lands on ZM x ↑ definitionally.
  sl-ZM : ∀ (x : ℤ* ₚ) → Sl (ZM x) (ZM x ↑)
  sl-ZM x = sl-• (sl-S^ (x .proj₁)) (sl-• sl-H (sl-• (sl-S^ ((x ⁻¹) .proj₁))
    (sl-• sl-H (sl-• (sl-S^ (x .proj₁)) sl-H))))

  sl-ZM↑ : ∀ (x : ℤ* ₚ) → Sl (ZM x ↑) (ZM x)
  sl-ZM↑ x = sl-flip (sl-ZM x)

  -- The transported equation: prove upstairs, cancel Ex.
  conj-eq : ∀ {A A' B B'} → Sl A A' → Sl B B' → A' ≈ B' → A ≈ B
  conj-eq {A} {A'} {B} {B'} sA sB eq = •-cancelʳ (begin
    A • Ex   ≈⟨ sA ⟩
    Ex • A'  ≈⟨ cright eq ⟩
    Ex • B'  ≈⟨ sym sB ⟩
    B • Ex ∎)

------------------------------------------------------------------------
-- Pads: the clause-4 CZ escape, its Ex-dual, and the commutation
-- normalising the dual back to pad shape with exchanged exponents.

  pad : (u v : ℤ ₚ) → Word (Gen (₂₊ m))
  pad u v = H • (H ↑ • (CZ • (S^ u • (H ^ 3 • (S^ v ↑ • (H ↑) ^ 3)))))

  padDual : (u v : ℤ ₚ) → Word (Gen (₂₊ m))
  padDual u v =
    H ↑ • (H • (CZ • (S^ u ↑ • ((H ↑) ^ 3 • (S^ v • H ^ 3)))))

  sl-pad : ∀ u v → Sl (pad u v) (padDual u v)
  sl-pad u v =
    sl-• sl-H (sl-• sl-H↑ (sl-• sl-CZ (sl-• (sl-S^ u)
      (sl-• (sl-pow sl-H 3) (sl-• (sl-S^↑ v) (sl-pow sl-H↑ 3))))))

  -- Disjoint-wire commutations for symbolic powers (as in SrelWDSel10l).
  SkW : ∀ (k : ℤ ₚ) (w : Word (Gen (₁₊ m))) → S^ k • w ↑ ≈ w ↑ • S^ k
  SkW k w = comm⇒pow-comm {w = S} {v = w ↑} (toℕ k) 1 (lemma-comm-S-w↑ w)

  H3W : ∀ (w : Word (Gen (₁₊ m))) → H ^ 3 • w ↑ ≈ w ↑ • H ^ 3
  H3W w = comm⇒pow-comm {w = H} {v = w ↑} 3 1 (lemma-comm-H-w↑ w)

  -- padDual u v ≈ pad v u : pure disjoint-wire commutation.
  pad-norm : ∀ u v → padDual u v ≈ pad v u
  pad-norm u v = begin
    H ↑ • (H • (CZ • (S^ u ↑ • ((H ↑) ^ 3 • (S^ v • H ^ 3)))))
      ≈⟨ sym assoc ⟩
    (H ↑ • H) • (CZ • (S^ u ↑ • ((H ↑) ^ 3 • (S^ v • H ^ 3))))
      ≈⟨ cleft (sym (lemma-comm-H-w↑ H)) ⟩
    (H • H ↑) • (CZ • (S^ u ↑ • ((H ↑) ^ 3 • (S^ v • H ^ 3))))
      ≈⟨ assoc ⟩
    H • (H ↑ • (CZ • (S^ u ↑ • ((H ↑) ^ 3 • (S^ v • H ^ 3)))))
      ≈⟨ cright (cright (cright inner)) ⟩
    H • (H ↑ • (CZ • (S^ v • (H ^ 3 • (S^ u ↑ • (H ↑) ^ 3))))) ∎
    where
    -- S^u↑ • ((H↑)³ • (S^v • H³)) ≈ S^v • (H³ • (S^u↑ • (H↑)³))
    inner : S^ u ↑ • ((H ↑) ^ 3 • (S^ v • H ^ 3))
          ≈ S^ v • (H ^ 3 • (S^ u ↑ • (H ↑) ^ 3))
    inner = begin
      S^ u ↑ • ((H ↑) ^ 3 • (S^ v • H ^ 3))
        ≈⟨ cright (sym assoc) ⟩
      S^ u ↑ • (((H ↑) ^ 3 • S^ v) • H ^ 3)
        ≈⟨ cright (cleft (refl' (Eq.cong (_• S^ v) (Eq.sym (↑-pow H 3))))) ⟩
      S^ u ↑ • (((H ^ 3) ↑ • S^ v) • H ^ 3)
        ≈⟨ cright (cleft (sym (SkW v (H ^ 3)))) ⟩
      S^ u ↑ • ((S^ v • (H ^ 3) ↑) • H ^ 3)
        ≈⟨ cright (cleft (cright (refl' (↑-pow H 3)))) ⟩
      S^ u ↑ • ((S^ v • (H ↑) ^ 3) • H ^ 3)
        ≈⟨ cright assoc ⟩
      S^ u ↑ • (S^ v • ((H ↑) ^ 3 • H ^ 3))
        ≈⟨ sym assoc ⟩
      (S^ u ↑ • S^ v) • ((H ↑) ^ 3 • H ^ 3)
        ≈⟨ cleft (sym (SkW v (S^ u))) ⟩
      (S^ v • S^ u ↑) • ((H ↑) ^ 3 • H ^ 3)
        ≈⟨ assoc ⟩
      S^ v • (S^ u ↑ • ((H ↑) ^ 3 • H ^ 3))
        ≈⟨ cright (sym assoc) ⟩
      S^ v • ((S^ u ↑ • (H ↑) ^ 3) • H ^ 3)
        ≈⟨ cright (cleft (refl' merge-top)) ⟩
      S^ v • (((S^ u • H ^ 3) ↑) • H ^ 3)
        ≈⟨ cright (sym (H3W (S^ u • H ^ 3))) ⟩
      S^ v • (H ^ 3 • ((S^ u • H ^ 3) ↑))
        ≈⟨ cright (cright (refl' (Eq.sym merge-top))) ⟩
      S^ v • (H ^ 3 • (S^ u ↑ • (H ↑) ^ 3)) ∎
      where
      merge-top : S^ u ↑ • (H ↑) ^ 3 ≡ (S^ u • H ^ 3) ↑
      merge-top = Eq.cong (S^ u ↑ •_) (Eq.sym (↑-pow H 3))

------------------------------------------------------------------------
-- The βα transport: SrelWDSel10l.idβα at swapped parameters, conjugated
-- by Ex, is exactly SrelWDSel11i's idβα-c11-Goal.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open Slide {m}

  idβα-c11-ident : ∀ (b1 b2 : ℤ ₚ) (a1' a2' w : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) → (eqZ : b1 + ₁₊ a1' ≡ ₀) →
    S11i.RSteps.idβα-c11-Goal {m} b1 b2 a1' a2' w lm2 eqY eqZ
  idβα-c11-ident b1 b2 a1' a2' w lm2 eqY eqZ =
    trans (refl' Lfix) (trans core (refl' (Eq.sym Rfix)))
    where
    -- the exponents, spelled as in SrelWDSel11i.RSteps
    u₁ v₁ uw vw r : ℤ ₚ
    u₁ = - ₁₊ a2' * ((₁₊ a1' , λ ()) ⁻¹) .proj₁
    v₁ = - ₁₊ a1' * ((₁₊ a2' , λ ()) ⁻¹) .proj₁
    uw = - ₁₊ a2' * ((₁₊ w , λ ()) ⁻¹) .proj₁
    vw = - ₁₊ w * ((₁₊ a2' , λ ()) ⁻¹) .proj₁
    r  = ₁₊ w * ((₁₊ a1' , λ ()) ⁻¹) .proj₁

    q : ℤ* ₚ
    q = (₁₊ a1' , λ ()) *' ((₁₊ w , λ ()) ⁻¹)

    LHS' RHS' : Word (Gen (₂₊ m))
    LHS' = pad u₁ v₁ • ((ZM q • S^ r) • pad uw vw)
    RHS' = (H • H) • ((S ^ p-1) • (H ↑ • (CZ • (H ↑) ^ 3)))

    -- the Goal's raw words reduce to the explicit ones
    Lfix : S11i.RSteps.PADg {m} b1 b2 a1' a2' w lm2 eqY eqZ •
             (S11i.RSteps.HU {m} b1 b2 a1' a2' w lm2 eqY eqZ •
              S11i.RSteps.PADy {m} b1 b2 a1' a2' w lm2 eqY eqZ) ≡ LHS'
    Lfix = Eq.cong₂ _•_ Eq.refl
      (Eq.cong₂ _•_ (hpad {₁₊ m} a1' w) Eq.refl)

    Rfix : S11i.RSteps.HH2 {m} b1 b2 a1' a2' w lm2 eqY eqZ •
             ((S ^ p-1) •
              S11i.RSteps.CZpad {m} b1 b2 a1' a2' w lm2 eqY eqZ) ≡ RHS'
    Rfix = Eq.refl

    -- slide both sides past Ex
    slL : Sl LHS' (padDual u₁ v₁ • ((ZM q ↑ • S^ r ↑) • padDual uw vw))
    slL = sl-• (sl-pad u₁ v₁)
            (sl-• (sl-• (sl-ZM q) (sl-S^ r)) (sl-pad uw vw))

    slR : Sl RHS' ((H ↑ • H ↑) •
            ((S ↑) ^ p-1 • (H • (CZ • H ^ 3))))
    slR = sl-• (sl-• sl-H sl-H)
            (sl-• (sl-pow sl-S p-1)
              (sl-• sl-H↑ (sl-• sl-CZ (sl-pow sl-H↑ 3))))

    -- the c10 identity at swapped parameters
    wSum : ₁₊ w ≡ - (₁₊ a1' + ₁₊ a2')
    wSum = S11i.Values.wSum a1' a2' w b1 eqY eqZ

    mid : padDual u₁ v₁ • ((ZM q ↑ • S^ r ↑) • padDual uw vw)
        ≈ (H ↑ • H ↑) • ((S ↑) ^ p-1 • (H • (CZ • H ^ 3)))
    mid = trans (cong (pad-norm u₁ v₁) (cong refl (pad-norm uw vw)))
          (trans (idβα a2' a1' w wSum)
                 (cright (cleft (refl' (↑-pow S p-1)))))

    core : LHS' ≈ RHS'
    core = conj-eq slL slR mid

------------------------------------------------------------------------
-- The αβ transport: SrelWDSel10k.idαβ at swapped parameters.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open Slide {m}

  idαβ-c11-ident : ∀ (b1 b2 : ℤ ₚ) (a1' a2' z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₀) → (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) →
    S11j.RStepsJ.idαβ-c11-Goal {m} b1 b2 a1' a2' z lm2 eqY eqZ
  idαβ-c11-ident b1 b2 a1' a2' z lm2 eqY eqZ =
    trans (refl' Lfix) (trans core (refl' (Eq.sym Rfix)))
    where
    u₁ v₁ uz vz r' : ℤ ₚ
    u₁ = - ₁₊ a2' * ((₁₊ a1' , λ ()) ⁻¹) .proj₁
    v₁ = - ₁₊ a1' * ((₁₊ a2' , λ ()) ⁻¹) .proj₁
    uz = - ₁₊ a2' * ((₁₊ z , λ ()) ⁻¹) .proj₁
    vz = - ₁₊ z * ((₁₊ a2' , λ ()) ⁻¹) .proj₁
    r' = ₁₊ z * ((₁₊ a1' , λ ()) ⁻¹) .proj₁

    q' : ℤ* ₚ
    q' = (₁₊ a1' , λ ()) *' ((₁₊ z , λ ()) ⁻¹)

    XCw : Word (Gen (₂₊ m))
    XCw = H ↑ • (CZ • (H ↑) ^ 3)

    LHS' RHS' : Word (Gen (₂₊ m))
    LHS' = pad u₁ v₁ • ((H • H) • XCw)
    RHS' = (ZM q' • S^ r') • (pad uz vz • ((H • H) • (S ^ p-1)))

    Lfix : S11j.RStepsJ.PADg {m} b1 b2 a1' a2' z lm2 eqY eqZ •
             (S11j.RStepsJ.HH2 {m} b1 b2 a1' a2' z lm2 eqY eqZ •
              S11j.RStepsJ.CZpadA {m} b1 b2 a1' a2' z lm2 eqY eqZ) ≡ LHS'
    Lfix = Eq.cong₂ _•_ (padSA a1' a2' b1 b2) Eq.refl

    Rfix : S11j.RStepsJ.HU {m} b1 b2 a1' a2' z lm2 eqY eqZ •
             (S11j.RStepsJ.PADz {m} b1 b2 a1' a2' z lm2 eqY eqZ •
              (S11j.RStepsJ.HHz {m} b1 b2 a1' a2' z lm2 eqY eqZ •
               (S ^ p-1))) ≡ RHS'
    Rfix = Eq.cong₂ _•_ (hpad {₁₊ m} a1' z) Eq.refl

    slL : Sl LHS' (padDual u₁ v₁ • ((H ↑ • H ↑) • (H • (CZ • H ^ 3))))
    slL = sl-• (sl-pad u₁ v₁)
            (sl-• (sl-• sl-H sl-H)
              (sl-• sl-H↑ (sl-• sl-CZ (sl-pow sl-H↑ 3))))

    slR : Sl RHS' ((ZM q' ↑ • S^ r' ↑) •
            (padDual uz vz • ((H ↑ • H ↑) • (S ↑) ^ p-1)))
    slR = sl-• (sl-• (sl-ZM q') (sl-S^ r'))
            (sl-• (sl-pad uz vz)
              (sl-• (sl-• sl-H sl-H) (sl-pow sl-S p-1)))

    zAA : ₁₊ a2' + ₁₊ a1' ≡ ₁₊ z
    zAA = Eq.sym (S11j.Values.zSum a1' a2' z b1 eqY eqZ)

    mid : padDual u₁ v₁ • ((H ↑ • H ↑) • (H • (CZ • H ^ 3)))
        ≈ (ZM q' ↑ • S^ r' ↑) •
          (padDual uz vz • ((H ↑ • H ↑) • (S ↑) ^ p-1))
    mid = trans (cleft (pad-norm u₁ v₁))
          (trans (idαβ a2' a1' z zAA)
            (cright (trans (cleft (sym (pad-norm uz vz)))
              (cright (cright (refl' (↑-pow S p-1)))))))

    core : LHS' ≈ RHS'
    core = conj-eq slL slR mid

------------------------------------------------------------------------
-- The ββ transport: SrelWDSel10n.idββ at swapped parameters.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open Slide {m}

  idββ-c11-ident : ∀ (b1 b2 : ℤ ₚ) (a1' a2' w z : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) →
    (eqY : b1 + - ₁₊ a2' ≡ ₁₊ w) → (eqZ : b1 + ₁₊ a1' ≡ ₁₊ z) →
    S11k.RStepsK.idββ-c11-Goal {m} b1 b2 a1' a2' w z lm2 eqY eqZ
  idββ-c11-ident b1 b2 a1' a2' w z lm2 eqY eqZ =
    trans (refl' Lfix) (trans core (refl' (Eq.sym Rfix)))
    where
    u₁ v₁ uw vw uz vz rw rz rzy : ℤ ₚ
    u₁  = - ₁₊ a2' * ((₁₊ a1' , λ ()) ⁻¹) .proj₁
    v₁  = - ₁₊ a1' * ((₁₊ a2' , λ ()) ⁻¹) .proj₁
    uw  = - ₁₊ a2' * ((₁₊ w , λ ()) ⁻¹) .proj₁
    vw  = - ₁₊ w * ((₁₊ a2' , λ ()) ⁻¹) .proj₁
    uz  = - ₁₊ a2' * ((₁₊ z , λ ()) ⁻¹) .proj₁
    vz  = - ₁₊ z * ((₁₊ a2' , λ ()) ⁻¹) .proj₁
    rw  = ₁₊ w * ((₁₊ a1' , λ ()) ⁻¹) .proj₁
    rz  = ₁₊ z * ((₁₊ a1' , λ ()) ⁻¹) .proj₁
    rzy = ₁₊ w * ((₁₊ z , λ ()) ⁻¹) .proj₁

    qw qz qzy : ℤ* ₚ
    qw  = (₁₊ a1' , λ ()) *' ((₁₊ w , λ ()) ⁻¹)
    qz  = (₁₊ a1' , λ ()) *' ((₁₊ z , λ ()) ⁻¹)
    qzy = (₁₊ z , λ ()) *' ((₁₊ w , λ ()) ⁻¹)

    LHS' RHS' : Word (Gen (₂₊ m))
    LHS' = pad u₁ v₁ • ((ZM qw • S^ rw) • pad uw vw)
    RHS' = (ZM qz • S^ rz) • (pad uz vz • (ZM qzy • S^ rzy))

    Lfix : S11k.RStepsK.PADg {m} b1 b2 a1' a2' w z lm2 eqY eqZ •
             (S11k.RStepsK.HU1 {m} b1 b2 a1' a2' w z lm2 eqY eqZ •
              S11k.RStepsK.PADw {m} b1 b2 a1' a2' w z lm2 eqY eqZ) ≡ LHS'
    Lfix = Eq.cong₂ _•_ (padSA a1' a2' b1 b2)
      (Eq.cong₂ _•_ (hpad {₁₊ m} a1' w) Eq.refl)

    Rfix : S11k.RStepsK.HU2 {m} b1 b2 a1' a2' w z lm2 eqY eqZ •
             (S11k.RStepsK.PADz {m} b1 b2 a1' a2' w z lm2 eqY eqZ •
              S11k.RStepsK.HU3 {m} b1 b2 a1' a2' w z lm2 eqY eqZ) ≡ RHS'
    Rfix = Eq.cong₂ _•_ (hpad {₁₊ m} a1' z)
      (Eq.cong₂ _•_ Eq.refl (hpad {₁₊ m} z w))

    slL : Sl LHS' (padDual u₁ v₁ •
            ((ZM qw ↑ • S^ rw ↑) • padDual uw vw))
    slL = sl-• (sl-pad u₁ v₁)
            (sl-• (sl-• (sl-ZM qw) (sl-S^ rw)) (sl-pad uw vw))

    slR : Sl RHS' ((ZM qz ↑ • S^ rz ↑) •
            (padDual uz vz • (ZM qzy ↑ • S^ rzy ↑)))
    slR = sl-• (sl-• (sl-ZM qz) (sl-S^ rz))
            (sl-• (sl-pad uz vz)
              (sl-• (sl-ZM qzy) (sl-S^ rzy)))

    zySum : ₁₊ z ≡ ₁₊ w + (₁₊ a1' + ₁₊ a2')
    zySum = Eq.trans (S11k.Values.zSum a1' a2' w z b1 eqY eqZ)
      (Eq.trans (+-assoc (₁₊ w) (₁₊ a2') (₁₊ a1'))
        (Eq.cong (₁₊ w +_) (+-comm (₁₊ a2') (₁₊ a1'))))

    mid : padDual u₁ v₁ • ((ZM qw ↑ • S^ rw ↑) • padDual uw vw)
        ≈ (ZM qz ↑ • S^ rz ↑) •
          (padDual uz vz • (ZM qzy ↑ • S^ rzy ↑))
    mid = trans (cong (pad-norm u₁ v₁) (cong refl (pad-norm uw vw)))
          (trans (idββ a2' a1' w z zySum)
            (cright (cleft (sym (pad-norm uz vz)))))

    core : LHS' ≈ RHS'
    core = conj-eq slL slR mid
