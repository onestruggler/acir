------------------------------------------------------------------------
-- Presentations of groups
--
-- g-well-defined: Selinger's Figure 8, modulo the global scalar, holds
-- inside the Clifford extension presentation.
--
-- This is the converse direction of Qubit.Selinger.Conjugation /
-- .Relators: every axiom C2-C15 has to be derived from the simplified
-- symplectic relators (through their twisted forms) together with the
-- Pauli relations.  How each one goes:
--
--   C2  H² = 1          — order-H says H² = M₋₁, and the scalar is ε;
--   C3  S⁴ = 1          — S² is the Pauli Z (order-S's correction), so
--                         S⁴ is Z², killed by the Pauli order relation;
--   C4  (SH)³ = 1       — (SH)³ is M₋₁ up to bracketing;
--   C5  CZ² = 1         — order-CZ;
--   C6, C7              — comm-CZ-S↓ / comm-CZ-S↑;
--   C8, C9              — pure Pauli content: X and Z are Pauli
--                         generators (Selinger.Extension), so both sides
--                         reduce by the conjugation axiom for CZ and the
--                         Pauli identities of Selinger.PauliSide;
--   C10, C11            — the simplified selinger-c10 / c11 after one
--                         transposition of CZ with S on the other wire;
--   C12-C15             — verbatim;
--   cong↑, comm₁, comm₂ — the shift of Selinger.Extension and the
--                         shared structural rules.
--
-- Also here: g-left-inv-gen, which on a Pauli generator is exactly
-- Extension.pauli-eq and on a gate generator is refl.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.Inverse where

open import Data.Nat using (ℕ ; zero)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _ʷ)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Presentation.Construct.Base using ([_]ₗ ; [_]ᵣ)

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot
  using (p-2 ; p-prime ; g* ; g-gen)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; gate₂ ; CZ-gate ; S ; H ; CZ ; _↑)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z ; SH ; _CRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; _Clifford,_===_ ; conj)

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations
  using ( _QRel,_===_ ; order-CZ ; comm-CZ-S↓ ; comm-CZ-S↑
        ; selinger-c10 ; selinger-c11 ; selinger-c12 ; selinger-c13
        ; selinger-c14 ; selinger-c15)
  renaming (srel to ssrel ; comm₁ to scomm₁ ; comm₂ to scomm₂)

open import Examples.Groups.Clifford.Qubit.Selinger.Translation
  using (f ; g ; gʷ≡ᵣ ; pauliGen→word ; X-gen ; Z-gen)
open import Examples.Groups.Clifford.Qubit.Selinger.PauliVec using (P-X ; P-Z)
open import Examples.Groups.Clifford.Qubit.Selinger.PauliSide
  using (Z-order ; c8-pauli ; c9-pauli ; comm-Z₀-X₁)
open import Examples.Groups.Clifford.Qubit.Selinger.Extension
  using ( twist ; conj-ax ; lefts ; M≈ε ; H²≈ε ; Z-gen-eq ; X-gen-eq
        ; ⇑ ; ⇑ᵣ ; lemma-shift ; pauli-eq)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- The wire-1 Pauli generators, as gate words

X↑-eq : PB._≈_ ((₂₊ m) Clifford,_===_)
               [ inj₁ (inj₂ (X-gen {m})) ]ʷ [ X {m} ↑ ]ᵣ
X↑-eq {m} =
  PB.trans (pauli-eq {₁₊ m} (inj₂ (X-gen {m})))
           (PB.refl' _ (Eq.cong (λ □ → [ □ ↑ ]ᵣ) (P-X {m})))

Z↑-eq : PB._≈_ ((₂₊ m) Clifford,_===_)
               [ inj₁ (inj₂ (Z-gen {m})) ]ʷ [ Z {m} ↑ ]ᵣ
Z↑-eq {m} =
  PB.trans (pauli-eq {₁₊ m} (inj₂ (Z-gen {m})))
           (PB.refl' _ (Eq.cong (λ □ → [ □ ↑ ]ᵣ) (P-Z {m})))

------------------------------------------------------------------------
-- The one-qubit axioms

module One (m : ℕ) where

  private Γ = (₁₊ m) Clifford,_===_
  open PB Γ
  open PP Γ using (by-assoc ; word-setoid)
  open SR word-setoid

  -- C2: H² = M₋₁ = ε.
  c2 : [ H ^ 2 ]ᵣ ≈ ε
  c2 = H²≈ε

  -- C3: S⁴ = Z² = ε.  S² is the Pauli Z on wire 0.
  c3 : [ S ^ 4 ]ᵣ ≈ ε
  c3 = begin
    [ S ^ 4 ]ᵣ
      ≈⟨ by-assoc auto ⟩
    [ Z {m} ]ᵣ • [ Z {m} ]ᵣ
      ≈⟨ cong (sym (Z-gen-eq {m})) (sym (Z-gen-eq {m})) ⟩
    [ inj₁ (Z-gen {m}) ]ʷ • [ inj₁ (Z-gen {m}) ]ʷ
      ≈⟨ lefts (Z-order {m}) ⟩
    ε
      ∎

  -- C4: (SH)³ is M₋₁, up to bracketing.
  c4 : [ SH ^ 3 ]ᵣ ≈ ε
  c4 = trans (by-assoc auto) (M≈ε {m})

------------------------------------------------------------------------
-- The two-qubit axioms

module Two (m : ℕ) where

  private Γ = (₂₊ m) Clifford,_===_
  open PB Γ
  open PP Γ using (by-assoc ; word-setoid)
  open SR word-setoid

  private CZg = gate₂ {n = m} CZ-gate

  c5 : [ CZ ^ 2 ]ᵣ ≈ ε
  c5 = trans (twist (ssrel order-CZ)) left-unit

  -- CZ commutes with S on either wire.
  cz-s : ([ CZ ]ᵣ • [ S ]ᵣ) ≈ ([ S ]ᵣ • [ CZ ]ᵣ)
  cz-s = trans (twist (ssrel comm-CZ-S↓)) left-unit

  cz-s↑ : ([ CZ ]ᵣ • [ S ↑ ]ᵣ) ≈ ([ S ↑ ]ᵣ • [ CZ ]ᵣ)
  cz-s↑ = trans (twist (ssrel comm-CZ-S↑)) left-unit

  c6 : ([ S ]ᵣ • [ CZ ]ᵣ) ≈ ([ CZ ]ᵣ • [ S ]ᵣ)
  c6 = sym cz-s

  c7 : ([ S ↑ ]ᵣ • [ CZ ]ᵣ) ≈ ([ CZ ]ᵣ • [ S ↑ ]ᵣ)
  c7 = sym cz-s↑

  -- C8: CZ X₀ CZ = X₀ Z₁, entirely inside the Pauli part.
  c8 : ([ X {₁₊ m} ]ᵣ • [ CZ ]ᵣ)
       ≈ ([ CZ ]ᵣ • ([ X {₁₊ m} ]ᵣ • [ Z {m} ↑ ]ᵣ))
  c8 = begin
    [ X {₁₊ m} ]ᵣ • [ CZ ]ᵣ
      ≈⟨ cleft (sym (X-gen-eq {₁₊ m})) ⟩
    [ inj₁ (X-gen {₁₊ m}) ]ʷ • [ CZ ]ᵣ
      ≈⟨ cleft (sym (lefts (c8-pauli {m}))) ⟩
    ([ conj CZg (X-gen {₁₊ m}) ]ₗ • [ conj CZg (inj₂ (Z-gen {m})) ]ₗ)
      • [ CZ ]ᵣ
      ≈⟨ assoc ⟩
    [ conj CZg (X-gen {₁₊ m}) ]ₗ
      • ([ conj CZg (inj₂ (Z-gen {m})) ]ₗ • [ CZ ]ᵣ)
      ≈⟨ cright (sym (conj-ax (inj₂ (Z-gen {m})) CZg)) ⟩
    [ conj CZg (X-gen {₁₊ m}) ]ₗ
      • ([ CZ ]ᵣ • [ inj₁ (inj₂ (Z-gen {m})) ]ʷ)
      ≈⟨ sym assoc ⟩
    ([ conj CZg (X-gen {₁₊ m}) ]ₗ • [ CZ ]ᵣ)
      • [ inj₁ (inj₂ (Z-gen {m})) ]ʷ
      ≈⟨ cleft (sym (conj-ax (X-gen {₁₊ m}) CZg)) ⟩
    ([ CZ ]ᵣ • [ inj₁ (X-gen {₁₊ m}) ]ʷ) • [ inj₁ (inj₂ (Z-gen {m})) ]ʷ
      ≈⟨ assoc ⟩
    [ CZ ]ᵣ • ([ inj₁ (X-gen {₁₊ m}) ]ʷ • [ inj₁ (inj₂ (Z-gen {m})) ]ʷ)
      ≈⟨ cright (cong (X-gen-eq {₁₊ m}) (Z↑-eq {m})) ⟩
    [ CZ ]ᵣ • ([ X {₁₊ m} ]ᵣ • [ Z {m} ↑ ]ᵣ)
      ∎

  -- C9: the mirror image, CZ X₁ CZ = X₁ Z₀.  The chain is unchanged up
  -- to its last two steps: conj-CZ-X↑ produces the Pauli pair as Z₀·X₁,
  -- and C9's right-hand side now lists them the other way round, so the
  -- two are swapped on the Pauli side (comm-Z₀-X₁ — disjoint wires)
  -- before being read back as gate words.
  c9 : ([ X {m} ↑ ]ᵣ • [ CZ ]ᵣ)
       ≈ ([ CZ ]ᵣ • ([ X {m} ↑ ]ᵣ • [ Z {₁₊ m} ]ᵣ))
  c9 = begin
    [ X {m} ↑ ]ᵣ • [ CZ ]ᵣ
      ≈⟨ cleft (sym (X↑-eq {m})) ⟩
    [ inj₁ (inj₂ (X-gen {m})) ]ʷ • [ CZ ]ᵣ
      ≈⟨ cleft (sym (lefts (c9-pauli {m}))) ⟩
    ([ conj CZg (Z-gen {₁₊ m}) ]ₗ • [ conj CZg (inj₂ (X-gen {m})) ]ₗ)
      • [ CZ ]ᵣ
      ≈⟨ assoc ⟩
    [ conj CZg (Z-gen {₁₊ m}) ]ₗ
      • ([ conj CZg (inj₂ (X-gen {m})) ]ₗ • [ CZ ]ᵣ)
      ≈⟨ cright (sym (conj-ax (inj₂ (X-gen {m})) CZg)) ⟩
    [ conj CZg (Z-gen {₁₊ m}) ]ₗ
      • ([ CZ ]ᵣ • [ inj₁ (inj₂ (X-gen {m})) ]ʷ)
      ≈⟨ sym assoc ⟩
    ([ conj CZg (Z-gen {₁₊ m}) ]ₗ • [ CZ ]ᵣ)
      • [ inj₁ (inj₂ (X-gen {m})) ]ʷ
      ≈⟨ cleft (sym (conj-ax (Z-gen {₁₊ m}) CZg)) ⟩
    ([ CZ ]ᵣ • [ inj₁ (Z-gen {₁₊ m}) ]ʷ) • [ inj₁ (inj₂ (X-gen {m})) ]ʷ
      ≈⟨ assoc ⟩
    [ CZ ]ᵣ • ([ inj₁ (Z-gen {₁₊ m}) ]ʷ • [ inj₁ (inj₂ (X-gen {m})) ]ʷ)
      ≈⟨ cright (lefts (comm-Z₀-X₁ {m})) ⟩
    [ CZ ]ᵣ • ([ inj₁ (inj₂ (X-gen {m})) ]ʷ • [ inj₁ (Z-gen {₁₊ m}) ]ʷ)
      ≈⟨ cright (cong (X↑-eq {m}) (Z-gen-eq {₁₊ m})) ⟩
    [ CZ ]ᵣ • ([ X {m} ↑ ]ᵣ • [ Z {₁₊ m} ]ᵣ)
      ∎

  -- C10 and C11: the simplified relators, then one CZ/S transposition.
  c10 : [ CZ • H ↑ • CZ ]ᵣ ≈ [ SH ↑ • CZ • (S • H • S) ↑ • S ]ᵣ
  c10 = trans (trans (twist (ssrel selinger-c10)) left-unit) shuffle
    where
    shuffle : [ S ↑ • H ↑ • S ↑ • CZ • H ↑ • S ↑ • S ]ᵣ
              ≈ [ SH ↑ • CZ • (S • H • S) ↑ • S ]ᵣ
    shuffle = begin
      [ S ↑ • H ↑ • S ↑ • CZ • H ↑ • S ↑ • S ]ᵣ
        ≈⟨ by-assoc auto ⟩
      ([ S ↑ ]ᵣ • [ H ↑ ]ᵣ)
        • (([ S ↑ ]ᵣ • [ CZ ]ᵣ) • ([ H ↑ ]ᵣ • ([ S ↑ ]ᵣ • [ S ]ᵣ)))
        ≈⟨ cright (cleft (sym cz-s↑)) ⟩
      ([ S ↑ ]ᵣ • [ H ↑ ]ᵣ)
        • (([ CZ ]ᵣ • [ S ↑ ]ᵣ) • ([ H ↑ ]ᵣ • ([ S ↑ ]ᵣ • [ S ]ᵣ)))
        ≈⟨ by-assoc auto ⟩
      [ SH ↑ • CZ • (S • H • S) ↑ • S ]ᵣ
        ∎

  c11 : [ CZ • H • CZ ]ᵣ ≈ [ SH • CZ • (S • H • S) • S ↑ ]ᵣ
  c11 = trans (trans (twist (ssrel selinger-c11)) left-unit) shuffle
    where
    shuffle : [ S • H • S • CZ • H • S • S ↑ ]ᵣ
              ≈ [ SH • CZ • (S • H • S) • S ↑ ]ᵣ
    shuffle = begin
      [ S • H • S • CZ • H • S • S ↑ ]ᵣ
        ≈⟨ by-assoc auto ⟩
      ([ S ]ᵣ • [ H ]ᵣ)
        • (([ S ]ᵣ • [ CZ ]ᵣ) • ([ H ]ᵣ • ([ S ]ᵣ • [ S ↑ ]ᵣ)))
        ≈⟨ cright (cleft (sym cz-s)) ⟩
      ([ S ]ᵣ • [ H ]ᵣ)
        • (([ CZ ]ᵣ • [ S ]ᵣ) • ([ H ]ᵣ • ([ S ]ᵣ • [ S ↑ ]ᵣ)))
        ≈⟨ by-assoc auto ⟩
      [ SH • CZ • (S • H • S) • S ↑ ]ᵣ
        ∎

------------------------------------------------------------------------
-- Every Figure-8 axiom, translated

g-wd-ax : {u t : Word (Gen n)} → (n CRel,_===_) u t →
          PB._≈_ (n Clifford,_===_) [ u ]ᵣ [ t ]ᵣ
g-wd-ax (srel MS.c2)  = One.c2 _
g-wd-ax (srel MS.c3)  = One.c3 _
g-wd-ax (srel MS.c4)  = One.c4 _
g-wd-ax (srel MS.c5)  = Two.c5 _
g-wd-ax (srel MS.c6)  = Two.c6 _
g-wd-ax (srel MS.c7)  = Two.c7 _
g-wd-ax (srel MS.c8)  = Two.c8 _
g-wd-ax (srel MS.c9)  = Two.c9 _
g-wd-ax (srel MS.c10) = Two.c10 _
g-wd-ax (srel MS.c11) = Two.c11 _
g-wd-ax (srel MS.c12) =
  PB.trans (twist (ssrel selinger-c12)) PB.left-unit
g-wd-ax (srel MS.c13) =
  PB.trans (twist (ssrel selinger-c13)) PB.left-unit
g-wd-ax (srel MS.c14) =
  PB.trans (twist (ssrel selinger-c14)) PB.left-unit
g-wd-ax (srel MS.c15) =
  PB.trans (twist (ssrel selinger-c15)) PB.left-unit
g-wd-ax (cong↑ {w = u} {v = t} r) =
  Eq.subst₂ (PB._≈_ _) (⇑ᵣ u) (⇑ᵣ t) (lemma-shift (g-wd-ax r))
g-wd-ax (comm₁ h gg) =
  PB.trans (twist (scomm₁ h gg)) PB.left-unit
g-wd-ax (comm₂ h gg) =
  PB.trans (twist (scomm₂ h gg)) PB.left-unit

------------------------------------------------------------------------
-- g-well-defined and g-left-inv-gen, as Qubit.Selinger.Iso asks

g-well-defined : {u t : Word (Gen n)} → (n CRel,_===_) u t →
                 PB._≈_ (n Clifford,_===_) ((g ʷ) u) ((g ʷ) t)
g-well-defined {n} {u} {t} ax =
  Eq.subst₂ (PB._≈_ (n Clifford,_===_))
            (Eq.sym (gʷ≡ᵣ u)) (Eq.sym (gʷ≡ᵣ t)) (g-wd-ax ax)

g-left-inv-gen : (x : PauliGen n ⊎ Gen n) →
                 PB._≈_ (n Clifford,_===_) [ x ]ʷ ((g ʷ) (f x))
g-left-inv-gen {₁₊ m} (inj₁ y) =
  Eq.subst (λ □ → PB._≈_ _ [ inj₁ y ]ʷ □)
           (Eq.sym (gʷ≡ᵣ (pauliGen→word y))) (pauli-eq {m} y)
g-left-inv-gen (inj₂ gg) = PB.refl
