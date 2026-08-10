------------------------------------------------------------------------
-- Presentations of groups
--
-- Working inside the Clifford extension presentation _Clifford,_===_.
--
-- Three things are set up here, all needed to run Selinger's Figure 8
-- backwards through the translation g (Selinger.Inverse):
--
--   * the scalar vanishes.  At p = 2 the simplified relator M-power at
--     exponent 0 reads ε = M₋₁ on the nose, so [ M₋₁ ]ᵣ ≈ ε — and hence
--     H² ≈ ε — with no work.  This was the lemma the earlier version of
--     Qubit.Selinger.Iso assumed.
--
--   * the shift.  ⇑ moves a word of the extension presentation up one
--     qubit (Pauli generators by shift-gen, gates by _↥).  It carries
--     the congruence with it: the Pauli axioms land in the right factor
--     of the n-fold product, the conjugation axioms hold because a
--     shifted gate ignores the new wire 0, and a twisted relator shifts
--     to the twisted relator of cong↑ — whose correction is, by
--     definition of corr, the shift of the correction.
--
--   * the Pauli generators are their gate words.  Z = S² is the twisted
--     relator for order-S read backwards; X = H Z H follows by
--     conjugating with H and cancelling H²; the higher wires come from
--     the shift.  This is g-left-inv-gen on the Pauli generators.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Selinger.Extension where

open import Data.Nat using (ℕ ; zero)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _ʷ ; wmap)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Presentation.Construct.Base
  using (_⋄_⋄_ ; _∪_ ; [_]ₗ ; [_]ᵣ ; ConjRelʷ ; _⊕^_)
open import Presentation.Construct.Properties.Extension using (tw)

open import ForStdlib.Data.Fin.Mod.Prime.Two
  using (p-2 ; p-prime ; g* ; g-gen)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; gate₁ ; H-gate ; _↥ ; _↑ ; S ; H)

import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (X ; Z)

open import Examples.Groups.ProjectivePauli.Presentation p-2 p-prime using (Γ-H)

open import Examples.Groups.ProjectiveClifford.Qubit.Presentation
  using (PauliGen ; _Clifford,_===_ ; conj ; corr ; shift-gen ; shiftPauli)

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations
  using (_QRel,_===_ ; M₋₁ ; order-S ; order-H ; M-power)
  renaming (srel to ssrel ; cong↑ to scong↑)

open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Translation
  using (pauliGen→word ; Pw ; X-gen ; Z-gen)
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.PauliVec
  using (P-X ; P-Z ; Z₀≡ ; PView ; vX ; vZ ; v↑ ; pview)
open import Examples.Groups.ProjectiveClifford.Qubit.Selinger.PauliSide
  using (conj-H-Z ; conj-shift ; pauli-shift-ax)

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- The three axiom families, as one-liners

-- A twisted symplectic relator.
twist : {u v : Word (Gen n)} (r̄ : (n QRel,_===_) u v) →
        PB._≈_ (n Clifford,_===_) [ u ]ᵣ ([ corr r̄ ]ₗ • [ v ]ᵣ)
twist r̄ = PB.axiom (_⋄_⋄_.mid (_∪_.right (tw r̄)))

-- Moving a gate rightwards past a Pauli generator.
conj-ax : (y : PauliGen n) (x : Gen n) →
          PB._≈_ (n Clifford,_===_)
                 ([ [ x ]ʷ ]ᵣ • [ [ y ]ʷ ]ₗ) ([ conj x y ]ₗ • [ [ x ]ʷ ]ᵣ)
conj-ax y x = PB.axiom (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm y x)))

-- The Pauli congruence, along the left embedding.
lefts : {u v : Word (PauliGen n)} →
        PB._≈_ (Γ-H ⊕^ n) u v →
        PB._≈_ (n Clifford,_===_) [ u ]ₗ [ v ]ₗ
lefts PB.refl         = PB.refl
lefts (PB.sym h)      = PB.sym (lefts h)
lefts (PB.trans h h₁) = PB.trans (lefts h) (lefts h₁)
lefts (PB.cong h h₁)  = PB.cong (lefts h) (lefts h₁)
lefts PB.assoc        = PB.assoc
lefts PB.left-unit    = PB.left-unit
lefts PB.right-unit   = PB.right-unit
lefts (PB.axiom x)    = PB.axiom (_⋄_⋄_.left x)

------------------------------------------------------------------------
-- The scalar vanishes
--
-- At p = 2 the group ℤ*₂ is trivial, so M-power at exponent ₀ reads
-- ε = M 1 = M₋₁, with no correction.  H² = M₋₁ (order-H) then collapses.

M≈ε : PB._≈_ ((₁₊ m) Clifford,_===_) [ M₋₁ {m} ]ᵣ ε
M≈ε = PB.sym (PB.trans (twist (ssrel (M-power ₀))) PB.left-unit)

H²≈ε : PB._≈_ ((₁₊ m) Clifford,_===_) [ H ^ 2 ]ᵣ ε
H²≈ε = PB.trans (twist (ssrel order-H)) (PB.trans PB.left-unit M≈ε)

------------------------------------------------------------------------
-- The wire-0 Pauli generators are their gate words

-- Z = S²: exactly the twisted relator for order-S, whose correction Z₀
-- is the one nontrivial entry of corr.
Z-gen-eq : PB._≈_ ((₁₊ m) Clifford,_===_) [ inj₁ (Z-gen {m}) ]ʷ [ Z {m} ]ᵣ
Z-gen-eq {m} =
  PB.sym (PB.trans (twist (ssrel order-S))
           (PB.trans PB.right-unit
                     (PB.refl' _ (Eq.cong (λ □ → [ □ ]ₗ) (Z₀≡ {m})))))

-- X = H Z H: conjugate Z by H (conj H Z-gen is the X generator) and
-- cancel the leftover H².
X-gen-eq : PB._≈_ ((₁₊ m) Clifford,_===_) [ inj₁ (X-gen {m}) ]ʷ [ X {m} ]ᵣ
X-gen-eq {m} = sym chain
  where
  open PB ((₁₊ m) Clifford,_===_)
  open PP ((₁₊ m) Clifford,_===_) using (word-setoid)
  open SR word-setoid

  chain : [ X {m} ]ᵣ ≈ [ inj₁ (X-gen {m}) ]ʷ
  chain = begin
    [ H ]ᵣ • ([ Z ]ᵣ • [ H ]ᵣ)
      ≈⟨ cright (cleft (sym (Z-gen-eq {m}))) ⟩
    [ H ]ᵣ • ([ inj₁ (Z-gen {m}) ]ʷ • [ H ]ᵣ)
      ≈⟨ sym assoc ⟩
    ([ H ]ᵣ • [ inj₁ (Z-gen {m}) ]ʷ) • [ H ]ᵣ
      ≈⟨ cleft (conj-ax (Z-gen {m}) (gate₁ H-gate)) ⟩
    ([ conj (gate₁ H-gate) (Z-gen {m}) ]ₗ • [ H ]ᵣ) • [ H ]ᵣ
      ≈⟨ cleft (cleft (lefts (conj-H-Z {m}))) ⟩
    ([ inj₁ (X-gen {m}) ]ʷ • [ H ]ᵣ) • [ H ]ᵣ
      ≈⟨ assoc ⟩
    [ inj₁ (X-gen {m}) ]ʷ • [ H ^ 2 ]ᵣ
      ≈⟨ cright (H²≈ε {m}) ⟩
    [ inj₁ (X-gen {m}) ]ʷ • ε
      ≈⟨ right-unit ⟩
    [ inj₁ (X-gen {m}) ]ʷ
      ∎

------------------------------------------------------------------------
-- Shifting a word of the extension presentation up one qubit

shift-sum : PauliGen n ⊎ Gen n → PauliGen (₁₊ n) ⊎ Gen (₁₊ n)
shift-sum (inj₁ y)  = inj₁ (shift-gen y)
shift-sum (inj₂ gg) = inj₂ (gg ↥)

⇑ : Word (PauliGen n ⊎ Gen n) → Word (PauliGen (₁₊ n) ⊎ Gen (₁₊ n))
⇑ = wmap shift-sum

⇑ᵣ : (w : Word (Gen n)) → ⇑ [ w ]ᵣ ≡ [ w ↑ ]ᵣ
⇑ᵣ [ x ]ʷ  = Eq.refl
⇑ᵣ ε       = Eq.refl
⇑ᵣ (u • v) = Eq.cong₂ _•_ (⇑ᵣ u) (⇑ᵣ v)

⇑ₗ : (u : Word (PauliGen n)) → ⇑ [ u ]ₗ ≡ [ shiftPauli u ]ₗ
⇑ₗ [ y ]ʷ  = Eq.refl
⇑ₗ ε       = Eq.refl
⇑ₗ (u • v) = Eq.cong₂ _•_ (⇑ₗ u) (⇑ₗ v)

-- Each axiom family survives the shift.
shift-ax : {u v : Word (PauliGen n ⊎ Gen n)} → (n Clifford,_===_) u v →
           PB._≈_ ((₁₊ n) Clifford,_===_) (⇑ u) (⇑ v)
shift-ax (_⋄_⋄_.left {u} {v} x) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (⇑ₗ u)) (Eq.sym (⇑ₗ v))
            (PB.axiom (_⋄_⋄_.left (pauli-shift-ax x)))
shift-ax (_⋄_⋄_.right ())
shift-ax {zero}  (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm () x)))
shift-ax {₁₊ k} (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm y x))) =
  PB.trans (conj-ax (inj₂ y) (x ↥))
           (PB.cong (PB.trans (lefts (conj-shift x y))
                              (PB.refl' _ (Eq.sym (⇑ₗ (conj x y)))))
                    PB.refl)
shift-ax (_⋄_⋄_.mid (_∪_.right (tw {u} {v} r̄))) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (⇑ᵣ u))
            (Eq.sym (Eq.cong₂ _•_ (⇑ₗ (corr r̄)) (⇑ᵣ v)))
            (twist (scong↑ r̄))

-- Hence so does the congruence.
lemma-shift : {u v : Word (PauliGen n ⊎ Gen n)} →
              PB._≈_ (n Clifford,_===_) u v →
              PB._≈_ ((₁₊ n) Clifford,_===_) (⇑ u) (⇑ v)
lemma-shift PB.refl         = PB.refl
lemma-shift (PB.sym h)      = PB.sym (lemma-shift h)
lemma-shift (PB.trans h h₁) = PB.trans (lemma-shift h) (lemma-shift h₁)
lemma-shift (PB.cong h h₁)  = PB.cong (lemma-shift h) (lemma-shift h₁)
lemma-shift PB.assoc        = PB.assoc
lemma-shift PB.left-unit    = PB.left-unit
lemma-shift PB.right-unit   = PB.right-unit
lemma-shift (PB.axiom x)    = shift-ax x

------------------------------------------------------------------------
-- Every Pauli generator equals its gate word

pauli-eq : (y : PauliGen (₁₊ m)) →
           PB._≈_ ((₁₊ m) Clifford,_===_)
                  [ inj₁ y ]ʷ [ pauliGen→word y ]ᵣ
pauli-eq {m} y with pview {m} y
... | vX =
  PB.trans (X-gen-eq {m}) (PB.refl' _ (Eq.cong (λ □ → [ □ ]ᵣ) (Eq.sym (P-X {m}))))
... | vZ =
  PB.trans (Z-gen-eq {m}) (PB.refl' _ (Eq.cong (λ □ → [ □ ]ᵣ) (Eq.sym (P-Z {m}))))
... | v↑ y' =
  Eq.subst (λ □ → PB._≈_ _ [ inj₁ (inj₂ y') ]ʷ □)
           (⇑ᵣ (pauliGen→word y')) (lemma-shift (pauli-eq y'))

-- … and so does every Pauli word.
pauli-eq-word : (u : Word (PauliGen (₁₊ m))) →
                PB._≈_ ((₁₊ m) Clifford,_===_) [ u ]ₗ [ Pw u ]ᵣ
pauli-eq-word [ y ]ʷ  = pauli-eq y
pauli-eq-word ε       = PB.refl
pauli-eq-word (u • v) = PB.cong (pauli-eq-word u) (pauli-eq-word v)
