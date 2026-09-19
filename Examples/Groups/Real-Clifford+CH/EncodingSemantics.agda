------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoding of Definition 8.2 preserves the semantics of every
-- generator, on any number n ≥ 3 of qubits
--
-- A generator is a gate on a wire (Encoding.view); its operator is the
-- form of that view (WireForms.gen-form), and the encoded word reads
-- as the same form: the sign products for Z and CZ (Diagonal) and the
-- two-level Hadamard products for H and CH (Hadamard).  This
-- discharges the hypothesis e-sem of Section8.Complete.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.EncodingSemantics where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ)

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧ ; ⟦⟧ₒ-gen)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.WireForms using (form ; gen-form)
open import Examples.Groups.Real-Clifford+CH.Encoding using (View ; one ; two ; view ; e ; E-H ; E-Z ; E-CZ ; E-CH)
open import Examples.Groups.Real-Clifford+CH.EncodingSemantics.Products using (⟦_⟧Y)
open import Examples.Groups.Real-Clifford+CH.EncodingSemantics.Strings using (view-bound₁ ; view-bound₂)
open import Examples.Groups.Real-Clifford+CH.EncodingSemantics.Diagonal using (E-Z-sem ; E-CZ-sem)
open import Examples.Groups.Real-Clifford+CH.EncodingSemantics.Hadamard using (E-H-sem ; E-CH-sem)
import Examples.Groups.Real-Clifford+CH.Section8 as Section8

private
  -- The operator of a generator is the form of its view, on the nose
  -- of the abstract reading.
  gen-view : ∀ {m} (g : Gen (₃₊ m)) (v : View (₃₊ m)) → view g ≡ v →
             ⟦ [ g ]ʷ ⟧ ~ (1 , form {n = ₂₊ m} v)
  gen-view g v eq =
    ~-reflexive {l = 1} {l' = 1} Eq.refl
      (≐-trans (⟦⟧ₒ-gen g)
        (≐-trans (gen-form g) (Eq.subst (λ v′ → form (view g) ≐ form v′) eq (≐-refl (form (view g))))))

  -- The encoded word and the generator, through the form.
  via : ∀ {m} (g : Gen (₃₊ m)) (v : View (₃₊ m)) → view g ≡ v →
        {w : _} → ⟦_⟧Y {m = m} w ~ (1 , form {n = ₂₊ m} v) → ⟦_⟧Y {m = m} w ~ ⟦ [ g ]ʷ ⟧
  via {m} g v eq {w} h =
    ~-trans {s = ⟦_⟧Y {m = m} w} {t = 1 , form {n = ₂₊ m} v} {u = ⟦ [ g ]ʷ ⟧}
      h (~-sym {s = ⟦ [ g ]ʷ ⟧} {t = 1 , form {n = ₂₊ m} v} (gen-view g v eq))

e-sem : ∀ m → Section8.E-sem m
e-sem m g with view g in eq
... | one p H-gate  = via g (one p H-gate)  eq {E-H  {m = m} p} (E-H-sem  p (view-bound₁ g eq))
... | one p Z-gate  = via g (one p Z-gate)  eq {E-Z  {m = m} p} (E-Z-sem  p (view-bound₁ g eq))
... | two p CZ-gate = via g (two p CZ-gate) eq {E-CZ {m = m} p} (E-CZ-sem p (view-bound₂ g eq))
... | two p CH-gate = via g (two p CH-gate) eq {E-CH {m = m} p} (E-CH-sem p (view-bound₂ g eq))
