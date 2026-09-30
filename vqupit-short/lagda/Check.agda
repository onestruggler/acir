------------------------------------------------------------------------
-- The derivation printed in §2 (lagda/ex-reasoning.lagda.tex), restated
-- with its width pinned so that it typechecks against Prelude: the
-- printed snippet leaves the width implicit, as the library does inside
-- a module parameterised by it, which a stand-alone file cannot.
-- Typecheck from the repository root:
--   agda vqupit-short/lagda/Check.agda
------------------------------------------------------------------------

module vqupit-short.lagda.Check where

open import vqupit-short.lagda.Prelude
open import vqupit-short.lagda.ex-circuit
open import vqupit-short.lagda.ex-relation

private variable
  n : ℕ

postulate
  axiom : ∀ {w v : Word (Gen n)} → n CRel, w === v → w ≈ v

conj-Ex-H↑ : Ex {n} • H ↑ • Ex ≈ H
conj-Ex-H↑ = begin
  Ex • H ↑ • Ex    ≈⟨ sym assoc ⟩
  (Ex • H ↑) • Ex  ≈⟨ cleft axiom semi-Ex-H↑ ⟩
  (H • Ex) • Ex    ≈⟨ assoc ⟩
  H • Ex • Ex      ≈⟨ cright axiom order-Ex ⟩
  H • ε            ≈⟨ right-unit ⟩
  H ∎
