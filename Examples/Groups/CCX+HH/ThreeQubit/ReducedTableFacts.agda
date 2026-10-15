------------------------------------------------------------------------
-- Presentations of groups
--
-- Traversing a finite-table edge twice returns its initial coset; the
-- two stabilizer factors cancel.  Both facts follow from the already
-- proved Table 1 factorizations, separation, and gate involutions.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.ReducedTableFacts where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Presentation.GroupLike as GL
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Derived {8} as Source
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.ThreeQubit.Presentation as Full
import Examples.Groups.CCX+HH.ThreeQubit.Compact.Presentation as Base
open import Examples.Groups.CCX+HH.ThreeQubit.Cosets using (rep)
open import Examples.Groups.CCX+HH.ThreeQubit.Factorizations using (factor)
open import Examples.Groups.CCX+HH.ThreeQubit.Separation using (separate)
open import Examples.Groups.CCX+HH.ThreeQubit.Involutions using (source-involution)
open import Examples.Groups.CCX+HH.ThreeQubit.ReducedTableData using (next ; emitted)
open Full.Theory using (encode ; base)

private
  module A = PB (T._===_ {8})
  module AP = PP (T._===_ {8})
  module G = GL.Group-Lemmas (T._===_ {8}) Source.grouplike
  open import Relation.Binary.Reasoning.Setoid AP.word-setoid

  twice : ∀ c g →
    (base (emitted c g • emitted (next c g) g) • encode (rep (next (next c g) g))) A.≈
    encode (rep c)
  twice c g = begin
    (base (emitted c g) • base (emitted (next c g) g)) •
      encode (rep (next (next c g) g)) ≈⟨ A.assoc ⟩
    base (emitted c g) •
      (base (emitted (next c g) g) • encode (rep (next (next c g) g)))
      ≈⟨ A.cong A.refl (A.sym (factor (next c g) g)) ⟩
    base (emitted c g) • (encode (rep (next c g)) • E.e g)
      ≈⟨ A.sym A.assoc ⟩
    (base (emitted c g) • encode (rep (next c g))) • E.e g
      ≈⟨ A.cong (A.sym (factor c g)) A.refl ⟩
    (encode (rep c) • E.e g) • E.e g ≈⟨ A.assoc ⟩
    encode (rep c) • (E.e g • E.e g)
      ≈⟨ A.cong A.refl (source-involution g) ⟩
    encode (rep c) • ε ≈⟨ A.right-unit ⟩
    encode (rep c) ∎

next-involutive : ∀ c g → next (next c g) g ≡ c
next-involutive c g = separate (next (next c g) g) c
  (emitted c g • emitted (next c g) g) ε
  (A.trans (twice c g) (A.sym A.left-unit))

factor-inverse : ∀ c g →
  (emitted c g • emitted (next c g) g) Base.≈ ε
factor-inverse c g = Base.encode-injective (G.•-cancelʳ
  (A.trans
    (A.cong A.refl (A.refl' (Eq.cong (λ q → encode (rep q))
      (Eq.sym (next-involutive c g)))))
    (A.trans (twice c g) (A.sym A.left-unit))))
