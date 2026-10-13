------------------------------------------------------------------------
-- Presentations of groups
--
-- Every CCX+HH circuit on at least four wires has auxiliary charge 00.
--
-- A gate at these widths always has a spectator.  The structural
-- encoder exhibits its two copies, and Charge.parallel-closed proves
-- that their charges cancel.  No bit-counting or determinant oracle is
-- needed, and all four starting cosets are covered.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Subgroup.CircuitCharge where

open import Data.Nat.Base using (ℕ ; _+_) renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.StructuralEncoding as E
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary
open import Examples.Groups.CCX+HH.Subgroup.Action using (Coset ; c00)
open import Examples.Groups.CCX+HH.Subgroup.Charge using (state ; parallel-closed)

copy-closed : ∀ {m n} (p : Partition m n) c w → state c (E.copy p w) ≡ c
copy-closed p = parallel-closed (left p) (right p)

gen-closed : ∀ {n} c (g : Gen (4 + n)) → state c (E.e g) ≡ c
gen-closed c (gate₀ ())
gen-closed {n} c X-gen =
  copy-closed (contiguous (2 ^ℕ (3 + n))) c (E.X-block (2 + n))
gen-closed {n} c CX-gen =
  copy-closed (contiguous (2 ^ℕ (3 + n))) c (E.CX-block (1 + n))
gen-closed {n} c HH-gen =
  copy-closed (contiguous (2 ^ℕ (3 + n))) c (E.HH-block (1 + n))
gen-closed {n} c CCX-gen =
  copy-closed (contiguous (2 ^ℕ (3 + n))) c (E.CCX-block n)
gen-closed {n} c (g ↥) =
  copy-closed (alternating (2 ^ℕ (3 + n))) c (E.e g)

image-closed : ∀ {n} c (w : Circuit (4 + n)) → state c (E.encode w) ≡ c
image-closed c [ g ]ʷ = gen-closed c g
image-closed c ε = Eq.refl
image-closed c (u • v) =
  Eq.trans (Eq.cong (λ d → state d (E.encode v)) (image-closed c u))
           (image-closed c v)
