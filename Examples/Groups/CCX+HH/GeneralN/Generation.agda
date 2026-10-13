------------------------------------------------------------------------
-- Presentations of groups
--
-- The physical image is exactly the charge-00 subgroup at every width
-- at least four.  A closed two-level word is synthesized into an actual
-- circuit, and equality with any actual circuit forces charge 00.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _^_)

module Examples.Groups.CCX+HH.GeneralN.Generation (n : ℕ) where

open import Data.Product.Base using (Σ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red
import Examples.Groups.CCX+HH.CircuitTranslation as Translation
import Examples.Groups.CCX+HH.GeneralN.Decoding as Decoding
open import Examples.Groups.CCX+HH.Subgroup.Action using (c00)
open import Examples.Groups.CCX+HH.Subgroup.CircuitCharge using (image-closed)

width = 4 + n
N = 2 ^ width
module D = Decoding n
module Transfer = Translation n
module Auxiliary = Transfer.Auxiliary
private module P = PB (T._===_ {N})

decode-correct : ∀ w → E.encode ((D.d ʷ) w) P.≈ Auxiliary.encode w
decode-correct [ y ]ʷ = D.source-correct y
decode-correct ε = P.refl
decode-correct (u • v) = P.cong (decode-correct u) (decode-correct v)

synthesize : Word (T.Gen N) → H.Circuit width
synthesize w = (D.d ʷ) (Auxiliary.decode c00 w)

source-correct : ∀ w → Auxiliary.state c00 w ≡ c00 →
  E.encode (synthesize w) P.≈ w
source-correct w closed = P.trans (decode-correct (Auxiliary.decode c00 w))
  (Auxiliary.decode-loop closed)

correct : ∀ w → Auxiliary.state c00 w ≡ c00 →
  Q.interpret (synthesize w) ≡ A.⟦ w ⟧ᵐ
correct w closed = Eq.trans (Eq.sym (Q.encoding-correct (synthesize w)))
  (Red.sound-act (source-correct w closed) A.𝕀)

generated : ∀ w → Auxiliary.state c00 w ≡ c00 →
  Σ (H.Circuit width) (λ c → Q.interpret c ≡ A.⟦ w ⟧ᵐ)
generated w closed = synthesize w , correct w closed

necessary : ∀ w (c : H.Circuit width) → Q.interpret c ≡ A.⟦ w ⟧ᵐ →
  Auxiliary.state c00 w ≡ c00
necessary w c eq = Eq.trans
  (Eq.sym (Auxiliary.state-semantic c00 {u = E.encode c} {v = w}
    (Eq.trans (Q.encoding-correct c) eq)))
  (image-closed c00 c)
