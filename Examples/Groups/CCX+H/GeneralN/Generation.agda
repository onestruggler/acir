------------------------------------------------------------------------
-- Presentations of groups
--
-- Exact physical image of CCX+H at every width >= 4: precisely the
-- scaled source words whose four-state action fixes 00.  Synthesis
-- returns an ordinary circuit on the same wires, without ancillas.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; _*_) renaming (_^_ to _^ℕ_)

module Examples.Groups.CCX+H.GeneralN.Generation (n : ℕ) where

open import Data.Product.Base using (Σ ; _,_)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.GeneralN.Semantics as Sem
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as Physical
import Examples.Groups.CCX+H.GeneralN.Decoding as Decoding
import Examples.Groups.CCX+H.CircuitTranslation as Translation
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
open import Examples.Groups.CCX+H.GeneralN.Action using (c00)

width = 4 + n
k = 2 ^ℕ (3 + n)
N = k * 2
module C = Sem.At (3 + n)
module D = Decoding n
module Transfer = Translation n
module Auxiliary = Transfer.Auxiliary
private module M = S.Dim k

decode-correct : ∀ w → C.interpret ((D.d ʷ) w) ≡ M.⟦ Auxiliary.encode w ⟧ᴸ
decode-correct [ y ]ʷ = D.correct y
decode-correct ε = Eq.refl
decode-correct (u • v) = Eq.trans (Eq.cong₂ _·*·_ (decode-correct u) (decode-correct v))
  (Eq.sym (M.⟦•⟧ᴸ (Auxiliary.encode u) (Auxiliary.encode v)))

synthesize : Word (T.Genᴸ N) → H.Circuit width
synthesize w = (D.d ʷ) (Auxiliary.decode c00 w)

correct : ∀ w → Auxiliary.state c00 w ≡ c00 →
  C.interpret (synthesize w) ≡ M.⟦ w ⟧ᴸ
correct w closed = Eq.trans (decode-correct (Auxiliary.decode c00 w))
  (Auxiliary.stabilizer-generated w closed)

generated : ∀ w → Auxiliary.state c00 w ≡ c00 →
  Σ (H.Circuit width) (λ c → C.interpret c ≡ M.⟦ w ⟧ᴸ)
generated w closed = synthesize w , correct w closed

necessary : ∀ w (c : H.Circuit width) → C.interpret c ≡ M.⟦ w ⟧ᴸ →
  Auxiliary.state c00 w ≡ c00
necessary w c eq = Eq.trans
  (Eq.sym (Auxiliary.state-semantic c00
    {u = Auxiliary.encode (Transfer.encode c)} {v = w}
    (Eq.trans (Transfer.encoding-correct c) eq)))
  (Auxiliary.encode-closed (Transfer.encode c))

private
  dimension : 2 ^ℕ width ≡ N
  dimension = NP.*-comm 2 k

physical-correct : ∀ w → Auxiliary.state c00 w ≡ c00 →
  Physical.interpret (synthesize w) ≡
    Physical.cast-matrix (Eq.sym dimension) M.⟦ w ⟧ᴸ
physical-correct w closed = Eq.trans (Eq.sym (Physical.At.correct (3 + n) (synthesize w)))
  (Eq.cong (Physical.cast-matrix (Eq.sym dimension)) (correct w closed))

physical-necessary : ∀ w (c : H.Circuit width) →
  Physical.interpret c ≡ Physical.cast-matrix (Eq.sym dimension) M.⟦ w ⟧ᴸ →
  Auxiliary.state c00 w ≡ c00
physical-necessary w c eq = necessary w c
  (Physical.cast-injective (Eq.sym dimension)
    (Eq.trans (Physical.At.correct (3 + n) c) eq))
