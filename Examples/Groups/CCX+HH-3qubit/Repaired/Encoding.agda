{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.Encoding where

open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (s≤s ; z≤n)
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Core using (CGen ; cX0 ; cCX01 ; cCCX12 ; cK12 ; cCCZ ; cNK ; cH2 ; embed ; core ; gen-expand)
import Examples.Groups.CCX+HH-3qubit.Core as Core
import Examples.Groups.CCX+HH-3qubit.PrimitiveFrames as PF
import Examples.Groups.CCX+HH-3qubit.FrameWords as F
import Examples.Groups.CCX+HH-3qubit.Normalization as N
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
open import Presentation.Base _===_ hiding (_===_ ; _≈_)
open import Presentation.Properties _===_ using (by-assoc ; by-assoc-and)

x04 : Word (T.Gen 8)
x04 = T.X (zero) (suc (suc (suc (suc (zero))))) (s≤s z≤n)
x15 : Word (T.Gen 8)
x15 = T.X (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (s≤s (s≤s z≤n))
x26 : Word (T.Gen 8)
x26 = T.X (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (s≤s (s≤s (s≤s z≤n)))
x37 : Word (T.Gen 8)
x37 = T.X (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (s≤s (s≤s (s≤s (s≤s z≤n))))
x46 : Word (T.Gen 8)
x46 = T.X (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
x57 : Word (T.Gen 8)
x57 = T.X (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
tk0123 : Word (T.Gen 8)
tk0123 = T.K (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n)))
tk4567 : Word (T.Gen 8)
tk4567 = T.K (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
m7 : Word (T.Gen 8)
m7 = T.M (suc (suc (suc (suc (suc (suc (suc (zero))))))))

encode : CGen → Word (L.Genᴸ 8)
encode cX0 = L.⌊ x04 • x15 • x26 • x37 ⌋ʷ
encode cCX01 = L.⌊ x46 • x57 ⌋ʷ
encode cCCX12 = L.⌊ x37 ⌋ʷ
encode cK12 = L.⌊ tk0123 • tk4567 ⌋ʷ
encode cCCZ = L.⌊ m7 ⌋ʷ
encode cNK = L.⌊ tk0123 ⌋ʷ
encode cH2 = L.H

decode : L.Genᴸ 8 → Word Gen
decode (L.⌊ g ⌋) = F.decode g
decode L.IH = H2

primitive-back : ∀ g → (decode ʷ) (encode g) ≈ [ embed g ]ʷ
primitive-back cX0 = lift PF.backX0
primitive-back cCX01 = lift PF.backCX01
primitive-back cCCX12 = lift PF.backCCX12
primitive-back cK12 = trans
  (cong (lift PF.backNK) (lift PF.backK4567))
  (sym (axiom K-definition))
primitive-back cCCZ = lift PF.backCCZ
primitive-back cNK = lift PF.backNK
primitive-back cH2 = refl

core-back : ∀ w → (decode ʷ) ((encode ʷ) w) ≈ Core.⌞ w ⌟
core-back [ g ]ʷ = primitive-back g
core-back ε = refl
core-back (w • v) = cong (core-back w) (core-back v)

e : Gen → Word (L.Genᴸ 8)
e g = (encode ʷ) (core g)

gen-back : ∀ g → (decode ʷ) (e g) ≈ [ g ]ʷ
gen-back g = trans (core-back (core g)) (sym (lift (gen-expand g)))

-- The encoding followed by decoding is the identity modulo the
-- repaired circuit relations, proved without using matrix equality.
word-back : ∀ w → (decode ʷ) ((e ʷ) w) ≈ w
word-back [ g ]ʷ = gen-back g
word-back ε = refl
word-back (w • v) = cong (word-back w) (word-back v)

encodeᴰ : N.DGen → Word (T.Gen 8)
encodeᴰ N.dX0 = x04 • x15 • x26 • x37
encodeᴰ N.dCX01 = x46 • x57
encodeᴰ N.dCCX12 = x37
encodeᴰ N.dK12 = tk0123 • tk4567
encodeᴰ N.dCCZ = m7
encodeᴰ N.dNK = tk0123

dyadic-encoding : ∀ w → (e ʷ) (N.dyadic w) Eq.≡ L.⌊ (encodeᴰ ʷ) w ⌋ʷ
dyadic-encoding [ N.dX0 ]ʷ = Eq.refl
dyadic-encoding [ N.dCX01 ]ʷ = Eq.refl
dyadic-encoding [ N.dCCX12 ]ʷ = Eq.refl
dyadic-encoding [ N.dK12 ]ʷ = Eq.refl
dyadic-encoding [ N.dCCZ ]ʷ = Eq.refl
dyadic-encoding [ N.dNK ]ʷ = Eq.refl
dyadic-encoding ε = Eq.refl
dyadic-encoding (w • v) = Eq.cong₂ _•_ (dyadic-encoding w) (dyadic-encoding v)

dyadic-decoding : ∀ w → (decode ʷ) L.⌊ w ⌋ʷ Eq.≡ (F.decode ʷ) w
dyadic-decoding [ g ]ʷ = Eq.refl
dyadic-decoding ε = Eq.refl
dyadic-decoding (w • v) = Eq.cong₂ _•_ (dyadic-decoding w) (dyadic-decoding v)
