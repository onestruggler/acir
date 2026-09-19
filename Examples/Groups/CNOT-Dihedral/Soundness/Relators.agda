------------------------------------------------------------------------
-- Presentations of groups
--
-- The relators of Figure 1 and the laws of the symmetry, checked as
-- identities of stored operators
--
-- Each relation is stated at the width it is drawn on and checked
-- there, as an equation between the tables of its two sides: every
-- check is `refl`, a computation over at most sixteen inputs.  The
-- relators are named so that these checks and the soundness proof
-- cannot drift apart, and each relator padded to any width is shown,
-- also by `refl`, to be the axiom's word, so that a check at one width
-- is an axiom at every width (Interpretation.by-relator).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT-Dihedral.Soundness.Relators where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.CNOT-Dihedral.Semantics
open import Examples.Groups.CNOT-Dihedral.Syntactics
open import Examples.Groups.CNOT-Dihedral.Interpretation

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The relators, at the width each is written for

r10ˡ r10ʳ : Circuit 0
r10ˡ = ω ^ 8
r10ʳ = ε

r1ˡ r1ʳ r7ˡ r7ʳ r11ˡ r11ʳ : Circuit 1
r1ˡ  = X • X
r1ʳ  = ε
r7ˡ  = T ^ 8
r7ʳ  = ε
r11ˡ = X • T • X
r11ʳ = ω • T ^ 7

r2ˡ r2ʳ r3ˡ r3ʳ r4ˡ r4ʳ r5ˡ r5ʳ r8ˡ r8ʳ r12ˡ r12ʳ : Circuit 2
r2ˡ  = CNOT • X • CNOT
r2ʳ  = X
r3ˡ  = CNOT • X ↑ • CNOT
r3ʳ  = X ↑ • X
r4ˡ  = CNOT • CNOT
r4ʳ  = ε
r5ˡ  = SWAP
r5ʳ  = CNOT • SWAP • CNOT • SWAP • CNOT
r8ˡ  = U ^ 4
r8ʳ  = T ^ 4 • (T ↑) ^ 4
r12ˡ = CNOT • T ↑ • CNOT
r12ʳ = T ↑

soˡ soʳ sXˡ sXʳ sTˡ sTʳ : Circuit 2
soˡ = SWAP • SWAP
soʳ = ε
sXˡ = X • SWAP
sXʳ = SWAP • X ↑
sTˡ = T • SWAP
sTʳ = SWAP • T ↑

r6ˡ r6ʳ r9ˡ r9ʳ sbˡ sbʳ sCˡ sCʳ : Circuit 3
r6ˡ = CNOT₂₀
r6ʳ = CNOT • CNOT ↑ • CNOT • CNOT ↑
r9ˡ = V ^ 2
r9ʳ = T ^ 6 • (T ↑) ^ 6 • (T ↑ ↑) ^ 6 • (U ↑) ^ 2 • U₀₂ ^ 2 • U ^ 2
sbˡ = SWAP • SWAP ↑ • SWAP
sbʳ = SWAP ↑ • SWAP • SWAP ↑
sCˡ = CNOT • SWAP ↑ • SWAP
sCʳ = SWAP ↑ • SWAP • CNOT ↑

r13ˡ r13ʳ : Circuit 4
r13ˡ = CNOT ↑ ↑ • V • CNOT ↑ ↑
r13ʳ = T ^ 5 • (T ↑) ^ 5 • (T ↑ ↑) ^ 5 • (T ↑ ↑ ↑) ^ 5 •
       (U ↑ ↑) ^ 3 • U₁₃ ^ 3 • U₀₃ ^ 3 • (U ↑) ^ 3 • U₀₂ ^ 3 • U ^ 3 •
       V ↑ • V₀₂₃ • V₀₁₃ • V

------------------------------------------------------------------------
-- The identities: both sides have the same table

Same : ∀ {k} → Circuit k → Circuit k → Set
Same u v = ⟦ u ⟧M ≡ ⟦ v ⟧M

m1 : Same r1ˡ r1ʳ
m1 = Eq.refl

m2 : Same r2ˡ r2ʳ
m2 = Eq.refl

m3 : Same r3ˡ r3ʳ
m3 = Eq.refl

m4 : Same r4ˡ r4ʳ
m4 = Eq.refl

m5 : Same r5ˡ r5ʳ
m5 = Eq.refl

m6 : Same r6ˡ r6ʳ
m6 = Eq.refl

m7 : Same r7ˡ r7ʳ
m7 = Eq.refl

m8 : Same r8ˡ r8ʳ
m8 = Eq.refl

m9 : Same r9ˡ r9ʳ
m9 = Eq.refl

m10 : Same r10ˡ r10ʳ
m10 = Eq.refl

m11 : Same r11ˡ r11ʳ
m11 = Eq.refl

m12 : Same r12ˡ r12ʳ
m12 = Eq.refl

m13 : Same r13ˡ r13ʳ
m13 = Eq.refl

mso : Same soˡ soʳ
mso = Eq.refl

msb : Same sbˡ sbʳ
msb = Eq.refl

msX : Same sXˡ sXʳ
msX = Eq.refl

msT : Same sTˡ sTʳ
msT = Eq.refl

msC : Same sCˡ sCʳ
msC = Eq.refl

------------------------------------------------------------------------
-- The relators, padded to any width, are the axioms' words

p1ˡ : r1ˡ ↓ᵏ n ≡ X • X
p1ˡ = Eq.refl
p1ʳ : r1ʳ ↓ᵏ n ≡ ε {Gen (₁₊ n)}
p1ʳ = Eq.refl
p7ˡ : r7ˡ ↓ᵏ n ≡ T ^ 8
p7ˡ = Eq.refl
p11ˡ : r11ˡ ↓ᵏ n ≡ X • T • X
p11ˡ = Eq.refl
p11ʳ : r11ʳ ↓ᵏ n ≡ ω • T ^ 7
p11ʳ = Eq.refl

p2ˡ : r2ˡ ↓ᵏ n ≡ CNOT • X • CNOT
p2ˡ = Eq.refl
p2ʳ : r2ʳ ↓ᵏ n ≡ X
p2ʳ = Eq.refl
p3ˡ : r3ˡ ↓ᵏ n ≡ CNOT • X ↑ • CNOT
p3ˡ = Eq.refl
p3ʳ : r3ʳ ↓ᵏ n ≡ X ↑ • X
p3ʳ = Eq.refl
p4ˡ : r4ˡ ↓ᵏ n ≡ CNOT • CNOT
p4ˡ = Eq.refl
p4ʳ : r4ʳ ↓ᵏ n ≡ ε {Gen (₂₊ n)}
p4ʳ = Eq.refl
p5ˡ : r5ˡ ↓ᵏ n ≡ SWAP
p5ˡ = Eq.refl
p5ʳ : r5ʳ ↓ᵏ n ≡ CNOT • SWAP • CNOT • SWAP • CNOT
p5ʳ = Eq.refl
p8ˡ : r8ˡ ↓ᵏ n ≡ U ^ 4
p8ˡ = Eq.refl
p8ʳ : r8ʳ ↓ᵏ n ≡ T ^ 4 • (T ↑) ^ 4
p8ʳ = Eq.refl
p12ˡ : r12ˡ ↓ᵏ n ≡ CNOT • T ↑ • CNOT
p12ˡ = Eq.refl
p12ʳ : r12ʳ ↓ᵏ n ≡ T ↑
p12ʳ = Eq.refl

psoˡ : soˡ ↓ᵏ n ≡ SWAP • SWAP
psoˡ = Eq.refl
psXˡ : sXˡ ↓ᵏ n ≡ X • SWAP
psXˡ = Eq.refl
psXʳ : sXʳ ↓ᵏ n ≡ SWAP • X ↑
psXʳ = Eq.refl
psTˡ : sTˡ ↓ᵏ n ≡ T • SWAP
psTˡ = Eq.refl
psTʳ : sTʳ ↓ᵏ n ≡ SWAP • T ↑
psTʳ = Eq.refl

p6ˡ : r6ˡ ↓ᵏ n ≡ CNOT₂₀
p6ˡ = Eq.refl
p6ʳ : r6ʳ ↓ᵏ n ≡ CNOT • CNOT ↑ • CNOT • CNOT ↑
p6ʳ = Eq.refl
p9ˡ : r9ˡ ↓ᵏ n ≡ V ^ 2
p9ˡ = Eq.refl
p9ʳ : r9ʳ ↓ᵏ n ≡ T ^ 6 • (T ↑) ^ 6 • (T ↑ ↑) ^ 6 • (U ↑) ^ 2 • U₀₂ ^ 2 • U ^ 2
p9ʳ = Eq.refl
psbˡ : sbˡ ↓ᵏ n ≡ SWAP • SWAP ↑ • SWAP
psbˡ = Eq.refl
psbʳ : sbʳ ↓ᵏ n ≡ SWAP ↑ • SWAP • SWAP ↑
psbʳ = Eq.refl
psCˡ : sCˡ ↓ᵏ n ≡ CNOT • SWAP ↑ • SWAP
psCˡ = Eq.refl
psCʳ : sCʳ ↓ᵏ n ≡ SWAP ↑ • SWAP • CNOT ↑
psCʳ = Eq.refl

p13ˡ : r13ˡ ↓ᵏ n ≡ CNOT ↑ ↑ • V • CNOT ↑ ↑
p13ˡ = Eq.refl
p13ʳ : r13ʳ ↓ᵏ n ≡
       T ^ 5 • (T ↑) ^ 5 • (T ↑ ↑) ^ 5 • (T ↑ ↑ ↑) ^ 5 •
       (U ↑ ↑) ^ 3 • U₁₃ ^ 3 • U₀₃ ^ 3 • (U ↑) ^ 3 • U₀₂ ^ 3 • U ^ 3 •
       V ↑ • V₀₂₃ • V₀₁₃ • V
p13ʳ = Eq.refl

p10ˡ : r10ˡ ↓ᵏ n ≡ ω ^ 8
p10ˡ = Eq.refl
p10ʳ : r10ʳ ↓ᵏ n ≡ ε {Gen n}
p10ʳ = Eq.refl
