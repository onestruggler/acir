------------------------------------------------------------------------
-- Presentations of groups
--
-- The relators of Figure 4, checked as matrix identities
--
-- Each equation of Figure 4 other than the schema (19), and each swap
-- rule of Remark 1, is stated at the width it is drawn on and checked
-- there, as an identity between stored integer matrices: the two sides
-- have different numbers of letters, hence different powers of 1/√2,
-- so each side is scaled by the other's power of √2 before comparison
-- (Interpretation.by-matrix).  Every check is `refl`, a computation on
-- tries; the longest sides — (15) has eighty letters once the non-
-- adjacent gates are spelled out with their swaps — are products of
-- eighty 8 × 8 matrices, which is where this module spends its time.
--
-- The relators are named rather than inlined so that these checks and
-- the soundness proof that uses them cannot drift apart.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Soundness.Relators where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation

------------------------------------------------------------------------
-- The relators, at the width each is written for

-- (1)–(3): one wire.
r1ˡ r1ʳ r2ˡ r2ʳ r3ˡ r3ʳ : Circuit 1
r1ˡ = H • H
r1ʳ = ε
r2ˡ = Z • Z
r2ʳ = ε
r3ˡ = (H • Z) ^ 8
r3ʳ = ε

-- (4)–(7), (9)–(11), and the two-wire swap rules: two wires.
r4ˡ r4ʳ r5ˡ r5ʳ r6ˡ r6ʳ r7ˡ r7ʳ r9ˡ r9ʳ r10ˡ r10ʳ r11ˡ r11ʳ : Circuit 2
r4ˡ  = CZ • CZ
r4ʳ  = ε
r5ˡ  = CH • CH
r5ʳ  = ε
r6ˡ  = CZ • °CZ
r6ʳ  = Z ↓
r7ˡ  = CH • °CH
r7ʳ  = H ↓
r9ˡ  = CZ • Ex
r9ʳ  = Ex • CZ
r10ˡ = CH • °CZ
r10ʳ = °CZ • CH
r11ˡ = CH • H ↑ • Z ↑ • CH • H ↑
r11ʳ = H ↑ • Z ↑ • CH • H ↑ • CH

sgˡ sgʳ sZˡ sZʳ sHˡ sHʳ : Circuit 2
sgˡ = Ex • Ex
sgʳ = ε
sZˡ = Z ↑ • Ex
sZʳ = Ex • Z ↓
sHˡ = H ↑ • Ex
sHʳ = Ex • H ↓

-- (12)–(18) and the three-wire swap rules: three wires.
r12ˡ r12ʳ r13ˡ r13ʳ r14ˡ r14ʳ r15ˡ r15ʳ r16ˡ r16ʳ r17ˡ r17ʳ r18ˡ r18ʳ : Circuit 3
r12ˡ = CZ ↑ • CZ ↓
r12ʳ = CZ ↓ • CZ ↑
r13ˡ = CZ ↑ • CH ↓
r13ʳ = CH ↓ • CZ ↑
r14ˡ = CH ↓ • CZ₂₀ • CH ↓ • CZ₂₀
r14ʳ = CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓
r15ˡ = (CH ↓ • CZ₂₀) ^ 4
r15ʳ = CZ ↑
r16ˡ = °CZ₂₀ • CH ↓ • CZ₂₀ • CH ↓
r16ʳ = CH ↓ • CZ₂₀ • CH ↓ • °CZ₂₀
r17ˡ = °CZ₂₀ • CH ↓ • CH ↑ • CH ↓
r17ʳ = CH ↓ • CH ↑ • CH ↓ • °CZ₂₀
r18ˡ = CZ ↑ • PP ↓
r18ʳ = PP ↓ • CH ↑

sCZˡ sCZʳ sCHˡ sCHʳ : Circuit 3
sCZˡ = CZ ↑ • Ex ↓ • Ex ↑
sCZʳ = Ex ↓ • Ex ↑ • CZ ↓
sCHˡ = CH ↑ • Ex ↓ • Ex ↑
sCHʳ = Ex ↓ • Ex ↑ • CH ↓

------------------------------------------------------------------------
-- The identities

-- Both sides denote the same matrix over ℤ[1/√2].
Same : ∀ {k} → Circuit k → Circuit k → Set
Same u v = scaleM (√2^ len v) ⟦ u ⟧M ≡ scaleM (√2^ len u) ⟦ v ⟧M

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

m14 : Same r14ˡ r14ʳ
m14 = Eq.refl

m15 : Same r15ˡ r15ʳ
m15 = Eq.refl

m16 : Same r16ˡ r16ʳ
m16 = Eq.refl

m17 : Same r17ˡ r17ʳ
m17 = Eq.refl

m18 : Same r18ˡ r18ʳ
m18 = Eq.refl

msg : Same sgˡ sgʳ
msg = Eq.refl

msZ : Same sZˡ sZʳ
msZ = Eq.refl

msH : Same sHˡ sHʳ
msH = Eq.refl

msCZ : Same sCZˡ sCZʳ
msCZ = Eq.refl

msCH : Same sCHˡ sCHʳ
msCH = Eq.refl

------------------------------------------------------------------------
-- The relators, padded to any width, are the axioms' words
--
-- Each is an equation of words and holds by computation; it is what
-- lets Interpretation.by-relator transport a matrix identity to an
-- axiom without comparing operators.

open import Data.Nat using (ℕ)

private
  variable
    n : ℕ

p1ˡ : r1ˡ ↓ᵏ n ≡ H • H
p1ˡ = Eq.refl
p1ʳ : r1ʳ ↓ᵏ n ≡ ε {Gen (₁₊ n)}
p1ʳ = Eq.refl
p2ˡ : r2ˡ ↓ᵏ n ≡ Z • Z
p2ˡ = Eq.refl
p3ˡ : r3ˡ ↓ᵏ n ≡ (H • Z) ^ 8
p3ˡ = Eq.refl

p4ˡ : r4ˡ ↓ᵏ n ≡ CZ • CZ
p4ˡ = Eq.refl
p4ʳ : r4ʳ ↓ᵏ n ≡ ε {Gen (₂₊ n)}
p4ʳ = Eq.refl
p5ˡ : r5ˡ ↓ᵏ n ≡ CH • CH
p5ˡ = Eq.refl
p6ˡ : r6ˡ ↓ᵏ n ≡ CZ • °CZ
p6ˡ = Eq.refl
p6ʳ : r6ʳ ↓ᵏ n ≡ Z ↓
p6ʳ = Eq.refl
p7ˡ : r7ˡ ↓ᵏ n ≡ CH • °CH
p7ˡ = Eq.refl
p7ʳ : r7ʳ ↓ᵏ n ≡ H ↓
p7ʳ = Eq.refl
p9ˡ : r9ˡ ↓ᵏ n ≡ CZ • Ex
p9ˡ = Eq.refl
p9ʳ : r9ʳ ↓ᵏ n ≡ Ex • CZ
p9ʳ = Eq.refl
p10ˡ : r10ˡ ↓ᵏ n ≡ CH • °CZ
p10ˡ = Eq.refl
p10ʳ : r10ʳ ↓ᵏ n ≡ °CZ • CH
p10ʳ = Eq.refl
p11ˡ : r11ˡ ↓ᵏ n ≡ CH • H ↑ • Z ↑ • CH • H ↑
p11ˡ = Eq.refl
p11ʳ : r11ʳ ↓ᵏ n ≡ H ↑ • Z ↑ • CH • H ↑ • CH
p11ʳ = Eq.refl

psgˡ : sgˡ ↓ᵏ n ≡ Ex • Ex
psgˡ = Eq.refl
psZˡ : sZˡ ↓ᵏ n ≡ Z ↑ • Ex
psZˡ = Eq.refl
psZʳ : sZʳ ↓ᵏ n ≡ Ex • Z ↓
psZʳ = Eq.refl
psHˡ : sHˡ ↓ᵏ n ≡ H ↑ • Ex
psHˡ = Eq.refl
psHʳ : sHʳ ↓ᵏ n ≡ Ex • H ↓
psHʳ = Eq.refl

p12ˡ : r12ˡ ↓ᵏ n ≡ CZ ↑ • CZ ↓
p12ˡ = Eq.refl
p12ʳ : r12ʳ ↓ᵏ n ≡ CZ ↓ • CZ ↑
p12ʳ = Eq.refl
p13ˡ : r13ˡ ↓ᵏ n ≡ CZ ↑ • CH ↓
p13ˡ = Eq.refl
p13ʳ : r13ʳ ↓ᵏ n ≡ CH ↓ • CZ ↑
p13ʳ = Eq.refl
p14ˡ : r14ˡ ↓ᵏ n ≡ CH ↓ • CZ₂₀ • CH ↓ • CZ₂₀
p14ˡ = Eq.refl
p14ʳ : r14ʳ ↓ᵏ n ≡ CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓
p14ʳ = Eq.refl
p15ˡ : r15ˡ ↓ᵏ n ≡ (CH ↓ • CZ₂₀) ^ 4
p15ˡ = Eq.refl
p15ʳ : r15ʳ ↓ᵏ n ≡ CZ ↑
p15ʳ = Eq.refl
p16ˡ : r16ˡ ↓ᵏ n ≡ °CZ₂₀ • CH ↓ • CZ₂₀ • CH ↓
p16ˡ = Eq.refl
p16ʳ : r16ʳ ↓ᵏ n ≡ CH ↓ • CZ₂₀ • CH ↓ • °CZ₂₀
p16ʳ = Eq.refl
p17ˡ : r17ˡ ↓ᵏ n ≡ °CZ₂₀ • CH ↓ • CH ↑ • CH ↓
p17ˡ = Eq.refl
p17ʳ : r17ʳ ↓ᵏ n ≡ CH ↓ • CH ↑ • CH ↓ • °CZ₂₀
p17ʳ = Eq.refl
p18ˡ : r18ˡ ↓ᵏ n ≡ CZ ↑ • PP ↓
p18ˡ = Eq.refl
p18ʳ : r18ʳ ↓ᵏ n ≡ PP ↓ • CH ↑
p18ʳ = Eq.refl

psCZˡ : sCZˡ ↓ᵏ n ≡ CZ ↑ • Ex ↓ • Ex ↑
psCZˡ = Eq.refl
psCZʳ : sCZʳ ↓ᵏ n ≡ Ex ↓ • Ex ↑ • CZ ↓
psCZʳ = Eq.refl
psCHˡ : sCHˡ ↓ᵏ n ≡ CH ↑ • Ex ↓ • Ex ↑
psCHˡ = Eq.refl
psCHʳ : sCHʳ ↓ᵏ n ≡ Ex ↓ • Ex ↑ • CH ↓
psCHʳ = Eq.refl
