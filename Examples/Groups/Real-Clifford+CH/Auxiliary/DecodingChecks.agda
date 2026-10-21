------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding of Definition 8.3 on three qubits: checks that a decoded
-- letter has the matrix of the letter
--
-- D(p) is a circuit of multi-controlled gates read off the Gray codes
-- of the indices of p (Decoding, MultiControlled).  Here its matrix is
-- compared with that of p: for every sign pair and every signed
-- exchange on eight indices (`zz-all`, `zx-all`), on samples of the
-- exchange pairs, and on samples of the Hadamard pairs, on and off the
-- H-pattern and with repeated indices.  A Hadamard-free letter decodes
-- to a word in 21 atoms (DecodingChecks.Atoms), so the sign pairs and
-- signed exchanges are decided by one boolean each on products of the
-- atoms' matrices, every atom read once (DecodingChecks.Base: `okD`);
-- a Hadamard pair is read gate by gate.  Read gate by gate, the 512
-- signed exchanges took about 100 s, in eight modules; read as a dense
-- product and compared by `mat-dec`, as this module first did, a
-- decoded letter cost about 1.27ⁿ in its n gates and only the five
-- letters under 43 gates were within reach, where a Hadamard pair off
-- the H-pattern has some 1800.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks where

open import Data.Bool using (Bool ; true)
open import Data.Fin using (Fin)
open import Data.List using (List ; map)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_ ; Mat)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧ ; len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx ; xx ; hh)
open import Examples.Groups.Real-Clifford+CH.Decoding using () renaming (d to D)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.Base
  using (all8₂ ; all8₃ ; all8₂-true ; all8₃-true)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.Base
  using (⟦_⟧Y ; decideD-sound ; check ; atoms ; okD ; okD-sound)

------------------------------------------------------------------------
-- The letters checked
--
-- The Gray codes of 0 … 7, top wire first: 000, 001, 011, 010, 110,
-- 111, 101, 100.

-- The families, over the atoms' matrices and lengths.
zzP : List (Mat 3) → List ℕ → Fin 8 → Fin 8 → Bool
zzP ms ls a b = okD ms ls (zz a b)

zxP : List (Mat 3) → List ℕ → Fin 8 → Fin 8 → Fin 8 → Bool
zxP ms ls c a b = okD ms ls (zx c a b)

-- Every sign pair (−1)_[a] (−1)_[b]: boxes on every wire, and chains of
-- up to seven of them.
zz-all : ∀ a b → ⟦ (D ʷ) (zz a b) ⟧ ~ ⟦ zz a b ⟧Y
zz-all a b =
  okD-sound (zz a b) (all8₂-true (zzP (map ⟦_⟧R atoms) (map len atoms)) Eq.refl a b)

-- Every signed exchange (−1)_[c] X_[a,b]: on its own pair, in either
-- order of the pair, and with the sign elsewhere.
zx-all : ∀ c a b → ⟦ (D ʷ) (zx c a b) ⟧ ~ ⟦ zx c a b ⟧Y
zx-all c a b =
  okD-sound (zx c a b) (all8₃-true (zxP (map ⟦_⟧R atoms) (map len atoms)) Eq.refl c a b)

-- Exchange pairs X_[a,b] X_[c,d].
xx-0123 : ⟦ (D ʷ) (xx ₀ ₁ ₂ ₃) ⟧ ~ ⟦ xx ₀ ₁ ₂ ₃ ⟧Y
xx-0123 = okD-sound (xx ₀ ₁ ₂ ₃) Eq.refl

xx-0725 : ⟦ (D ʷ) (xx ₀ ₇ ₂ ₅) ⟧ ~ ⟦ xx ₀ ₇ ₂ ₅ ⟧Y
xx-0725 = okD-sound (xx ₀ ₇ ₂ ₅) Eq.refl

xx-6134 : ⟦ (D ʷ) (xx ₆ ₁ ₃ ₄) ⟧ ~ ⟦ xx ₆ ₁ ₃ ₄ ⟧Y
xx-6134 = okD-sound (xx ₆ ₁ ₃ ₄) Eq.refl

-- Hadamard pairs of the H-pattern: the all-white gate, a black
-- control, and the other order of the two varying wires.
hh-0132 : check (hh ₀ ₁ ₃ ₂) ≡ true
hh-0132 = Eq.refl

hh-7645 : check (hh ₇ ₆ ₄ ₅) ≡ true
hh-7645 = Eq.refl

hh-0312 : check (hh ₀ ₃ ₁ ₂) ≡ true
hh-0312 = Eq.refl

-- Off the H-pattern: Definition E.1's words around the gadget.
hh-0246 : check (hh ₀ ₂ ₄ ₆) ≡ true
hh-0246 = Eq.refl

hh-1527 : check (hh ₁ ₅ ₂ ₇) ≡ true
hh-1527 = Eq.refl

-- Repeated indices: the pair is split over two fresh ones.
hh-0102 : check (hh ₀ ₁ ₀ ₂) ≡ true
hh-0102 = Eq.refl

-- As a statement about the semantics.
D-hh-0132 : ⟦ (D ʷ) (hh ₀ ₁ ₃ ₂) ⟧ ~ ⟦ hh ₀ ₁ ₃ ₂ ⟧Y
D-hh-0132 = decideD-sound ((D ʷ) (hh ₀ ₁ ₃ ₂)) (hh ₀ ₁ ₃ ₂) hh-0132
