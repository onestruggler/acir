------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-wire evaluations over the box and the triply controlled
-- rotations, decided by one boolean (Clément, Lemma D.13)
--
-- Ten families, each once a module of its own (Base322 … Base38,
-- Base338Eq, BaseRotMerge's four-wire pair), are one ProdEval family
-- here, so that the gates they share — the box Λ□ 3, the rotations
-- ΛZX 3 and ΛXZ 3, the H gates — are read once in all: reading them was
-- nearly all of each module's time (ΛZX 3 about a second, read in nine
-- of them, twice in some).
--
-- (322) `d322`, `d322b`: FourQubit.PForms' Aᴾ α β true on four wires
-- (`AᴾF`, β true resp. false) against the placed box (`P322`) — the base
-- of GeneralN.Gadget322.
--
-- (335) `d335`: the box Λ□ 3 commutes with each colouring of itself
-- whose bit on the box wire is true; the other colourings follow by X
-- on the box wire (GeneralN/BoxComm).
--
-- (336) `d336`: the box commutes with each colouring of the box on wire
-- 1 controlled by wire 0 and the wires 2 3 whose bit on wire 1 is true;
-- the others by X on wire 1 (GeneralN/BoxComm).
--
-- (337) `d337r b c`: the triply controlled ZX of the box's (320), on
-- wire 0 (b true) or on wire 1 (b false), against the triply controlled
-- ZX of the H gate's, on wire 0 (c true) or on wire 1 (c false), between
-- P ⊗ P on the wires 0 1 and white on wire 2 — the rotation pairs of
-- GeneralN.Box337 on the bottom four wires.
--
-- (338) `d338`: the box commutes with the H gate on wire 0 whose box
-- wire is wire 1, in each colouring of the H gate's controls on the
-- wires 2 3; and `d320`: the box is the product (320) of the triply
-- controlled rotations and the doubly controlled box with wire 3 idle,
-- on four wires, where (320) proper (GeneralN.Box320) starts at five
-- (GeneralN.Gadget322, GeneralN.Box338).
--
-- (339) `d339 a`: the statement C339 on four wires, the box's control on
-- wire 3 of either colour.  `d339r a b c`: the triply controlled ZX of
-- the box's (320), on wire 0 (b true) or on wire 1 (b false) and
-- coloured a on wire 3, against the triply controlled ZX of the H
-- gate's, on wire 1 (c true) or wire 0 (c false) between P ⊗ P on the
-- wires 1 3 and white on wire 2 — the pairs of GeneralN.Box339 on the
-- bottom four wires.
--
-- (354) `e-333`, `e-334`: (333) and (334) on four wires, the rotations
-- as words in the H gate (H on wire 0, box wire 1) and the box on wire
-- 2 — the base of the width induction of GeneralN.ZX354.
--
-- (38) for GeneralN.Canon38: c is the CH from wire 2 onto wire 3 and Q
-- the negations of the wires 2 3.  The letters of (320) on the wires
-- 0–3 — the triply controlled ZX and XZ on wire 0 and on wire 1 — pass
-- c once coloured white on the wires 2 3 (`e-ZX`, `e-XZ`, `e-Kb`,
-- `e-Kb′`); c with its control negated is the CH from wire 3 onto wire
-- 1, white, under the swaps of the wires 2 3 and 1 2 (`e-°c`); and c is
-- the CH from wire 2 onto wire 0 under the transposition of the wires
-- 0 3 (`e-pc`).
--
-- (338) with x = y, `d-base`, `d-zx`, `d-kb`: CCZX between P ⊗ P
-- against the box and two rotations under the swap of the wires 0 1
-- around X on wire 2 (GeneralN.Box338Eq).
--
-- The merges of the rotations on four wires, `e-zx3`, `e-xz3`
-- (GeneralN.RotMerge; the smaller ones are in BaseRotMerge).
--
-- Each is, with completeness on four wires, an equation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base4 where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Nat using (ℕ ; _+_ ; _*_)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R)
open import Examples.Groups.Real-Clifford+CH.ProdEval using (allOK ; fam-eval)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; B₁ ; Hg ; Hg₃ ; P₁₃ ; Vb ; bot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)

------------------------------------------------------------------------
-- The circuits the statements name

-- (322): X on wire 3, resp. wire 1, around w when the colour is false;
-- FourQubit.PForms' Aᴾ α β true on four wires, and the placed box.
N3F N1F : Bool → Circuit 4 → Circuit 4
N3F true  w = w
N3F false w = X ↑ ↑ ↑ • w • X ↑ ↑ ↑
N1F true  w = w
N1F false w = X ↑ • w • X ↑

AᴾF : Bool → Bool → Circuit 4
AᴾF α β = PP ↓ • N3F α (N1F β (ΛZX 3 ↓ᵏ 0)) • PP ↓

P322 : Bool → Bool → Circuit 4
P322 v γ = place 3 (col (bot v γ []) (Vb v 0))

-- (337): the triply controlled ZX on wire 0 (true) or on wire 1
-- (false), and the H gate's, between P ⊗ P on the wires 0 1 and white
-- on wire 2.
U₄ : Bool → Circuit 4
U₄ true  = ΛZX 3
U₄ false = Ex ↓ • ΛZX 3 • Ex ↓

G2 : Bool → Circuit 4
G2 c = X ↑ ↑ • (PP ↓ • U₄ c • PP ↓) • X ↑ ↑

-- (320) on four wires, spelled as GeneralN.Gadget322's product of
-- letters at width 4 + 0.
W320 : Circuit 4
W320 = (ΛZX 3 ↓ᵏ 0) • (Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓) • place 3 (Λ□ 2) • (Ex ↓ • (ΛXZ 3 ↓ᵏ 0) • Ex ↓) •
       (ΛXZ 3 ↓ᵏ 0) • (Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓) • place 3 (Λ□ 2) • (Ex ↓ • (ΛXZ 3 ↓ᵏ 0) • Ex ↓) • ε

-- (339): the triply controlled ZX on wire 0 (true) or on wire 1
-- (false); the box's rotation, coloured a on wire 3, and the H gate's,
-- under the swap of the wires 0 1, between P ⊗ P on the wires 1 3 and
-- white on wire 2.
L₄ : Bool → Circuit 4
L₄ true  = ΛZX 3 ↓ᵏ 0
L₄ false = Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓

G1r : Bool → Bool → Circuit 4
G1r a b = N3F a (L₄ b)

G2r : Bool → Circuit 4
G2r c = X ↑ ↑ • (P₁₃ • (Ex ↓ • L₄ c • Ex ↓) • P₁₃) • X ↑ ↑

-- (354): the box on wire 2 at width 4.
K₄ : Circuit 4
K₄ = Ex ↑ • (Ex ↓ • Λ□ 3 • Ex ↓) • Ex ↑

-- (38): the CH from wire 2 onto wire 3, and the negations of the wires
-- 2 3.
c₄ Q₄ : Circuit 4
c₄ = (Ex • CH • Ex) ↑ ↑
Q₄ = X ↑ ↑ • X ↑ ↑ ↑

-- (338) with x = y: CCZX between P ⊗ P, and the swap of the wires 0 1
-- around X on wire 2 around w.
RW₄ : Circuit 4
RW₄ = PP ↓ • CCZX • PP ↓

SN : Circuit 4 → Circuit 4
SN w = Ex ↓ • (X ↑ ↑ • w • X ↑ ↑) • Ex ↓

Dw₄ L-zx L-kb : Circuit 4
Dw₄  = SN (Λ□ 3)
L-zx = SN (ΛZX 3 ↓ᵏ 0)
L-kb = SN (Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓)

------------------------------------------------------------------------
-- The family
--
-- A factor that a statement spells `w ↓ᵏ 0` is w's: the two are the
-- same word once each gate is re-indexed; and `Xat 3` is X ↑ ↑ ↑.

private
  -- The factors, then the sixteen negations negsB (a ∷ b ∷ c ∷ d ∷ [])
  -- in binary order (only those used are read).
  F : List (Circuit 4)
  F = Λ□ 3 ∷ Hg 1 ∷ Hg₃ 0 ∷ B₁ 1 ∷ ΛZX 3 ∷ ΛXZ 3 ∷ place 3 (Λ□ 2)
    ∷ Ex ↓ ∷ Ex ↑ ∷ Ex ∷ Ex ↑ ↑ ∷ X ↑ ↑ ∷ X ↑ ↑ ↑ ∷ PP ↓ ∷ P₁₃
    ∷ c₄ ∷ Q₄ ∷ (Ex ↑ • °CH • Ex ↑) ↑ ∷ CH
    ∷ negsB (false ∷ false ∷ false ∷ false ∷ []) ∷ negsB (false ∷ false ∷ false ∷ true ∷ [])
    ∷ negsB (false ∷ false ∷ true ∷ false ∷ []) ∷ negsB (false ∷ false ∷ true ∷ true ∷ [])
    ∷ negsB (false ∷ true ∷ false ∷ false ∷ []) ∷ negsB (false ∷ true ∷ false ∷ true ∷ [])
    ∷ negsB (false ∷ true ∷ true ∷ false ∷ []) ∷ negsB (false ∷ true ∷ true ∷ true ∷ [])
    ∷ negsB (true ∷ false ∷ false ∷ false ∷ []) ∷ negsB (true ∷ false ∷ false ∷ true ∷ [])
    ∷ negsB (true ∷ false ∷ true ∷ false ∷ []) ∷ negsB (true ∷ false ∷ true ∷ true ∷ [])
    ∷ negsB (true ∷ true ∷ false ∷ false ∷ []) ∷ negsB (true ∷ true ∷ false ∷ true ∷ [])
    ∷ negsB (true ∷ true ∷ true ∷ false ∷ []) ∷ negsB (true ∷ true ∷ true ∷ true ∷ [])
    ∷ X ↑ ∷ P322 true true ∷ P322 true false ∷ P322 false true ∷ P322 false false
    ∷ CCZX ∷ placeAt 3 (ΛZX 2) ∷ placeAt 3 (ΛXZ 2)
    ∷ []

  box hg hg3 b1 zx xz pl exd exu ex ex2 x2 x3 ppd p13 c4 q4 chw ch : Word ℕ
  box = [ 0 ]ʷ
  hg  = [ 1 ]ʷ
  hg3 = [ 2 ]ʷ
  b1  = [ 3 ]ʷ
  zx  = [ 4 ]ʷ
  xz  = [ 5 ]ʷ
  pl  = [ 6 ]ʷ
  exd = [ 7 ]ʷ
  exu = [ 8 ]ʷ
  ex  = [ 9 ]ʷ
  ex2 = [ 10 ]ʷ
  x2  = [ 11 ]ʷ
  x3  = [ 12 ]ʷ
  ppd = [ 13 ]ʷ
  p13 = [ 14 ]ʷ
  c4  = [ 15 ]ʷ
  q4  = [ 16 ]ʷ
  chw = [ 17 ]ʷ
  ch  = [ 18 ]ʷ

  bit : Bool → ℕ
  bit true  = 1
  bit false = 0

  -- negsB (a ∷ b ∷ c ∷ d ∷ []).
  ng : Bool → Bool → Bool → Bool → Word ℕ
  ng a b c d = [ 19 + (8 * bit a + (4 * bit b + (2 * bit c + bit d))) ]ʷ

  comm : Word ℕ → Word ℕ → Word ℕ × Word ℕ
  comm a b = a • b , b • a

  -- (335) and (336): the box against a colouring of the box, of B₁ 1.
  c335 : Bool → Bool → Bool → Word ℕ × Word ℕ
  c335 r₀ r₁ r₂ = comm box (ng true r₀ r₁ r₂ • box • ng true r₀ r₁ r₂)

  c336 : Bool → Bool → Bool → Word ℕ × Word ℕ
  c336 a r₀ r₁ = comm box (ng a true r₀ r₁ • b1 • ng a true r₀ r₁)

  -- (337): U₄ and G2.
  u₄ g₂ : Bool → Word ℕ
  u₄ true  = zx
  u₄ false = exd • zx • exd
  g₂ c = x2 • (ppd • u₄ c • ppd) • x2

  -- (338): the box against a colouring of the H gate.
  c338 : Bool → Bool → Word ℕ × Word ℕ
  c338 b c = comm box (ng true true b c • hg • ng true true b c)

  -- (339): L₄, G1r and G2r.
  l₄ : Bool → Word ℕ
  l₄ true  = zx
  l₄ false = exd • zx • exd

  g1r : Bool → Bool → Word ℕ
  g1r true  b = l₄ b
  g1r false b = x3 • l₄ b • x3

  g2r : Bool → Word ℕ
  g2r c = x2 • (p13 • (exd • l₄ c • exd) • p13) • x2

  c339 : Bool → Word ℕ × Word ℕ
  c339 a = comm (ng true true true a • box • ng true true true a) (ng true true false true • hg3 • ng true true false true)

  -- (354): K₄.
  k₄ : Word ℕ
  k₄ = exu • (exd • box • exd) • exu

  -- (322): AᴾF, and P322.
  x1 ccz pzx pxz : Word ℕ
  x1  = [ 35 ]ʷ
  ccz = [ 40 ]ʷ
  pzx = [ 41 ]ʷ
  pxz = [ 42 ]ʷ

  n3f n1f : Bool → Word ℕ → Word ℕ
  n3f true  w = w
  n3f false w = x3 • w • x3
  n1f true  w = w
  n1f false w = x1 • w • x1

  aᴾ : Bool → Bool → Word ℕ
  aᴾ α β = ppd • n3f α (n1f β zx) • ppd

  p322 : Bool → Bool → Word ℕ
  p322 true  true  = [ 36 ]ʷ
  p322 true  false = [ 37 ]ʷ
  p322 false true  = [ 38 ]ʷ
  p322 false false = [ 39 ]ʷ

  c322 : Bool → Bool → Bool → Bool → Word ℕ × Word ℕ
  c322 β α γ v = comm (aᴾ α β) (p322 v γ)

  -- (338) with x = y: SN.
  sn : Word ℕ → Word ℕ
  sn w = exd • (x2 • w • x2) • exd

  -- (38): c₄ against a gate between the two Q₄.
  c38 : Word ℕ → Word ℕ × Word ℕ
  c38 g = c4 • (q4 • g • q4) , (q4 • g • q4) • c4

  E : List (Word ℕ × Word ℕ)
  E = -- (335), 0 … 7
      c335 true true true ∷ c335 true true false ∷ c335 true false true ∷ c335 true false false
    ∷ c335 false true true ∷ c335 false true false ∷ c335 false false true ∷ c335 false false false
      -- (336), 8 … 15
    ∷ c336 true true true ∷ c336 true true false ∷ c336 true false true ∷ c336 true false false
    ∷ c336 false true true ∷ c336 false true false ∷ c336 false false true ∷ c336 false false false
      -- (337), 16 … 19
    ∷ comm (u₄ true) (g₂ true) ∷ comm (u₄ true) (g₂ false)
    ∷ comm (u₄ false) (g₂ true) ∷ comm (u₄ false) (g₂ false)
      -- (338), 20 … 24
    ∷ c338 true true ∷ c338 true false ∷ c338 false true ∷ c338 false false
    ∷ (box , zx • (exd • zx • exd) • pl • (exd • xz • exd) • xz • (exd • zx • exd) • pl • (exd • xz • exd) • ε)
      -- (339), 25 … 34
    ∷ c339 true ∷ c339 false
    ∷ comm (g1r true true) (g2r true) ∷ comm (g1r true true) (g2r false)
    ∷ comm (g1r true false) (g2r true) ∷ comm (g1r true false) (g2r false)
    ∷ comm (g1r false true) (g2r true) ∷ comm (g1r false true) (g2r false)
    ∷ comm (g1r false false) (g2r true) ∷ comm (g1r false false) (g2r false)
      -- (354), 35 36
    ∷ (hg • k₄ • hg • k₄ , zx)
    ∷ (k₄ • hg • k₄ • hg , xz)
      -- (38), 37 … 42
    ∷ c38 zx ∷ c38 xz ∷ c38 (ex • zx • ex) ∷ c38 (ex • xz • ex)
    ∷ (x2 • c4 • x2 , (ex2 • exu) • chw • (exu • ex2))
    ∷ ((ex • (exu • (ex2 • (exu • ex)))) • (exu • ch • exu) • ((((ex • exu) • ex2) • exu) • ex) , c4)
      -- (322), 43 … 50, and with β false, 51 … 58
    ∷ c322 true true true true ∷ c322 true true true false ∷ c322 true true false true ∷ c322 true true false false
    ∷ c322 true false true true ∷ c322 true false true false ∷ c322 true false false true ∷ c322 true false false false
    ∷ c322 false true true true ∷ c322 false true true false ∷ c322 false true false true ∷ c322 false true false false
    ∷ c322 false false true true ∷ c322 false false true false ∷ c322 false false false true ∷ c322 false false false false
      -- (338) with x = y, 59 … 61
    ∷ comm (ppd • ccz • ppd) (sn box) ∷ comm (ppd • ccz • ppd) (sn zx) ∷ comm (ppd • ccz • ppd) (sn (exd • zx • exd))
      -- the merges, 62 63
    ∷ ((x3 • zx • x3) • zx , pzx) ∷ ((x3 • xz • x3) • xz , pxz)
    ∷ []

  all4 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all4 = Eq.refl

------------------------------------------------------------------------
-- The statements

d335 : ∀ (r : Bits 3) → Evaluated (Λ□ 3 • col (true ∷ r) (Λ□ 3)) (col (true ∷ r) (Λ□ 3) • Λ□ 3)
d335 (true ∷ true ∷ true ∷ [])    = fam-eval F E all4 0
d335 (true ∷ true ∷ false ∷ [])   = fam-eval F E all4 1
d335 (true ∷ false ∷ true ∷ [])   = fam-eval F E all4 2
d335 (true ∷ false ∷ false ∷ [])  = fam-eval F E all4 3
d335 (false ∷ true ∷ true ∷ [])   = fam-eval F E all4 4
d335 (false ∷ true ∷ false ∷ [])  = fam-eval F E all4 5
d335 (false ∷ false ∷ true ∷ [])  = fam-eval F E all4 6
d335 (false ∷ false ∷ false ∷ []) = fam-eval F E all4 7

d336 : ∀ (a : Bool) (r : Bits 2) → Evaluated (Λ□ 3 • col (a ∷ true ∷ r) (B₁ 1)) (col (a ∷ true ∷ r) (B₁ 1) • Λ□ 3)
d336 true (true ∷ true ∷ [])    = fam-eval F E all4 8
d336 true (true ∷ false ∷ [])   = fam-eval F E all4 9
d336 true (false ∷ true ∷ [])   = fam-eval F E all4 10
d336 true (false ∷ false ∷ [])  = fam-eval F E all4 11
d336 false (true ∷ true ∷ [])   = fam-eval F E all4 12
d336 false (true ∷ false ∷ [])  = fam-eval F E all4 13
d336 false (false ∷ true ∷ [])  = fam-eval F E all4 14
d336 false (false ∷ false ∷ []) = fam-eval F E all4 15

d337r : ∀ (b c : Bool) → Evaluated (U₄ b • G2 c) (G2 c • U₄ b)
d337r true  true  = fam-eval F E all4 16
d337r true  false = fam-eval F E all4 17
d337r false true  = fam-eval F E all4 18
d337r false false = fam-eval F E all4 19

d338 : ∀ (b c : Bool) →
       Evaluated (Λ□ 3 • col (true ∷ true ∷ b ∷ c ∷ []) (Hg 1)) (col (true ∷ true ∷ b ∷ c ∷ []) (Hg 1) • Λ□ 3)
d338 true  true  = fam-eval F E all4 20
d338 true  false = fam-eval F E all4 21
d338 false true  = fam-eval F E all4 22
d338 false false = fam-eval F E all4 23

d320 : Evaluated (Λ□ 3) W320
d320 = fam-eval F E all4 24

d339 : ∀ (a : Bool) →
       Evaluated (col (true ∷ true ∷ true ∷ a ∷ []) (Λ□ 3) • col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0))
                 (col (true ∷ true ∷ false ∷ true ∷ []) (Hg₃ 0) • col (true ∷ true ∷ true ∷ a ∷ []) (Λ□ 3))
d339 true  = fam-eval F E all4 25
d339 false = fam-eval F E all4 26

d339r : ∀ (a b c : Bool) → Evaluated (G1r a b • G2r c) (G2r c • G1r a b)
d339r true  true  true  = fam-eval F E all4 27
d339r true  true  false = fam-eval F E all4 28
d339r true  false true  = fam-eval F E all4 29
d339r true  false false = fam-eval F E all4 30
d339r false true  true  = fam-eval F E all4 31
d339r false true  false = fam-eval F E all4 32
d339r false false true  = fam-eval F E all4 33
d339r false false false = fam-eval F E all4 34

e-333 : Evaluated {4} (Hg 1 • K₄ • Hg 1 • K₄) (ΛZX 3)
e-333 = fam-eval F E all4 35

e-334 : Evaluated {4} (K₄ • Hg 1 • K₄ • Hg 1) (ΛXZ 3)
e-334 = fam-eval F E all4 36

e-ZX : Evaluated {4} (c₄ • (Q₄ • ΛZX 3 • Q₄)) ((Q₄ • ΛZX 3 • Q₄) • c₄)
e-ZX = fam-eval F E all4 37

e-XZ : Evaluated {4} (c₄ • (Q₄ • ΛXZ 3 • Q₄)) ((Q₄ • ΛXZ 3 • Q₄) • c₄)
e-XZ = fam-eval F E all4 38

e-Kb : Evaluated {4} (c₄ • (Q₄ • (Ex • ΛZX 3 • Ex) • Q₄)) ((Q₄ • (Ex • ΛZX 3 • Ex) • Q₄) • c₄)
e-Kb = fam-eval F E all4 39

e-Kb′ : Evaluated {4} (c₄ • (Q₄ • (Ex • ΛXZ 3 • Ex) • Q₄)) ((Q₄ • (Ex • ΛXZ 3 • Ex) • Q₄) • c₄)
e-Kb′ = fam-eval F E all4 40

e-°c : Evaluated {4} (X ↑ ↑ • c₄ • X ↑ ↑) ((Ex ↑ ↑ • Ex ↑) • (Ex ↑ • °CH • Ex ↑) ↑ • (Ex ↑ • Ex ↑ ↑))
e-°c = fam-eval F E all4 41

e-pc : Evaluated {4} ((Ex • (Ex ↑ • (Ex ↑ ↑ • (Ex ↑ • Ex)))) • (Ex ↑ • CH • Ex ↑) • ((((Ex • Ex ↑) • Ex ↑ ↑) • Ex ↑) • Ex)) c₄
e-pc = fam-eval F E all4 42

d322 : ∀ (α γ v : Bool) → Evaluated (AᴾF α true • P322 v γ) (P322 v γ • AᴾF α true)
d322 true  true  true  = fam-eval F E all4 43
d322 true  true  false = fam-eval F E all4 44
d322 true  false true  = fam-eval F E all4 45
d322 true  false false = fam-eval F E all4 46
d322 false true  true  = fam-eval F E all4 47
d322 false true  false = fam-eval F E all4 48
d322 false false true  = fam-eval F E all4 49
d322 false false false = fam-eval F E all4 50

d322b : ∀ (α γ v : Bool) → Evaluated (AᴾF α false • P322 v γ) (P322 v γ • AᴾF α false)
d322b true  true  true  = fam-eval F E all4 51
d322b true  true  false = fam-eval F E all4 52
d322b true  false true  = fam-eval F E all4 53
d322b true  false false = fam-eval F E all4 54
d322b false true  true  = fam-eval F E all4 55
d322b false true  false = fam-eval F E all4 56
d322b false false true  = fam-eval F E all4 57
d322b false false false = fam-eval F E all4 58

d-base : Evaluated (RW₄ • Dw₄) (Dw₄ • RW₄)
d-base = fam-eval F E all4 59

d-zx : Evaluated (RW₄ • L-zx) (L-zx • RW₄)
d-zx = fam-eval F E all4 60

d-kb : Evaluated (RW₄ • L-kb) (L-kb • RW₄)
d-kb = fam-eval F E all4 61

e-zx3 : Evaluated {4} ((Xat 3 • ΛZX 3 • Xat 3) • ΛZX 3) (placeAt 3 (ΛZX 2))
e-zx3 = fam-eval F E all4 62

e-xz3 : Evaluated {4} ((Xat 3 • ΛXZ 3 • Xat 3) • ΛXZ 3) (placeAt 3 (ΛXZ 2))
e-xz3 = fam-eval F E all4 63
