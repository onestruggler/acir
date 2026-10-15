------------------------------------------------------------------------
-- Presentations of groups
--
-- (338) and (320) on four wires, decided (Clément, Lemma D.13)
--
-- The box Λ□ 3 commutes with the H gate on wire 0 whose box wire is
-- wire 1, in each colouring of the H gate's controls on the wires 2 3
-- (`d338`); and the box is the product (320) of the triply controlled
-- rotations and the doubly controlled box with wire 3 idle, also on
-- four wires (`d320`), where (320) proper (GeneralN.Box320) starts at
-- five.  Each an evaluation of a few seconds: with completeness on four
-- wires, an equation (GeneralN.Gadget322, GeneralN.Box338).  In a module
-- of their own: Agda frees the memory of an evaluation only when its
-- module is done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base338 where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R)
open import Examples.Groups.Real-Clifford+CH.ProdEval using (allOK ; fam-eval)

-- One family over shared factors, decided by one boolean that reads each
-- once (ProdEval): the box, the H gate, the four negations of its
-- colourings (col s w is negsB s • w • negsB s), and (320)'s rotations,
-- swap and smaller box.
private
  F : List (Circuit 4)
  F = Λ□ 3 ∷ Hg 1
    ∷ negsB (true ∷ true ∷ true ∷ true ∷ []) ∷ negsB (true ∷ true ∷ true ∷ false ∷ [])
    ∷ negsB (true ∷ true ∷ false ∷ true ∷ []) ∷ negsB (true ∷ true ∷ false ∷ false ∷ [])
    ∷ (ΛZX 3 ↓ᵏ 0) ∷ Ex ↓ ∷ place 3 (Λ□ 2) ∷ (ΛXZ 3 ↓ᵏ 0) ∷ []

  box hg zx ex pl xz : Word ℕ
  box = [ 0 ]ʷ
  hg  = [ 1 ]ʷ
  zx  = [ 6 ]ʷ
  ex  = [ 7 ]ʷ
  pl  = [ 8 ]ʷ
  xz  = [ 9 ]ʷ

  -- The box against the H gate in the colouring whose negations are
  -- factor i.
  comm : ℕ → Word ℕ × Word ℕ
  comm i = box • ([ i ]ʷ • hg • [ i ]ʷ) , ([ i ]ʷ • hg • [ i ]ʷ) • box

  E : List (Word ℕ × Word ℕ)
  E = comm 2 ∷ comm 3 ∷ comm 4 ∷ comm 5
    ∷ (box , zx • (ex • zx • ex) • pl • (ex • xz • ex) • xz • (ex • zx • ex) • pl • (ex • xz • ex) • ε)
    ∷ []

  all338 : allOK (map ⟦_⟧R F) (map len F) E ≡ true
  all338 = Eq.refl

d338 : ∀ (b c : Bool) →
       Evaluated (Λ□ 3 • col (true ∷ true ∷ b ∷ c ∷ []) (Hg 1)) (col (true ∷ true ∷ b ∷ c ∷ []) (Hg 1) • Λ□ 3)
d338 true  true  = fam-eval F E all338 0
d338 true  false = fam-eval F E all338 1
d338 false true  = fam-eval F E all338 2
d338 false false = fam-eval F E all338 3

-- (320) on four wires, spelled as GeneralN.Gadget322's product of
-- letters at width 4 + 0.
W320 : Circuit 4
W320 = (ΛZX 3 ↓ᵏ 0) • (Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓) • place 3 (Λ□ 2) • (Ex ↓ • (ΛXZ 3 ↓ᵏ 0) • Ex ↓) •
       (ΛXZ 3 ↓ᵏ 0) • (Ex ↓ • (ΛZX 3 ↓ᵏ 0) • Ex ↓) • place 3 (Λ□ 2) • (Ex ↓ • (ΛXZ 3 ↓ᵏ 0) • Ex ↓) • ε

d320 : Evaluated (Λ□ 3) W320
d320 = fam-eval F E all338 4
