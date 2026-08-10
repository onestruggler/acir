------------------------------------------------------------------------
-- This is the Agda code accompanying the qupit paper.
--
-- Drivation of box relations from axioms.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Nat.Primality

module Examples.Groups.Symplectic.Lemmas.BoxRelations (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec

open import Relation.Binary.PropositionalEquality using (_≢_)

import Presentation.Base as PB
open import Word.Base as WB

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic

open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
import Examples.Groups.Symplectic.BR.One.A p-2 p-prime 0 as OA
import Examples.Groups.Symplectic.BR.One.E p-2 p-prime 0 as OE
import Examples.Groups.Symplectic.BR.Two.L-CZ p-2 p-prime as TLCZ
import Examples.Groups.Symplectic.BR.Two.B p-2 p-prime as TB
import Examples.Groups.Symplectic.BR.Two.D p-2 p-prime as TD
import Examples.Groups.Symplectic.BR.Three.BB-CZ p-2 p-prime as TBB
open TBB using (_⇣)
import Examples.Groups.Symplectic.BR.Three.B-CZ p-2 p-prime as TBCZ
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as TDD


------------------------------------------------------------------------
-- One qupit box relations
------------------------------------------------------------------------
module One where

  open PB (₁ QRel,_===_)

  -- Pushing H through an A box.
  A←H : ∀ (x : A) → let (dir , x') = OA.dir-and-A'-of x H-gen tt in

    [ x ]ᵃ • H ≈ dir • [ x' ]ᵃ

  A←H x = OA.lemma-single-qupit-br-A x H-gen tt

  -- Pushing S through an A box.
  A←S : ∀ (x : A) → let (dir , x') = OA.dir-and-A'-of x S-gen tt in

    [ x ]ᵃ • S ≈ dir • [ x' ]ᵃ

  A←S x = OA.lemma-single-qupit-br-A x S-gen tt

  -- Pushing S through an E box.
  E←S : ∀ (b : ℤ ₚ) →

    [ b ]ᵉ • S ≈ [ b + - ₁ ]ᵉ

  E←S = OE.lemma-single-qupit-br-E


------------------------------------------------------------------------
-- Two qupit box relations
------------------------------------------------------------------------
module Two where

  open PB (₂ QRel,_===_)

  -- Pushing CZ through an L box.
  L←CZ : ∀ (l : L 2) →
    let dir = TLCZ.dir-of l in
    let l' = TLCZ.l'-of l in

    [ l ]ˡ • CZ ≈ dir • [ l' ]ˡ

  L←CZ = TLCZ.lemma-dir-and-l'


  -- Pushing H ↑ , S ↑ , S  through an B box.
  B←H↑-S↑-S : ∀ (b : B) (g : Gen 2) (neqH : g ≢ H-gen) (neqCZ : g ≢ CZ-gen) →
    let
    dir = TB.dir-of b g neqH neqCZ
    b' = TB.b'-of b g neqH neqCZ
    in

    [ b ]ᵇ • [ g ]ʷ ≈ dir • [ b' ]ᵇ
    
  B←H↑-S↑-S = TB.lemma-B-br


  -- Pushing H  , S ↑ , S  , CZ through an D box.
  D←H-S↑-S-CZ : ∀ (d : D) (g : Gen 2) (neq : g ≢ H-gen ↥) →
    let
    (e , dir) = TD.dir-of d g neq
    d'        = TD.d'-of d g neq
    in

    [ d ]ᵈ • [ g ]ʷ ≈ S^ e  • dir ↑ • [ d' ]ᵈ

  D←H-S↑-S-CZ = TD.lemma-D-br


------------------------------------------------------------------------
-- Three qupit box relations
------------------------------------------------------------------------
module Three where

  open PB (₃ QRel,_===_)

  -- Pushing CZ ↑ through an BB box.
  BB←CZ↑ : ∀ (vb : Vec B 2) →
    let
    dir = TBB.dir-of vb
    vb' = TBB.vb'-of vb
    in

    [ vb ]ᵛᵇ • CZ ↑ ≈ dir ⇣ • [ vb' ]ᵛᵇ

  BB←CZ↑ = TBB.lemma-dir-and-vb'

  -- Pushing CZ through an B ↑ box.
  B↑←CZ : ∀ (b : B) →
    let
    dir = TBCZ.dir-of b
    in

    [ b ]ᵇ ↑ • CZ ≈ dir • [ b ]ᵇ ↑

  B↑←CZ = TBCZ.lemma-dir-and-b'-cz


  -- Pushing CZ through an DD box.
  DD←CZ : ∀ (vd : Vec D 2) →
    let
    dir = TDD.dir-of vd
    vd' = TDD.vd'-of vd
    in

    [ vd ]ᵛᵈ • CZ ≈ dir ↑ • [ vd' ]ᵛᵈ

  DD←CZ = TDD.lemma-dir-and-vd'

