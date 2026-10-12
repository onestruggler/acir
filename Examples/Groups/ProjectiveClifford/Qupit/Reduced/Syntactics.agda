{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The reduced qupit Clifford rules: the paper's Figure 1, as Paper-V1
-- states it, less semi-MR, order-Ex, yang-baxter and cz-slide.
--
-- None of the four is needed.  semi-MR is a consequence of the other
-- four one-wire rules (Paper-V1.Lemmas.SemiMR), and order-Ex of those
-- four and the other six two-wire rules (Paper-V1.Lemmas.OrderEx);
-- neither derivation uses the other rule, nor any three-wire one.
-- yang-baxter and cz-slide follow from all of those and semi-CX↑-CZ↓,
-- the one three-wire rule kept (Paper-V0.Lemmas.ThreeWire, reached
-- through Paper-V1.Lemmas.V0Rules).  So dropping all four changes
-- nothing: Iso proves these eleven rules isomorphic to Paper-V1's
-- fifteen, by the identity on words, and Presentation that they present
-- the same group.
--
-- The generator layer and the derived words are Paper-V1's, re-exported
-- rather than restated, so that a word here is literally a word there
-- and the identity is well-typed in both directions.  Only the relation
-- is new.
------------------------------------------------------------------------

open import Data.Product using (_,_ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Circuit.Base
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Reduced.Syntactics
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- Everything of Paper-V1's except its relation: the gates, the words
-- over them, and ½.
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen as Paper-V1
open Paper-V1 public
  hiding (module Clifford-Relations ; module Lemmas-Clifford)

module Clifford-Relations where

  private variable
    n : ℕ

  open Paper-V1.Clifford-Relations public
    using ( Z ; X ; Z⁻¹ ; X⁻¹ ; Z^ ; X^ ; R ; R^ ; SHS' ; SHS ; M ; XM
          ; XM≡M⁻¹ ; M₁ ; M₋₁ ; XM₋₁ ; XM₋₁≡M₋₁ ; XMg ; XMg^ )

  -- Paper-V1's group-specific axioms, each stated exactly as there, less
  -- semi-MR, order-Ex, yang-baxter and cz-slide.  The structural rules
  -- come from Lift-Relation below, as for Paper-V1.
  module Base where
    infix 4 _SRel,_===_
    data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where

      order-S :       (₁₊ n) SRel,  S ^ p === ε
      order-H :       (₁₊ n) SRel,  H ^ 2 === XM₋₁
      M-power : ∀ k → (₁₊ n) SRel,  XMg^ k === XM (g^ k)
      comm-HHSHHS :   (₁₊ n) SRel,  H • H • S • H • H • S === S • H • H • S • H • H

      order-CZ :      (₂₊ n) SRel,  CZ ^ p === ε
      comm-CZ-S↑ :    (₂₊ n) SRel,  CZ • S ↑ === S ↑ • CZ
      semi-M↑CZ :     (₂₊ n) SRel,  XMg ↑ • CZ^ g === CZ • XMg ↑
      semi-Ex-S↑ :    (₂₊ n) SRel,  Ex • S ↑ === S ↓ • Ex
      semi-Ex-H↑ :    (₂₊ n) SRel,  Ex • H ↑ === H ↓ • Ex
      blake-c12 :     (₂₊ n) SRel,  (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX === CZ

      semi-CX↑-CZ↓ :  (₃₊ n) SRel,  CZ ↓ • CX ↑ === CZ02 • CX ↑ • CZ ↓

  private module SC = Circuit.Base SympGate
  private module LR = SC.Lift-Relation Base._SRel,_===_

  infix 4 _QRel,_===_
  _QRel,_===_ : (n : ℕ) → WRel (Gen n)
  _QRel,_===_ = LR._VRel,_===_

  open LR public using (srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑)

  -- The axioms under Paper-V1's names, as pattern synonyms, so that
  -- they match and build alike.
  pattern order-S = srel (Base.order-S)
  pattern order-H = srel (Base.order-H)
  pattern M-power k = srel (Base.M-power k)
  pattern comm-HHSHHS = srel (Base.comm-HHSHHS)

  pattern order-CZ = srel (Base.order-CZ)
  pattern comm-CZ-S↑ = srel (Base.comm-CZ-S↑)
  pattern semi-M↑CZ = srel (Base.semi-M↑CZ)

  pattern semi-Ex-S↑ = srel (Base.semi-Ex-S↑)
  pattern semi-Ex-H↑ = srel (Base.semi-Ex-H↑)

  pattern blake-c12 = srel (Base.blake-c12)

  pattern semi-CX↑-CZ↓ = srel (Base.semi-CX↑-CZ↓)
