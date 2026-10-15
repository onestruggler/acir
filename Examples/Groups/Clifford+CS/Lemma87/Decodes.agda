------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.7 from a convenient spelling (the analogue of Clément's
-- Lemma 8.7, the generic half)
--
-- Given Lemma 8.8 (the decoding respects the rules of P′), the rules of
-- P′ being complete (Theorem410), the decoding of a word over P′
-- depends only on its matrix.  So the decoding inverts the encoding of
-- a generator g as soon as some word w over P′ with g's matrix decodes
-- to g: w need not be the encoding of g, and may be chosen for the
-- circuit derivation it makes.  `Decodes w c` says that w decodes to the
-- circuit c and has c's matrix; it is closed under products, holds for
-- a letter whose decoding has the letter's matrix, and for the encoding
-- of every circuit whose generators are already done, so a generator
-- can also be done by writing it as a circuit in generators done
-- before (`by-decodes`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Lemma87.Decodes (m : ℕ) where

open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Clifford+CS.Semantics
  using (Scaled ; _~_ ; ~-trans ; ~-sym ; ~-refl ; ∙-cong ; ε∙)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; module Ext ; ⟦⟧ᴱ-def)
open import Examples.Groups.Clifford+CS.Soundness using (soundᴱ)
open import Examples.Groups.Clifford+CS.Encoding m using (n ; N ; e ; big)
open import Examples.Groups.Clifford+CS.Decoding m using (d)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)
open import Examples.Groups.Clifford+CS.BridgeGray n using (⟦_⟧PY ; module Complete)
open import Examples.Groups.Clifford+CS.Section8 m using (e-sem)
open import Examples.Groups.Clifford+CS.CompletenessInduction using (DWD)

open Complete big using (complete-P)
open PB (n VRel,_===_) using (refl ; sym ; trans ; cong)

private
  ⟦_⟧ᴱ : Circuit n → Scaled n
  ⟦_⟧ᴱ = Ext.⟦_⟧ᴱ n

  W : Set
  W = Word (GenP N)

  variable
    w w′ : W
    c c′ : Circuit n

------------------------------------------------------------------------
-- A word over P′ decoding to a circuit

record Decodes (w : W) (c : Circuit n) : Set where
  field
    dec : n ⊢ (d ʷ) w ≈ c         -- its decoding is the circuit
    sem : ⟦ w ⟧PY ~ ⟦ c ⟧ᴱ        -- and it has the circuit's matrix

open Decodes public

-- Products.
εᵈ : Decodes ε ε
εᵈ = record { dec = refl ; sem = ~-refl ε∙ }

infixr 7 _•ᵈ_
_•ᵈ_ : Decodes w c → Decodes w′ c′ → Decodes (w • w′) (c • c′)
_•ᵈ_ {w} {c} {w′} {c′} p q = record
  { dec = cong (dec p) (dec q)
  ; sem = ∙-cong {s = ⟦ w ⟧PY} {⟦ c ⟧ᴱ} {⟦ w′ ⟧PY} {⟦ c′ ⟧ᴱ} (sem p) (sem q)
  }

-- The circuit may be rewritten.
≈ᵈ : Decodes w c → n ⊢ c ≈ c′ → Decodes w c′
≈ᵈ {w} {c} {c′} p h = record
  { dec = trans (dec p) h
  ; sem = ~-trans {s = ⟦ w ⟧PY} {⟦ c ⟧ᴱ} {⟦ c′ ⟧ᴱ} (sem p) (soundᴱ h)
  }

-- A letter whose decoding has the letter's matrix.
letterᵈ : (x : GenP N) → ⟦ d x ⟧ ~ ⟦ [ x ]ʷ ⟧PY → Decodes [ x ]ʷ (d x)
letterᵈ x h = record
  { dec = refl
  ; sem = Eq.subst (⟦ [ x ]ʷ ⟧PY ~_) (Eq.sym (⟦⟧ᴱ-def (d x)))
            (~-sym {s = ⟦ d x ⟧} {⟦ [ x ]ʷ ⟧PY} h)
  }

------------------------------------------------------------------------
-- Generators done

-- The decoding inverts the encoding of g.
Done : Gen n → Set
Done g = n ⊢ [ g ]ʷ ≈ (d ʷ) (e g)

-- Every generator of a circuit done.
AllDone : Circuit n → Set
AllDone [ g ]ʷ   = Done g
AllDone ε        = ⊤
AllDone (u • v)  = AllDone u × AllDone v

-- The encoding of a generator done decodes to the generator.
genᵈ : (g : Gen n) → Done g → Decodes (e g) [ g ]ʷ
genᵈ g h = record
  { dec = sym h
  ; sem = Eq.subst (⟦ e g ⟧PY ~_) (Eq.sym (⟦⟧ᴱ-def [ g ]ʷ)) (e-sem g)
  }

-- The encoding of a circuit whose generators are done.
encᵈ : (c : Circuit n) → AllDone c → Decodes ((e ʷ) c) c
encᵈ [ g ]ʷ  h        = genᵈ g h
encᵈ ε       tt       = εᵈ
encᵈ (u • v) (hu , hv) = encᵈ u hu •ᵈ encᵈ v hv

------------------------------------------------------------------------
-- Lemma 8.7 for a generator, from any word over P′ decoding to it

module _ (d-wd : DWD m) where

  -- The decoding respects the congruence of P′.
  d-≈ : ∀ {u t : W} → PB._≈_ (N R,_===_) u t → n ⊢ (d ʷ) u ≈ (d ʷ) t
  d-≈ = PP.StarCongruence.fʷ-cong (N R,_===_) (n VRel,_===_) d d-wd

  by-decodes : (g : Gen n) → Decodes w c → n ⊢ [ g ]ʷ ≈ c → Done g
  by-decodes {w} {c} g p h =
    trans h (trans (sym (dec p)) (d-≈ (complete-P {w} {e g} same)))
    where
    gᴱ : ⟦ [ g ]ʷ ⟧ᴱ ≡ ⟦ [ g ]ʷ ⟧
    gᴱ = ⟦⟧ᴱ-def [ g ]ʷ

    same : ⟦ w ⟧PY ~ ⟦ e g ⟧PY
    same =
      ~-trans {s = ⟦ w ⟧PY} {⟦ c ⟧ᴱ} {⟦ e g ⟧PY} (sem p)
        (~-trans {s = ⟦ c ⟧ᴱ} {⟦ [ g ]ʷ ⟧ᴱ} {⟦ e g ⟧PY} (soundᴱ (sym h))
          (Eq.subst (_~ ⟦ e g ⟧PY) (Eq.sym gᴱ)
            (~-sym {s = ⟦ e g ⟧PY} {⟦ [ g ]ʷ ⟧} (e-sem g))))
