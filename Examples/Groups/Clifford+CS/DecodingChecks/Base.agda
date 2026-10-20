------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding checked on four qubits: the shared definitions
--
-- Each check compares the circuit's row-operation reading with the
-- letter's two-level word read at the Gray numbering (BridgeGray), by
-- one boolean, as scratchpad/dec.py does for every letter; it pins the
-- spelling of the networks and the orientations.  The checks are
-- spread over the modules beside this one, a few per module, since Agda
-- frees the memory of an evaluation only when its module is done.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.DecodingChecks.Base where

open import Data.Bool using (T ; true)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (_<ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Interpretation using (len)
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM)
open import Examples.Groups.Clifford+CS.FastEval using (⟦_⟧Q ; nK)
open import Examples.Groups.Clifford+CS.BridgeGray 4 using (⟦_⟧ʸ ; ⟦_⟧Y)
open import Examples.Groups.Clifford+CS.Decoding 0 using (d)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG ; pp ; px ; dx ; ki)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL

-- The stored reading of a two-level word at the Gray numbering.
⟦_⟧GM : Word (TL.Gen 16) → Mat 4
⟦ [ y ]ʷ ⟧GM = matOf (proj₂ ⟦ y ⟧ʸ)
⟦ ε ⟧GM      = idM
⟦ u • t ⟧GM  = mulM ⟦ u ⟧GM ⟦ t ⟧GM

-- The decoded letter has the letter's matrix.
chk : GenP 16 → Set
chk p = eqM (scaleM (γ^ proj₁ ⟦ asG p ⟧Y) ⟦ d p ⟧Q) (scaleM (γ^ nK (d p)) ⟦ asG p ⟧GM) ≡ true

-- An order of two literal indices.
lt : ∀ (a b : Fin 16) {p : T (toℕ a <ᵇ toℕ b)} → Data.Fin._<_ a b
lt a b {p} = <ᵇ⇒< (toℕ a) (toℕ b) p

