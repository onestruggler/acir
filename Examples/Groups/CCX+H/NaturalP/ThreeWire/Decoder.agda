------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoder on eight levels, as circuits over X, CX, CCX and H.
--
-- A generator decodes to the circuit of its element list (DecTable), a
-- word to the product (`D′`); read in the rules, the decoding of a word
-- is the list of its elements (`D-flat`), so a loop through the lists of
-- two words, equal to ε, makes their decodings equal (`byLoop`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.ThreeWire.Decoder where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Kit
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Chain using (⦅_⦆)
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Elements
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.DecTable public using (Lels)
import Examples.Groups.CCX+H.NaturalP.Bridge as Br
import Examples.Groups.CCX+H.Syntactics as C
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics using (Genᴸ)

private
  refl≡ : ∀ {u v : Circuit 3} → u ≡ v → 3 ⊢ u ≈ v
  refl≡ Eq.refl = refl

d′ : Genᴸ 8 → C.Circuit 3
d′ y = ⦅ map cE (Lels y) ⦆ᶜ

D′ : Word (Genᴸ 8) → C.Circuit 3
D′ = d′ ʷ

Lw : Word (Genᴸ 8) → List El
Lw [ y ]ʷ  = Lels y
Lw ε       = []
Lw (u • v) = Lw u ++ Lw v

D-flat : ∀ u → 3 ⊢ Br.ι (D′ u) ≈ ⦅ map ⟦_⟧ₑ (Lw u) ⦆
D-flat [ y ]ʷ  = refl≡ (ι-cE (Lels y))
D-flat ε       = refl
D-flat (u • v) = trans (cong (D-flat u) (D-flat v)) (sym (⟦⟧-++ (Lw u) (Lw v)))

byLoop : ∀ u v → 3 ⊢ ⦅ map ⟦_⟧ₑ (Lw u ++ invL (Lw v)) ⦆ ≈ ε → 3 ⊢ Br.ι (D′ u) ≈ Br.ι (D′ v)
byLoop u v e = trans (D-flat u) (trans (from-loop (Lw u) (Lw v) e) (sym (D-flat v)))
