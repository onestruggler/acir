------------------------------------------------------------------------
-- Presentations of groups
--
-- The tables of the four-wire windows
--
-- For each idle wire i, the three-wire word of every letter spelled
-- off wire i that a window meets (Four.Win.lwin); `lwI` is a window
-- step with i idle.  Written by `scratchpad/four/wintable4.py`, which
-- read the words off the window libraries.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Lits where

open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (_•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Four.Letters

import Examples.Groups.Clifford+CS.Four.Win
module W0 = Examples.Groups.Clifford+CS.Four.Win 0 3 Mac ⟪_⟫
module W1 = Examples.Groups.Clifford+CS.Four.Win 1 2 Mac ⟪_⟫
module W2 = Examples.Groups.Clifford+CS.Four.Win 2 1 Mac ⟪_⟫
module W3 = Examples.Groups.Clifford+CS.Four.Win 3 0 Mac ⟪_⟫

lit0 : (g : Mac) → Maybe (W0.Lit g)
lit0 ι1 = just (W0.lit (iI) tt Eq.refl)
lit0 ι2 = just (W0.lit (iI ↑) tt Eq.refl)
lit0 ι3 = just (W0.lit (iI ↑ ↑) tt Eq.refl)
lit0 S1 = just (W0.lit (S) tt Eq.refl)
lit0 S1⁻ = just (W0.lit (S • S • S) tt Eq.refl)
lit0 K1 = just (W0.lit (K) tt Eq.refl)
lit0 K1⁻ = just (W0.lit (K • iI) tt Eq.refl)
lit0 X1 = just (W0.lit (X) tt Eq.refl)
lit0 Z1 = just (W0.lit (Z) tt Eq.refl)
lit0 S2 = just (W0.lit (S ↑) tt Eq.refl)
lit0 S2⁻ = just (W0.lit ((S • S • S) ↑) tt Eq.refl)
lit0 K2 = just (W0.lit (K ↑) tt Eq.refl)
lit0 K2⁻ = just (W0.lit ((K • iI) ↑) tt Eq.refl)
lit0 X2 = just (W0.lit (X ↑) tt Eq.refl)
lit0 Z2 = just (W0.lit (Z ↑) tt Eq.refl)
lit0 S3 = just (W0.lit (S ↑ ↑) tt Eq.refl)
lit0 S3⁻ = just (W0.lit ((S • S • S) ↑ ↑) tt Eq.refl)
lit0 K3 = just (W0.lit (K ↑ ↑) tt Eq.refl)
lit0 K3⁻ = just (W0.lit ((K • iI) ↑ ↑) tt Eq.refl)
lit0 X3 = just (W0.lit (X ↑ ↑) tt Eq.refl)
lit0 Z3 = just (W0.lit (Z ↑ ↑) tt Eq.refl)
lit0 CS12 = just (W0.lit (CS) tt Eq.refl)
lit0 CS12⁻ = just (W0.lit (CS • CS • CS) tt Eq.refl)
lit0 CZ12 = just (W0.lit (CZ) tt Eq.refl)
lit0 CX12 = just (W0.lit (CX₀₁) tt Eq.refl)
lit0 CK12 = just (W0.lit (CK₀₁) tt Eq.refl)
lit0 CK12⁻ = just (W0.lit (S • CK₀₁) tt Eq.refl)
lit0 Sw12 = just (W0.lit (Swap) tt Eq.refl)
lit0 CS13 = just (W0.lit (Swap ↑ • CS • Swap ↑) tt Eq.refl)
lit0 CS13⁻ = just (W0.lit (Swap ↑ • (CS • CS • CS) • Swap ↑) tt Eq.refl)
lit0 CZ13 = just (W0.lit (Swap ↑ • CZ • Swap ↑) tt Eq.refl)
lit0 CX13 = just (W0.lit (Swap ↑ • CX₀₁ • Swap ↑) tt Eq.refl)
lit0 CK13 = just (W0.lit (Swap ↑ • CK₀₁ • Swap ↑) tt Eq.refl)
lit0 CK13⁻ = just (W0.lit (Swap ↑ • (S • CK₀₁) • Swap ↑) tt Eq.refl)
lit0 CX21 = just (W0.lit (CX₁₀) tt Eq.refl)
lit0 CK21 = just (W0.lit (CK₁₀) tt Eq.refl)
lit0 CK21⁻ = just (W0.lit (S ↑ • CK₁₀) tt Eq.refl)
lit0 CS23 = just (W0.lit (CS ↑) tt Eq.refl)
lit0 CS23⁻ = just (W0.lit ((CS • CS • CS) ↑) tt Eq.refl)
lit0 CZ23 = just (W0.lit (CZ ↑) tt Eq.refl)
lit0 CX23 = just (W0.lit (CX₀₁ ↑) tt Eq.refl)
lit0 CK23 = just (W0.lit (CK₀₁ ↑) tt Eq.refl)
lit0 CK23⁻ = just (W0.lit ((S • CK₀₁) ↑) tt Eq.refl)
lit0 Sw23 = just (W0.lit (Swap ↑) tt Eq.refl)
lit0 CX31 = just (W0.lit (Swap ↑ • CX₁₀ • Swap ↑) tt Eq.refl)
lit0 CK31 = just (W0.lit (Swap ↑ • CK₁₀ • Swap ↑) tt Eq.refl)
lit0 CK31⁻ = just (W0.lit (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) tt Eq.refl)
lit0 CX32 = just (W0.lit (CX₁₀ ↑) tt Eq.refl)
lit0 CK32 = just (W0.lit (CK₁₀ ↑) tt Eq.refl)
lit0 CK32⁻ = just (W0.lit ((S ↑ • CK₁₀) ↑) tt Eq.refl)
lit0 CCZ123 = just (W0.lit (CCZ) tt Eq.refl)
lit0 Toff123 = just (W0.lit (Toff) tt Eq.refl)
lit0 Toff213 = just (W0.lit (K ↑ • CCZ • K ↑ • iI) tt Eq.refl)
lit0 Toff312 = just (W0.lit (Toffᵗ) tt Eq.refl)
lit0 _ = nothing

lw0 : _
lw0 = W0.lwin lit0

lit1 : (g : Mac) → Maybe (W1.Lit g)
lit1 S0 = just (W1.lit (S) tt Eq.refl)
lit1 S0⁻ = just (W1.lit (S • S • S) tt Eq.refl)
lit1 K0 = just (W1.lit (K) tt Eq.refl)
lit1 K0⁻ = just (W1.lit (K • iI) tt Eq.refl)
lit1 X0 = just (W1.lit (X) tt Eq.refl)
lit1 X2 = just (W1.lit (X ↑) tt Eq.refl)
lit1 X3 = just (W1.lit (X ↑ ↑) tt Eq.refl)
lit1 CS23 = just (W1.lit (CS ↑) tt Eq.refl)
lit1 CS23⁻ = just (W1.lit ((CS • CS • CS) ↑) tt Eq.refl)
lit1 CK23 = just (W1.lit (CK₀₁ ↑) tt Eq.refl)
lit1 CK23⁻ = just (W1.lit ((S • CK₀₁) ↑) tt Eq.refl)
lit1 CK32 = just (W1.lit (CK₁₀ ↑) tt Eq.refl)
lit1 CK32⁻ = just (W1.lit ((S ↑ • CK₁₀) ↑) tt Eq.refl)
lit1 _ = nothing

lw1 : _
lw1 = W1.lwin lit1

lit2 : (g : Mac) → Maybe (W2.Lit g)
lit2 X1 = just (W2.lit (X ↑) tt Eq.refl)
lit2 X3 = just (W2.lit (X ↑ ↑) tt Eq.refl)
lit2 CS01 = just (W2.lit (CS) tt Eq.refl)
lit2 CS01⁻ = just (W2.lit (CS • CS • CS) tt Eq.refl)
lit2 CK10 = just (W2.lit (CK₁₀) tt Eq.refl)
lit2 CK10⁻ = just (W2.lit (S ↑ • CK₁₀) tt Eq.refl)
lit2 _ = nothing

lw2 : _
lw2 = W2.lwin lit2

lit3 : (g : Mac) → Maybe (W3.Lit g)
lit3 ι = just (W3.lit (iI) tt Eq.refl)
lit3 ι1 = just (W3.lit (iI ↑) tt Eq.refl)
lit3 ι2 = just (W3.lit (iI ↑ ↑) tt Eq.refl)
lit3 S0 = just (W3.lit (S) tt Eq.refl)
lit3 S0⁻ = just (W3.lit (S • S • S) tt Eq.refl)
lit3 K0 = just (W3.lit (K) tt Eq.refl)
lit3 K0⁻ = just (W3.lit (K • iI) tt Eq.refl)
lit3 X0 = just (W3.lit (X) tt Eq.refl)
lit3 Z0 = just (W3.lit (Z) tt Eq.refl)
lit3 S1 = just (W3.lit (S ↑) tt Eq.refl)
lit3 S1⁻ = just (W3.lit ((S • S • S) ↑) tt Eq.refl)
lit3 K1 = just (W3.lit (K ↑) tt Eq.refl)
lit3 K1⁻ = just (W3.lit ((K • iI) ↑) tt Eq.refl)
lit3 X1 = just (W3.lit (X ↑) tt Eq.refl)
lit3 Z1 = just (W3.lit (Z ↑) tt Eq.refl)
lit3 S2 = just (W3.lit (S ↑ ↑) tt Eq.refl)
lit3 S2⁻ = just (W3.lit ((S • S • S) ↑ ↑) tt Eq.refl)
lit3 K2 = just (W3.lit (K ↑ ↑) tt Eq.refl)
lit3 K2⁻ = just (W3.lit ((K • iI) ↑ ↑) tt Eq.refl)
lit3 X2 = just (W3.lit (X ↑ ↑) tt Eq.refl)
lit3 Z2 = just (W3.lit (Z ↑ ↑) tt Eq.refl)
lit3 CS01 = just (W3.lit (CS) tt Eq.refl)
lit3 CS01⁻ = just (W3.lit (CS • CS • CS) tt Eq.refl)
lit3 CZ01 = just (W3.lit (CZ) tt Eq.refl)
lit3 CX01 = just (W3.lit (CX₀₁) tt Eq.refl)
lit3 CK01 = just (W3.lit (CK₀₁) tt Eq.refl)
lit3 CK01⁻ = just (W3.lit (S • CK₀₁) tt Eq.refl)
lit3 Sw01 = just (W3.lit (Swap) tt Eq.refl)
lit3 CS02 = just (W3.lit (Swap ↑ • CS • Swap ↑) tt Eq.refl)
lit3 CS02⁻ = just (W3.lit (Swap ↑ • (CS • CS • CS) • Swap ↑) tt Eq.refl)
lit3 CZ02 = just (W3.lit (Swap ↑ • CZ • Swap ↑) tt Eq.refl)
lit3 CX02 = just (W3.lit (Swap ↑ • CX₀₁ • Swap ↑) tt Eq.refl)
lit3 CK02 = just (W3.lit (Swap ↑ • CK₀₁ • Swap ↑) tt Eq.refl)
lit3 CK02⁻ = just (W3.lit (Swap ↑ • (S • CK₀₁) • Swap ↑) tt Eq.refl)
lit3 CX10 = just (W3.lit (CX₁₀) tt Eq.refl)
lit3 CK10 = just (W3.lit (CK₁₀) tt Eq.refl)
lit3 CK10⁻ = just (W3.lit (S ↑ • CK₁₀) tt Eq.refl)
lit3 CS12 = just (W3.lit (CS ↑) tt Eq.refl)
lit3 CS12⁻ = just (W3.lit ((CS • CS • CS) ↑) tt Eq.refl)
lit3 CZ12 = just (W3.lit (CZ ↑) tt Eq.refl)
lit3 CX12 = just (W3.lit (CX₀₁ ↑) tt Eq.refl)
lit3 CK12 = just (W3.lit (CK₀₁ ↑) tt Eq.refl)
lit3 CK12⁻ = just (W3.lit ((S • CK₀₁) ↑) tt Eq.refl)
lit3 Sw12 = just (W3.lit (Swap ↑) tt Eq.refl)
lit3 CX20 = just (W3.lit (Swap ↑ • CX₁₀ • Swap ↑) tt Eq.refl)
lit3 CK20 = just (W3.lit (Swap ↑ • CK₁₀ • Swap ↑) tt Eq.refl)
lit3 CK20⁻ = just (W3.lit (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) tt Eq.refl)
lit3 CX21 = just (W3.lit (CX₁₀ ↑) tt Eq.refl)
lit3 CK21 = just (W3.lit (CK₁₀ ↑) tt Eq.refl)
lit3 CK21⁻ = just (W3.lit ((S ↑ • CK₁₀) ↑) tt Eq.refl)
lit3 CCZ012 = just (W3.lit (CCZ) tt Eq.refl)
lit3 Toff012 = just (W3.lit (Toff) tt Eq.refl)
lit3 Toff102 = just (W3.lit (K ↑ • CCZ • K ↑ • iI) tt Eq.refl)
lit3 Toff201 = just (W3.lit (Toffᵗ) tt Eq.refl)
lit3 _ = nothing

lw3 : _
lw3 = W3.lwin lit3
