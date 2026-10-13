------------------------------------------------------------------------
-- Presentations of groups
--
-- A two-wire decoder for the scaled dyadic auxiliary presentation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.TwoQubit.Decoding where

open import Data.Fin.Base using (Fin)
open import Notations using (₀ ; ₁ ; ₂ ; ₃)
open import Word.Base using (ε ; _•_)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T

X0 X1 H0 H1 C10 C01 CZ HH : Circuit 2
X0 = X
X1 = X ↑
H0 = H
H1 = H ↑
C10 = CX
C01 = H0 • H1 • C10 • H0 • H1
CZ = H0 • C10 • H0
HH = H0 • H1

sign : Fin 4 → Circuit 2
sign ₀ = X0 • X1 • CZ • X1 • X0
sign ₁ = X1 • CZ • X1
sign ₂ = X0 • CZ • X0
sign ₃ = CZ

x01 x02 x03 x12 x13 x23 : Circuit 2
x01 = X1 • C10 • X1
x02 = X0 • C01 • X0
x03 = x01 • C01 • x01
x12 = C10 • C01 • C10
x13 = C01
x23 = C10

exchange : Fin 4 → Fin 4 → Circuit 2
exchange ₀ ₀ = ε
exchange ₀ ₁ = x01
exchange ₀ ₂ = x02
exchange ₀ ₃ = x03
exchange ₁ ₀ = x01
exchange ₁ ₁ = ε
exchange ₁ ₂ = x12
exchange ₁ ₃ = x13
exchange ₂ ₀ = x02
exchange ₂ ₁ = x12
exchange ₂ ₂ = ε
exchange ₂ ₃ = x23
exchange ₃ ₀ = x03
exchange ₃ ₁ = x13
exchange ₃ ₂ = x23
exchange ₃ ₃ = ε

d : T.Genᴸ 4 → Circuit 2
d T.IH = H0
d T.⌊ U.M-gen a ⌋ = sign a
d T.⌊ U.X-gen a b p ⌋ = exchange a b
d T.⌊ U.K-gen a b c d p q r ⌋ = HH
