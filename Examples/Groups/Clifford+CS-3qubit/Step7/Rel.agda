------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base
open import Presentation.Tactics.Judgement

open import Examples.Groups.Clifford+CS-3qubit.Gate

module Examples.Groups.Clifford+CS-3qubit.Step7.Rel where

data Rel : Context Gate where

  ax-K1=Swap01-K0-Swap01 : K1 === Swap01 • K0 • Swap01 ∈ Rel
  ax-K2=Swap12-Swap01-K0-Swap01-Swap12 : K2 === Swap12 • Swap01 • K0 • Swap01 • Swap12 ∈ Rel
  ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI : CK10 === CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI ∈ Rel
  ax-CK20=CS02-K0-CS02-K0-CS02-S2-S2-S2-iI : CK20 === CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI ∈ Rel
  ax-CCK'=K0-CS01-K0-CS02-K0-CS01-K0-CCX0-CX10-CS12-CS12-CS12-CS02-CS02-CS02-iI-iI : CCK' === K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI ∈ Rel


  ax-iI-K0=K0-iI : iI • K0 === K0 • iI ∈ Rel
  ax-S1-K0=K0-S1 : S1 • K0 === K0 • S1 ∈ Rel
  ax-X1-K0=K0-X1 : X1 • K0 === K0 • X1 ∈ Rel
  ax-CS12-K0=K0-CS12 : CS12 • K0 === K0 • CS12 ∈ Rel
  ax-CX12-K0=K0-CX12 : CX12 • K0 === K0 • CX12 ∈ Rel
  ax-Swap12-K0=K0-Swap12 : Swap12 • K0 === K0 • Swap12 ∈ Rel
  ax-S0-S0-K0=K0-X0 : S0 • S0 • K0 === K0 • X0 ∈ Rel
  ax-CS01-CS01-K0=K0-CX10 : CS01 • CS01 • K0 === K0 • CX10 ∈ Rel
  ax-CCZ-K0=K0-CCX0 : CCZ • K0 === K0 • CCX0 ∈ Rel
  ax-S0-K0-S0-K0-S0-K0=iI-iI-iI : (S0 • K0) ^ 3 === iI ^ 3 ∈ Rel
  ax-Swap01-K0-Swap01-K0=K0-Swap01-K0-Swap01 : Swap01 • K0 • Swap01 • K0 === K0 • Swap01 • K0 • Swap01 ∈ Rel
  ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01 : CS01 • K0 • CS01 • K0 • S0 === S0 • K0 • CS01 • K0 • CS01 ∈ Rel
  ax-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ : CS01 • CS02 • K0 • CS01 • CS02 • K0 • S0 === S0 • K0 • CS01 • CS02 • K0 • CS01 • CS02 • CS12 • CCZ ∈ Rel

  
  ax-X0-S0=S0-S0-S0-iI-X0 : X0 • S0 === S0 • S0 • S0 • iI • X0 ∈ Rel
  ax-X0-S1=S1-X0 : X0 • S1 === S1 • X0 ∈ Rel
  ax-X0-CS01=S1-CS01-CS01-CS01-X0 : X0 • CS01 === S1 • CS01 • CS01 • CS01 • X0 ∈ Rel
  ax-X0-CS12=CS12-X0 : X0 • CS12 === CS12 • X0 ∈ Rel
  ax-X0-CCZ=CS12-CS12-CCZ-X0 : X0 • CCZ === CS12 • CS12 • CCZ • X0 ∈ Rel
  ax-CX10-S0=S0-S1-CS01-CS01-CX10 : CX10 • S0 === S0 • S1 • CS01 • CS01 • CX10 ∈ Rel
  ax-CX10-S1=S1-CX10 : CX10 • S1 === S1 • CX10 ∈ Rel
  ax-CX10-S2=S2-CX10 : CX10 • S2 === S2 • CX10 ∈ Rel
  ax-CX10-CS01=S1-CS01-CS01-CS01-CX10 : CX10 • CS01 === S1 • CS01 • CS01 • CS01 • CX10 ∈ Rel
  ax-CX10-CS12=CS12-CX10 : CX10 • CS12 === CS12 • CX10 ∈ Rel
  ax-CX10-CS02=CS02-CS12-CCZ-CX10 : CX10 • CS02 === CS02 • CS12 • CCZ • CX10 ∈ Rel
  ax-CX10-CCZ=CS12-CS12-CCZ-CX10 : CX10 • CCZ === CS12 • CS12 • CCZ • CX10 ∈ Rel
  ax-CCX0-S0=S0-CS12-CCZ-CCX0 : CCX0 • S0 === S0 • CS12 • CCZ • CCX0 ∈ Rel
  ax-CCX0-S1=S1-CCX0 : CCX0 • S1 === S1 • CCX0 ∈ Rel
  ax-CCX0-CS01=CS01-CS12-CCZ-CCX0 : CCX0 • CS01 === CS01 • CS12 • CCZ • CCX0 ∈ Rel
  ax-CCX0-CS12=CS12-CCX0 : CCX0 • CS12 === CS12 • CCX0 ∈ Rel
  ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0 : CCX0 • CCZ === CS12 • CS12 • CCZ • CCX0 ∈ Rel


  ax-S1-S0=S0-S1 : S1 • S0 === S0 • S1 ∈ Rel
  ax-CS01-S0=S0-CS01 : CS01 • S0 === S0 • CS01 ∈ Rel
  ax-CS01-S2=S2-CS01 : CS01 • S2 === S2 • CS01 ∈ Rel
  ax-CS12-CS01=CS01-CS12 : CS12 • CS01 === CS01 • CS12 ∈ Rel
  ax-CCZ-S0=S0-CCZ : CCZ • S0 === S0 • CCZ ∈ Rel
  ax-CCZ-CS01=CS01-CCZ : CCZ • CS01 === CS01 • CCZ ∈ Rel


  ax-CCX0-CCX0=ε : CCX0 • CCX0 === ε ∈ Rel
  ax-CCX0-CCX1-CCX0=CCX1-CCX0-CCX1 : CCX0 • CCX1 • CCX0 === CCX1 • CCX0 • CCX1 ∈ Rel
  ax-CCX0-CCX2-CCX1-CCX2=CCX2-CCX1-CCX2-CCX0 : CCX0 • CCX2 • CCX1 • CCX2 === CCX2 • CCX1 • CCX2 • CCX0 ∈ Rel
  
  ax-CX01-CX01=ε : CX01 • CX01 === ε ∈ Rel
  ax-CCX0-CX10=CX10-CCX0 : CCX0 • CX10 === CX10 • CCX0 ∈ Rel
  ax-CCX0-CX01=CX01-CCX1-CCX0-CCX1 : CCX0 • CX01 === CX01 • CCX1 • CCX0 • CCX1 ∈ Rel
  ax-CCX2-CX01=CX01-CX02-CCX2 : CCX2 • CX01 === CX01 • CX02 • CCX2 ∈ Rel

  ax-CX01-CX02=CX02-CX01 : CX01 • CX02 === CX02 • CX01 ∈ Rel
  ax-CX01-CX21=CX21-CX01 : CX01 • CX21 === CX21 • CX01 ∈ Rel  
  ax-CX10-CX02=CX02-CX12-CX10 : CX10 • CX02 === CX02 • CX12 • CX10 ∈ Rel
  ax-CX10-CX21=CX21-CX20-CX10 : CX10 • CX21 === CX21 • CX20 • CX10 ∈ Rel

  ax-X1-X0=X0-X1 : X1 • X0 === X0 • X1 ∈ Rel
  ax-X0-CX12=CX12-X0 : X0 • CX12 === CX12 • X0 ∈ Rel
  ax-X0-CX10=CX10-X0 : X0 • CX10 === CX10 • X0 ∈ Rel
  ax-X0-CX01=CX01-X0-X1 : X0 • CX01 === CX01 • X0 • X1 ∈ Rel
  ax-X0-CCX1=CCX1-CX21-X0 : X0 • CCX1 === CCX1 • CX21 • X0 ∈ Rel
  ax-X0-CCX0=CCX0-X0 : X0 • CCX0 === CCX0 • X0 ∈ Rel

  
  ax-X0-X0=ε : X0 • X0 === ε ∈ Rel
  ax-S0-S0-S0-S0=ε : S0 • S0 • S0 • S0 === ε ∈ Rel
  ax-CS01-CS01-CS01-CS01=ε : CS01 • CS01 • CS01 • CS01 === ε ∈ Rel
  ax-CCZ-CCZ=ε : CCZ • CCZ === ε ∈ Rel
  ax-iI-iI-iI-iI=ε : iI • iI • iI • iI === ε ∈ Rel
  ax-K0-K0=iI-iI-iI : K0 • K0 === iI • iI • iI ∈ Rel
  
  ax-iI-CCX0=CCX0-iI : iI • CCX0 === CCX0 • iI ∈ Rel
  ax-iI-CX01=CX01-iI : iI • CX01 === CX01 • iI ∈ Rel
  ax-iI-X0=X0-iI : iI • X0 === X0 • iI ∈ Rel
  ax-iI-S0=S0-iI : iI • S0 === S0 • iI ∈ Rel
  ax-iI-CS01=CS01-iI : iI • CS01 === CS01 • iI ∈ Rel
  ax-iI-CCZ=CCZ-iI : iI • CCZ === CCZ • iI ∈ Rel

  
  ax-Swap01-Swap01=ε : Swap01 • Swap01 === ε ∈ Rel
  ax-Swap12-Swap12=ε : Swap12 • Swap12 === ε ∈ Rel
  ax-Swap01=CX01-CX10-CX01 : Swap01 === CX01 • CX10 • CX01 ∈ Rel 
  ax-Swap12=CX12-CX21-CX12 : Swap12 === CX12 • CX21 • CX12 ∈ Rel 
  ax-Swap12-Swap01-Swap12=Swap01-Swap12-Swap01 : Swap12 • Swap01 • Swap12 === Swap01 • Swap12 • Swap01 ∈ Rel
  
  ax-Swap01-X0=X1-Swap01 : Swap01 • X0 === X1 • Swap01 ∈ Rel
  ax-Swap01-X1=X0-Swap01 : Swap01 • X1 === X0 • Swap01 ∈ Rel
  ax-Swap01-X2=X2-Swap01 : Swap01 • X2 === X2 • Swap01 ∈ Rel
  ax-Swap01-CX01=CX10-Swap01 : Swap01 • CX01 === CX10 • Swap01 ∈ Rel
  ax-Swap01-CX10=CX01-Swap01 : Swap01 • CX10 === CX01 • Swap01 ∈ Rel
  ax-Swap01-CX12=CX02-Swap01 : Swap01 • CX12 === CX02 • Swap01 ∈ Rel
  ax-Swap01-CX21=CX20-Swap01 : Swap01 • CX21 === CX20 • Swap01 ∈ Rel
  ax-Swap01-CX02=CX12-Swap01 : Swap01 • CX02 === CX12 • Swap01 ∈ Rel
  ax-Swap01-CX20=CX21-Swap01 : Swap01 • CX20 === CX21 • Swap01 ∈ Rel
  ax-Swap01-CCX2=CCX2-Swap01 : Swap01 • CCX2 === CCX2 • Swap01 ∈ Rel
  ax-Swap01-CCX0=CCX1-Swap01 : Swap01 • CCX0 === CCX1 • Swap01 ∈ Rel
  ax-Swap01-CCX1=CCX0-Swap01 : Swap01 • CCX1 === CCX0 • Swap01 ∈ Rel
  ax-Swap01-S0=S1-Swap01 : Swap01 • S0 === S1 • Swap01 ∈ Rel
  ax-Swap01-S1=S0-Swap01 : Swap01 • S1 === S0 • Swap01 ∈ Rel
  ax-Swap01-S2=S2-Swap01 : Swap01 • S2 === S2 • Swap01 ∈ Rel
  ax-Swap01-CS01=CS01-Swap01 : Swap01 • CS01 === CS01 • Swap01 ∈ Rel
  ax-Swap01-CS02=CS12-Swap01 : Swap01 • CS02 === CS12 • Swap01 ∈ Rel
  ax-Swap01-CS12=CS02-Swap01 : Swap01 • CS12 === CS02 • Swap01 ∈ Rel
  ax-Swap01-CCZ=CCZ-Swap01 : Swap01 • CCZ === CCZ • Swap01 ∈ Rel
  ax-iI-Swap01=Swap01-iI : iI • Swap01 === Swap01 • iI ∈ Rel
  
  ax-Swap12-X0=X0-Swap12 : Swap12 • X0 === X0 • Swap12 ∈ Rel
  ax-Swap12-X1=X2-Swap12 : Swap12 • X1 === X2 • Swap12 ∈ Rel
  ax-Swap12-X2=X1-Swap12 : Swap12 • X2 === X1 • Swap12 ∈ Rel
  ax-Swap12-CX01=CX02-Swap12 : Swap12 • CX01 === CX02 • Swap12 ∈ Rel
  ax-Swap12-CX10=CX20-Swap12 : Swap12 • CX10 === CX20 • Swap12 ∈ Rel
  ax-Swap12-CX12=CX21-Swap12 : Swap12 • CX12 === CX21 • Swap12 ∈ Rel
  ax-Swap12-CX21=CX12-Swap12 : Swap12 • CX21 === CX12 • Swap12 ∈ Rel
  ax-Swap12-CX02=CX01-Swap12 : Swap12 • CX02 === CX01 • Swap12 ∈ Rel
  ax-Swap12-CX20=CX10-Swap12 : Swap12 • CX20 === CX10 • Swap12 ∈ Rel
  ax-Swap12-CCX2=CCX1-Swap12 : Swap12 • CCX2 === CCX1 • Swap12 ∈ Rel
  ax-Swap12-CCX1=CCX2-Swap12 : Swap12 • CCX1 === CCX2 • Swap12 ∈ Rel
  ax-Swap12-CCX0=CCX0-Swap12 : Swap12 • CCX0 === CCX0 • Swap12 ∈ Rel
  ax-Swap12-S0=S0-Swap12 : Swap12 • S0 === S0 • Swap12 ∈ Rel
  ax-Swap12-S1=S2-Swap12 : Swap12 • S1 === S2 • Swap12 ∈ Rel
  ax-Swap12-S2=S1-Swap12 : Swap12 • S2 === S1 • Swap12 ∈ Rel
  ax-Swap12-CS01=CS02-Swap12 : Swap12 • CS01 === CS02 • Swap12 ∈ Rel
  ax-Swap12-CS02=CS01-Swap12 : Swap12 • CS02 === CS01 • Swap12 ∈ Rel
  ax-Swap12-CS12=CS12-Swap12 : Swap12 • CS12 === CS12 • Swap12 ∈ Rel
  ax-Swap12-CCZ=CCZ-Swap12 : Swap12 • CCZ === CCZ • Swap12 ∈ Rel
  ax-iI-Swap12=Swap12-iI : iI • Swap12 === Swap12 • iI ∈ Rel
