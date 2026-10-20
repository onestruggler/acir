{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4678 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0063 as B63
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0082 as B82
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0086 as B86
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0407 as B407
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0504 as B504
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0775 as B775
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1066 as B1066
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1215 as B1215

p0 : CCX02 • CX12 • SWAP01 • SWAP12 • CX02 ≈ CX21 • CCX02 • CX12 • SWAP02 • CX02
p0 = by-assoc-and (under (ε) (CX02) B1066.proved) Eq.refl Eq.refl

p1 : CCX02 • CX12 • SWAP01 • SWAP12 • CX02 ≈ CCX02 • CX12 • SWAP01 • CX01 • SWAP12
p1 = by-assoc-and (under (CCX02 • CX12 • SWAP01) (ε) B82.proved) Eq.refl Eq.refl

p2 : CX21 • CCX02 • CX12 • SWAP02 • CX02 ≈ CCX02 • CX12 • SWAP01 • CX01 • SWAP12
p2 = trans (sym p0) p1

p3 : CX21 • CCX02 • CX12 • SWAP02 • CX02 ≈ CX21 • CCX02 • CX12 • CX02 • CX20
p3 = by-assoc-and (under (CX21 • CCX02 • CX12) (ε) B86.proved) Eq.refl Eq.refl

p4 : CX21 • CCX02 • CX12 • CX02 • CX20 ≈ CX21 • CCX02 • CX02 • CX12 • CX20
p4 = by-assoc-and (under (CX21 • CCX02) (CX20) B27.proved) Eq.refl Eq.refl

p5 : CX21 • CCX02 • CX02 • CX12 • CX20 ≈ CX02 • CX21 • CCX02 • CX12 • CX20
p5 = by-assoc-and (under (ε) (CX12 • CX20) B407.proved) Eq.refl Eq.refl

p6 : CX02 • CX21 • CCX02 • CX12 • CX20 ≈ CX02 • CX20 • CCX02 • CX10 • CX12
p6 = by-assoc-and (under (CX02) (ε) B775.proved) Eq.refl Eq.refl

p7 : CX21 • CCX02 • CX12 • SWAP02 • CX02 ≈ CX02 • CX20 • CCX02 • CX10 • CX12
p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

p8 : CCX02 • CX12 • SWAP01 • CX01 • SWAP12 ≈ CCX02 • CX12 • CX01 • CX10 • SWAP12
p8 = by-assoc-and (under (CCX02 • CX12) (SWAP12) B63.proved) Eq.refl Eq.refl

p9 : CCX02 • CX12 • CX01 • CX10 • SWAP12 ≈ CX02 • CCX02 • CX12 • CX10 • SWAP12
p9 = by-assoc-and (under (ε) (CX10 • SWAP12) B504.proved) Eq.refl Eq.refl

p10 : CX02 • CCX02 • CX12 • CX10 • SWAP12 ≈ CX02 • CCX02 • CX10 • CX12 • SWAP12
p10 = by-assoc-and (under (CX02 • CCX02) (SWAP12) B26.proved) Eq.refl Eq.refl

p11 : CX02 • CCX02 • CX10 • CX12 • SWAP12 ≈ CX01 • CCX02 • CX10 • CX02 • SWAP12
p11 = by-assoc-and (under (ε) (SWAP12) B1215.proved) Eq.refl Eq.refl

p12 : CCX02 • CX12 • SWAP01 • CX01 • SWAP12 ≈ CX01 • CCX02 • CX10 • CX02 • SWAP12
p12 = trans p8 (trans p9 (trans p10 (trans p11 (refl))))

p13 : CX02 • CX20 • CCX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02 • SWAP12
p13 = trans (sym p7) (trans p2 p12)

proved : CX02 • CX20 • CCX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02 • SWAP12
proved = p13
