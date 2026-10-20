{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.invol3 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX10 ; CX12 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0146 as B146
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0147 as B147
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0337 as B337
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0366 as B366
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0481 as B481
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0623 as B623
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0963 as B963

p0 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p0 = by-assoc-and (under (ε) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B481.proved) Eq.refl Eq.refl

p1 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p1 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B215.proved) Eq.refl Eq.refl

p2 : X2 • CX12 • CCX01 • CX10 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p2 = by-assoc-and (under (X2) (CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B118.proved) Eq.refl Eq.refl

p3 : X2 • CX10 • CCX01 • CCX02 • CX10 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p3 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B47.proved) Eq.refl Eq.refl

p4 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p4 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • CX10) (X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B29.proved) Eq.refl Eq.refl

p5 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X2 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p5 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B21.proved) Eq.refl Eq.refl

p6 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • CX10 • CCX01 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p6 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0 • X2) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B366.proved) Eq.refl Eq.refl

p7 : X2 • CX10 • CCX01 • CCX02 • X0 • X2 • X0 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p7 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B18.proved) Eq.refl Eq.refl

p8 : X2 • CX10 • CCX01 • CCX02 • X0 • X0 • X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p8 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B12.proved) Eq.refl Eq.refl

p9 : X2 • CX10 • CCX01 • CCX02 • X2 • CCX01 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p9 = by-assoc-and (under (X2 • CX10) (CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B963.proved) Eq.refl Eq.refl

p10 : X2 • CX10 • CX12 • CCX02 • X2 • CX12 • CX10 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p10 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B26.proved) Eq.refl Eq.refl

p11 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • CX12 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • CX10 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p11 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2 • CX10) (X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B45.proved) Eq.refl Eq.refl

p12 : X2 • CX10 • CX12 • CCX02 • X2 • CX10 • X0 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X2 • X0 • CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p12 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X2) (CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B47.proved) Eq.refl Eq.refl

p13 : X2 • CX10 • CX12 • CCX02 • X2 • X0 • CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p13 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02) (CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B18.proved) Eq.refl Eq.refl

p14 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • CX12 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p14 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10) (CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B36.proved) Eq.refl Eq.refl

p15 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • CX10 • X2 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • X2 • X2 • CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p15 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0 • X2) (CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B21.proved) Eq.refl Eq.refl

p16 : X2 • CX10 • CX12 • CCX02 • X0 • X2 • X2 • CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p16 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B4.proved) Eq.refl Eq.refl

p17 : X2 • CX10 • CX12 • CCX02 • X0 • CX10 • CX12 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CX12 • CCX02 • X0 • CCX01 • CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p17 = by-assoc-and (under (X2 • CX10 • CX12 • CCX02 • X0) (X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B147.proved) Eq.refl Eq.refl

p18 : X2 • CX10 • CX12 • CCX02 • X0 • CCX01 • CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p18 = by-assoc-and (under (X2 • CX10) (CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B623.proved) Eq.refl Eq.refl

p19 : X2 • CX10 • CCX01 • CCX02 • X0 • CX10 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • X0 • X0 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p19 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02 • X0) (CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B47.proved) Eq.refl Eq.refl

p20 : X2 • CX10 • CCX01 • CCX02 • X0 • X0 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CCX02 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p20 = by-assoc-and (under (X2 • CX10 • CCX01 • CCX02) (CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B12.proved) Eq.refl Eq.refl

p21 : X2 • CX10 • CCX01 • CCX02 • CX10 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX10 • CCX01 • CX10 • CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p21 = by-assoc-and (under (X2 • CX10 • CCX01) (CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B337.proved) Eq.refl Eq.refl

p22 : X2 • CX10 • CCX01 • CX10 • CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
p22 = by-assoc-and (under (X2) (CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0) B146.proved) Eq.refl Eq.refl

p23 : X2 • CX12 • CCX01 • CCX12 • CCX02 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • CCX12 • CCX12 • X0 • CCX01 • X2 • X0
p23 = by-assoc-and (under (X2 • CX12 • CCX01 • CCX12) (CCX12 • X0 • CCX01 • X2 • X0) B10.proved) Eq.refl Eq.refl

p24 : X2 • CX12 • CCX01 • CCX12 • CCX12 • X0 • CCX01 • X2 • X0 ≈ X2 • CX12 • CCX01 • X0 • CCX01 • X2 • X0
p24 = by-assoc-and (under (X2 • CX12 • CCX01) (X0 • CCX01 • X2 • X0) B14.proved) Eq.refl Eq.refl

p25 : X2 • CX12 • CCX01 • X0 • CCX01 • X2 • X0 ≈ X2 • X0 • CCX01 • CCX01 • X2 • X0
p25 = by-assoc-and (under (X2) (CCX01 • X2 • X0) B140.proved) Eq.refl Eq.refl

p26 : X2 • X0 • CCX01 • CCX01 • X2 • X0 ≈ X0 • X2 • CCX01 • CCX01 • X2 • X0
p26 = by-assoc-and (under (ε) (CCX01 • CCX01 • X2 • X0) B18.proved) Eq.refl Eq.refl

p27 : X0 • X2 • CCX01 • CCX01 • X2 • X0 ≈ X0 • X2 • X2 • X0
p27 = by-assoc-and (under (X0 • X2) (X2 • X0) B11.proved) Eq.refl Eq.refl

p28 : X0 • X2 • X2 • X0 ≈ X0 • X0
p28 = by-assoc-and (under (X0) (X0) B4.proved) Eq.refl Eq.refl

p29 : X0 • X0 ≈ ε
p29 = by-assoc-and (under (ε) (ε) B12.proved) Eq.refl Eq.refl

p30 : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ ε
p30 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (trans p24 (trans p25 (trans p26 (trans p27 (trans p28 (trans p29 (refl))))))))))))))))))))))))))))))

p31 : ε ≈ ε
p31 = refl

proved : X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 • X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0 ≈ ε
proved = trans p30 (sym p31)
