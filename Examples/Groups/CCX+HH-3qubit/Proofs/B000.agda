{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.B000 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; K01 ; SWAP01 ; X0 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; module Eq ; r002 ; r012 ; r013 ; r021 ; r022 ; r025 ; r028 ; refl ; sym ; trans ; under ; ε)
open K

module KB0001 where

  p0 : CX01 • CX01 ≈ ε
  p0 = by-assoc-and (axiom r022) Eq.refl Eq.refl

  p1 : CX01 • CX01 ≈ CX01 • CX01
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : CX01 • CX01 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : CX01 • CX01 ≈ ε
  proved = p3

module KB0000 where

  p0 : X0 • X0 ≈ ε
  p0 = by-assoc-and (axiom r021) Eq.refl Eq.refl

  p1 : X0 • X0 ≈ X0 • X0
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : X0 • X0 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : X0 • X0 ≈ ε
  proved = p3

module KB0233 where

  p0 : X1 ≈ CX01 • X0 • CX01 • X0
  p0 = by-assoc-and (axiom r002) Eq.refl Eq.refl

  p1 : X1 ≈ X1
  p1 = refl

  p2 : CX01 • X0 • CX01 • X0 ≈ CX01 • X0 • CX01 • X0
  p2 = refl

  p3 : X1 ≈ CX01 • X0 • CX01 • X0
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX01 • X0 • CX01 • X0 ≈ X1
  p4 = sym p3

  proved : CX01 • X0 • CX01 • X0 ≈ X1
  proved = p4

module KB0234 where

  p0 : CX01 • X0 • CX01 • X0 • X0 ≈ X1 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0233.proved) Eq.refl Eq.refl

  p1 : CX01 • X0 • CX01 • X0 • X0 ≈ CX01 • X0 • CX01
  p1 = by-assoc-and (under (CX01 • X0 • CX01) (ε) KB0000.proved) Eq.refl Eq.refl

  p2 : X1 • X0 ≈ CX01 • X0 • CX01
  p2 = trans (sym p0) p1

  p3 : X1 • X0 ≈ X1 • X0
  p3 = refl

  p4 : CX01 • X0 • CX01 ≈ CX01 • X0 • CX01
  p4 = refl

  p5 : X1 • X0 ≈ CX01 • X0 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX01 • X0 • CX01 ≈ X1 • X0
  p6 = sym p5

  proved : CX01 • X0 • CX01 ≈ X1 • X0
  proved = p6

module KB0029 where

  p0 : SWAP01 ≈ CX01 • CX10 • CX01
  p0 = by-assoc-and (axiom r013) Eq.refl Eq.refl

  p1 : SWAP01 ≈ SWAP01
  p1 = refl

  p2 : CX01 • CX10 • CX01 ≈ CX01 • CX10 • CX01
  p2 = refl

  p3 : SWAP01 ≈ CX01 • CX10 • CX01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : CX01 • CX10 • CX01 ≈ SWAP01
  p4 = sym p3

  proved : CX01 • CX10 • CX01 ≈ SWAP01
  proved = p4

module KB0030 where

  p0 : CX01 • CX01 • CX10 • CX01 ≈ CX01 • SWAP01
  p0 = by-assoc-and (under (CX01) (ε) KB0029.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • CX10 • CX01 ≈ CX10 • CX01
  p1 = by-assoc-and (under (ε) (CX10 • CX01) KB0001.proved) Eq.refl Eq.refl

  p2 : CX01 • SWAP01 ≈ CX10 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • SWAP01 ≈ CX01 • SWAP01
  p3 = refl

  p4 : CX10 • CX01 ≈ CX10 • CX01
  p4 = refl

  p5 : CX01 • SWAP01 ≈ CX10 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : CX10 • CX01 ≈ CX01 • SWAP01
  p6 = sym p5

  proved : CX10 • CX01 ≈ CX01 • SWAP01
  proved = p6

module KB0004 where

  p0 : K01 • K01 ≈ ε
  p0 = by-assoc-and (axiom r025) Eq.refl Eq.refl

  p1 : K01 • K01 ≈ K01 • K01
  p1 = refl

  p2 : ε ≈ ε
  p2 = refl

  p3 : K01 • K01 ≈ ε
  p3 = trans (sym p1) (trans p0 p2)

  proved : K01 • K01 ≈ ε
  proved = p3

module KB0026 where

  p0 : CX10 ≈ K01 • CX01 • K01
  p0 = by-assoc-and (axiom r012) Eq.refl Eq.refl

  p1 : CX10 ≈ CX10
  p1 = refl

  p2 : K01 • CX01 • K01 ≈ K01 • CX01 • K01
  p2 = refl

  p3 : CX10 ≈ K01 • CX01 • K01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : K01 • CX01 • K01 ≈ CX10
  p4 = sym p3

  proved : K01 • CX01 • K01 ≈ CX10
  proved = p4

module KB0028 where

  p0 : K01 • CX01 • K01 • K01 ≈ CX10 • K01
  p0 = by-assoc-and (under (ε) (K01) KB0026.proved) Eq.refl Eq.refl

  p1 : K01 • CX01 • K01 • K01 ≈ K01 • CX01
  p1 = by-assoc-and (under (K01 • CX01) (ε) KB0004.proved) Eq.refl Eq.refl

  p2 : CX10 • K01 ≈ K01 • CX01
  p2 = trans (sym p0) p1

  p3 : CX10 • K01 ≈ CX10 • K01
  p3 = refl

  p4 : K01 • CX01 ≈ K01 • CX01
  p4 = refl

  p5 : CX10 • K01 ≈ K01 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  p6 : K01 • CX01 ≈ CX10 • K01
  p6 = sym p5

  proved : K01 • CX01 ≈ CX10 • K01
  proved = p6

module KB0052 where

  p0 : K01 • CX01 • CX01 ≈ CX10 • K01 • CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0028.proved) Eq.refl Eq.refl

  p1 : K01 • CX01 • CX01 ≈ K01
  p1 = by-assoc-and (under (K01) (ε) KB0001.proved) Eq.refl Eq.refl

  p2 : CX10 • K01 • CX01 ≈ K01
  p2 = trans (sym p0) p1

  p3 : CX10 • K01 • CX01 ≈ CX10 • CX10 • K01
  p3 = by-assoc-and (under (CX10) (ε) KB0028.proved) Eq.refl Eq.refl

  p4 : CX10 • K01 • CX01 ≈ CX10 • CX10 • K01
  p4 = trans p3 (refl)

  p5 : K01 ≈ K01
  p5 = refl

  p6 : CX10 • CX10 • K01 ≈ K01
  p6 = trans (sym p4) (trans p2 p5)

  proved : CX10 • CX10 • K01 ≈ K01
  proved = p6

module KB0053 where

  p0 : CX10 • CX10 • K01 • K01 ≈ K01 • K01
  p0 = by-assoc-and (under (ε) (K01) KB0052.proved) Eq.refl Eq.refl

  p1 : CX10 • CX10 • K01 • K01 ≈ CX10 • CX10
  p1 = by-assoc-and (under (CX10 • CX10) (ε) KB0004.proved) Eq.refl Eq.refl

  p2 : K01 • K01 ≈ CX10 • CX10
  p2 = trans (sym p0) p1

  p3 : K01 • K01 ≈ ε
  p3 = by-assoc-and (under (ε) (ε) KB0004.proved) Eq.refl Eq.refl

  p4 : K01 • K01 ≈ ε
  p4 = trans p3 (refl)

  p5 : CX10 • CX10 ≈ CX10 • CX10
  p5 = refl

  p6 : ε ≈ CX10 • CX10
  p6 = trans (sym p4) (trans p2 p5)

  p7 : CX10 • CX10 ≈ ε
  p7 = sym p6

  proved : CX10 • CX10 ≈ ε
  proved = p7

module KB0056 where

  p0 : CX10 • CX10 • CX01 ≈ CX01
  p0 = by-assoc-and (under (ε) (CX01) KB0053.proved) Eq.refl Eq.refl

  p1 : CX10 • CX10 • CX01 ≈ CX10 • CX01 • SWAP01
  p1 = by-assoc-and (under (CX10) (ε) KB0030.proved) Eq.refl Eq.refl

  p2 : CX01 ≈ CX10 • CX01 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CX01 ≈ CX01
  p3 = refl

  p4 : CX10 • CX01 • SWAP01 ≈ CX01 • SWAP01 • SWAP01
  p4 = by-assoc-and (under (ε) (SWAP01) KB0030.proved) Eq.refl Eq.refl

  p5 : CX10 • CX01 • SWAP01 ≈ CX01 • SWAP01 • SWAP01
  p5 = trans p4 (refl)

  p6 : CX01 ≈ CX01 • SWAP01 • SWAP01
  p6 = trans (sym p3) (trans p2 p5)

  p7 : CX01 • SWAP01 • SWAP01 ≈ CX01
  p7 = sym p6

  proved : CX01 • SWAP01 • SWAP01 ≈ CX01
  proved = p7

module KB0057 where

  p0 : CX01 • CX01 • SWAP01 • SWAP01 ≈ CX01 • CX01
  p0 = by-assoc-and (under (CX01) (ε) KB0056.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01
  p1 = by-assoc-and (under (ε) (SWAP01 • SWAP01) KB0001.proved) Eq.refl Eq.refl

  p2 : CX01 • CX01 ≈ SWAP01 • SWAP01
  p2 = trans (sym p0) p1

  p3 : CX01 • CX01 ≈ ε
  p3 = by-assoc-and (under (ε) (ε) KB0001.proved) Eq.refl Eq.refl

  p4 : CX01 • CX01 ≈ ε
  p4 = trans p3 (refl)

  p5 : SWAP01 • SWAP01 ≈ SWAP01 • SWAP01
  p5 = refl

  p6 : ε ≈ SWAP01 • SWAP01
  p6 = trans (sym p4) (trans p2 p5)

  p7 : SWAP01 • SWAP01 ≈ ε
  p7 = sym p6

  proved : SWAP01 • SWAP01 ≈ ε
  proved = p7

module KB0040 where

  p0 : X1 ≈ SWAP01 • X0 • SWAP01
  p0 = by-assoc-and (axiom r028) Eq.refl Eq.refl

  p1 : X1 ≈ X1
  p1 = refl

  p2 : SWAP01 • X0 • SWAP01 ≈ SWAP01 • X0 • SWAP01
  p2 = refl

  p3 : X1 ≈ SWAP01 • X0 • SWAP01
  p3 = trans (sym p1) (trans p0 p2)

  p4 : SWAP01 • X0 • SWAP01 ≈ X1
  p4 = sym p3

  proved : SWAP01 • X0 • SWAP01 ≈ X1
  proved = p4

module KB0062 where

  p0 : SWAP01 • X0 • SWAP01 • SWAP01 ≈ SWAP01 • X0
  p0 = by-assoc-and (under (SWAP01 • X0) (ε) KB0057.proved) Eq.refl Eq.refl

  p1 : SWAP01 • X0 • SWAP01 • SWAP01 ≈ X1 • SWAP01
  p1 = by-assoc-and (under (ε) (SWAP01) KB0040.proved) Eq.refl Eq.refl

  p2 : SWAP01 • X0 ≈ X1 • SWAP01
  p2 = trans (sym p0) p1

  p3 : SWAP01 • X0 ≈ SWAP01 • X0
  p3 = refl

  p4 : X1 • SWAP01 ≈ X1 • SWAP01
  p4 = refl

  p5 : SWAP01 • X0 ≈ X1 • SWAP01
  p5 = trans (sym p3) (trans p2 p4)

  proved : SWAP01 • X0 ≈ X1 • SWAP01
  proved = p5

module KB0073 where

  p0 : SWAP01 • X0 • X0 ≈ X1 • SWAP01 • X0
  p0 = by-assoc-and (under (ε) (X0) KB0062.proved) Eq.refl Eq.refl

  p1 : SWAP01 • X0 • X0 ≈ SWAP01
  p1 = by-assoc-and (under (SWAP01) (ε) KB0000.proved) Eq.refl Eq.refl

  p2 : X1 • SWAP01 • X0 ≈ SWAP01
  p2 = trans (sym p0) p1

  p3 : X1 • SWAP01 • X0 ≈ X1 • X1 • SWAP01
  p3 = by-assoc-and (under (X1) (ε) KB0062.proved) Eq.refl Eq.refl

  p4 : X1 • SWAP01 • X0 ≈ X1 • X1 • SWAP01
  p4 = trans p3 (refl)

  p5 : SWAP01 ≈ SWAP01
  p5 = refl

  p6 : X1 • X1 • SWAP01 ≈ SWAP01
  p6 = trans (sym p4) (trans p2 p5)

  proved : X1 • X1 • SWAP01 ≈ SWAP01
  proved = p6

module KB0074 where

  p0 : X1 • X1 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01
  p0 = by-assoc-and (under (ε) (SWAP01) KB0073.proved) Eq.refl Eq.refl

  p1 : X1 • X1 • SWAP01 • SWAP01 ≈ X1 • X1
  p1 = by-assoc-and (under (X1 • X1) (ε) KB0057.proved) Eq.refl Eq.refl

  p2 : SWAP01 • SWAP01 ≈ X1 • X1
  p2 = trans (sym p0) p1

  p3 : SWAP01 • SWAP01 ≈ ε
  p3 = by-assoc-and (under (ε) (ε) KB0057.proved) Eq.refl Eq.refl

  p4 : SWAP01 • SWAP01 ≈ ε
  p4 = trans p3 (refl)

  p5 : X1 • X1 ≈ X1 • X1
  p5 = refl

  p6 : ε ≈ X1 • X1
  p6 = trans (sym p4) (trans p2 p5)

  p7 : X1 • X1 ≈ ε
  p7 = sym p6

  proved : X1 • X1 ≈ ε
  proved = p7

module KB0235 where

  p0 : CX01 • CX01 • X0 • CX01 • X0 ≈ CX01 • X1
  p0 = by-assoc-and (under (CX01) (ε) KB0233.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • X0 • CX01 • X0 ≈ X0 • CX01 • X0
  p1 = by-assoc-and (under (ε) (X0 • CX01 • X0) KB0001.proved) Eq.refl Eq.refl

  p2 : CX01 • X1 ≈ X0 • CX01 • X0
  p2 = trans (sym p0) p1

  p3 : CX01 • X1 ≈ CX01 • X1
  p3 = refl

  p4 : X0 • CX01 • X0 ≈ X0 • CX01 • X0
  p4 = refl

  p5 : CX01 • X1 ≈ X0 • CX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  p6 : X0 • CX01 • X0 ≈ CX01 • X1
  p6 = sym p5

  proved : X0 • CX01 • X0 ≈ CX01 • X1
  proved = p6

module KB0238 where

  p0 : X0 • X0 • CX01 • X0 ≈ X0 • CX01 • X1
  p0 = by-assoc-and (under (X0) (ε) KB0235.proved) Eq.refl Eq.refl

  p1 : X0 • X0 • CX01 • X0 ≈ CX01 • X0
  p1 = by-assoc-and (under (ε) (CX01 • X0) KB0000.proved) Eq.refl Eq.refl

  p2 : X0 • CX01 • X1 ≈ CX01 • X0
  p2 = trans (sym p0) p1

  p3 : X0 • CX01 • X1 ≈ X0 • CX01 • X1
  p3 = refl

  p4 : CX01 • X0 ≈ CX01 • X0
  p4 = refl

  p5 : X0 • CX01 • X1 ≈ CX01 • X0
  p5 = trans (sym p3) (trans p2 p4)

  proved : X0 • CX01 • X1 ≈ CX01 • X0
  proved = p5

module KB0240 where

  p0 : X0 • CX01 • X1 • X1 ≈ CX01 • X0 • X1
  p0 = by-assoc-and (under (ε) (X1) KB0238.proved) Eq.refl Eq.refl

  p1 : X0 • CX01 • X1 • X1 ≈ X0 • CX01
  p1 = by-assoc-and (under (X0 • CX01) (ε) KB0074.proved) Eq.refl Eq.refl

  p2 : CX01 • X0 • X1 ≈ X0 • CX01
  p2 = trans (sym p0) p1

  p3 : CX01 • X0 • X1 ≈ CX01 • X0 • X1
  p3 = refl

  p4 : X0 • CX01 ≈ X0 • CX01
  p4 = refl

  p5 : CX01 • X0 • X1 ≈ X0 • CX01
  p5 = trans (sym p3) (trans p2 p4)

  proved : CX01 • X0 • X1 ≈ X0 • CX01
  proved = p5

module KB0242 where

  p0 : CX01 • CX01 • X0 • X1 ≈ CX01 • X0 • CX01
  p0 = by-assoc-and (under (CX01) (ε) KB0240.proved) Eq.refl Eq.refl

  p1 : CX01 • CX01 • X0 • X1 ≈ X0 • X1
  p1 = by-assoc-and (under (ε) (X0 • X1) KB0001.proved) Eq.refl Eq.refl

  p2 : CX01 • X0 • CX01 ≈ X0 • X1
  p2 = trans (sym p0) p1

  p3 : CX01 • X0 • CX01 ≈ X1 • X0
  p3 = by-assoc-and (under (ε) (ε) KB0234.proved) Eq.refl Eq.refl

  p4 : CX01 • X0 • CX01 ≈ X1 • X0
  p4 = trans p3 (refl)

  p5 : X0 • X1 ≈ X0 • X1
  p5 = refl

  p6 : X1 • X0 ≈ X0 • X1
  p6 = trans (sym p4) (trans p2 p5)

  proved : X1 • X0 ≈ X0 • X1
  proved = p6

module X0X1 where

  p0 : X0 • X1 ≈ X0 • X1
  p0 = refl

  p1 : X1 • X0 ≈ X0 • X1
  p1 = by-assoc-and (under (ε) (ε) KB0242.proved) Eq.refl Eq.refl

  p2 : X1 • X0 ≈ X0 • X1
  p2 = trans p1 (refl)

  proved : X0 • X1 ≈ X1 • X0
  proved = trans p0 (sym p2)
