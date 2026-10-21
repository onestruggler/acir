{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameWords where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL

M0 : Word Gen
M0 = p (ε) • m0 • p (ε)

M1 : Word Gen
M1 = p (s0) • m0 • p (s0)

M2 : Word Gen
M2 = p (s0 • s1 • s0) • m0 • p (s0 • s1 • s0)

M3 : Word Gen
M3 = p (s0 • s1 • s2 • s1 • s0) • m0 • p (s0 • s1 • s2 • s1 • s0)

M4 : Word Gen
M4 = p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)

M5 : Word Gen
M5 = p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)

M6 : Word Gen
M6 = p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)

M7 : Word Gen
M7 = p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)

X01 : Word Gen
X01 = p (s0)

X02 : Word Gen
X02 = p (s0 • s1 • s0)

X03 : Word Gen
X03 = p (s0 • s1 • s2 • s1 • s0)

X04 : Word Gen
X04 = p (s0 • s1 • s2 • s3 • s2 • s1 • s0)

X05 : Word Gen
X05 = p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)

X06 : Word Gen
X06 = p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)

X07 : Word Gen
X07 = p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)

X12 : Word Gen
X12 = p (s1)

X13 : Word Gen
X13 = p (s1 • s2 • s1)

X14 : Word Gen
X14 = p (s1 • s2 • s3 • s2 • s1)

X15 : Word Gen
X15 = p (s1 • s2 • s3 • s4 • s3 • s2 • s1)

X16 : Word Gen
X16 = p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)

X17 : Word Gen
X17 = p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)

X23 : Word Gen
X23 = p (s2)

X24 : Word Gen
X24 = p (s2 • s3 • s2)

X25 : Word Gen
X25 = p (s2 • s3 • s4 • s3 • s2)

X26 : Word Gen
X26 = p (s2 • s3 • s4 • s5 • s4 • s3 • s2)

X27 : Word Gen
X27 = p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)

X34 : Word Gen
X34 = p (s3)

X35 : Word Gen
X35 = p (s3 • s4 • s3)

X36 : Word Gen
X36 = p (s3 • s4 • s5 • s4 • s3)

X37 : Word Gen
X37 = p (s3 • s4 • s5 • s6 • s5 • s4 • s3)

X45 : Word Gen
X45 = p (s4)

X46 : Word Gen
X46 = p (s4 • s5 • s4)

X47 : Word Gen
X47 = p (s4 • s5 • s6 • s5 • s4)

X56 : Word Gen
X56 = p (s5)

X57 : Word Gen
X57 = p (s5 • s6 • s5)

X67 : Word Gen
X67 = p (s6)

K0123 : Word Gen
K0123 = p (ε) • NK • p (ε)

K0124 : Word Gen
K0124 = p (s3) • NK • p (s3)

K0125 : Word Gen
K0125 = p (s3 • s4 • s3) • NK • p (s3 • s4 • s3)

K0126 : Word Gen
K0126 = p (s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3)

K0127 : Word Gen
K0127 = p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)

K0134 : Word Gen
K0134 = p (s2 • s3) • NK • p (s3 • s2)

K0135 : Word Gen
K0135 = p (s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2)

K0136 : Word Gen
K0136 = p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2)

K0137 : Word Gen
K0137 = p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)

K0145 : Word Gen
K0145 = p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2)

K0146 : Word Gen
K0146 = p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)

K0147 : Word Gen
K0147 = p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)

K0156 : Word Gen
K0156 = p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)

K0157 : Word Gen
K0157 = p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)

K0167 : Word Gen
K0167 = p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)

K0234 : Word Gen
K0234 = p (s1 • s2 • s3) • NK • p (s3 • s2 • s1)

K0235 : Word Gen
K0235 = p (s1 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s1)

K0236 : Word Gen
K0236 = p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)

K0237 : Word Gen
K0237 = p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)

K0245 : Word Gen
K0245 = p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)

K0246 : Word Gen
K0246 = p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)

K0247 : Word Gen
K0247 = p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)

K0256 : Word Gen
K0256 = p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1)

K0257 : Word Gen
K0257 = p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1)

K0267 : Word Gen
K0267 = p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)

K0345 : Word Gen
K0345 = p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)

K0346 : Word Gen
K0346 = p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)

K0347 : Word Gen
K0347 = p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)

K0356 : Word Gen
K0356 = p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1)

K0357 : Word Gen
K0357 = p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1)

K0367 : Word Gen
K0367 = p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1)

K0456 : Word Gen
K0456 = p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)

K0457 : Word Gen
K0457 = p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)

K0467 : Word Gen
K0467 = p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)

K0567 : Word Gen
K0567 = p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)

K1234 : Word Gen
K1234 = p (s0 • s1 • s2 • s3) • NK • p (s3 • s2 • s1 • s0)

K1235 : Word Gen
K1235 = p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s1 • s0)

K1236 : Word Gen
K1236 = p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)

K1237 : Word Gen
K1237 = p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)

K1245 : Word Gen
K1245 = p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)

K1246 : Word Gen
K1246 = p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)

K1247 : Word Gen
K1247 = p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)

K1256 : Word Gen
K1256 = p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)

K1257 : Word Gen
K1257 = p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)

K1267 : Word Gen
K1267 = p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)

K1345 : Word Gen
K1345 = p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)

K1346 : Word Gen
K1346 = p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)

K1347 : Word Gen
K1347 = p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)

K1356 : Word Gen
K1356 = p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0)

K1357 : Word Gen
K1357 = p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0)

K1367 : Word Gen
K1367 = p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1 • s0)

K1456 : Word Gen
K1456 = p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)

K1457 : Word Gen
K1457 = p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)

K1467 : Word Gen
K1467 = p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)

K1567 : Word Gen
K1567 = p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)

K2345 : Word Gen
K2345 = p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)

K2346 : Word Gen
K2346 = p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)

K2347 : Word Gen
K2347 = p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)

K2356 : Word Gen
K2356 = p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)

K2357 : Word Gen
K2357 = p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)

K2367 : Word Gen
K2367 = p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)

K2456 : Word Gen
K2456 = p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s0)

K2457 : Word Gen
K2457 = p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s0)

K2467 : Word Gen
K2467 = p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s0)

K2567 : Word Gen
K2567 = p (s0 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s0)

K3456 : Word Gen
K3456 = p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)

K3457 : Word Gen
K3457 = p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)

K3467 : Word Gen
K3467 = p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)

K3567 : Word Gen
K3567 = p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)

K4567 : Word Gen
K4567 = p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)

-- The Coxeter words of the generators as tables: dM, dX and dK are
-- uniform in them, and agree with the words above.

fM : Fin 8 → PWord
fM (zero) = ε
fM (suc (zero)) = s0
fM (suc (suc (zero))) = s0 • s1 • s0
fM (suc (suc (suc (zero)))) = s0 • s1 • s2 • s1 • s0
fM (suc (suc (suc (suc (zero))))) = s0 • s1 • s2 • s3 • s2 • s1 • s0
fM (suc (suc (suc (suc (suc (zero)))))) = s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0
fM (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0
fM (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0

fX : Fin 8 → Fin 8 → PWord
fX (zero) (suc (zero)) = s0
fX (zero) (suc (suc (zero))) = s0 • s1 • s0
fX (zero) (suc (suc (suc (zero)))) = s0 • s1 • s2 • s1 • s0
fX (zero) (suc (suc (suc (suc (zero))))) = s0 • s1 • s2 • s3 • s2 • s1 • s0
fX (zero) (suc (suc (suc (suc (suc (zero)))))) = s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0
fX (zero) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0
fX (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0
fX (suc (zero)) (suc (suc (zero))) = s1
fX (suc (zero)) (suc (suc (suc (zero)))) = s1 • s2 • s1
fX (suc (zero)) (suc (suc (suc (suc (zero))))) = s1 • s2 • s3 • s2 • s1
fX (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) = s1 • s2 • s3 • s4 • s3 • s2 • s1
fX (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) = s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1
fX (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1
fX (suc (suc (zero))) (suc (suc (suc (zero)))) = s2
fX (suc (suc (zero))) (suc (suc (suc (suc (zero))))) = s2 • s3 • s2
fX (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) = s2 • s3 • s4 • s3 • s2
fX (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) = s2 • s3 • s4 • s5 • s4 • s3 • s2
fX (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2
fX (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) = s3
fX (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3
fX (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3
fX (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3
fX (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s4
fX (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s4 • s5 • s4
fX (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s4 • s5 • s6 • s5 • s4
fX (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s5
fX (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s5 • s6 • s5
fX (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s6
fX _ _ = ε

fK : Fin 8 → Fin 8 → Fin 8 → Fin 8 → PWord
fK (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) = ε
fK (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) = s3
fK (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) = s2 • s3
fK (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) = s2 • s3 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) = s2 • s3 • s4 • s5 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s2 • s3 • s2 • s3 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) = s1 • s2 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) = s1 • s2 • s3 • s4 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) = s1 • s2 • s3 • s4 • s5 • s4 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s1 • s2 • s3 • s2 • s3 • s4 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3
fK (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) = s0 • s1 • s2 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) = s0 • s1 • s2 • s3 • s4 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3
fK (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3
fK (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3
fK _ _ _ _ = ε

fK′ : Fin 8 → Fin 8 → Fin 8 → Fin 8 → PWord
fK′ (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) = ε
fK′ (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) = s3
fK′ (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3
fK′ (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3
fK′ (zero) (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3
fK′ (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) = s3 • s2
fK′ (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3 • s2
fK′ (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2
fK′ (zero) (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2
fK′ (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3 • s2 • s3 • s2
fK′ (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2
fK′ (zero) (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2
fK′ (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2
fK′ (zero) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2
fK′ (zero) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) = s3 • s2 • s1
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3 • s2 • s1
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s1
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3 • s2 • s3 • s2 • s1
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1
fK′ (zero) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1
fK′ (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1
fK′ (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1
fK′ (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1
fK′ (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1
fK′ (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1
fK′ (zero) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1
fK′ (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1
fK′ (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1
fK′ (zero) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1
fK′ (zero) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) = s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0
fK′ (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) = s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s0
fK′ (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) = s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0
fK′ (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0
fK′ (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0
fK′ (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0
fK′ (suc (suc (suc (suc (zero))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0
fK′ _ _ _ _ = ε

dM : Fin 8 → Word Gen
dM a = p (fM a) • m0 • p (fM a)

dX : Fin 8 → Fin 8 → Word Gen
dX a b = p (fX a b)

dK : Fin 8 → Fin 8 → Fin 8 → Fin 8 → Word Gen
dK a b c d = p (fK a b c d) • NK • p (fK′ a b c d)

decode : TL.Gen 8 → Word Gen
decode (TL.M-gen a) = dM a
decode (TL.X-gen a b _) = dX a b
decode (TL.K-gen a b c d _ _ _) = dK a b c d
