{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij013467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; K0136 ; K1467 ; K3467 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01778 as MV01778
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03065 as MV03065
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03066 as MV03066
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03067 as MV03067
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0134 • K1467 ≈ K3467 • K0136
proved = GL.•-cancelʳ {g = K0134 • K1467} {g' = K3467 • K0136} {h = p (s2 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01778.proved (MV03065.proved))) (trans (cong refl Base.proved) (move-product MV03066.proved (MV03067.proved))))
