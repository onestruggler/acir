{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij670 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01022 as MV01022
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01023 as MV01023
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X67 • M0 ≈ M0 • X67
proved = GL.•-cancelʳ {g = X67 • M0} {g' = M0 • X67} {h = p (s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01022.proved (MV01023.proved))) (trans (cong refl Base.proved) (move-product MV01023.proved (MV01022.proved))))
