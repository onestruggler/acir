{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01629 as MV01629
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01630 as MV01630
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0136 ≈ K0136 • X45
proved = GL.•-cancelʳ {g = X45 • K0136} {g' = K0136 • X45} {h = p (s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01629.proved (MV01630.proved))) (trans (cong refl Base.proved) (move-product MV01630.proved (MV01629.proved))))
