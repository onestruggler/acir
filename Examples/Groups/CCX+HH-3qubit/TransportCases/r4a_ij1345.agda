{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; M3 ; M5 ; X13 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00685 as MV00685
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02731 as MV02731
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02732 as MV02732
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02733 as MV02733
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02734 as MV02734
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X13 • K1345 ≈ K1345 • X35 • M3 • M5
proved = GL.•-cancelʳ {g = X13 • K1345} {g' = K1345 • X35 • M3 • M5} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02731.proved (MV00685.proved))) (trans (cong refl Base.proved) (move-product MV00685.proved (move-product MV02732.proved (move-product MV02733.proved (MV02734.proved))))))
