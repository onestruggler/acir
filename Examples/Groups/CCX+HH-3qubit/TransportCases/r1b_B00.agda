{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; _•_ ; _≈_ ; cong ; left-unit ; module GL ; move-product ; p ; refl ; right-unit ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as R083
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00630)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00635 ; module MV00636 ; module MV00637 ; module MV00638 ; module MV00639 ; module MV00640)

module r1b_ij0 where

  proved : M0 • M0 ≈ ε
  proved = GL.•-cancelʳ {g = M0 • M0} {g' = ε} {h = p (ε)}
    (trans (sym (move-product MV00635.proved (MV00635.proved))) (trans (cong refl R083.proved) (trans right-unit (sym left-unit))))

module r1b_ij1 where

  proved : M1 • M1 ≈ ε
  proved = GL.•-cancelʳ {g = M1 • M1} {g' = ε} {h = p (s0)}
    (trans (sym (move-product MV00000.proved (MV00000.proved))) (trans (cong refl R083.proved) (trans right-unit (sym left-unit))))

module r1b_ij2 where

  proved : M2 • M2 ≈ ε
  proved = GL.•-cancelʳ {g = M2 • M2} {g' = ε} {h = p (s1 • s0)}
    (trans (sym (move-product MV00636.proved (MV00636.proved))) (trans (cong refl R083.proved) (trans right-unit (sym left-unit))))

module r1b_ij3 where

  proved : M3 • M3 ≈ ε
  proved = GL.•-cancelʳ {g = M3 • M3} {g' = ε} {h = p (s2 • s1 • s0)}
    (trans (sym (move-product MV00630.proved (MV00630.proved))) (trans (cong refl R083.proved) (trans right-unit (sym left-unit))))

module r1b_ij4 where

  proved : M4 • M4 ≈ ε
  proved = GL.•-cancelʳ {g = M4 • M4} {g' = ε} {h = p (s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00637.proved (MV00637.proved))) (trans (cong refl R083.proved) (trans right-unit (sym left-unit))))

module r1b_ij5 where

  proved : M5 • M5 ≈ ε
  proved = GL.•-cancelʳ {g = M5 • M5} {g' = ε} {h = p (s4 • s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00638.proved (MV00638.proved))) (trans (cong refl R083.proved) (trans right-unit (sym left-unit))))

module r1b_ij6 where

  proved : M6 • M6 ≈ ε
  proved = GL.•-cancelʳ {g = M6 • M6} {g' = ε} {h = p (s5 • s4 • s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00639.proved (MV00639.proved))) (trans (cong refl R083.proved) (trans right-unit (sym left-unit))))

module r1b_ij7 where

  proved : M7 • M7 ≈ ε
  proved = GL.•-cancelʳ {g = M7 • M7} {g' = ε} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00640.proved (MV00640.proved))) (trans (cong refl R083.proved) (trans right-unit (sym left-unit))))
