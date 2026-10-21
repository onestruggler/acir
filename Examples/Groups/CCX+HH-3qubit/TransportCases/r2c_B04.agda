{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_B04 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0456 ; K0457 ; K0467 ; K0567 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1456 ; K1457 ; K1467 ; K1567 ; K2467 ; K2567 ; K3456 ; K3457 ; X26 ; X27 ; X34 ; X35 ; X36 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00209)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00642 ; module MV00643)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00644)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B038 using (module MV01455 ; module MV01456 ; module MV01457 ; module MV01458 ; module MV01459 ; module MV01460 ; module MV01461 ; module MV01462 ; module MV01463)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B039 using (module MV01464 ; module MV01465 ; module MV01466 ; module MV01467 ; module MV01468 ; module MV01469 ; module MV01470 ; module MV01471 ; module MV01472 ; module MV01473 ; module MV01474 ; module MV01475 ; module MV01476 ; module MV01477 ; module MV01478 ; module MV01479 ; module MV01480 ; module MV01481 ; module MV01482 ; module MV01483 ; module MV01484 ; module MV01485 ; module MV01486 ; module MV01487 ; module MV01488 ; module MV01489 ; module MV01490 ; module MV01491 ; module MV01492 ; module MV01493 ; module MV01494 ; module MV01495 ; module MV01496 ; module MV01497 ; module MV01498 ; module MV01499 ; module MV01500)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B040 using (module MV01501 ; module MV01502 ; module MV01503 ; module MV01504 ; module MV01505 ; module MV01506 ; module MV01507 ; module MV01508 ; module MV01509 ; module MV01510 ; module MV01511 ; module MV01512 ; module MV01513 ; module MV01514 ; module MV01515 ; module MV01516 ; module MV01517 ; module MV01518 ; module MV01519 ; module MV01520 ; module MV01521 ; module MV01522 ; module MV01523 ; module MV01524 ; module MV01525 ; module MV01526 ; module MV01527 ; module MV01528 ; module MV01529 ; module MV01530 ; module MV01531 ; module MV01532 ; module MV01533 ; module MV01534)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B041 using (module MV01535 ; module MV01536 ; module MV01537 ; module MV01538 ; module MV01539 ; module MV01540 ; module MV01541 ; module MV01542 ; module MV01543 ; module MV01544 ; module MV01545 ; module MV01546 ; module MV01547 ; module MV01548 ; module MV01549 ; module MV01550 ; module MV01551 ; module MV01552 ; module MV01553 ; module MV01554 ; module MV01555 ; module MV01556 ; module MV01557 ; module MV01558 ; module MV01559 ; module MV01560 ; module MV01561 ; module MV01562 ; module MV01563 ; module MV01564 ; module MV01565 ; module MV01566 ; module MV01567 ; module MV01568 ; module MV01569 ; module MV01570 ; module MV01571)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R091)

module r2c_ij260145 where

  proved : X26 • K0145 ≈ K0145 • X26
  proved = GL.•-cancelʳ {g = X26 • K0145} {g' = K0145 • X26} {h = p (s3 • s2 • s4 • s3 • s5)}
    (trans (sym (move-product MV01455.proved (MV01456.proved))) (trans (cong refl R091.proved) (move-product MV01456.proved (MV01455.proved))))

module r2c_ij260147 where

  proved : X26 • K0147 ≈ K0147 • X26
  proved = GL.•-cancelʳ {g = X26 • K0147} {g' = K0147 • X26} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01457.proved (MV01458.proved))) (trans (cong refl R091.proved) (move-product MV01458.proved (MV01457.proved))))

module r2c_ij260157 where

  proved : X26 • K0157 ≈ K0157 • X26
  proved = GL.•-cancelʳ {g = X26 • K0157} {g' = K0157 • X26} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01459.proved (MV01460.proved))) (trans (cong refl R091.proved) (move-product MV01460.proved (MV01459.proved))))

module r2c_ij260345 where

  proved : X26 • K0345 ≈ K0345 • X26
  proved = GL.•-cancelʳ {g = X26 • K0345} {g' = K0345 • X26} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01461.proved (MV01462.proved))) (trans (cong refl R091.proved) (move-product MV01462.proved (MV01461.proved))))

module r2c_ij260347 where

  proved : X26 • K0347 ≈ K0347 • X26
  proved = GL.•-cancelʳ {g = X26 • K0347} {g' = K0347 • X26} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01463.proved (MV01464.proved))) (trans (cong refl R091.proved) (move-product MV01464.proved (MV01463.proved))))

module r2c_ij260357 where

  proved : X26 • K0357 ≈ K0357 • X26
  proved = GL.•-cancelʳ {g = X26 • K0357} {g' = K0357 • X26} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01465.proved (MV01466.proved))) (trans (cong refl R091.proved) (move-product MV01466.proved (MV01465.proved))))

module r2c_ij260457 where

  proved : X26 • K0457 ≈ K0457 • X26
  proved = GL.•-cancelʳ {g = X26 • K0457} {g' = K0457 • X26} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01467.proved (MV01468.proved))) (trans (cong refl R091.proved) (move-product MV01468.proved (MV01467.proved))))

module r2c_ij261345 where

  proved : X26 • K1345 ≈ K1345 • X26
  proved = GL.•-cancelʳ {g = X26 • K1345} {g' = K1345 • X26} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01469.proved (MV01470.proved))) (trans (cong refl R091.proved) (move-product MV01470.proved (MV01469.proved))))

module r2c_ij261347 where

  proved : X26 • K1347 ≈ K1347 • X26
  proved = GL.•-cancelʳ {g = X26 • K1347} {g' = K1347 • X26} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01471.proved (MV01472.proved))) (trans (cong refl R091.proved) (move-product MV01472.proved (MV01471.proved))))

module r2c_ij261357 where

  proved : X26 • K1357 ≈ K1357 • X26
  proved = GL.•-cancelʳ {g = X26 • K1357} {g' = K1357 • X26} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01473.proved (MV01474.proved))) (trans (cong refl R091.proved) (move-product MV01474.proved (MV01473.proved))))

module r2c_ij261457 where

  proved : X26 • K1457 ≈ K1457 • X26
  proved = GL.•-cancelʳ {g = X26 • K1457} {g' = K1457 • X26} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01475.proved (MV01476.proved))) (trans (cong refl R091.proved) (move-product MV01476.proved (MV01475.proved))))

module r2c_ij263457 where

  proved : X26 • K3457 ≈ K3457 • X26
  proved = GL.•-cancelʳ {g = X26 • K3457} {g' = K3457 • X26} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01477.proved (MV01478.proved))) (trans (cong refl R091.proved) (move-product MV01478.proved (MV01477.proved))))

module r2c_ij270134 where

  proved : X27 • K0134 ≈ K0134 • X27
  proved = GL.•-cancelʳ {g = X27 • K0134} {g' = K0134 • X27} {h = p (s2 • s3 • s6 • s5)}
    (trans (sym (move-product MV01479.proved (MV01480.proved))) (trans (cong refl R091.proved) (move-product MV01480.proved (MV01479.proved))))

module r2c_ij270135 where

  proved : X27 • K0135 ≈ K0135 • X27
  proved = GL.•-cancelʳ {g = X27 • K0135} {g' = K0135 • X27} {h = p (s2 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01481.proved (MV01482.proved))) (trans (cong refl R091.proved) (move-product MV01482.proved (MV01481.proved))))

module r2c_ij270136 where

  proved : X27 • K0136 ≈ K0136 • X27
  proved = GL.•-cancelʳ {g = X27 • K0136} {g' = K0136 • X27} {h = p (s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01483.proved (MV01484.proved))) (trans (cong refl R091.proved) (move-product MV01484.proved (MV01483.proved))))

module r2c_ij270145 where

  proved : X27 • K0145 ≈ K0145 • X27
  proved = GL.•-cancelʳ {g = X27 • K0145} {g' = K0145 • X27} {h = p (s3 • s2 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01485.proved (MV01486.proved))) (trans (cong refl R091.proved) (move-product MV01486.proved (MV01485.proved))))

module r2c_ij270146 where

  proved : X27 • K0146 ≈ K0146 • X27
  proved = GL.•-cancelʳ {g = X27 • K0146} {g' = K0146 • X27} {h = p (s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01487.proved (MV01488.proved))) (trans (cong refl R091.proved) (move-product MV01488.proved (MV01487.proved))))

module r2c_ij270156 where

  proved : X27 • K0156 ≈ K0156 • X27
  proved = GL.•-cancelʳ {g = X27 • K0156} {g' = K0156 • X27} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01489.proved (MV01490.proved))) (trans (cong refl R091.proved) (move-product MV01490.proved (MV01489.proved))))

module r2c_ij270345 where

  proved : X27 • K0345 ≈ K0345 • X27
  proved = GL.•-cancelʳ {g = X27 • K0345} {g' = K0345 • X27} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01491.proved (MV01492.proved))) (trans (cong refl R091.proved) (move-product MV01492.proved (MV01491.proved))))

module r2c_ij270346 where

  proved : X27 • K0346 ≈ K0346 • X27
  proved = GL.•-cancelʳ {g = X27 • K0346} {g' = K0346 • X27} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01493.proved (MV01494.proved))) (trans (cong refl R091.proved) (move-product MV01494.proved (MV01493.proved))))

module r2c_ij270356 where

  proved : X27 • K0356 ≈ K0356 • X27
  proved = GL.•-cancelʳ {g = X27 • K0356} {g' = K0356 • X27} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01495.proved (MV01496.proved))) (trans (cong refl R091.proved) (move-product MV01496.proved (MV01495.proved))))

module r2c_ij270456 where

  proved : X27 • K0456 ≈ K0456 • X27
  proved = GL.•-cancelʳ {g = X27 • K0456} {g' = K0456 • X27} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01497.proved (MV01498.proved))) (trans (cong refl R091.proved) (move-product MV01498.proved (MV01497.proved))))

module r2c_ij271345 where

  proved : X27 • K1345 ≈ K1345 • X27
  proved = GL.•-cancelʳ {g = X27 • K1345} {g' = K1345 • X27} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01499.proved (MV01500.proved))) (trans (cong refl R091.proved) (move-product MV01500.proved (MV01499.proved))))

module r2c_ij271346 where

  proved : X27 • K1346 ≈ K1346 • X27
  proved = GL.•-cancelʳ {g = X27 • K1346} {g' = K1346 • X27} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01501.proved (MV01502.proved))) (trans (cong refl R091.proved) (move-product MV01502.proved (MV01501.proved))))

module r2c_ij271356 where

  proved : X27 • K1356 ≈ K1356 • X27
  proved = GL.•-cancelʳ {g = X27 • K1356} {g' = K1356 • X27} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01503.proved (MV01504.proved))) (trans (cong refl R091.proved) (move-product MV01504.proved (MV01503.proved))))

module r2c_ij271456 where

  proved : X27 • K1456 ≈ K1456 • X27
  proved = GL.•-cancelʳ {g = X27 • K1456} {g' = K1456 • X27} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01505.proved (MV01506.proved))) (trans (cong refl R091.proved) (move-product MV01506.proved (MV01505.proved))))

module r2c_ij273456 where

  proved : X27 • K3456 ≈ K3456 • X27
  proved = GL.•-cancelʳ {g = X27 • K3456} {g' = K3456 • X27} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01507.proved (MV01508.proved))) (trans (cong refl R091.proved) (move-product MV01508.proved (MV01507.proved))))

module r2c_ij340125 where

  proved : X34 • K0125 ≈ K0125 • X34
  proved = GL.•-cancelʳ {g = X34 • K0125} {g' = K0125 • X34} {h = p (s4 • s3)}
    (trans (sym (move-product MV01509.proved (MV00642.proved))) (trans (cong refl R091.proved) (move-product MV00642.proved (MV01509.proved))))

module r2c_ij340126 where

  proved : X34 • K0126 ≈ K0126 • X34
  proved = GL.•-cancelʳ {g = X34 • K0126} {g' = K0126 • X34} {h = p (s5 • s4 • s3)}
    (trans (sym (move-product MV01510.proved (MV00643.proved))) (trans (cong refl R091.proved) (move-product MV00643.proved (MV01510.proved))))

module r2c_ij340127 where

  proved : X34 • K0127 ≈ K0127 • X34
  proved = GL.•-cancelʳ {g = X34 • K0127} {g' = K0127 • X34} {h = p (s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01511.proved (MV00644.proved))) (trans (cong refl R091.proved) (move-product MV00644.proved (MV01511.proved))))

module r2c_ij340156 where

  proved : X34 • K0156 ≈ K0156 • X34
  proved = GL.•-cancelʳ {g = X34 • K0156} {g' = K0156 • X34} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01512.proved (MV01513.proved))) (trans (cong refl R091.proved) (move-product MV01513.proved (MV01512.proved))))

module r2c_ij340157 where

  proved : X34 • K0157 ≈ K0157 • X34
  proved = GL.•-cancelʳ {g = X34 • K0157} {g' = K0157 • X34} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01514.proved (MV01515.proved))) (trans (cong refl R091.proved) (move-product MV01515.proved (MV01514.proved))))

module r2c_ij340167 where

  proved : X34 • K0167 ≈ K0167 • X34
  proved = GL.•-cancelʳ {g = X34 • K0167} {g' = K0167 • X34} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01516.proved (MV01517.proved))) (trans (cong refl R091.proved) (move-product MV01517.proved (MV01516.proved))))

module r2c_ij340256 where

  proved : X34 • K0256 ≈ K0256 • X34
  proved = GL.•-cancelʳ {g = X34 • K0256} {g' = K0256 • X34} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01518.proved (MV01519.proved))) (trans (cong refl R091.proved) (move-product MV01519.proved (MV01518.proved))))

module r2c_ij340257 where

  proved : X34 • K0257 ≈ K0257 • X34
  proved = GL.•-cancelʳ {g = X34 • K0257} {g' = K0257 • X34} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01520.proved (MV01521.proved))) (trans (cong refl R091.proved) (move-product MV01521.proved (MV01520.proved))))

module r2c_ij340267 where

  proved : X34 • K0267 ≈ K0267 • X34
  proved = GL.•-cancelʳ {g = X34 • K0267} {g' = K0267 • X34} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01522.proved (MV01523.proved))) (trans (cong refl R091.proved) (move-product MV01523.proved (MV01522.proved))))

module r2c_ij340567 where

  proved : X34 • K0567 ≈ K0567 • X34
  proved = GL.•-cancelʳ {g = X34 • K0567} {g' = K0567 • X34} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01524.proved (MV01525.proved))) (trans (cong refl R091.proved) (move-product MV01525.proved (MV01524.proved))))

module r2c_ij341256 where

  proved : X34 • K1256 ≈ K1256 • X34
  proved = GL.•-cancelʳ {g = X34 • K1256} {g' = K1256 • X34} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01526.proved (MV01527.proved))) (trans (cong refl R091.proved) (move-product MV01527.proved (MV01526.proved))))

module r2c_ij341257 where

  proved : X34 • K1257 ≈ K1257 • X34
  proved = GL.•-cancelʳ {g = X34 • K1257} {g' = K1257 • X34} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01528.proved (MV01529.proved))) (trans (cong refl R091.proved) (move-product MV01529.proved (MV01528.proved))))

module r2c_ij341267 where

  proved : X34 • K1267 ≈ K1267 • X34
  proved = GL.•-cancelʳ {g = X34 • K1267} {g' = K1267 • X34} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01530.proved (MV01531.proved))) (trans (cong refl R091.proved) (move-product MV01531.proved (MV01530.proved))))

module r2c_ij341567 where

  proved : X34 • K1567 ≈ K1567 • X34
  proved = GL.•-cancelʳ {g = X34 • K1567} {g' = K1567 • X34} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01532.proved (MV01533.proved))) (trans (cong refl R091.proved) (move-product MV01533.proved (MV01532.proved))))

module r2c_ij342567 where

  proved : X34 • K2567 ≈ K2567 • X34
  proved = GL.•-cancelʳ {g = X34 • K2567} {g' = K2567 • X34} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01534.proved (MV01535.proved))) (trans (cong refl R091.proved) (move-product MV01535.proved (MV01534.proved))))

module r2c_ij350124 where

  proved : X35 • K0124 ≈ K0124 • X35
  proved = GL.•-cancelʳ {g = X35 • K0124} {g' = K0124 • X35} {h = p (s3)}
    (trans (sym (move-product MV00209.proved (MV00245.proved))) (trans (cong refl R091.proved) (move-product MV00245.proved (MV00209.proved))))

module r2c_ij350126 where

  proved : X35 • K0126 ≈ K0126 • X35
  proved = GL.•-cancelʳ {g = X35 • K0126} {g' = K0126 • X35} {h = p (s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01536.proved (MV01537.proved))) (trans (cong refl R091.proved) (move-product MV01537.proved (MV01536.proved))))

module r2c_ij350127 where

  proved : X35 • K0127 ≈ K0127 • X35
  proved = GL.•-cancelʳ {g = X35 • K0127} {g' = K0127 • X35} {h = p (s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01538.proved (MV01539.proved))) (trans (cong refl R091.proved) (move-product MV01539.proved (MV01538.proved))))

module r2c_ij350146 where

  proved : X35 • K0146 ≈ K0146 • X35
  proved = GL.•-cancelʳ {g = X35 • K0146} {g' = K0146 • X35} {h = p (s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01540.proved (MV01541.proved))) (trans (cong refl R091.proved) (move-product MV01541.proved (MV01540.proved))))

module r2c_ij350147 where

  proved : X35 • K0147 ≈ K0147 • X35
  proved = GL.•-cancelʳ {g = X35 • K0147} {g' = K0147 • X35} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01542.proved (MV01543.proved))) (trans (cong refl R091.proved) (move-product MV01543.proved (MV01542.proved))))

module r2c_ij350167 where

  proved : X35 • K0167 ≈ K0167 • X35
  proved = GL.•-cancelʳ {g = X35 • K0167} {g' = K0167 • X35} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01544.proved (MV01545.proved))) (trans (cong refl R091.proved) (move-product MV01545.proved (MV01544.proved))))

module r2c_ij350246 where

  proved : X35 • K0246 ≈ K0246 • X35
  proved = GL.•-cancelʳ {g = X35 • K0246} {g' = K0246 • X35} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01546.proved (MV01547.proved))) (trans (cong refl R091.proved) (move-product MV01547.proved (MV01546.proved))))

module r2c_ij350247 where

  proved : X35 • K0247 ≈ K0247 • X35
  proved = GL.•-cancelʳ {g = X35 • K0247} {g' = K0247 • X35} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01548.proved (MV01549.proved))) (trans (cong refl R091.proved) (move-product MV01549.proved (MV01548.proved))))

module r2c_ij350267 where

  proved : X35 • K0267 ≈ K0267 • X35
  proved = GL.•-cancelʳ {g = X35 • K0267} {g' = K0267 • X35} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01550.proved (MV01551.proved))) (trans (cong refl R091.proved) (move-product MV01551.proved (MV01550.proved))))

module r2c_ij350467 where

  proved : X35 • K0467 ≈ K0467 • X35
  proved = GL.•-cancelʳ {g = X35 • K0467} {g' = K0467 • X35} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01552.proved (MV01553.proved))) (trans (cong refl R091.proved) (move-product MV01553.proved (MV01552.proved))))

module r2c_ij351246 where

  proved : X35 • K1246 ≈ K1246 • X35
  proved = GL.•-cancelʳ {g = X35 • K1246} {g' = K1246 • X35} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01554.proved (MV01555.proved))) (trans (cong refl R091.proved) (move-product MV01555.proved (MV01554.proved))))

module r2c_ij351247 where

  proved : X35 • K1247 ≈ K1247 • X35
  proved = GL.•-cancelʳ {g = X35 • K1247} {g' = K1247 • X35} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01556.proved (MV01557.proved))) (trans (cong refl R091.proved) (move-product MV01557.proved (MV01556.proved))))

module r2c_ij351267 where

  proved : X35 • K1267 ≈ K1267 • X35
  proved = GL.•-cancelʳ {g = X35 • K1267} {g' = K1267 • X35} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01558.proved (MV01559.proved))) (trans (cong refl R091.proved) (move-product MV01559.proved (MV01558.proved))))

module r2c_ij351467 where

  proved : X35 • K1467 ≈ K1467 • X35
  proved = GL.•-cancelʳ {g = X35 • K1467} {g' = K1467 • X35} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01560.proved (MV01561.proved))) (trans (cong refl R091.proved) (move-product MV01561.proved (MV01560.proved))))

module r2c_ij352467 where

  proved : X35 • K2467 ≈ K2467 • X35
  proved = GL.•-cancelʳ {g = X35 • K2467} {g' = K2467 • X35} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01562.proved (MV01563.proved))) (trans (cong refl R091.proved) (move-product MV01563.proved (MV01562.proved))))

module r2c_ij360124 where

  proved : X36 • K0124 ≈ K0124 • X36
  proved = GL.•-cancelʳ {g = X36 • K0124} {g' = K0124 • X36} {h = p (s3 • s5)}
    (trans (sym (move-product MV01564.proved (MV01565.proved))) (trans (cong refl R091.proved) (move-product MV01565.proved (MV01564.proved))))

module r2c_ij360125 where

  proved : X36 • K0125 ≈ K0125 • X36
  proved = GL.•-cancelʳ {g = X36 • K0125} {g' = K0125 • X36} {h = p (s4 • s3 • s5)}
    (trans (sym (move-product MV01566.proved (MV01567.proved))) (trans (cong refl R091.proved) (move-product MV01567.proved (MV01566.proved))))

module r2c_ij360127 where

  proved : X36 • K0127 ≈ K0127 • X36
  proved = GL.•-cancelʳ {g = X36 • K0127} {g' = K0127 • X36} {h = p (s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01568.proved (MV01569.proved))) (trans (cong refl R091.proved) (move-product MV01569.proved (MV01568.proved))))

module r2c_ij360145 where

  proved : X36 • K0145 ≈ K0145 • X36
  proved = GL.•-cancelʳ {g = X36 • K0145} {g' = K0145 • X36} {h = p (s3 • s2 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01570.proved (MV01571.proved))) (trans (cong refl R091.proved) (move-product MV01571.proved (MV01570.proved))))
