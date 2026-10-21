{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_B05 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0357 ; K0367 ; K0456 ; K0457 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1357 ; K1367 ; K1456 ; K1457 ; K2357 ; K2367 ; K2456 ; K2457 ; X36 ; X37 ; X45 ; X46 ; X47 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as R091
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00210)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00641)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B041 using (module MV01572 ; module MV01573)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B042 using (module MV01574 ; module MV01575 ; module MV01576 ; module MV01577 ; module MV01578 ; module MV01579 ; module MV01580 ; module MV01581 ; module MV01582 ; module MV01583 ; module MV01584 ; module MV01585 ; module MV01586 ; module MV01587 ; module MV01588 ; module MV01589 ; module MV01590 ; module MV01591 ; module MV01592 ; module MV01593 ; module MV01594 ; module MV01595 ; module MV01596 ; module MV01597 ; module MV01598 ; module MV01599 ; module MV01600 ; module MV01601 ; module MV01602 ; module MV01603 ; module MV01604 ; module MV01605 ; module MV01606 ; module MV01607 ; module MV01608 ; module MV01609 ; module MV01610 ; module MV01611)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B043 using (module MV01612 ; module MV01613 ; module MV01614 ; module MV01615 ; module MV01616 ; module MV01617 ; module MV01618 ; module MV01619 ; module MV01620 ; module MV01621 ; module MV01622 ; module MV01623 ; module MV01624 ; module MV01625 ; module MV01626 ; module MV01627 ; module MV01628 ; module MV01629 ; module MV01630 ; module MV01631 ; module MV01632 ; module MV01633 ; module MV01634 ; module MV01635 ; module MV01636 ; module MV01637 ; module MV01638 ; module MV01639 ; module MV01640 ; module MV01641 ; module MV01642 ; module MV01643 ; module MV01644 ; module MV01645 ; module MV01646 ; module MV01647 ; module MV01648)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B044 using (module MV01649 ; module MV01650 ; module MV01651 ; module MV01652 ; module MV01653 ; module MV01654 ; module MV01655 ; module MV01656 ; module MV01657 ; module MV01658 ; module MV01659 ; module MV01660 ; module MV01661 ; module MV01662 ; module MV01663 ; module MV01664 ; module MV01665 ; module MV01666 ; module MV01667 ; module MV01668 ; module MV01669 ; module MV01670 ; module MV01671 ; module MV01672 ; module MV01673 ; module MV01674 ; module MV01675 ; module MV01676 ; module MV01677 ; module MV01678 ; module MV01679 ; module MV01680 ; module MV01681 ; module MV01682 ; module MV01683 ; module MV01684 ; module MV01685 ; module MV01686 ; module MV01687)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B045 using (module MV01688 ; module MV01689 ; module MV01690 ; module MV01691 ; module MV01692)

module r2c_ij360147 where

  proved : X36 • K0147 ≈ K0147 • X36
  proved = GL.•-cancelʳ {g = X36 • K0147} {g' = K0147 • X36} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01572.proved (MV01573.proved))) (trans (cong refl R091.proved) (move-product MV01573.proved (MV01572.proved))))

module r2c_ij360157 where

  proved : X36 • K0157 ≈ K0157 • X36
  proved = GL.•-cancelʳ {g = X36 • K0157} {g' = K0157 • X36} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01574.proved (MV01575.proved))) (trans (cong refl R091.proved) (move-product MV01575.proved (MV01574.proved))))

module r2c_ij360245 where

  proved : X36 • K0245 ≈ K0245 • X36
  proved = GL.•-cancelʳ {g = X36 • K0245} {g' = K0245 • X36} {h = p (s1 • s3 • s2 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01576.proved (MV01577.proved))) (trans (cong refl R091.proved) (move-product MV01577.proved (MV01576.proved))))

module r2c_ij360247 where

  proved : X36 • K0247 ≈ K0247 • X36
  proved = GL.•-cancelʳ {g = X36 • K0247} {g' = K0247 • X36} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01578.proved (MV01579.proved))) (trans (cong refl R091.proved) (move-product MV01579.proved (MV01578.proved))))

module r2c_ij360257 where

  proved : X36 • K0257 ≈ K0257 • X36
  proved = GL.•-cancelʳ {g = X36 • K0257} {g' = K0257 • X36} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01580.proved (MV01581.proved))) (trans (cong refl R091.proved) (move-product MV01581.proved (MV01580.proved))))

module r2c_ij360457 where

  proved : X36 • K0457 ≈ K0457 • X36
  proved = GL.•-cancelʳ {g = X36 • K0457} {g' = K0457 • X36} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01582.proved (MV01583.proved))) (trans (cong refl R091.proved) (move-product MV01583.proved (MV01582.proved))))

module r2c_ij361245 where

  proved : X36 • K1245 ≈ K1245 • X36
  proved = GL.•-cancelʳ {g = X36 • K1245} {g' = K1245 • X36} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01584.proved (MV01585.proved))) (trans (cong refl R091.proved) (move-product MV01585.proved (MV01584.proved))))

module r2c_ij361247 where

  proved : X36 • K1247 ≈ K1247 • X36
  proved = GL.•-cancelʳ {g = X36 • K1247} {g' = K1247 • X36} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01586.proved (MV01587.proved))) (trans (cong refl R091.proved) (move-product MV01587.proved (MV01586.proved))))

module r2c_ij361257 where

  proved : X36 • K1257 ≈ K1257 • X36
  proved = GL.•-cancelʳ {g = X36 • K1257} {g' = K1257 • X36} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01588.proved (MV01589.proved))) (trans (cong refl R091.proved) (move-product MV01589.proved (MV01588.proved))))

module r2c_ij361457 where

  proved : X36 • K1457 ≈ K1457 • X36
  proved = GL.•-cancelʳ {g = X36 • K1457} {g' = K1457 • X36} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01590.proved (MV01591.proved))) (trans (cong refl R091.proved) (move-product MV01591.proved (MV01590.proved))))

module r2c_ij362457 where

  proved : X36 • K2457 ≈ K2457 • X36
  proved = GL.•-cancelʳ {g = X36 • K2457} {g' = K2457 • X36} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01592.proved (MV01593.proved))) (trans (cong refl R091.proved) (move-product MV01593.proved (MV01592.proved))))

module r2c_ij370124 where

  proved : X37 • K0124 ≈ K0124 • X37
  proved = GL.•-cancelʳ {g = X37 • K0124} {g' = K0124 • X37} {h = p (s3 • s6 • s5)}
    (trans (sym (move-product MV01594.proved (MV01595.proved))) (trans (cong refl R091.proved) (move-product MV01595.proved (MV01594.proved))))

module r2c_ij370125 where

  proved : X37 • K0125 ≈ K0125 • X37
  proved = GL.•-cancelʳ {g = X37 • K0125} {g' = K0125 • X37} {h = p (s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01596.proved (MV01597.proved))) (trans (cong refl R091.proved) (move-product MV01597.proved (MV01596.proved))))

module r2c_ij370126 where

  proved : X37 • K0126 ≈ K0126 • X37
  proved = GL.•-cancelʳ {g = X37 • K0126} {g' = K0126 • X37} {h = p (s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01598.proved (MV01599.proved))) (trans (cong refl R091.proved) (move-product MV01599.proved (MV01598.proved))))

module r2c_ij370145 where

  proved : X37 • K0145 ≈ K0145 • X37
  proved = GL.•-cancelʳ {g = X37 • K0145} {g' = K0145 • X37} {h = p (s3 • s2 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01600.proved (MV01601.proved))) (trans (cong refl R091.proved) (move-product MV01601.proved (MV01600.proved))))

module r2c_ij370146 where

  proved : X37 • K0146 ≈ K0146 • X37
  proved = GL.•-cancelʳ {g = X37 • K0146} {g' = K0146 • X37} {h = p (s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01602.proved (MV01603.proved))) (trans (cong refl R091.proved) (move-product MV01603.proved (MV01602.proved))))

module r2c_ij370156 where

  proved : X37 • K0156 ≈ K0156 • X37
  proved = GL.•-cancelʳ {g = X37 • K0156} {g' = K0156 • X37} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01604.proved (MV01605.proved))) (trans (cong refl R091.proved) (move-product MV01605.proved (MV01604.proved))))

module r2c_ij370245 where

  proved : X37 • K0245 ≈ K0245 • X37
  proved = GL.•-cancelʳ {g = X37 • K0245} {g' = K0245 • X37} {h = p (s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01606.proved (MV01607.proved))) (trans (cong refl R091.proved) (move-product MV01607.proved (MV01606.proved))))

module r2c_ij370246 where

  proved : X37 • K0246 ≈ K0246 • X37
  proved = GL.•-cancelʳ {g = X37 • K0246} {g' = K0246 • X37} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01608.proved (MV01609.proved))) (trans (cong refl R091.proved) (move-product MV01609.proved (MV01608.proved))))

module r2c_ij370256 where

  proved : X37 • K0256 ≈ K0256 • X37
  proved = GL.•-cancelʳ {g = X37 • K0256} {g' = K0256 • X37} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01610.proved (MV01611.proved))) (trans (cong refl R091.proved) (move-product MV01611.proved (MV01610.proved))))

module r2c_ij370456 where

  proved : X37 • K0456 ≈ K0456 • X37
  proved = GL.•-cancelʳ {g = X37 • K0456} {g' = K0456 • X37} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01612.proved (MV01613.proved))) (trans (cong refl R091.proved) (move-product MV01613.proved (MV01612.proved))))

module r2c_ij371245 where

  proved : X37 • K1245 ≈ K1245 • X37
  proved = GL.•-cancelʳ {g = X37 • K1245} {g' = K1245 • X37} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01614.proved (MV01615.proved))) (trans (cong refl R091.proved) (move-product MV01615.proved (MV01614.proved))))

module r2c_ij371246 where

  proved : X37 • K1246 ≈ K1246 • X37
  proved = GL.•-cancelʳ {g = X37 • K1246} {g' = K1246 • X37} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01616.proved (MV01617.proved))) (trans (cong refl R091.proved) (move-product MV01617.proved (MV01616.proved))))

module r2c_ij371256 where

  proved : X37 • K1256 ≈ K1256 • X37
  proved = GL.•-cancelʳ {g = X37 • K1256} {g' = K1256 • X37} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01618.proved (MV01619.proved))) (trans (cong refl R091.proved) (move-product MV01619.proved (MV01618.proved))))

module r2c_ij371456 where

  proved : X37 • K1456 ≈ K1456 • X37
  proved = GL.•-cancelʳ {g = X37 • K1456} {g' = K1456 • X37} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01620.proved (MV01621.proved))) (trans (cong refl R091.proved) (move-product MV01621.proved (MV01620.proved))))

module r2c_ij372456 where

  proved : X37 • K2456 ≈ K2456 • X37
  proved = GL.•-cancelʳ {g = X37 • K2456} {g' = K2456 • X37} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01622.proved (MV01623.proved))) (trans (cong refl R091.proved) (move-product MV01623.proved (MV01622.proved))))

module r2c_ij450123 where

  proved : X45 • K0123 ≈ K0123 • X45
  proved = GL.•-cancelʳ {g = X45 • K0123} {g' = K0123 • X45} {h = p (ε)}
    (trans (sym (move-product MV01624.proved (MV00641.proved))) (trans (cong refl R091.proved) (move-product MV00641.proved (MV01624.proved))))

module r2c_ij450126 where

  proved : X45 • K0126 ≈ K0126 • X45
  proved = GL.•-cancelʳ {g = X45 • K0126} {g' = K0126 • X45} {h = p (s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01625.proved (MV01626.proved))) (trans (cong refl R091.proved) (move-product MV01626.proved (MV01625.proved))))

module r2c_ij450127 where

  proved : X45 • K0127 ≈ K0127 • X45
  proved = GL.•-cancelʳ {g = X45 • K0127} {g' = K0127 • X45} {h = p (s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01627.proved (MV01628.proved))) (trans (cong refl R091.proved) (move-product MV01628.proved (MV01627.proved))))

module r2c_ij450136 where

  proved : X45 • K0136 ≈ K0136 • X45
  proved = GL.•-cancelʳ {g = X45 • K0136} {g' = K0136 • X45} {h = p (s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01629.proved (MV01630.proved))) (trans (cong refl R091.proved) (move-product MV01630.proved (MV01629.proved))))

module r2c_ij450137 where

  proved : X45 • K0137 ≈ K0137 • X45
  proved = GL.•-cancelʳ {g = X45 • K0137} {g' = K0137 • X45} {h = p (s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01631.proved (MV01632.proved))) (trans (cong refl R091.proved) (move-product MV01632.proved (MV01631.proved))))

module r2c_ij450167 where

  proved : X45 • K0167 ≈ K0167 • X45
  proved = GL.•-cancelʳ {g = X45 • K0167} {g' = K0167 • X45} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01633.proved (MV01634.proved))) (trans (cong refl R091.proved) (move-product MV01634.proved (MV01633.proved))))

module r2c_ij450236 where

  proved : X45 • K0236 ≈ K0236 • X45
  proved = GL.•-cancelʳ {g = X45 • K0236} {g' = K0236 • X45} {h = p (s1 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01635.proved (MV01636.proved))) (trans (cong refl R091.proved) (move-product MV01636.proved (MV01635.proved))))

module r2c_ij450237 where

  proved : X45 • K0237 ≈ K0237 • X45
  proved = GL.•-cancelʳ {g = X45 • K0237} {g' = K0237 • X45} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01637.proved (MV01638.proved))) (trans (cong refl R091.proved) (move-product MV01638.proved (MV01637.proved))))

module r2c_ij450267 where

  proved : X45 • K0267 ≈ K0267 • X45
  proved = GL.•-cancelʳ {g = X45 • K0267} {g' = K0267 • X45} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01639.proved (MV01640.proved))) (trans (cong refl R091.proved) (move-product MV01640.proved (MV01639.proved))))

module r2c_ij450367 where

  proved : X45 • K0367 ≈ K0367 • X45
  proved = GL.•-cancelʳ {g = X45 • K0367} {g' = K0367 • X45} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01641.proved (MV01642.proved))) (trans (cong refl R091.proved) (move-product MV01642.proved (MV01641.proved))))

module r2c_ij451236 where

  proved : X45 • K1236 ≈ K1236 • X45
  proved = GL.•-cancelʳ {g = X45 • K1236} {g' = K1236 • X45} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01643.proved (MV01644.proved))) (trans (cong refl R091.proved) (move-product MV01644.proved (MV01643.proved))))

module r2c_ij451237 where

  proved : X45 • K1237 ≈ K1237 • X45
  proved = GL.•-cancelʳ {g = X45 • K1237} {g' = K1237 • X45} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01645.proved (MV01646.proved))) (trans (cong refl R091.proved) (move-product MV01646.proved (MV01645.proved))))

module r2c_ij451267 where

  proved : X45 • K1267 ≈ K1267 • X45
  proved = GL.•-cancelʳ {g = X45 • K1267} {g' = K1267 • X45} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01647.proved (MV01648.proved))) (trans (cong refl R091.proved) (move-product MV01648.proved (MV01647.proved))))

module r2c_ij451367 where

  proved : X45 • K1367 ≈ K1367 • X45
  proved = GL.•-cancelʳ {g = X45 • K1367} {g' = K1367 • X45} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01649.proved (MV01650.proved))) (trans (cong refl R091.proved) (move-product MV01650.proved (MV01649.proved))))

module r2c_ij452367 where

  proved : X45 • K2367 ≈ K2367 • X45
  proved = GL.•-cancelʳ {g = X45 • K2367} {g' = K2367 • X45} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01651.proved (MV01652.proved))) (trans (cong refl R091.proved) (move-product MV01652.proved (MV01651.proved))))

module r2c_ij460123 where

  proved : X46 • K0123 ≈ K0123 • X46
  proved = GL.•-cancelʳ {g = X46 • K0123} {g' = K0123 • X46} {h = p (s5)}
    (trans (sym (move-product MV00210.proved (MV00247.proved))) (trans (cong refl R091.proved) (move-product MV00247.proved (MV00210.proved))))

module r2c_ij460125 where

  proved : X46 • K0125 ≈ K0125 • X46
  proved = GL.•-cancelʳ {g = X46 • K0125} {g' = K0125 • X46} {h = p (s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01653.proved (MV01654.proved))) (trans (cong refl R091.proved) (move-product MV01654.proved (MV01653.proved))))

module r2c_ij460127 where

  proved : X46 • K0127 ≈ K0127 • X46
  proved = GL.•-cancelʳ {g = X46 • K0127} {g' = K0127 • X46} {h = p (s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01655.proved (MV01656.proved))) (trans (cong refl R091.proved) (move-product MV01656.proved (MV01655.proved))))

module r2c_ij460135 where

  proved : X46 • K0135 ≈ K0135 • X46
  proved = GL.•-cancelʳ {g = X46 • K0135} {g' = K0135 • X46} {h = p (s2 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01657.proved (MV01658.proved))) (trans (cong refl R091.proved) (move-product MV01658.proved (MV01657.proved))))

module r2c_ij460137 where

  proved : X46 • K0137 ≈ K0137 • X46
  proved = GL.•-cancelʳ {g = X46 • K0137} {g' = K0137 • X46} {h = p (s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01659.proved (MV01660.proved))) (trans (cong refl R091.proved) (move-product MV01660.proved (MV01659.proved))))

module r2c_ij460157 where

  proved : X46 • K0157 ≈ K0157 • X46
  proved = GL.•-cancelʳ {g = X46 • K0157} {g' = K0157 • X46} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01661.proved (MV01662.proved))) (trans (cong refl R091.proved) (move-product MV01662.proved (MV01661.proved))))

module r2c_ij460235 where

  proved : X46 • K0235 ≈ K0235 • X46
  proved = GL.•-cancelʳ {g = X46 • K0235} {g' = K0235 • X46} {h = p (s1 • s2 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01663.proved (MV01664.proved))) (trans (cong refl R091.proved) (move-product MV01664.proved (MV01663.proved))))

module r2c_ij460237 where

  proved : X46 • K0237 ≈ K0237 • X46
  proved = GL.•-cancelʳ {g = X46 • K0237} {g' = K0237 • X46} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01665.proved (MV01666.proved))) (trans (cong refl R091.proved) (move-product MV01666.proved (MV01665.proved))))

module r2c_ij460257 where

  proved : X46 • K0257 ≈ K0257 • X46
  proved = GL.•-cancelʳ {g = X46 • K0257} {g' = K0257 • X46} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01667.proved (MV01668.proved))) (trans (cong refl R091.proved) (move-product MV01668.proved (MV01667.proved))))

module r2c_ij460357 where

  proved : X46 • K0357 ≈ K0357 • X46
  proved = GL.•-cancelʳ {g = X46 • K0357} {g' = K0357 • X46} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01669.proved (MV01670.proved))) (trans (cong refl R091.proved) (move-product MV01670.proved (MV01669.proved))))

module r2c_ij461235 where

  proved : X46 • K1235 ≈ K1235 • X46
  proved = GL.•-cancelʳ {g = X46 • K1235} {g' = K1235 • X46} {h = p (s0 • s1 • s2 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01671.proved (MV01672.proved))) (trans (cong refl R091.proved) (move-product MV01672.proved (MV01671.proved))))

module r2c_ij461237 where

  proved : X46 • K1237 ≈ K1237 • X46
  proved = GL.•-cancelʳ {g = X46 • K1237} {g' = K1237 • X46} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01673.proved (MV01674.proved))) (trans (cong refl R091.proved) (move-product MV01674.proved (MV01673.proved))))

module r2c_ij461257 where

  proved : X46 • K1257 ≈ K1257 • X46
  proved = GL.•-cancelʳ {g = X46 • K1257} {g' = K1257 • X46} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01675.proved (MV01676.proved))) (trans (cong refl R091.proved) (move-product MV01676.proved (MV01675.proved))))

module r2c_ij461357 where

  proved : X46 • K1357 ≈ K1357 • X46
  proved = GL.•-cancelʳ {g = X46 • K1357} {g' = K1357 • X46} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01677.proved (MV01678.proved))) (trans (cong refl R091.proved) (move-product MV01678.proved (MV01677.proved))))

module r2c_ij462357 where

  proved : X46 • K2357 ≈ K2357 • X46
  proved = GL.•-cancelʳ {g = X46 • K2357} {g' = K2357 • X46} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01679.proved (MV01680.proved))) (trans (cong refl R091.proved) (move-product MV01680.proved (MV01679.proved))))

module r2c_ij470123 where

  proved : X47 • K0123 ≈ K0123 • X47
  proved = GL.•-cancelʳ {g = X47 • K0123} {g' = K0123 • X47} {h = p (s6 • s5)}
    (trans (sym (move-product MV01681.proved (MV01682.proved))) (trans (cong refl R091.proved) (move-product MV01682.proved (MV01681.proved))))

module r2c_ij470125 where

  proved : X47 • K0125 ≈ K0125 • X47
  proved = GL.•-cancelʳ {g = X47 • K0125} {g' = K0125 • X47} {h = p (s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01683.proved (MV01684.proved))) (trans (cong refl R091.proved) (move-product MV01684.proved (MV01683.proved))))

module r2c_ij470126 where

  proved : X47 • K0126 ≈ K0126 • X47
  proved = GL.•-cancelʳ {g = X47 • K0126} {g' = K0126 • X47} {h = p (s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01685.proved (MV01686.proved))) (trans (cong refl R091.proved) (move-product MV01686.proved (MV01685.proved))))

module r2c_ij470135 where

  proved : X47 • K0135 ≈ K0135 • X47
  proved = GL.•-cancelʳ {g = X47 • K0135} {g' = K0135 • X47} {h = p (s2 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01687.proved (MV01688.proved))) (trans (cong refl R091.proved) (move-product MV01688.proved (MV01687.proved))))

module r2c_ij470136 where

  proved : X47 • K0136 ≈ K0136 • X47
  proved = GL.•-cancelʳ {g = X47 • K0136} {g' = K0136 • X47} {h = p (s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01689.proved (MV01690.proved))) (trans (cong refl R091.proved) (move-product MV01690.proved (MV01689.proved))))

module r2c_ij470156 where

  proved : X47 • K0156 ≈ K0156 • X47
  proved = GL.•-cancelʳ {g = X47 • K0156} {g' = K0156 • X47} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01691.proved (MV01692.proved))) (trans (cong refl R091.proved) (move-product MV01692.proved (MV01691.proved))))
