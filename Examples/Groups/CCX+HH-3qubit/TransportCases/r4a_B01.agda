{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_B01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; M3 ; M4 ; M5 ; M6 ; M7 ; X13 ; X14 ; X15 ; X23 ; X24 ; X25 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X57 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00632)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00685 ; module MV00686 ; module MV00687 ; module MV00688 ; module MV00689 ; module MV00690)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00691 ; module MV00692 ; module MV00693 ; module MV00694 ; module MV00695 ; module MV00696 ; module MV00697 ; module MV00698 ; module MV00699 ; module MV00700 ; module MV00701 ; module MV00702 ; module MV00703 ; module MV00704 ; module MV00705 ; module MV00706 ; module MV00707 ; module MV00708)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B069 using (module MV02731 ; module MV02732 ; module MV02733 ; module MV02734 ; module MV02735 ; module MV02736 ; module MV02737 ; module MV02738 ; module MV02739 ; module MV02740 ; module MV02741 ; module MV02742 ; module MV02743 ; module MV02744 ; module MV02745 ; module MV02746 ; module MV02747 ; module MV02748 ; module MV02749 ; module MV02750 ; module MV02751 ; module MV02752 ; module MV02753 ; module MV02754 ; module MV02755 ; module MV02756 ; module MV02757 ; module MV02758 ; module MV02759 ; module MV02760)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B070 using (module MV02761 ; module MV02762 ; module MV02763 ; module MV02764 ; module MV02765 ; module MV02766 ; module MV02767 ; module MV02768 ; module MV02769 ; module MV02770 ; module MV02771 ; module MV02772 ; module MV02773 ; module MV02774 ; module MV02775 ; module MV02776 ; module MV02777 ; module MV02778 ; module MV02779 ; module MV02780 ; module MV02781 ; module MV02782 ; module MV02783 ; module MV02784 ; module MV02785 ; module MV02786 ; module MV02787 ; module MV02788 ; module MV02789 ; module MV02790 ; module MV02791 ; module MV02792 ; module MV02793 ; module MV02794 ; module MV02795)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B071 using (module MV02796 ; module MV02797 ; module MV02798 ; module MV02799 ; module MV02800 ; module MV02801 ; module MV02802 ; module MV02803 ; module MV02804 ; module MV02805 ; module MV02806 ; module MV02807 ; module MV02808 ; module MV02809 ; module MV02810 ; module MV02811 ; module MV02812 ; module MV02813 ; module MV02814 ; module MV02815 ; module MV02816 ; module MV02817 ; module MV02818 ; module MV02819 ; module MV02820 ; module MV02821 ; module MV02822 ; module MV02823 ; module MV02824 ; module MV02825)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B072 using (module MV02826 ; module MV02827 ; module MV02828 ; module MV02829 ; module MV02830)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R097)

module r4a_ij1345 where

  proved : X13 • K1345 ≈ K1345 • X35 • M3 • M5
  proved = GL.•-cancelʳ {g = X13 • K1345} {g' = K1345 • X35 • M3 • M5} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02731.proved (MV00685.proved))) (trans (cong refl R097.proved) (move-product MV00685.proved (move-product MV02732.proved (move-product MV02733.proved (MV02734.proved))))))

module r4a_ij1346 where

  proved : X13 • K1346 ≈ K1346 • X36 • M3 • M6
  proved = GL.•-cancelʳ {g = X13 • K1346} {g' = K1346 • X36 • M3 • M6} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02735.proved (MV00686.proved))) (trans (cong refl R097.proved) (move-product MV00686.proved (move-product MV02736.proved (move-product MV02737.proved (MV02738.proved))))))

module r4a_ij1347 where

  proved : X13 • K1347 ≈ K1347 • X37 • M3 • M7
  proved = GL.•-cancelʳ {g = X13 • K1347} {g' = K1347 • X37 • M3 • M7} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02739.proved (MV00687.proved))) (trans (cong refl R097.proved) (move-product MV00687.proved (move-product MV02740.proved (move-product MV02741.proved (MV02742.proved))))))

module r4a_ij1356 where

  proved : X13 • K1356 ≈ K1356 • X36 • M3 • M6
  proved = GL.•-cancelʳ {g = X13 • K1356} {g' = K1356 • X36 • M3 • M6} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02743.proved (MV00688.proved))) (trans (cong refl R097.proved) (move-product MV00688.proved (move-product MV02744.proved (move-product MV02745.proved (MV02746.proved))))))

module r4a_ij1357 where

  proved : X13 • K1357 ≈ K1357 • X37 • M3 • M7
  proved = GL.•-cancelʳ {g = X13 • K1357} {g' = K1357 • X37 • M3 • M7} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02747.proved (MV00689.proved))) (trans (cong refl R097.proved) (move-product MV00689.proved (move-product MV02748.proved (move-product MV02749.proved (MV02750.proved))))))

module r4a_ij1367 where

  proved : X13 • K1367 ≈ K1367 • X37 • M3 • M7
  proved = GL.•-cancelʳ {g = X13 • K1367} {g' = K1367 • X37 • M3 • M7} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02751.proved (MV00690.proved))) (trans (cong refl R097.proved) (move-product MV00690.proved (move-product MV02752.proved (move-product MV02753.proved (MV02754.proved))))))

module r4a_ij1456 where

  proved : X14 • K1456 ≈ K1456 • X46 • M4 • M6
  proved = GL.•-cancelʳ {g = X14 • K1456} {g' = K1456 • X46 • M4 • M6} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02755.proved (MV00691.proved))) (trans (cong refl R097.proved) (move-product MV00691.proved (move-product MV02756.proved (move-product MV02757.proved (MV02758.proved))))))

module r4a_ij1457 where

  proved : X14 • K1457 ≈ K1457 • X47 • M4 • M7
  proved = GL.•-cancelʳ {g = X14 • K1457} {g' = K1457 • X47 • M4 • M7} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02759.proved (MV00692.proved))) (trans (cong refl R097.proved) (move-product MV00692.proved (move-product MV02760.proved (move-product MV02761.proved (MV02762.proved))))))

module r4a_ij1467 where

  proved : X14 • K1467 ≈ K1467 • X47 • M4 • M7
  proved = GL.•-cancelʳ {g = X14 • K1467} {g' = K1467 • X47 • M4 • M7} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02763.proved (MV00693.proved))) (trans (cong refl R097.proved) (move-product MV00693.proved (move-product MV02764.proved (move-product MV02765.proved (MV02766.proved))))))

module r4a_ij1567 where

  proved : X15 • K1567 ≈ K1567 • X57 • M5 • M7
  proved = GL.•-cancelʳ {g = X15 • K1567} {g' = K1567 • X57 • M5 • M7} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02767.proved (MV00694.proved))) (trans (cong refl R097.proved) (move-product MV00694.proved (move-product MV02768.proved (move-product MV02769.proved (MV02770.proved))))))

module r4a_ij2345 where

  proved : X23 • K2345 ≈ K2345 • X35 • M3 • M5
  proved = GL.•-cancelʳ {g = X23 • K2345} {g' = K2345 • X35 • M3 • M5} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02771.proved (MV00695.proved))) (trans (cong refl R097.proved) (move-product MV00695.proved (move-product MV02772.proved (move-product MV02773.proved (MV02774.proved))))))

module r4a_ij2346 where

  proved : X23 • K2346 ≈ K2346 • X36 • M3 • M6
  proved = GL.•-cancelʳ {g = X23 • K2346} {g' = K2346 • X36 • M3 • M6} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02775.proved (MV00696.proved))) (trans (cong refl R097.proved) (move-product MV00696.proved (move-product MV02776.proved (move-product MV02777.proved (MV02778.proved))))))

module r4a_ij2347 where

  proved : X23 • K2347 ≈ K2347 • X37 • M3 • M7
  proved = GL.•-cancelʳ {g = X23 • K2347} {g' = K2347 • X37 • M3 • M7} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02779.proved (MV00697.proved))) (trans (cong refl R097.proved) (move-product MV00697.proved (move-product MV02780.proved (move-product MV02781.proved (MV02782.proved))))))

module r4a_ij2356 where

  proved : X23 • K2356 ≈ K2356 • X36 • M3 • M6
  proved = GL.•-cancelʳ {g = X23 • K2356} {g' = K2356 • X36 • M3 • M6} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02783.proved (MV00698.proved))) (trans (cong refl R097.proved) (move-product MV00698.proved (move-product MV02784.proved (move-product MV02785.proved (MV02786.proved))))))

module r4a_ij2357 where

  proved : X23 • K2357 ≈ K2357 • X37 • M3 • M7
  proved = GL.•-cancelʳ {g = X23 • K2357} {g' = K2357 • X37 • M3 • M7} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02787.proved (MV00699.proved))) (trans (cong refl R097.proved) (move-product MV00699.proved (move-product MV02788.proved (move-product MV02789.proved (MV02790.proved))))))

module r4a_ij2367 where

  proved : X23 • K2367 ≈ K2367 • X37 • M3 • M7
  proved = GL.•-cancelʳ {g = X23 • K2367} {g' = K2367 • X37 • M3 • M7} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02791.proved (MV00700.proved))) (trans (cong refl R097.proved) (move-product MV00700.proved (move-product MV02792.proved (move-product MV02793.proved (MV02794.proved))))))

module r4a_ij2456 where

  proved : X24 • K2456 ≈ K2456 • X46 • M4 • M6
  proved = GL.•-cancelʳ {g = X24 • K2456} {g' = K2456 • X46 • M4 • M6} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02795.proved (MV00701.proved))) (trans (cong refl R097.proved) (move-product MV00701.proved (move-product MV02796.proved (move-product MV02797.proved (MV02798.proved))))))

module r4a_ij2457 where

  proved : X24 • K2457 ≈ K2457 • X47 • M4 • M7
  proved = GL.•-cancelʳ {g = X24 • K2457} {g' = K2457 • X47 • M4 • M7} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02799.proved (MV00702.proved))) (trans (cong refl R097.proved) (move-product MV00702.proved (move-product MV02800.proved (move-product MV02801.proved (MV02802.proved))))))

module r4a_ij2467 where

  proved : X24 • K2467 ≈ K2467 • X47 • M4 • M7
  proved = GL.•-cancelʳ {g = X24 • K2467} {g' = K2467 • X47 • M4 • M7} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02803.proved (MV00703.proved))) (trans (cong refl R097.proved) (move-product MV00703.proved (move-product MV02804.proved (move-product MV02805.proved (MV02806.proved))))))

module r4a_ij2567 where

  proved : X25 • K2567 ≈ K2567 • X57 • M5 • M7
  proved = GL.•-cancelʳ {g = X25 • K2567} {g' = K2567 • X57 • M5 • M7} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02807.proved (MV00704.proved))) (trans (cong refl R097.proved) (move-product MV00704.proved (move-product MV02808.proved (move-product MV02809.proved (MV02810.proved))))))

module r4a_ij3456 where

  proved : X34 • K3456 ≈ K3456 • X46 • M4 • M6
  proved = GL.•-cancelʳ {g = X34 • K3456} {g' = K3456 • X46 • M4 • M6} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02811.proved (MV00705.proved))) (trans (cong refl R097.proved) (move-product MV00705.proved (move-product MV02812.proved (move-product MV02813.proved (MV02814.proved))))))

module r4a_ij3457 where

  proved : X34 • K3457 ≈ K3457 • X47 • M4 • M7
  proved = GL.•-cancelʳ {g = X34 • K3457} {g' = K3457 • X47 • M4 • M7} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02815.proved (MV00706.proved))) (trans (cong refl R097.proved) (move-product MV00706.proved (move-product MV02816.proved (move-product MV02817.proved (MV02818.proved))))))

module r4a_ij3467 where

  proved : X34 • K3467 ≈ K3467 • X47 • M4 • M7
  proved = GL.•-cancelʳ {g = X34 • K3467} {g' = K3467 • X47 • M4 • M7} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02819.proved (MV00707.proved))) (trans (cong refl R097.proved) (move-product MV00707.proved (move-product MV02820.proved (move-product MV02821.proved (MV02822.proved))))))

module r4a_ij3567 where

  proved : X35 • K3567 ≈ K3567 • X57 • M5 • M7
  proved = GL.•-cancelʳ {g = X35 • K3567} {g' = K3567 • X57 • M5 • M7} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02823.proved (MV00708.proved))) (trans (cong refl R097.proved) (move-product MV00708.proved (move-product MV02824.proved (move-product MV02825.proved (MV02826.proved))))))

module r4a_ij4567 where

  proved : X45 • K4567 ≈ K4567 • X57 • M5 • M7
  proved = GL.•-cancelʳ {g = X45 • K4567} {g' = K4567 • X57 • M5 • M7} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02827.proved (MV00632.proved))) (trans (cong refl R097.proved) (move-product MV00632.proved (move-product MV02828.proved (move-product MV02829.proved (MV02830.proved))))))
