{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B019 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00073 ; module MV00074 ; module MV00075 ; module MV00077 ; module MV00078 ; module MV00079 ; module MV00081 ; module MV00082 ; module MV00084 ; module MV00085 ; module MV00086 ; module MV00087 ; module MV00089 ; module MV00091 ; module MV00092 ; module MV00093 ; module MV00094 ; module MV00095 ; module MV00098 ; module MV00099 ; module MV00100 ; module MV00101 ; module MV00102 ; module MV00103 ; module MV00105 ; module MV00113 ; module MV00117)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00124 ; module MV00129 ; module MV00131 ; module MV00137 ; module MV00138)

module MV00735 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2) • X12 ≈ X03 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00075.proved (move-compose MV00074.proved (move-compose MV00073.proved (move-compose MV00079.proved (move-compose MV00078.proved (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00736 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00737 where

  proved : p (s0 • s3 • s2) • X12 ≈ X04 • p (s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00113.proved (MV00105.proved))) Eq.refl Eq.refl

module MV00738 where

  proved : p (s0 • s3 • s2) • M0 ≈ M1 • p (s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00003.proved (MV00002.proved))) Eq.refl Eq.refl

module MV00739 where

  proved : p (s1 • s0 • s3 • s2) • X12 ≈ X04 • p (s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00113.proved (MV00105.proved)))) Eq.refl Eq.refl

module MV00740 where

  proved : p (s1 • s0 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (MV00002.proved)))) Eq.refl Eq.refl

module MV00741 where

  proved : p (s2 • s1 • s0 • s3 • s2) • X12 ≈ X04 • p (s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00078.proved (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00113.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00742 where

  proved : p (s2 • s1 • s0 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00743 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2) • X12 ≈ X04 • p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00087.proved (move-compose MV00086.proved (move-compose MV00085.proved (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00744 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00745 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2) • X12 ≈ X04 • p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00081.proved (move-compose MV00087.proved (move-compose MV00086.proved (move-compose MV00085.proved (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00746 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00747 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2) • X12 ≈ X04 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00082.proved (move-compose MV00081.proved (move-compose MV00087.proved (move-compose MV00086.proved (move-compose MV00085.proved (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00748 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00749 where

  proved : p (s0 • s4 • s3 • s2) • X12 ≈ X05 • p (s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00124.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))) Eq.refl Eq.refl

module MV00750 where

  proved : p (s0 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))) Eq.refl Eq.refl

module MV00751 where

  proved : p (s1 • s0 • s4 • s3 • s2) • X12 ≈ X05 • p (s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00752 where

  proved : p (s1 • s0 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00753 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2) • X12 ≈ X05 • p (s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00085.proved (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00754 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00755 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2) • X12 ≈ X05 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00086.proved (move-compose MV00085.proved (move-compose MV00084.proved (move-compose MV00124.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00756 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00757 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2) • X12 ≈ X05 • p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00095.proved (move-compose MV00094.proved (move-compose MV00093.proved (move-compose MV00092.proved (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00758 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00759 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2) • X12 ≈ X05 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00089.proved (move-compose MV00095.proved (move-compose MV00094.proved (move-compose MV00093.proved (move-compose MV00092.proved (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00760 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00761 where

  proved : p (s0 • s5 • s4 • s3 • s2) • X12 ≈ X06 • p (s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00131.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00762 where

  proved : p (s0 • s5 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00763 where

  proved : p (s1 • s0 • s5 • s4 • s3 • s2) • X12 ≈ X06 • p (s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00764 where

  proved : p (s1 • s0 • s5 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00765 where

  proved : p (s2 • s1 • s0 • s5 • s4 • s3 • s2) • X12 ≈ X06 • p (s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00092.proved (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00766 where

  proved : p (s2 • s1 • s0 • s5 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00767 where

  proved : p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2) • X12 ≈ X06 • p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00093.proved (move-compose MV00092.proved (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00768 where

  proved : p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00769 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2) • X12 ≈ X06 • p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00094.proved (move-compose MV00093.proved (move-compose MV00092.proved (move-compose MV00091.proved (move-compose MV00131.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00770 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00771 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X06 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00103.proved (move-compose MV00102.proved (move-compose MV00101.proved (move-compose MV00100.proved (move-compose MV00099.proved (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl

module MV00772 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV00773 where

  proved : p (s0 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X07 • p (s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00138.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00774 where

  proved : p (s0 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00775 where

  proved : p (s1 • s0 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X07 • p (s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00776 where

  proved : p (s1 • s0 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00777 where

  proved : p (s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X07 • p (s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00099.proved (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00778 where

  proved : p (s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00779 where

  proved : p (s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X07 • p (s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00100.proved (move-compose MV00099.proved (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00780 where

  proved : p (s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl
