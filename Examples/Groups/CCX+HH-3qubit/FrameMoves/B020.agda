{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B020 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X07 ; X12 ; X13 ; X14 ; X15 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00098 ; module MV00099 ; module MV00100 ; module MV00101 ; module MV00102 ; module MV00105 ; module MV00106 ; module MV00107 ; module MV00108 ; module MV00109 ; module MV00111 ; module MV00112 ; module MV00113 ; module MV00114 ; module MV00115 ; module MV00116 ; module MV00118)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00119 ; module MV00120 ; module MV00121 ; module MV00122 ; module MV00123 ; module MV00125 ; module MV00126 ; module MV00127 ; module MV00128 ; module MV00129 ; module MV00132 ; module MV00133 ; module MV00134 ; module MV00135 ; module MV00136 ; module MV00137 ; module MV00138 ; module MV00145 ; module MV00146 ; module MV00151 ; module MV00152 ; module MV00158 ; module MV00159 ; module MV00165 ; module MV00166)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00002)

module MV00781 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X07 • p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00101.proved (move-compose MV00100.proved (move-compose MV00099.proved (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00782 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00783 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X07 • p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00102.proved (move-compose MV00101.proved (move-compose MV00100.proved (move-compose MV00099.proved (move-compose MV00098.proved (move-compose MV00138.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00784 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00785 where

  proved : p (ε) • X12 ≈ X12 • p (ε)
  proved = by-assoc-and PE00002.proved Eq.refl Eq.refl

module MV00786 where

  proved : p (s2 • s1 • s0 • s1 • s2) • X12 ≈ X12 • p (s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00111.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00787 where

  proved : p (s2 • s1 • s0 • s1 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00788 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s2) • X12 ≈ X12 • p (s3 • s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00111.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00789 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00790 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s2) • X12 ≈ X12 • p (s4 • s3 • s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00107.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00111.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00791 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00792 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2) • X12 ≈ X12 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00108.proved (move-compose MV00107.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00111.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00793 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00794 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2) • X12 ≈ X12 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00111.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00795 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00796 where

  proved : p (s1 • s0 • s1 • s2) • X12 ≈ X13 • p (s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00111.proved (MV00105.proved)))) Eq.refl Eq.refl

module MV00797 where

  proved : p (s1 • s0 • s1 • s2) • M0 ≈ M2 • p (s1 • s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (MV00002.proved)))) Eq.refl Eq.refl

module MV00798 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s3 • s2) • X12 ≈ X13 • p (s3 • s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00799 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00800 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2) • X12 ≈ X13 • p (s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00114.proved (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00801 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00802 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2) • X12 ≈ X13 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00115.proved (move-compose MV00114.proved (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00803 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00804 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2) • X12 ≈ X13 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00116.proved (move-compose MV00115.proved (move-compose MV00114.proved (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00805 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00806 where

  proved : p (s3 • s2) • X12 ≈ X14 • p (s3 • s2)
  proved = by-assoc-and (move-compose MV00113.proved (MV00105.proved)) Eq.refl Eq.refl

module MV00807 where

  proved : p (s3 • s2) • M0 ≈ M0 • p (s3 • s2)
  proved = by-assoc-and (move-compose MV00003.proved (MV00002.proved)) Eq.refl Eq.refl

module MV00808 where

  proved : p (s1 • s0 • s1 • s3 • s2) • X12 ≈ X14 • p (s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00152.proved (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00809 where

  proved : p (s1 • s0 • s1 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00810 where

  proved : p (s2 • s1 • s0 • s1 • s3 • s2) • X12 ≈ X14 • p (s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00811 where

  proved : p (s2 • s1 • s0 • s1 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00812 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2) • X12 ≈ X14 • p (s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00128.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00813 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00814 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2) • X12 ≈ X14 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00122.proved (move-compose MV00128.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00815 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00816 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2) • X12 ≈ X14 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00123.proved (move-compose MV00122.proved (move-compose MV00128.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00817 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00818 where

  proved : p (s4 • s3 • s2) • X12 ≈ X15 • p (s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))) Eq.refl Eq.refl

module MV00819 where

  proved : p (s4 • s3 • s2) • M0 ≈ M0 • p (s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))) Eq.refl Eq.refl

module MV00820 where

  proved : p (s1 • s0 • s1 • s4 • s3 • s2) • X12 ≈ X15 • p (s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00159.proved (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00821 where

  proved : p (s1 • s0 • s1 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00822 where

  proved : p (s2 • s1 • s0 • s1 • s4 • s3 • s2) • X12 ≈ X15 • p (s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00823 where

  proved : p (s2 • s1 • s0 • s1 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00824 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2) • X12 ≈ X15 • p (s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00825 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00826 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X15 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00136.proved (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00827 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl
