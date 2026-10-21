{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B021 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X12 ; X15 ; X16 ; X17 ; X23 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00105 ; module MV00111 ; module MV00113 ; module MV00118)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00129 ; module MV00130 ; module MV00132 ; module MV00133 ; module MV00134 ; module MV00135 ; module MV00136 ; module MV00137 ; module MV00139 ; module MV00140 ; module MV00141 ; module MV00142 ; module MV00143 ; module MV00144 ; module MV00145 ; module MV00148 ; module MV00149 ; module MV00150 ; module MV00151 ; module MV00153 ; module MV00154 ; module MV00165 ; module MV00166 ; module MV00172 ; module MV00173 ; module MV00179 ; module MV00180 ; module MV00181)

module MV00828 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X15 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00130.proved (move-compose MV00136.proved (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl

module MV00829 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV00830 where

  proved : p (s5 • s4 • s3 • s2) • X12 ≈ X16 • p (s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))) Eq.refl Eq.refl

module MV00831 where

  proved : p (s5 • s4 • s3 • s2) • M0 ≈ M0 • p (s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))) Eq.refl Eq.refl

module MV00832 where

  proved : p (s1 • s0 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X16 • p (s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00833 where

  proved : p (s1 • s0 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00834 where

  proved : p (s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X16 • p (s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00835 where

  proved : p (s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00836 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X16 • p (s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00837 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00838 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X16 • p (s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00166.proved (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00839 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00840 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X16 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00144.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))) Eq.refl Eq.refl

module MV00841 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))) Eq.refl Eq.refl

module MV00842 where

  proved : p (s6 • s5 • s4 • s3 • s2) • X12 ≈ X17 • p (s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00843 where

  proved : p (s6 • s5 • s4 • s3 • s2) • M0 ≈ M0 • p (s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00844 where

  proved : p (s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X17 • p (s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00173.proved (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00845 where

  proved : p (s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00846 where

  proved : p (s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X17 • p (s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00847 where

  proved : p (s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00848 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X17 • p (s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00849 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00850 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X17 • p (s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00851 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00852 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X17 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00173.proved (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl

module MV00853 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV00854 where

  proved : p (s1 • s2) • X12 ≈ X23 • p (s1 • s2)
  proved = by-assoc-and (move-compose MV00111.proved (MV00105.proved)) Eq.refl Eq.refl

module MV00855 where

  proved : p (s1 • s2) • M0 ≈ M0 • p (s1 • s2)
  proved = by-assoc-and (move-compose MV00001.proved (MV00002.proved)) Eq.refl Eq.refl

module MV00856 where

  proved : p (s0 • s1 • s2) • X12 ≈ X23 • p (s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00145.proved (move-compose MV00111.proved (MV00105.proved))) Eq.refl Eq.refl

module MV00857 where

  proved : p (s0 • s1 • s2) • M0 ≈ M1 • p (s0 • s1 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (MV00002.proved))) Eq.refl Eq.refl

module MV00858 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2) • X12 ≈ X23 • p (s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00859 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00860 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2) • X12 ≈ X23 • p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00861 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00862 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2) • X12 ≈ X23 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00863 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00864 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2) • X12 ≈ X23 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00150.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00865 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00866 where

  proved : p (s1 • s3 • s2) • X12 ≈ X24 • p (s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved))) Eq.refl Eq.refl

module MV00867 where

  proved : p (s1 • s3 • s2) • M0 ≈ M0 • p (s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved))) Eq.refl Eq.refl

module MV00868 where

  proved : p (s0 • s1 • s3 • s2) • X12 ≈ X24 • p (s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved)))) Eq.refl Eq.refl

module MV00869 where

  proved : p (s0 • s1 • s3 • s2) • M0 ≈ M1 • p (s0 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved)))) Eq.refl Eq.refl

module MV00870 where

  proved : p (s2 • s1 • s0 • s2 • s1 • s3 • s2) • X12 ≈ X24 • p (s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00871 where

  proved : p (s2 • s1 • s0 • s2 • s1 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl
