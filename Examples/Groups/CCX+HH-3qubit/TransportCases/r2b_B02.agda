{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_B02 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B024 using (module MV00952 ; module MV00953 ; module MV00954 ; module MV00955 ; module MV00956 ; module MV00957 ; module MV00958 ; module MV00959 ; module MV00960 ; module MV00961 ; module MV00962 ; module MV00963 ; module MV00964 ; module MV00965 ; module MV00966 ; module MV00967 ; module MV00968 ; module MV00969 ; module MV00970 ; module MV00971 ; module MV00972 ; module MV00973 ; module MV00974 ; module MV00975 ; module MV00976 ; module MV00977 ; module MV00978 ; module MV00979 ; module MV00980 ; module MV00981 ; module MV00982 ; module MV00983 ; module MV00984 ; module MV00985)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B025 using (module MV00986 ; module MV00987 ; module MV00988 ; module MV00989 ; module MV00990 ; module MV00991 ; module MV00992 ; module MV00993 ; module MV00994 ; module MV00995 ; module MV00996 ; module MV00997 ; module MV00998 ; module MV00999 ; module MV01000 ; module MV01001 ; module MV01002 ; module MV01003 ; module MV01004 ; module MV01005 ; module MV01006 ; module MV01007 ; module MV01008 ; module MV01009 ; module MV01010 ; module MV01011 ; module MV01012 ; module MV01013 ; module MV01014 ; module MV01015 ; module MV01016 ; module MV01017 ; module MV01018 ; module MV01019)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B026 using (module MV01020 ; module MV01021 ; module MV01022 ; module MV01023 ; module MV01024 ; module MV01025 ; module MV01026 ; module MV01027 ; module MV01028 ; module MV01029 ; module MV01030 ; module MV01031 ; module MV01032 ; module MV01033)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R085)

module r2b_ij371 where

  proved : X37 • M1 ≈ M1 • X37
  proved = GL.•-cancelʳ {g = X37 • M1} {g' = M1 • X37} {h = p (s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00952.proved (MV00953.proved))) (trans (cong refl R085.proved) (move-product MV00953.proved (MV00952.proved))))

module r2b_ij372 where

  proved : X37 • M2 ≈ M2 • X37
  proved = GL.•-cancelʳ {g = X37 • M2} {g' = M2 • X37} {h = p (s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00954.proved (MV00955.proved))) (trans (cong refl R085.proved) (move-product MV00955.proved (MV00954.proved))))

module r2b_ij374 where

  proved : X37 • M4 ≈ M4 • X37
  proved = GL.•-cancelʳ {g = X37 • M4} {g' = M4 • X37} {h = p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00956.proved (MV00957.proved))) (trans (cong refl R085.proved) (move-product MV00957.proved (MV00956.proved))))

module r2b_ij375 where

  proved : X37 • M5 ≈ M5 • X37
  proved = GL.•-cancelʳ {g = X37 • M5} {g' = M5 • X37} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00958.proved (MV00959.proved))) (trans (cong refl R085.proved) (move-product MV00959.proved (MV00958.proved))))

module r2b_ij376 where

  proved : X37 • M6 ≈ M6 • X37
  proved = GL.•-cancelʳ {g = X37 • M6} {g' = M6 • X37} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00960.proved (MV00961.proved))) (trans (cong refl R085.proved) (move-product MV00961.proved (MV00960.proved))))

module r2b_ij450 where

  proved : X45 • M0 ≈ M0 • X45
  proved = GL.•-cancelʳ {g = X45 • M0} {g' = M0 • X45} {h = p (s3 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00962.proved (MV00963.proved))) (trans (cong refl R085.proved) (move-product MV00963.proved (MV00962.proved))))

module r2b_ij451 where

  proved : X45 • M1 ≈ M1 • X45
  proved = GL.•-cancelʳ {g = X45 • M1} {g' = M1 • X45} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00964.proved (MV00965.proved))) (trans (cong refl R085.proved) (move-product MV00965.proved (MV00964.proved))))

module r2b_ij452 where

  proved : X45 • M2 ≈ M2 • X45
  proved = GL.•-cancelʳ {g = X45 • M2} {g' = M2 • X45} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00966.proved (MV00967.proved))) (trans (cong refl R085.proved) (move-product MV00967.proved (MV00966.proved))))

module r2b_ij453 where

  proved : X45 • M3 ≈ M3 • X45
  proved = GL.•-cancelʳ {g = X45 • M3} {g' = M3 • X45} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00968.proved (MV00969.proved))) (trans (cong refl R085.proved) (move-product MV00969.proved (MV00968.proved))))

module r2b_ij456 where

  proved : X45 • M6 ≈ M6 • X45
  proved = GL.•-cancelʳ {g = X45 • M6} {g' = M6 • X45} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00970.proved (MV00971.proved))) (trans (cong refl R085.proved) (move-product MV00971.proved (MV00970.proved))))

module r2b_ij457 where

  proved : X45 • M7 ≈ M7 • X45
  proved = GL.•-cancelʳ {g = X45 • M7} {g' = M7 • X45} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00972.proved (MV00973.proved))) (trans (cong refl R085.proved) (move-product MV00973.proved (MV00972.proved))))

module r2b_ij460 where

  proved : X46 • M0 ≈ M0 • X46
  proved = GL.•-cancelʳ {g = X46 • M0} {g' = M0 • X46} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00974.proved (MV00975.proved))) (trans (cong refl R085.proved) (move-product MV00975.proved (MV00974.proved))))

module r2b_ij461 where

  proved : X46 • M1 ≈ M1 • X46
  proved = GL.•-cancelʳ {g = X46 • M1} {g' = M1 • X46} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00976.proved (MV00977.proved))) (trans (cong refl R085.proved) (move-product MV00977.proved (MV00976.proved))))

module r2b_ij462 where

  proved : X46 • M2 ≈ M2 • X46
  proved = GL.•-cancelʳ {g = X46 • M2} {g' = M2 • X46} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00978.proved (MV00979.proved))) (trans (cong refl R085.proved) (move-product MV00979.proved (MV00978.proved))))

module r2b_ij463 where

  proved : X46 • M3 ≈ M3 • X46
  proved = GL.•-cancelʳ {g = X46 • M3} {g' = M3 • X46} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00980.proved (MV00981.proved))) (trans (cong refl R085.proved) (move-product MV00981.proved (MV00980.proved))))

module r2b_ij465 where

  proved : X46 • M5 ≈ M5 • X46
  proved = GL.•-cancelʳ {g = X46 • M5} {g' = M5 • X46} {h = p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00982.proved (MV00983.proved))) (trans (cong refl R085.proved) (move-product MV00983.proved (MV00982.proved))))

module r2b_ij467 where

  proved : X46 • M7 ≈ M7 • X46
  proved = GL.•-cancelʳ {g = X46 • M7} {g' = M7 • X46} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00984.proved (MV00985.proved))) (trans (cong refl R085.proved) (move-product MV00985.proved (MV00984.proved))))

module r2b_ij470 where

  proved : X47 • M0 ≈ M0 • X47
  proved = GL.•-cancelʳ {g = X47 • M0} {g' = M0 • X47} {h = p (s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00986.proved (MV00987.proved))) (trans (cong refl R085.proved) (move-product MV00987.proved (MV00986.proved))))

module r2b_ij471 where

  proved : X47 • M1 ≈ M1 • X47
  proved = GL.•-cancelʳ {g = X47 • M1} {g' = M1 • X47} {h = p (s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00988.proved (MV00989.proved))) (trans (cong refl R085.proved) (move-product MV00989.proved (MV00988.proved))))

module r2b_ij472 where

  proved : X47 • M2 ≈ M2 • X47
  proved = GL.•-cancelʳ {g = X47 • M2} {g' = M2 • X47} {h = p (s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00990.proved (MV00991.proved))) (trans (cong refl R085.proved) (move-product MV00991.proved (MV00990.proved))))

module r2b_ij473 where

  proved : X47 • M3 ≈ M3 • X47
  proved = GL.•-cancelʳ {g = X47 • M3} {g' = M3 • X47} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00992.proved (MV00993.proved))) (trans (cong refl R085.proved) (move-product MV00993.proved (MV00992.proved))))

module r2b_ij475 where

  proved : X47 • M5 ≈ M5 • X47
  proved = GL.•-cancelʳ {g = X47 • M5} {g' = M5 • X47} {h = p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00994.proved (MV00995.proved))) (trans (cong refl R085.proved) (move-product MV00995.proved (MV00994.proved))))

module r2b_ij476 where

  proved : X47 • M6 ≈ M6 • X47
  proved = GL.•-cancelʳ {g = X47 • M6} {g' = M6 • X47} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00996.proved (MV00997.proved))) (trans (cong refl R085.proved) (move-product MV00997.proved (MV00996.proved))))

module r2b_ij560 where

  proved : X56 • M0 ≈ M0 • X56
  proved = GL.•-cancelʳ {g = X56 • M0} {g' = M0 • X56} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00998.proved (MV00999.proved))) (trans (cong refl R085.proved) (move-product MV00999.proved (MV00998.proved))))

module r2b_ij561 where

  proved : X56 • M1 ≈ M1 • X56
  proved = GL.•-cancelʳ {g = X56 • M1} {g' = M1 • X56} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01000.proved (MV01001.proved))) (trans (cong refl R085.proved) (move-product MV01001.proved (MV01000.proved))))

module r2b_ij562 where

  proved : X56 • M2 ≈ M2 • X56
  proved = GL.•-cancelʳ {g = X56 • M2} {g' = M2 • X56} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01002.proved (MV01003.proved))) (trans (cong refl R085.proved) (move-product MV01003.proved (MV01002.proved))))

module r2b_ij563 where

  proved : X56 • M3 ≈ M3 • X56
  proved = GL.•-cancelʳ {g = X56 • M3} {g' = M3 • X56} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01004.proved (MV01005.proved))) (trans (cong refl R085.proved) (move-product MV01005.proved (MV01004.proved))))

module r2b_ij564 where

  proved : X56 • M4 ≈ M4 • X56
  proved = GL.•-cancelʳ {g = X56 • M4} {g' = M4 • X56} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01006.proved (MV01007.proved))) (trans (cong refl R085.proved) (move-product MV01007.proved (MV01006.proved))))

module r2b_ij567 where

  proved : X56 • M7 ≈ M7 • X56
  proved = GL.•-cancelʳ {g = X56 • M7} {g' = M7 • X56} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01008.proved (MV01009.proved))) (trans (cong refl R085.proved) (move-product MV01009.proved (MV01008.proved))))

module r2b_ij570 where

  proved : X57 • M0 ≈ M0 • X57
  proved = GL.•-cancelʳ {g = X57 • M0} {g' = M0 • X57} {h = p (s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01010.proved (MV01011.proved))) (trans (cong refl R085.proved) (move-product MV01011.proved (MV01010.proved))))

module r2b_ij571 where

  proved : X57 • M1 ≈ M1 • X57
  proved = GL.•-cancelʳ {g = X57 • M1} {g' = M1 • X57} {h = p (s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01012.proved (MV01013.proved))) (trans (cong refl R085.proved) (move-product MV01013.proved (MV01012.proved))))

module r2b_ij572 where

  proved : X57 • M2 ≈ M2 • X57
  proved = GL.•-cancelʳ {g = X57 • M2} {g' = M2 • X57} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01014.proved (MV01015.proved))) (trans (cong refl R085.proved) (move-product MV01015.proved (MV01014.proved))))

module r2b_ij573 where

  proved : X57 • M3 ≈ M3 • X57
  proved = GL.•-cancelʳ {g = X57 • M3} {g' = M3 • X57} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01016.proved (MV01017.proved))) (trans (cong refl R085.proved) (move-product MV01017.proved (MV01016.proved))))

module r2b_ij574 where

  proved : X57 • M4 ≈ M4 • X57
  proved = GL.•-cancelʳ {g = X57 • M4} {g' = M4 • X57} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01018.proved (MV01019.proved))) (trans (cong refl R085.proved) (move-product MV01019.proved (MV01018.proved))))

module r2b_ij576 where

  proved : X57 • M6 ≈ M6 • X57
  proved = GL.•-cancelʳ {g = X57 • M6} {g' = M6 • X57} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01020.proved (MV01021.proved))) (trans (cong refl R085.proved) (move-product MV01021.proved (MV01020.proved))))

module r2b_ij670 where

  proved : X67 • M0 ≈ M0 • X67
  proved = GL.•-cancelʳ {g = X67 • M0} {g' = M0 • X67} {h = p (s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01022.proved (MV01023.proved))) (trans (cong refl R085.proved) (move-product MV01023.proved (MV01022.proved))))

module r2b_ij671 where

  proved : X67 • M1 ≈ M1 • X67
  proved = GL.•-cancelʳ {g = X67 • M1} {g' = M1 • X67} {h = p (s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01024.proved (MV01025.proved))) (trans (cong refl R085.proved) (move-product MV01025.proved (MV01024.proved))))

module r2b_ij672 where

  proved : X67 • M2 ≈ M2 • X67
  proved = GL.•-cancelʳ {g = X67 • M2} {g' = M2 • X67} {h = p (s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01026.proved (MV01027.proved))) (trans (cong refl R085.proved) (move-product MV01027.proved (MV01026.proved))))

module r2b_ij673 where

  proved : X67 • M3 ≈ M3 • X67
  proved = GL.•-cancelʳ {g = X67 • M3} {g' = M3 • X67} {h = p (s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01028.proved (MV01029.proved))) (trans (cong refl R085.proved) (move-product MV01029.proved (MV01028.proved))))

module r2b_ij674 where

  proved : X67 • M4 ≈ M4 • X67
  proved = GL.•-cancelʳ {g = X67 • M4} {g' = M4 • X67} {h = p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01030.proved (MV01031.proved))) (trans (cong refl R085.proved) (move-product MV01031.proved (MV01030.proved))))

module r2b_ij675 where

  proved : X67 • M5 ≈ M5 • X67
  proved = GL.•-cancelʳ {g = X67 • M5} {g' = M5 • X67} {h = p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV01032.proved (MV01033.proved))) (trans (cong refl R085.proved) (move-product MV01033.proved (MV01032.proved))))
