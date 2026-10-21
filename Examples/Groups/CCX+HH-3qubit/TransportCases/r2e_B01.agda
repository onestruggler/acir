{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_B01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; M1 ; M2 ; M3 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as R094
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00031)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00642 ; module MV00643)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00644 ; module MV00645 ; module MV00646 ; module MV00647 ; module MV00648 ; module MV00649 ; module MV00650 ; module MV00651 ; module MV00652 ; module MV00653 ; module MV00654)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B047 using (module MV01804)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B051 using (module MV01967 ; module MV01968 ; module MV01969 ; module MV01970 ; module MV01971 ; module MV01972 ; module MV01973 ; module MV01974 ; module MV01975 ; module MV01976 ; module MV01977 ; module MV01978 ; module MV01979 ; module MV01980 ; module MV01981 ; module MV01982 ; module MV01983 ; module MV01984 ; module MV01985 ; module MV01986 ; module MV01987 ; module MV01988)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B052 using (module MV01989 ; module MV01990 ; module MV01991 ; module MV01992 ; module MV01993 ; module MV01994 ; module MV01995 ; module MV01996 ; module MV01997 ; module MV01998 ; module MV01999 ; module MV02000 ; module MV02001 ; module MV02002 ; module MV02003 ; module MV02004 ; module MV02005 ; module MV02006 ; module MV02007 ; module MV02008 ; module MV02009 ; module MV02010 ; module MV02011 ; module MV02012 ; module MV02013 ; module MV02014 ; module MV02015 ; module MV02016 ; module MV02017 ; module MV02018 ; module MV02019 ; module MV02020 ; module MV02021 ; module MV02022 ; module MV02023 ; module MV02024 ; module MV02025)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B053 using (module MV02026 ; module MV02027 ; module MV02028 ; module MV02029 ; module MV02030 ; module MV02031 ; module MV02032 ; module MV02033 ; module MV02034 ; module MV02035 ; module MV02036 ; module MV02037 ; module MV02038 ; module MV02039 ; module MV02040 ; module MV02041 ; module MV02042 ; module MV02043 ; module MV02044 ; module MV02045 ; module MV02046 ; module MV02047 ; module MV02048 ; module MV02049 ; module MV02050 ; module MV02051 ; module MV02052 ; module MV02053 ; module MV02054 ; module MV02055 ; module MV02056 ; module MV02057 ; module MV02058 ; module MV02059 ; module MV02060 ; module MV02061 ; module MV02062)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B054 using (module MV02063 ; module MV02064 ; module MV02065 ; module MV02066 ; module MV02067 ; module MV02068 ; module MV02069 ; module MV02070 ; module MV02071 ; module MV02072 ; module MV02073 ; module MV02074)

module r2e_ij12457 where

  proved : M1 • K2457 ≈ K2457 • M1
  proved = GL.•-cancelʳ {g = M1 • K2457} {g' = K2457 • M1} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01967.proved (MV01968.proved))) (trans (cong refl R094.proved) (move-product MV01968.proved (MV01967.proved))))

module r2e_ij12467 where

  proved : M1 • K2467 ≈ K2467 • M1
  proved = GL.•-cancelʳ {g = M1 • K2467} {g' = K2467 • M1} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01969.proved (MV01970.proved))) (trans (cong refl R094.proved) (move-product MV01970.proved (MV01969.proved))))

module r2e_ij12567 where

  proved : M1 • K2567 ≈ K2567 • M1
  proved = GL.•-cancelʳ {g = M1 • K2567} {g' = K2567 • M1} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01971.proved (MV01972.proved))) (trans (cong refl R094.proved) (move-product MV01972.proved (MV01971.proved))))

module r2e_ij13456 where

  proved : M1 • K3456 ≈ K3456 • M1
  proved = GL.•-cancelʳ {g = M1 • K3456} {g' = K3456 • M1} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01973.proved (MV01974.proved))) (trans (cong refl R094.proved) (move-product MV01974.proved (MV01973.proved))))

module r2e_ij13457 where

  proved : M1 • K3457 ≈ K3457 • M1
  proved = GL.•-cancelʳ {g = M1 • K3457} {g' = K3457 • M1} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01975.proved (MV01976.proved))) (trans (cong refl R094.proved) (move-product MV01976.proved (MV01975.proved))))

module r2e_ij13467 where

  proved : M1 • K3467 ≈ K3467 • M1
  proved = GL.•-cancelʳ {g = M1 • K3467} {g' = K3467 • M1} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01977.proved (MV01978.proved))) (trans (cong refl R094.proved) (move-product MV01978.proved (MV01977.proved))))

module r2e_ij13567 where

  proved : M1 • K3567 ≈ K3567 • M1
  proved = GL.•-cancelʳ {g = M1 • K3567} {g' = K3567 • M1} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01979.proved (MV01980.proved))) (trans (cong refl R094.proved) (move-product MV01980.proved (MV01979.proved))))

module r2e_ij14567 where

  proved : M1 • K4567 ≈ K4567 • M1
  proved = GL.•-cancelʳ {g = M1 • K4567} {g' = K4567 • M1} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01981.proved (MV01982.proved))) (trans (cong refl R094.proved) (move-product MV01982.proved (MV01981.proved))))

module r2e_ij20134 where

  proved : M2 • K0134 ≈ K0134 • M2
  proved = GL.•-cancelʳ {g = M2 • K0134} {g' = K0134 • M2} {h = p (s2 • s3)}
    (trans (sym (move-product MV01804.proved (MV00645.proved))) (trans (cong refl R094.proved) (move-product MV00645.proved (MV01804.proved))))

module r2e_ij20135 where

  proved : M2 • K0135 ≈ K0135 • M2
  proved = GL.•-cancelʳ {g = M2 • K0135} {g' = K0135 • M2} {h = p (s2 • s4 • s3)}
    (trans (sym (move-product MV01983.proved (MV00646.proved))) (trans (cong refl R094.proved) (move-product MV00646.proved (MV01983.proved))))

module r2e_ij20136 where

  proved : M2 • K0136 ≈ K0136 • M2
  proved = GL.•-cancelʳ {g = M2 • K0136} {g' = K0136 • M2} {h = p (s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01984.proved (MV00647.proved))) (trans (cong refl R094.proved) (move-product MV00647.proved (MV01984.proved))))

module r2e_ij20137 where

  proved : M2 • K0137 ≈ K0137 • M2
  proved = GL.•-cancelʳ {g = M2 • K0137} {g' = K0137 • M2} {h = p (s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01985.proved (MV00648.proved))) (trans (cong refl R094.proved) (move-product MV00648.proved (MV01985.proved))))

module r2e_ij20145 where

  proved : M2 • K0145 ≈ K0145 • M2
  proved = GL.•-cancelʳ {g = M2 • K0145} {g' = K0145 • M2} {h = p (s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01986.proved (MV00649.proved))) (trans (cong refl R094.proved) (move-product MV00649.proved (MV01986.proved))))

module r2e_ij20146 where

  proved : M2 • K0146 ≈ K0146 • M2
  proved = GL.•-cancelʳ {g = M2 • K0146} {g' = K0146 • M2} {h = p (s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01987.proved (MV00650.proved))) (trans (cong refl R094.proved) (move-product MV00650.proved (MV01987.proved))))

module r2e_ij20147 where

  proved : M2 • K0147 ≈ K0147 • M2
  proved = GL.•-cancelʳ {g = M2 • K0147} {g' = K0147 • M2} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01988.proved (MV00651.proved))) (trans (cong refl R094.proved) (move-product MV00651.proved (MV01988.proved))))

module r2e_ij20156 where

  proved : M2 • K0156 ≈ K0156 • M2
  proved = GL.•-cancelʳ {g = M2 • K0156} {g' = K0156 • M2} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01989.proved (MV00652.proved))) (trans (cong refl R094.proved) (move-product MV00652.proved (MV01989.proved))))

module r2e_ij20157 where

  proved : M2 • K0157 ≈ K0157 • M2
  proved = GL.•-cancelʳ {g = M2 • K0157} {g' = K0157 • M2} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01990.proved (MV00653.proved))) (trans (cong refl R094.proved) (move-product MV00653.proved (MV01990.proved))))

module r2e_ij20167 where

  proved : M2 • K0167 ≈ K0167 • M2
  proved = GL.•-cancelʳ {g = M2 • K0167} {g' = K0167 • M2} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01991.proved (MV00654.proved))) (trans (cong refl R094.proved) (move-product MV00654.proved (MV01991.proved))))

module r2e_ij20345 where

  proved : M2 • K0345 ≈ K0345 • M2
  proved = GL.•-cancelʳ {g = M2 • K0345} {g' = K0345 • M2} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s4)}
    (trans (sym (move-product MV01992.proved (MV01993.proved))) (trans (cong refl R094.proved) (move-product MV01993.proved (MV01992.proved))))

module r2e_ij20346 where

  proved : M2 • K0346 ≈ K0346 • M2
  proved = GL.•-cancelʳ {g = M2 • K0346} {g' = K0346 • M2} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01994.proved (MV01995.proved))) (trans (cong refl R094.proved) (move-product MV01995.proved (MV01994.proved))))

module r2e_ij20347 where

  proved : M2 • K0347 ≈ K0347 • M2
  proved = GL.•-cancelʳ {g = M2 • K0347} {g' = K0347 • M2} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01996.proved (MV01997.proved))) (trans (cong refl R094.proved) (move-product MV01997.proved (MV01996.proved))))

module r2e_ij20356 where

  proved : M2 • K0356 ≈ K0356 • M2
  proved = GL.•-cancelʳ {g = M2 • K0356} {g' = K0356 • M2} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01998.proved (MV01999.proved))) (trans (cong refl R094.proved) (move-product MV01999.proved (MV01998.proved))))

module r2e_ij20357 where

  proved : M2 • K0357 ≈ K0357 • M2
  proved = GL.•-cancelʳ {g = M2 • K0357} {g' = K0357 • M2} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02000.proved (MV02001.proved))) (trans (cong refl R094.proved) (move-product MV02001.proved (MV02000.proved))))

module r2e_ij20367 where

  proved : M2 • K0367 ≈ K0367 • M2
  proved = GL.•-cancelʳ {g = M2 • K0367} {g' = K0367 • M2} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02002.proved (MV02003.proved))) (trans (cong refl R094.proved) (move-product MV02003.proved (MV02002.proved))))

module r2e_ij20456 where

  proved : M2 • K0456 ≈ K0456 • M2
  proved = GL.•-cancelʳ {g = M2 • K0456} {g' = K0456 • M2} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02004.proved (MV02005.proved))) (trans (cong refl R094.proved) (move-product MV02005.proved (MV02004.proved))))

module r2e_ij20457 where

  proved : M2 • K0457 ≈ K0457 • M2
  proved = GL.•-cancelʳ {g = M2 • K0457} {g' = K0457 • M2} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02006.proved (MV02007.proved))) (trans (cong refl R094.proved) (move-product MV02007.proved (MV02006.proved))))

module r2e_ij20467 where

  proved : M2 • K0467 ≈ K0467 • M2
  proved = GL.•-cancelʳ {g = M2 • K0467} {g' = K0467 • M2} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02008.proved (MV02009.proved))) (trans (cong refl R094.proved) (move-product MV02009.proved (MV02008.proved))))

module r2e_ij20567 where

  proved : M2 • K0567 ≈ K0567 • M2
  proved = GL.•-cancelʳ {g = M2 • K0567} {g' = K0567 • M2} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02010.proved (MV02011.proved))) (trans (cong refl R094.proved) (move-product MV02011.proved (MV02010.proved))))

module r2e_ij21345 where

  proved : M2 • K1345 ≈ K1345 • M2
  proved = GL.•-cancelʳ {g = M2 • K1345} {g' = K1345 • M2} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4)}
    (trans (sym (move-product MV02012.proved (MV02013.proved))) (trans (cong refl R094.proved) (move-product MV02013.proved (MV02012.proved))))

module r2e_ij21346 where

  proved : M2 • K1346 ≈ K1346 • M2
  proved = GL.•-cancelʳ {g = M2 • K1346} {g' = K1346 • M2} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02014.proved (MV02015.proved))) (trans (cong refl R094.proved) (move-product MV02015.proved (MV02014.proved))))

module r2e_ij21347 where

  proved : M2 • K1347 ≈ K1347 • M2
  proved = GL.•-cancelʳ {g = M2 • K1347} {g' = K1347 • M2} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02016.proved (MV02017.proved))) (trans (cong refl R094.proved) (move-product MV02017.proved (MV02016.proved))))

module r2e_ij21356 where

  proved : M2 • K1356 ≈ K1356 • M2
  proved = GL.•-cancelʳ {g = M2 • K1356} {g' = K1356 • M2} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02018.proved (MV02019.proved))) (trans (cong refl R094.proved) (move-product MV02019.proved (MV02018.proved))))

module r2e_ij21357 where

  proved : M2 • K1357 ≈ K1357 • M2
  proved = GL.•-cancelʳ {g = M2 • K1357} {g' = K1357 • M2} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02020.proved (MV02021.proved))) (trans (cong refl R094.proved) (move-product MV02021.proved (MV02020.proved))))

module r2e_ij21367 where

  proved : M2 • K1367 ≈ K1367 • M2
  proved = GL.•-cancelʳ {g = M2 • K1367} {g' = K1367 • M2} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02022.proved (MV02023.proved))) (trans (cong refl R094.proved) (move-product MV02023.proved (MV02022.proved))))

module r2e_ij21456 where

  proved : M2 • K1456 ≈ K1456 • M2
  proved = GL.•-cancelʳ {g = M2 • K1456} {g' = K1456 • M2} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02024.proved (MV02025.proved))) (trans (cong refl R094.proved) (move-product MV02025.proved (MV02024.proved))))

module r2e_ij21457 where

  proved : M2 • K1457 ≈ K1457 • M2
  proved = GL.•-cancelʳ {g = M2 • K1457} {g' = K1457 • M2} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02026.proved (MV02027.proved))) (trans (cong refl R094.proved) (move-product MV02027.proved (MV02026.proved))))

module r2e_ij21467 where

  proved : M2 • K1467 ≈ K1467 • M2
  proved = GL.•-cancelʳ {g = M2 • K1467} {g' = K1467 • M2} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02028.proved (MV02029.proved))) (trans (cong refl R094.proved) (move-product MV02029.proved (MV02028.proved))))

module r2e_ij21567 where

  proved : M2 • K1567 ≈ K1567 • M2
  proved = GL.•-cancelʳ {g = M2 • K1567} {g' = K1567 • M2} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02030.proved (MV02031.proved))) (trans (cong refl R094.proved) (move-product MV02031.proved (MV02030.proved))))

module r2e_ij23456 where

  proved : M2 • K3456 ≈ K3456 • M2
  proved = GL.•-cancelʳ {g = M2 • K3456} {g' = K3456 • M2} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02032.proved (MV02033.proved))) (trans (cong refl R094.proved) (move-product MV02033.proved (MV02032.proved))))

module r2e_ij23457 where

  proved : M2 • K3457 ≈ K3457 • M2
  proved = GL.•-cancelʳ {g = M2 • K3457} {g' = K3457 • M2} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02034.proved (MV02035.proved))) (trans (cong refl R094.proved) (move-product MV02035.proved (MV02034.proved))))

module r2e_ij23467 where

  proved : M2 • K3467 ≈ K3467 • M2
  proved = GL.•-cancelʳ {g = M2 • K3467} {g' = K3467 • M2} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02036.proved (MV02037.proved))) (trans (cong refl R094.proved) (move-product MV02037.proved (MV02036.proved))))

module r2e_ij23567 where

  proved : M2 • K3567 ≈ K3567 • M2
  proved = GL.•-cancelʳ {g = M2 • K3567} {g' = K3567 • M2} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02038.proved (MV02039.proved))) (trans (cong refl R094.proved) (move-product MV02039.proved (MV02038.proved))))

module r2e_ij24567 where

  proved : M2 • K4567 ≈ K4567 • M2
  proved = GL.•-cancelʳ {g = M2 • K4567} {g' = K4567 • M2} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02040.proved (MV02041.proved))) (trans (cong refl R094.proved) (move-product MV02041.proved (MV02040.proved))))

module r2e_ij30124 where

  proved : M3 • K0124 ≈ K0124 • M3
  proved = GL.•-cancelʳ {g = M3 • K0124} {g' = K0124 • M3} {h = p (s3)}
    (trans (sym (move-product MV00031.proved (MV00245.proved))) (trans (cong refl R094.proved) (move-product MV00245.proved (MV00031.proved))))

module r2e_ij30125 where

  proved : M3 • K0125 ≈ K0125 • M3
  proved = GL.•-cancelʳ {g = M3 • K0125} {g' = K0125 • M3} {h = p (s4 • s3)}
    (trans (sym (move-product MV02042.proved (MV00642.proved))) (trans (cong refl R094.proved) (move-product MV00642.proved (MV02042.proved))))

module r2e_ij30126 where

  proved : M3 • K0126 ≈ K0126 • M3
  proved = GL.•-cancelʳ {g = M3 • K0126} {g' = K0126 • M3} {h = p (s5 • s4 • s3)}
    (trans (sym (move-product MV02043.proved (MV00643.proved))) (trans (cong refl R094.proved) (move-product MV00643.proved (MV02043.proved))))

module r2e_ij30127 where

  proved : M3 • K0127 ≈ K0127 • M3
  proved = GL.•-cancelʳ {g = M3 • K0127} {g' = K0127 • M3} {h = p (s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02044.proved (MV00644.proved))) (trans (cong refl R094.proved) (move-product MV00644.proved (MV02044.proved))))

module r2e_ij30145 where

  proved : M3 • K0145 ≈ K0145 • M3
  proved = GL.•-cancelʳ {g = M3 • K0145} {g' = K0145 • M3} {h = p (s3 • s2 • s4 • s3 • s4)}
    (trans (sym (move-product MV02045.proved (MV02046.proved))) (trans (cong refl R094.proved) (move-product MV02046.proved (MV02045.proved))))

module r2e_ij30146 where

  proved : M3 • K0146 ≈ K0146 • M3
  proved = GL.•-cancelʳ {g = M3 • K0146} {g' = K0146 • M3} {h = p (s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02047.proved (MV02048.proved))) (trans (cong refl R094.proved) (move-product MV02048.proved (MV02047.proved))))

module r2e_ij30147 where

  proved : M3 • K0147 ≈ K0147 • M3
  proved = GL.•-cancelʳ {g = M3 • K0147} {g' = K0147 • M3} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02049.proved (MV02050.proved))) (trans (cong refl R094.proved) (move-product MV02050.proved (MV02049.proved))))

module r2e_ij30156 where

  proved : M3 • K0156 ≈ K0156 • M3
  proved = GL.•-cancelʳ {g = M3 • K0156} {g' = K0156 • M3} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02051.proved (MV02052.proved))) (trans (cong refl R094.proved) (move-product MV02052.proved (MV02051.proved))))

module r2e_ij30157 where

  proved : M3 • K0157 ≈ K0157 • M3
  proved = GL.•-cancelʳ {g = M3 • K0157} {g' = K0157 • M3} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02053.proved (MV02054.proved))) (trans (cong refl R094.proved) (move-product MV02054.proved (MV02053.proved))))

module r2e_ij30167 where

  proved : M3 • K0167 ≈ K0167 • M3
  proved = GL.•-cancelʳ {g = M3 • K0167} {g' = K0167 • M3} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02055.proved (MV02056.proved))) (trans (cong refl R094.proved) (move-product MV02056.proved (MV02055.proved))))

module r2e_ij30245 where

  proved : M3 • K0245 ≈ K0245 • M3
  proved = GL.•-cancelʳ {g = M3 • K0245} {g' = K0245 • M3} {h = p (s1 • s3 • s2 • s4 • s3 • s4)}
    (trans (sym (move-product MV02057.proved (MV02058.proved))) (trans (cong refl R094.proved) (move-product MV02058.proved (MV02057.proved))))

module r2e_ij30246 where

  proved : M3 • K0246 ≈ K0246 • M3
  proved = GL.•-cancelʳ {g = M3 • K0246} {g' = K0246 • M3} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02059.proved (MV02060.proved))) (trans (cong refl R094.proved) (move-product MV02060.proved (MV02059.proved))))

module r2e_ij30247 where

  proved : M3 • K0247 ≈ K0247 • M3
  proved = GL.•-cancelʳ {g = M3 • K0247} {g' = K0247 • M3} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02061.proved (MV02062.proved))) (trans (cong refl R094.proved) (move-product MV02062.proved (MV02061.proved))))

module r2e_ij30256 where

  proved : M3 • K0256 ≈ K0256 • M3
  proved = GL.•-cancelʳ {g = M3 • K0256} {g' = K0256 • M3} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02063.proved (MV02064.proved))) (trans (cong refl R094.proved) (move-product MV02064.proved (MV02063.proved))))

module r2e_ij30257 where

  proved : M3 • K0257 ≈ K0257 • M3
  proved = GL.•-cancelʳ {g = M3 • K0257} {g' = K0257 • M3} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02065.proved (MV02066.proved))) (trans (cong refl R094.proved) (move-product MV02066.proved (MV02065.proved))))

module r2e_ij30267 where

  proved : M3 • K0267 ≈ K0267 • M3
  proved = GL.•-cancelʳ {g = M3 • K0267} {g' = K0267 • M3} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02067.proved (MV02068.proved))) (trans (cong refl R094.proved) (move-product MV02068.proved (MV02067.proved))))

module r2e_ij30456 where

  proved : M3 • K0456 ≈ K0456 • M3
  proved = GL.•-cancelʳ {g = M3 • K0456} {g' = K0456 • M3} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02069.proved (MV02070.proved))) (trans (cong refl R094.proved) (move-product MV02070.proved (MV02069.proved))))

module r2e_ij30457 where

  proved : M3 • K0457 ≈ K0457 • M3
  proved = GL.•-cancelʳ {g = M3 • K0457} {g' = K0457 • M3} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02071.proved (MV02072.proved))) (trans (cong refl R094.proved) (move-product MV02072.proved (MV02071.proved))))

module r2e_ij30467 where

  proved : M3 • K0467 ≈ K0467 • M3
  proved = GL.•-cancelʳ {g = M3 • K0467} {g' = K0467 • M3} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02073.proved (MV02074.proved))) (trans (cong refl R094.proved) (move-product MV02074.proved (MV02073.proved))))
