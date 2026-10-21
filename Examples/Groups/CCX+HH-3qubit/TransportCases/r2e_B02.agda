{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_B02 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0256 ; K0257 ; K0267 ; K0356 ; K0357 ; K0367 ; K0567 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3567 ; K4567 ; M3 ; M4 ; M5 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00032)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00641)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B047 using (module MV01805)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B054 using (module MV02075 ; module MV02076 ; module MV02077 ; module MV02078 ; module MV02079 ; module MV02080 ; module MV02081 ; module MV02082 ; module MV02083 ; module MV02084 ; module MV02085 ; module MV02086 ; module MV02087 ; module MV02088 ; module MV02089 ; module MV02090 ; module MV02091 ; module MV02092 ; module MV02093 ; module MV02094 ; module MV02095 ; module MV02096)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B055 using (module MV02097 ; module MV02098 ; module MV02099 ; module MV02100 ; module MV02101 ; module MV02102 ; module MV02103 ; module MV02104 ; module MV02105 ; module MV02106 ; module MV02107 ; module MV02108 ; module MV02109 ; module MV02110 ; module MV02111 ; module MV02112 ; module MV02113 ; module MV02114 ; module MV02115 ; module MV02116 ; module MV02117 ; module MV02118 ; module MV02119 ; module MV02120 ; module MV02121 ; module MV02122 ; module MV02123 ; module MV02124 ; module MV02125 ; module MV02126 ; module MV02127 ; module MV02128 ; module MV02129 ; module MV02130 ; module MV02131 ; module MV02132 ; module MV02133 ; module MV02134 ; module MV02135 ; module MV02136)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B056 using (module MV02137 ; module MV02138 ; module MV02139 ; module MV02140 ; module MV02141 ; module MV02142 ; module MV02143 ; module MV02144 ; module MV02145 ; module MV02146 ; module MV02147 ; module MV02148 ; module MV02149 ; module MV02150 ; module MV02151 ; module MV02152 ; module MV02153 ; module MV02154 ; module MV02155 ; module MV02156 ; module MV02157 ; module MV02158 ; module MV02159 ; module MV02160 ; module MV02161 ; module MV02162 ; module MV02163 ; module MV02164 ; module MV02165 ; module MV02166 ; module MV02167 ; module MV02168 ; module MV02169)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B057 using (module MV02170 ; module MV02171 ; module MV02172 ; module MV02173 ; module MV02174 ; module MV02175 ; module MV02176 ; module MV02177 ; module MV02178 ; module MV02179 ; module MV02180 ; module MV02181 ; module MV02182 ; module MV02183 ; module MV02184 ; module MV02185 ; module MV02186 ; module MV02187 ; module MV02188 ; module MV02189 ; module MV02190 ; module MV02191 ; module MV02192 ; module MV02193 ; module MV02194)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R094)

module r2e_ij30567 where

  proved : M3 • K0567 ≈ K0567 • M3
  proved = GL.•-cancelʳ {g = M3 • K0567} {g' = K0567 • M3} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02075.proved (MV02076.proved))) (trans (cong refl R094.proved) (move-product MV02076.proved (MV02075.proved))))

module r2e_ij31245 where

  proved : M3 • K1245 ≈ K1245 • M3
  proved = GL.•-cancelʳ {g = M3 • K1245} {g' = K1245 • M3} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s4)}
    (trans (sym (move-product MV02077.proved (MV02078.proved))) (trans (cong refl R094.proved) (move-product MV02078.proved (MV02077.proved))))

module r2e_ij31246 where

  proved : M3 • K1246 ≈ K1246 • M3
  proved = GL.•-cancelʳ {g = M3 • K1246} {g' = K1246 • M3} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02079.proved (MV02080.proved))) (trans (cong refl R094.proved) (move-product MV02080.proved (MV02079.proved))))

module r2e_ij31247 where

  proved : M3 • K1247 ≈ K1247 • M3
  proved = GL.•-cancelʳ {g = M3 • K1247} {g' = K1247 • M3} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02081.proved (MV02082.proved))) (trans (cong refl R094.proved) (move-product MV02082.proved (MV02081.proved))))

module r2e_ij31256 where

  proved : M3 • K1256 ≈ K1256 • M3
  proved = GL.•-cancelʳ {g = M3 • K1256} {g' = K1256 • M3} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02083.proved (MV02084.proved))) (trans (cong refl R094.proved) (move-product MV02084.proved (MV02083.proved))))

module r2e_ij31257 where

  proved : M3 • K1257 ≈ K1257 • M3
  proved = GL.•-cancelʳ {g = M3 • K1257} {g' = K1257 • M3} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02085.proved (MV02086.proved))) (trans (cong refl R094.proved) (move-product MV02086.proved (MV02085.proved))))

module r2e_ij31267 where

  proved : M3 • K1267 ≈ K1267 • M3
  proved = GL.•-cancelʳ {g = M3 • K1267} {g' = K1267 • M3} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02087.proved (MV02088.proved))) (trans (cong refl R094.proved) (move-product MV02088.proved (MV02087.proved))))

module r2e_ij31456 where

  proved : M3 • K1456 ≈ K1456 • M3
  proved = GL.•-cancelʳ {g = M3 • K1456} {g' = K1456 • M3} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02089.proved (MV02090.proved))) (trans (cong refl R094.proved) (move-product MV02090.proved (MV02089.proved))))

module r2e_ij31457 where

  proved : M3 • K1457 ≈ K1457 • M3
  proved = GL.•-cancelʳ {g = M3 • K1457} {g' = K1457 • M3} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02091.proved (MV02092.proved))) (trans (cong refl R094.proved) (move-product MV02092.proved (MV02091.proved))))

module r2e_ij31467 where

  proved : M3 • K1467 ≈ K1467 • M3
  proved = GL.•-cancelʳ {g = M3 • K1467} {g' = K1467 • M3} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02093.proved (MV02094.proved))) (trans (cong refl R094.proved) (move-product MV02094.proved (MV02093.proved))))

module r2e_ij31567 where

  proved : M3 • K1567 ≈ K1567 • M3
  proved = GL.•-cancelʳ {g = M3 • K1567} {g' = K1567 • M3} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02095.proved (MV02096.proved))) (trans (cong refl R094.proved) (move-product MV02096.proved (MV02095.proved))))

module r2e_ij32456 where

  proved : M3 • K2456 ≈ K2456 • M3
  proved = GL.•-cancelʳ {g = M3 • K2456} {g' = K2456 • M3} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02097.proved (MV02098.proved))) (trans (cong refl R094.proved) (move-product MV02098.proved (MV02097.proved))))

module r2e_ij32457 where

  proved : M3 • K2457 ≈ K2457 • M3
  proved = GL.•-cancelʳ {g = M3 • K2457} {g' = K2457 • M3} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02099.proved (MV02100.proved))) (trans (cong refl R094.proved) (move-product MV02100.proved (MV02099.proved))))

module r2e_ij32467 where

  proved : M3 • K2467 ≈ K2467 • M3
  proved = GL.•-cancelʳ {g = M3 • K2467} {g' = K2467 • M3} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02101.proved (MV02102.proved))) (trans (cong refl R094.proved) (move-product MV02102.proved (MV02101.proved))))

module r2e_ij32567 where

  proved : M3 • K2567 ≈ K2567 • M3
  proved = GL.•-cancelʳ {g = M3 • K2567} {g' = K2567 • M3} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02103.proved (MV02104.proved))) (trans (cong refl R094.proved) (move-product MV02104.proved (MV02103.proved))))

module r2e_ij34567 where

  proved : M3 • K4567 ≈ K4567 • M3
  proved = GL.•-cancelʳ {g = M3 • K4567} {g' = K4567 • M3} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02105.proved (MV02106.proved))) (trans (cong refl R094.proved) (move-product MV02106.proved (MV02105.proved))))

module r2e_ij40123 where

  proved : M4 • K0123 ≈ K0123 • M4
  proved = GL.•-cancelʳ {g = M4 • K0123} {g' = K0123 • M4} {h = p (ε)}
    (trans (sym (move-product MV01805.proved (MV00641.proved))) (trans (cong refl R094.proved) (move-product MV00641.proved (MV01805.proved))))

module r2e_ij40125 where

  proved : M4 • K0125 ≈ K0125 • M4
  proved = GL.•-cancelʳ {g = M4 • K0125} {g' = K0125 • M4} {h = p (s4 • s3 • s4)}
    (trans (sym (move-product MV02107.proved (MV02108.proved))) (trans (cong refl R094.proved) (move-product MV02108.proved (MV02107.proved))))

module r2e_ij40126 where

  proved : M4 • K0126 ≈ K0126 • M4
  proved = GL.•-cancelʳ {g = M4 • K0126} {g' = K0126 • M4} {h = p (s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02109.proved (MV02110.proved))) (trans (cong refl R094.proved) (move-product MV02110.proved (MV02109.proved))))

module r2e_ij40127 where

  proved : M4 • K0127 ≈ K0127 • M4
  proved = GL.•-cancelʳ {g = M4 • K0127} {g' = K0127 • M4} {h = p (s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02111.proved (MV02112.proved))) (trans (cong refl R094.proved) (move-product MV02112.proved (MV02111.proved))))

module r2e_ij40135 where

  proved : M4 • K0135 ≈ K0135 • M4
  proved = GL.•-cancelʳ {g = M4 • K0135} {g' = K0135 • M4} {h = p (s2 • s4 • s3 • s4)}
    (trans (sym (move-product MV02113.proved (MV02114.proved))) (trans (cong refl R094.proved) (move-product MV02114.proved (MV02113.proved))))

module r2e_ij40136 where

  proved : M4 • K0136 ≈ K0136 • M4
  proved = GL.•-cancelʳ {g = M4 • K0136} {g' = K0136 • M4} {h = p (s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02115.proved (MV02116.proved))) (trans (cong refl R094.proved) (move-product MV02116.proved (MV02115.proved))))

module r2e_ij40137 where

  proved : M4 • K0137 ≈ K0137 • M4
  proved = GL.•-cancelʳ {g = M4 • K0137} {g' = K0137 • M4} {h = p (s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02117.proved (MV02118.proved))) (trans (cong refl R094.proved) (move-product MV02118.proved (MV02117.proved))))

module r2e_ij40156 where

  proved : M4 • K0156 ≈ K0156 • M4
  proved = GL.•-cancelʳ {g = M4 • K0156} {g' = K0156 • M4} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02119.proved (MV02120.proved))) (trans (cong refl R094.proved) (move-product MV02120.proved (MV02119.proved))))

module r2e_ij40157 where

  proved : M4 • K0157 ≈ K0157 • M4
  proved = GL.•-cancelʳ {g = M4 • K0157} {g' = K0157 • M4} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02121.proved (MV02122.proved))) (trans (cong refl R094.proved) (move-product MV02122.proved (MV02121.proved))))

module r2e_ij40167 where

  proved : M4 • K0167 ≈ K0167 • M4
  proved = GL.•-cancelʳ {g = M4 • K0167} {g' = K0167 • M4} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02123.proved (MV02124.proved))) (trans (cong refl R094.proved) (move-product MV02124.proved (MV02123.proved))))

module r2e_ij40235 where

  proved : M4 • K0235 ≈ K0235 • M4
  proved = GL.•-cancelʳ {g = M4 • K0235} {g' = K0235 • M4} {h = p (s1 • s2 • s4 • s3 • s4)}
    (trans (sym (move-product MV02125.proved (MV02126.proved))) (trans (cong refl R094.proved) (move-product MV02126.proved (MV02125.proved))))

module r2e_ij40236 where

  proved : M4 • K0236 ≈ K0236 • M4
  proved = GL.•-cancelʳ {g = M4 • K0236} {g' = K0236 • M4} {h = p (s1 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02127.proved (MV02128.proved))) (trans (cong refl R094.proved) (move-product MV02128.proved (MV02127.proved))))

module r2e_ij40237 where

  proved : M4 • K0237 ≈ K0237 • M4
  proved = GL.•-cancelʳ {g = M4 • K0237} {g' = K0237 • M4} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02129.proved (MV02130.proved))) (trans (cong refl R094.proved) (move-product MV02130.proved (MV02129.proved))))

module r2e_ij40256 where

  proved : M4 • K0256 ≈ K0256 • M4
  proved = GL.•-cancelʳ {g = M4 • K0256} {g' = K0256 • M4} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02131.proved (MV02132.proved))) (trans (cong refl R094.proved) (move-product MV02132.proved (MV02131.proved))))

module r2e_ij40257 where

  proved : M4 • K0257 ≈ K0257 • M4
  proved = GL.•-cancelʳ {g = M4 • K0257} {g' = K0257 • M4} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02133.proved (MV02134.proved))) (trans (cong refl R094.proved) (move-product MV02134.proved (MV02133.proved))))

module r2e_ij40267 where

  proved : M4 • K0267 ≈ K0267 • M4
  proved = GL.•-cancelʳ {g = M4 • K0267} {g' = K0267 • M4} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02135.proved (MV02136.proved))) (trans (cong refl R094.proved) (move-product MV02136.proved (MV02135.proved))))

module r2e_ij40356 where

  proved : M4 • K0356 ≈ K0356 • M4
  proved = GL.•-cancelʳ {g = M4 • K0356} {g' = K0356 • M4} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02137.proved (MV02138.proved))) (trans (cong refl R094.proved) (move-product MV02138.proved (MV02137.proved))))

module r2e_ij40357 where

  proved : M4 • K0357 ≈ K0357 • M4
  proved = GL.•-cancelʳ {g = M4 • K0357} {g' = K0357 • M4} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02139.proved (MV02140.proved))) (trans (cong refl R094.proved) (move-product MV02140.proved (MV02139.proved))))

module r2e_ij40367 where

  proved : M4 • K0367 ≈ K0367 • M4
  proved = GL.•-cancelʳ {g = M4 • K0367} {g' = K0367 • M4} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02141.proved (MV02142.proved))) (trans (cong refl R094.proved) (move-product MV02142.proved (MV02141.proved))))

module r2e_ij40567 where

  proved : M4 • K0567 ≈ K0567 • M4
  proved = GL.•-cancelʳ {g = M4 • K0567} {g' = K0567 • M4} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02143.proved (MV02144.proved))) (trans (cong refl R094.proved) (move-product MV02144.proved (MV02143.proved))))

module r2e_ij41235 where

  proved : M4 • K1235 ≈ K1235 • M4
  proved = GL.•-cancelʳ {g = M4 • K1235} {g' = K1235 • M4} {h = p (s0 • s1 • s2 • s4 • s3 • s4)}
    (trans (sym (move-product MV02145.proved (MV02146.proved))) (trans (cong refl R094.proved) (move-product MV02146.proved (MV02145.proved))))

module r2e_ij41236 where

  proved : M4 • K1236 ≈ K1236 • M4
  proved = GL.•-cancelʳ {g = M4 • K1236} {g' = K1236 • M4} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02147.proved (MV02148.proved))) (trans (cong refl R094.proved) (move-product MV02148.proved (MV02147.proved))))

module r2e_ij41237 where

  proved : M4 • K1237 ≈ K1237 • M4
  proved = GL.•-cancelʳ {g = M4 • K1237} {g' = K1237 • M4} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV02149.proved (MV02150.proved))) (trans (cong refl R094.proved) (move-product MV02150.proved (MV02149.proved))))

module r2e_ij41256 where

  proved : M4 • K1256 ≈ K1256 • M4
  proved = GL.•-cancelʳ {g = M4 • K1256} {g' = K1256 • M4} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02151.proved (MV02152.proved))) (trans (cong refl R094.proved) (move-product MV02152.proved (MV02151.proved))))

module r2e_ij41257 where

  proved : M4 • K1257 ≈ K1257 • M4
  proved = GL.•-cancelʳ {g = M4 • K1257} {g' = K1257 • M4} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02153.proved (MV02154.proved))) (trans (cong refl R094.proved) (move-product MV02154.proved (MV02153.proved))))

module r2e_ij41267 where

  proved : M4 • K1267 ≈ K1267 • M4
  proved = GL.•-cancelʳ {g = M4 • K1267} {g' = K1267 • M4} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02155.proved (MV02156.proved))) (trans (cong refl R094.proved) (move-product MV02156.proved (MV02155.proved))))

module r2e_ij41356 where

  proved : M4 • K1356 ≈ K1356 • M4
  proved = GL.•-cancelʳ {g = M4 • K1356} {g' = K1356 • M4} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02157.proved (MV02158.proved))) (trans (cong refl R094.proved) (move-product MV02158.proved (MV02157.proved))))

module r2e_ij41357 where

  proved : M4 • K1357 ≈ K1357 • M4
  proved = GL.•-cancelʳ {g = M4 • K1357} {g' = K1357 • M4} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02159.proved (MV02160.proved))) (trans (cong refl R094.proved) (move-product MV02160.proved (MV02159.proved))))

module r2e_ij41367 where

  proved : M4 • K1367 ≈ K1367 • M4
  proved = GL.•-cancelʳ {g = M4 • K1367} {g' = K1367 • M4} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02161.proved (MV02162.proved))) (trans (cong refl R094.proved) (move-product MV02162.proved (MV02161.proved))))

module r2e_ij41567 where

  proved : M4 • K1567 ≈ K1567 • M4
  proved = GL.•-cancelʳ {g = M4 • K1567} {g' = K1567 • M4} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02163.proved (MV02164.proved))) (trans (cong refl R094.proved) (move-product MV02164.proved (MV02163.proved))))

module r2e_ij42356 where

  proved : M4 • K2356 ≈ K2356 • M4
  proved = GL.•-cancelʳ {g = M4 • K2356} {g' = K2356 • M4} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02165.proved (MV02166.proved))) (trans (cong refl R094.proved) (move-product MV02166.proved (MV02165.proved))))

module r2e_ij42357 where

  proved : M4 • K2357 ≈ K2357 • M4
  proved = GL.•-cancelʳ {g = M4 • K2357} {g' = K2357 • M4} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02167.proved (MV02168.proved))) (trans (cong refl R094.proved) (move-product MV02168.proved (MV02167.proved))))

module r2e_ij42367 where

  proved : M4 • K2367 ≈ K2367 • M4
  proved = GL.•-cancelʳ {g = M4 • K2367} {g' = K2367 • M4} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02169.proved (MV02170.proved))) (trans (cong refl R094.proved) (move-product MV02170.proved (MV02169.proved))))

module r2e_ij42567 where

  proved : M4 • K2567 ≈ K2567 • M4
  proved = GL.•-cancelʳ {g = M4 • K2567} {g' = K2567 • M4} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02171.proved (MV02172.proved))) (trans (cong refl R094.proved) (move-product MV02172.proved (MV02171.proved))))

module r2e_ij43567 where

  proved : M4 • K3567 ≈ K3567 • M4
  proved = GL.•-cancelʳ {g = M4 • K3567} {g' = K3567 • M4} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02173.proved (MV02174.proved))) (trans (cong refl R094.proved) (move-product MV02174.proved (MV02173.proved))))

module r2e_ij50123 where

  proved : M5 • K0123 ≈ K0123 • M5
  proved = GL.•-cancelʳ {g = M5 • K0123} {g' = K0123 • M5} {h = p (s4)}
    (trans (sym (move-product MV00032.proved (MV00246.proved))) (trans (cong refl R094.proved) (move-product MV00246.proved (MV00032.proved))))

module r2e_ij50124 where

  proved : M5 • K0124 ≈ K0124 • M5
  proved = GL.•-cancelʳ {g = M5 • K0124} {g' = K0124 • M5} {h = p (s3 • s4)}
    (trans (sym (move-product MV02175.proved (MV02176.proved))) (trans (cong refl R094.proved) (move-product MV02176.proved (MV02175.proved))))

module r2e_ij50126 where

  proved : M5 • K0126 ≈ K0126 • M5
  proved = GL.•-cancelʳ {g = M5 • K0126} {g' = K0126 • M5} {h = p (s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02177.proved (MV02178.proved))) (trans (cong refl R094.proved) (move-product MV02178.proved (MV02177.proved))))

module r2e_ij50127 where

  proved : M5 • K0127 ≈ K0127 • M5
  proved = GL.•-cancelʳ {g = M5 • K0127} {g' = K0127 • M5} {h = p (s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02179.proved (MV02180.proved))) (trans (cong refl R094.proved) (move-product MV02180.proved (MV02179.proved))))

module r2e_ij50134 where

  proved : M5 • K0134 ≈ K0134 • M5
  proved = GL.•-cancelʳ {g = M5 • K0134} {g' = K0134 • M5} {h = p (s2 • s3 • s4)}
    (trans (sym (move-product MV02181.proved (MV02182.proved))) (trans (cong refl R094.proved) (move-product MV02182.proved (MV02181.proved))))

module r2e_ij50136 where

  proved : M5 • K0136 ≈ K0136 • M5
  proved = GL.•-cancelʳ {g = M5 • K0136} {g' = K0136 • M5} {h = p (s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02183.proved (MV02184.proved))) (trans (cong refl R094.proved) (move-product MV02184.proved (MV02183.proved))))

module r2e_ij50137 where

  proved : M5 • K0137 ≈ K0137 • M5
  proved = GL.•-cancelʳ {g = M5 • K0137} {g' = K0137 • M5} {h = p (s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02185.proved (MV02186.proved))) (trans (cong refl R094.proved) (move-product MV02186.proved (MV02185.proved))))

module r2e_ij50146 where

  proved : M5 • K0146 ≈ K0146 • M5
  proved = GL.•-cancelʳ {g = M5 • K0146} {g' = K0146 • M5} {h = p (s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02187.proved (MV02188.proved))) (trans (cong refl R094.proved) (move-product MV02188.proved (MV02187.proved))))

module r2e_ij50147 where

  proved : M5 • K0147 ≈ K0147 • M5
  proved = GL.•-cancelʳ {g = M5 • K0147} {g' = K0147 • M5} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02189.proved (MV02190.proved))) (trans (cong refl R094.proved) (move-product MV02190.proved (MV02189.proved))))

module r2e_ij50167 where

  proved : M5 • K0167 ≈ K0167 • M5
  proved = GL.•-cancelʳ {g = M5 • K0167} {g' = K0167 • M5} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02191.proved (MV02192.proved))) (trans (cong refl R094.proved) (move-product MV02192.proved (MV02191.proved))))

module r2e_ij50234 where

  proved : M5 • K0234 ≈ K0234 • M5
  proved = GL.•-cancelʳ {g = M5 • K0234} {g' = K0234 • M5} {h = p (s1 • s2 • s3 • s4)}
    (trans (sym (move-product MV02193.proved (MV02194.proved))) (trans (cong refl R094.proved) (move-product MV02194.proved (MV02193.proved))))
