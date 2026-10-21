{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0134 ; K0135 ; K0136 ; K0145 ; K0146 ; K0234 ; K0235 ; K0236 ; K0245 ; K0246 ; K0345 ; K0346 ; K1234 ; K1235 ; K1236 ; K1245 ; K1246 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as R100
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00252)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00500)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00557)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00641)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B044 using (module MV01682)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B045 using (module MV01712 ; module MV01714 ; module MV01718 ; module MV01724)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B046 using (module MV01732 ; module MV01742 ; module MV01744 ; module MV01748 ; module MV01754 ; module MV01762)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B047 using (module MV01772 ; module MV01774 ; module MV01776 ; module MV01778 ; module MV01780 ; module MV01782 ; module MV01784 ; module MV01786 ; module MV01788 ; module MV01790 ; module MV01792 ; module MV01794 ; module MV01796 ; module MV01798 ; module MV01800)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B076 using (module MV03032 ; module MV03033 ; module MV03034)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B077 using (module MV03035 ; module MV03036 ; module MV03037 ; module MV03038 ; module MV03039 ; module MV03040 ; module MV03041 ; module MV03042 ; module MV03043 ; module MV03044 ; module MV03045 ; module MV03046 ; module MV03047 ; module MV03048 ; module MV03049 ; module MV03050 ; module MV03051 ; module MV03052 ; module MV03053 ; module MV03054 ; module MV03055 ; module MV03056 ; module MV03057 ; module MV03058 ; module MV03059 ; module MV03060 ; module MV03061 ; module MV03062 ; module MV03063 ; module MV03064 ; module MV03065 ; module MV03066 ; module MV03067 ; module MV03068 ; module MV03069 ; module MV03070 ; module MV03071 ; module MV03072 ; module MV03073 ; module MV03074 ; module MV03075 ; module MV03076 ; module MV03077 ; module MV03078 ; module MV03079 ; module MV03080 ; module MV03081 ; module MV03082 ; module MV03083 ; module MV03084 ; module MV03085 ; module MV03086 ; module MV03087 ; module MV03088 ; module MV03089 ; module MV03090)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B078 using (module MV03091 ; module MV03092 ; module MV03093 ; module MV03094 ; module MV03095 ; module MV03096 ; module MV03097 ; module MV03098 ; module MV03099 ; module MV03100 ; module MV03101 ; module MV03102 ; module MV03103 ; module MV03104 ; module MV03105 ; module MV03106 ; module MV03107 ; module MV03108 ; module MV03109 ; module MV03110 ; module MV03111 ; module MV03112)

module r5a_ij012345 where

  proved : K0123 • K1345 ≈ K2345 • K0124
  proved = GL.•-cancelʳ {g = K0123 • K1345} {g' = K2345 • K0124} {h = p (ε)}
    (trans (sym (move-product MV00641.proved (MV03032.proved))) (trans (cong refl R100.proved) (move-product MV03033.proved (MV03034.proved))))

module r5a_ij012346 where

  proved : K0123 • K1346 ≈ K2346 • K0124
  proved = GL.•-cancelʳ {g = K0123 • K1346} {g' = K2346 • K0124} {h = p (s5)}
    (trans (sym (move-product MV00247.proved (MV00500.proved))) (trans (cong refl R100.proved) (move-product MV00557.proved (MV00252.proved))))

module r5a_ij012347 where

  proved : K0123 • K1347 ≈ K2347 • K0124
  proved = GL.•-cancelʳ {g = K0123 • K1347} {g' = K2347 • K0124} {h = p (s6 • s5)}
    (trans (sym (move-product MV01682.proved (MV03035.proved))) (trans (cong refl R100.proved) (move-product MV03036.proved (MV03037.proved))))

module r5a_ij012356 where

  proved : K0123 • K1356 ≈ K2356 • K0125
  proved = GL.•-cancelʳ {g = K0123 • K1356} {g' = K2356 • K0125} {h = p (s4 • s5)}
    (trans (sym (move-product MV01712.proved (MV03038.proved))) (trans (cong refl R100.proved) (move-product MV03039.proved (MV03040.proved))))

module r5a_ij012357 where

  proved : K0123 • K1357 ≈ K2357 • K0125
  proved = GL.•-cancelʳ {g = K0123 • K1357} {g' = K2357 • K0125} {h = p (s4 • s6 • s5)}
    (trans (sym (move-product MV01742.proved (MV03041.proved))) (trans (cong refl R100.proved) (move-product MV03042.proved (MV03043.proved))))

module r5a_ij012367 where

  proved : K0123 • K1367 ≈ K2367 • K0126
  proved = GL.•-cancelʳ {g = K0123 • K1367} {g' = K2367 • K0126} {h = p (s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01772.proved (MV03044.proved))) (trans (cong refl R100.proved) (move-product MV03045.proved (MV03046.proved))))

module r5a_ij012456 where

  proved : K0124 • K1456 ≈ K2456 • K0125
  proved = GL.•-cancelʳ {g = K0124 • K1456} {g' = K2456 • K0125} {h = p (s3 • s4 • s5)}
    (trans (sym (move-product MV01714.proved (MV03047.proved))) (trans (cong refl R100.proved) (move-product MV03048.proved (MV03049.proved))))

module r5a_ij012457 where

  proved : K0124 • K1457 ≈ K2457 • K0125
  proved = GL.•-cancelʳ {g = K0124 • K1457} {g' = K2457 • K0125} {h = p (s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01744.proved (MV03050.proved))) (trans (cong refl R100.proved) (move-product MV03051.proved (MV03052.proved))))

module r5a_ij012467 where

  proved : K0124 • K1467 ≈ K2467 • K0126
  proved = GL.•-cancelʳ {g = K0124 • K1467} {g' = K2467 • K0126} {h = p (s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01774.proved (MV03053.proved))) (trans (cong refl R100.proved) (move-product MV03054.proved (MV03055.proved))))

module r5a_ij012567 where

  proved : K0125 • K1567 ≈ K2567 • K0126
  proved = GL.•-cancelʳ {g = K0125 • K1567} {g' = K2567 • K0126} {h = p (s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01776.proved (MV03056.proved))) (trans (cong refl R100.proved) (move-product MV03057.proved (MV03058.proved))))

module r5a_ij013456 where

  proved : K0134 • K1456 ≈ K3456 • K0135
  proved = GL.•-cancelʳ {g = K0134 • K1456} {g' = K3456 • K0135} {h = p (s2 • s3 • s4 • s5)}
    (trans (sym (move-product MV01718.proved (MV03059.proved))) (trans (cong refl R100.proved) (move-product MV03060.proved (MV03061.proved))))

module r5a_ij013457 where

  proved : K0134 • K1457 ≈ K3457 • K0135
  proved = GL.•-cancelʳ {g = K0134 • K1457} {g' = K3457 • K0135} {h = p (s2 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01748.proved (MV03062.proved))) (trans (cong refl R100.proved) (move-product MV03063.proved (MV03064.proved))))

module r5a_ij013467 where

  proved : K0134 • K1467 ≈ K3467 • K0136
  proved = GL.•-cancelʳ {g = K0134 • K1467} {g' = K3467 • K0136} {h = p (s2 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01778.proved (MV03065.proved))) (trans (cong refl R100.proved) (move-product MV03066.proved (MV03067.proved))))

module r5a_ij013567 where

  proved : K0135 • K1567 ≈ K3567 • K0136
  proved = GL.•-cancelʳ {g = K0135 • K1567} {g' = K3567 • K0136} {h = p (s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01780.proved (MV03068.proved))) (trans (cong refl R100.proved) (move-product MV03069.proved (MV03070.proved))))

module r5a_ij014567 where

  proved : K0145 • K1567 ≈ K4567 • K0146
  proved = GL.•-cancelʳ {g = K0145 • K1567} {g' = K4567 • K0146} {h = p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01782.proved (MV03071.proved))) (trans (cong refl R100.proved) (move-product MV03072.proved (MV03073.proved))))

module r5a_ij023456 where

  proved : K0234 • K2456 ≈ K3456 • K0235
  proved = GL.•-cancelʳ {g = K0234 • K2456} {g' = K3456 • K0235} {h = p (s1 • s2 • s3 • s4 • s5)}
    (trans (sym (move-product MV01724.proved (MV03074.proved))) (trans (cong refl R100.proved) (move-product MV03075.proved (MV03076.proved))))

module r5a_ij023457 where

  proved : K0234 • K2457 ≈ K3457 • K0235
  proved = GL.•-cancelʳ {g = K0234 • K2457} {g' = K3457 • K0235} {h = p (s1 • s2 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01754.proved (MV03077.proved))) (trans (cong refl R100.proved) (move-product MV03078.proved (MV03079.proved))))

module r5a_ij023467 where

  proved : K0234 • K2467 ≈ K3467 • K0236
  proved = GL.•-cancelʳ {g = K0234 • K2467} {g' = K3467 • K0236} {h = p (s1 • s2 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01784.proved (MV03080.proved))) (trans (cong refl R100.proved) (move-product MV03081.proved (MV03082.proved))))

module r5a_ij023567 where

  proved : K0235 • K2567 ≈ K3567 • K0236
  proved = GL.•-cancelʳ {g = K0235 • K2567} {g' = K3567 • K0236} {h = p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01786.proved (MV03083.proved))) (trans (cong refl R100.proved) (move-product MV03084.proved (MV03085.proved))))

module r5a_ij024567 where

  proved : K0245 • K2567 ≈ K4567 • K0246
  proved = GL.•-cancelʳ {g = K0245 • K2567} {g' = K4567 • K0246} {h = p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01788.proved (MV03086.proved))) (trans (cong refl R100.proved) (move-product MV03087.proved (MV03088.proved))))

module r5a_ij034567 where

  proved : K0345 • K3567 ≈ K4567 • K0346
  proved = GL.•-cancelʳ {g = K0345 • K3567} {g' = K4567 • K0346} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01790.proved (MV03089.proved))) (trans (cong refl R100.proved) (move-product MV03090.proved (MV03091.proved))))

module r5a_ij123456 where

  proved : K1234 • K2456 ≈ K3456 • K1235
  proved = GL.•-cancelʳ {g = K1234 • K2456} {g' = K3456 • K1235} {h = p (s0 • s1 • s2 • s3 • s4 • s5)}
    (trans (sym (move-product MV01732.proved (MV03092.proved))) (trans (cong refl R100.proved) (move-product MV03093.proved (MV03094.proved))))

module r5a_ij123457 where

  proved : K1234 • K2457 ≈ K3457 • K1235
  proved = GL.•-cancelʳ {g = K1234 • K2457} {g' = K3457 • K1235} {h = p (s0 • s1 • s2 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01762.proved (MV03095.proved))) (trans (cong refl R100.proved) (move-product MV03096.proved (MV03097.proved))))

module r5a_ij123467 where

  proved : K1234 • K2467 ≈ K3467 • K1236
  proved = GL.•-cancelʳ {g = K1234 • K2467} {g' = K3467 • K1236} {h = p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01792.proved (MV03098.proved))) (trans (cong refl R100.proved) (move-product MV03099.proved (MV03100.proved))))

module r5a_ij123567 where

  proved : K1235 • K2567 ≈ K3567 • K1236
  proved = GL.•-cancelʳ {g = K1235 • K2567} {g' = K3567 • K1236} {h = p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01794.proved (MV03101.proved))) (trans (cong refl R100.proved) (move-product MV03102.proved (MV03103.proved))))

module r5a_ij124567 where

  proved : K1245 • K2567 ≈ K4567 • K1246
  proved = GL.•-cancelʳ {g = K1245 • K2567} {g' = K4567 • K1246} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01796.proved (MV03104.proved))) (trans (cong refl R100.proved) (move-product MV03105.proved (MV03106.proved))))

module r5a_ij134567 where

  proved : K1345 • K3567 ≈ K4567 • K1346
  proved = GL.•-cancelʳ {g = K1345 • K3567} {g' = K4567 • K1346} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01798.proved (MV03107.proved))) (trans (cong refl R100.proved) (move-product MV03108.proved (MV03109.proved))))

module r5a_ij234567 where

  proved : K2345 • K3567 ≈ K4567 • K2346
  proved = GL.•-cancelʳ {g = K2345 • K3567} {g' = K4567 • K2346} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01800.proved (MV03110.proved))) (trans (cong refl R100.proved) (move-product MV03111.proved (MV03112.proved))))
