------------------------------------------------------------------------
-- Presentations of groups
--
-- The windows of the four-wire derivations, the parameter of Four.D
--
-- Written by `scratchpad/four/reflect4.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.WinInst where

open import Examples.Groups.Clifford+CS.Four.Chain using (refl)
open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; leaf ; node)
open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Swaps using (facts)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
import Examples.Groups.Clifford+CS.Four.Wins.W01 as W01
import Examples.Groups.Clifford+CS.Four.Wins.W02 as W02
import Examples.Groups.Clifford+CS.Four.Wins.W03 as W03
import Examples.Groups.Clifford+CS.Four.Wins.W04 as W04
import Examples.Groups.Clifford+CS.Four.Wins.W05 as W05
import Examples.Groups.Clifford+CS.Four.Wins.W06 as W06
import Examples.Groups.Clifford+CS.Four.Wins.W07 as W07
import Examples.Groups.Clifford+CS.Four.Wins.W08 as W08
import Examples.Groups.Clifford+CS.Four.Wins.W09 as W09
import Examples.Groups.Clifford+CS.Four.Wins.W10 as W10
import Examples.Groups.Clifford+CS.Four.Wins.W11 as W11
import Examples.Groups.Clifford+CS.Four.Wins.W12 as W12
import Examples.Groups.Clifford+CS.Four.Wins.W13 as W13
import Examples.Groups.Clifford+CS.Four.Wins.W14 as W14
import Examples.Groups.Clifford+CS.Four.Wins.W15 as W15
import Examples.Groups.Clifford+CS.Four.Wins.W16 as W16
import Examples.Groups.Clifford+CS.Four.Wins.W17 as W17
import Examples.Groups.Clifford+CS.Four.Wins.W18 as W18
import Examples.Groups.Clifford+CS.Four.Wins.W19 as W19
import Examples.Groups.Clifford+CS.Four.Wins.W20 as W20
import Examples.Groups.Clifford+CS.Four.Wins.W21 as W21
import Examples.Groups.Clifford+CS.Four.Wins.W22 as W22
import Examples.Groups.Clifford+CS.Four.Wins.W23 as W23
import Examples.Groups.Clifford+CS.Four.Wins.W24 as W24
import Examples.Groups.Clifford+CS.Four.Wins.W25 as W25
import Examples.Groups.Clifford+CS.Four.Wins.W26 as W26
import Examples.Groups.Clifford+CS.Four.Wins.W27 as W27
import Examples.Groups.Clifford+CS.Four.Wins.W28 as W28
import Examples.Groups.Clifford+CS.Four.Wins.W29 as W29
import Examples.Groups.Clifford+CS.Four.Wins.W30 as W30
import Examples.Groups.Clifford+CS.Four.Wins.W31 as W31
import Examples.Groups.Clifford+CS.Four.Wins.W32 as W32
import Examples.Groups.Clifford+CS.Four.Wins.W33 as W33
import Examples.Groups.Clifford+CS.Four.Wins.W34 as W34
import Examples.Groups.Clifford+CS.Four.Wins.W35 as W35
import Examples.Groups.Clifford+CS.Four.Wins.W36 as W36
import Examples.Groups.Clifford+CS.Four.Wins.W37 as W37
import Examples.Groups.Clifford+CS.Four.Wins.W38 as W38
import Examples.Groups.Clifford+CS.Four.Wins.W39 as W39
import Examples.Groups.Clifford+CS.Four.Wins.W40 as W40
import Examples.Groups.Clifford+CS.Four.Wins.W41 as W41
import Examples.Groups.Clifford+CS.Four.Wins.W42 as W42
import Examples.Groups.Clifford+CS.Four.Wins.W43 as W43
import Examples.Groups.Clifford+CS.Four.Wins.W44 as W44
import Examples.Groups.Clifford+CS.Four.Wins.W45 as W45
import Examples.Groups.Clifford+CS.Four.Wins.W46 as W46
import Examples.Groups.Clifford+CS.Four.Wins.W47 as W47
import Examples.Groups.Clifford+CS.Four.Wins.W48 as W48
import Examples.Groups.Clifford+CS.Four.Wins.W49 as W49

ws : Ws
ws =
  (node
    (node
      (node
        (node
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02047 b)
                          leaf
                        )
                        (W20.wn01023 b)
                        leaf
                      )
                      (W04.wn00511 b)
                      (node
                        (node
                          leaf
                          (W48.wn02559 b)
                          leaf
                        )
                        (W29.wn01535 b)
                        leaf
                      )
                    )
                    (W02.wn00255 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02303 b)
                          leaf
                        )
                        (W25.wn01279 b)
                        leaf
                      )
                      (W10.wn00767 b)
                      (node
                        leaf
                        (W36.wn01791 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00127 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02175 b)
                          leaf
                        )
                        (W22.wn01151 b)
                        leaf
                      )
                      (W07.wn00639 b)
                      (node
                        leaf
                        (W34.wn01663 b)
                        leaf
                      )
                    )
                    (W02.wn00383 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02431 b)
                          leaf
                        )
                        (W27.wn01407 b)
                        leaf
                      )
                      (W14.wn00895 b)
                      (node
                        leaf
                        (W40.wn01919 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00063 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02111 b)
                          leaf
                        )
                        (W21.wn01087 b)
                        leaf
                      )
                      (W05.wn00575 b)
                      (node
                        leaf
                        (W31.wn01599 b)
                        leaf
                      )
                    )
                    (W02.wn00319 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02367 b)
                          leaf
                        )
                        (W27.wn01343 b)
                        leaf
                      )
                      (W12.wn00831 b)
                      (node
                        leaf
                        (W38.wn01855 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00191 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02239 b)
                          leaf
                        )
                        (W24.wn01215 b)
                        leaf
                      )
                      (W09.wn00703 b)
                      (node
                        leaf
                        (W35.wn01727 b)
                        leaf
                      )
                    )
                    (W03.wn00447 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02495 b)
                          leaf
                        )
                        (W28.wn01471 b)
                        leaf
                      )
                      (W18.wn00959 b)
                      (node
                        leaf
                        (W42.wn01983 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00031 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02079 b)
                          leaf
                        )
                        (W20.wn01055 b)
                        leaf
                      )
                      (W04.wn00543 b)
                      (node
                        leaf
                        (W29.wn01567 b)
                        leaf
                      )
                    )
                    (W02.wn00287 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02335 b)
                          leaf
                        )
                        (W26.wn01311 b)
                        leaf
                      )
                      (W11.wn00799 b)
                      (node
                        leaf
                        (W37.wn01823 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00159 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02207 b)
                          leaf
                        )
                        (W23.wn01183 b)
                        leaf
                      )
                      (W08.wn00671 b)
                      (node
                        leaf
                        (W35.wn01695 b)
                        leaf
                      )
                    )
                    (W03.wn00415 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02463 b)
                          leaf
                        )
                        (W28.wn01439 b)
                        leaf
                      )
                      (W15.wn00927 b)
                      (node
                        leaf
                        (W41.wn01951 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00095 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02143 b)
                          leaf
                        )
                        (W21.wn01119 b)
                        leaf
                      )
                      (W06.wn00607 b)
                      (node
                        leaf
                        (W32.wn01631 b)
                        leaf
                      )
                    )
                    (W02.wn00351 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02399 b)
                          leaf
                        )
                        (W27.wn01375 b)
                        leaf
                      )
                      (W14.wn00863 b)
                      (node
                        leaf
                        (W38.wn01887 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00223 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02271 b)
                          leaf
                        )
                        (W25.wn01247 b)
                        leaf
                      )
                      (W09.wn00735 b)
                      (node
                        leaf
                        (W35.wn01759 b)
                        leaf
                      )
                    )
                    (W03.wn00479 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02527 b)
                          leaf
                        )
                        (W28.wn01503 b)
                        leaf
                      )
                      (W19.wn00991 b)
                      (node
                        leaf
                        (W42.wn02015 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00015 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02063 b)
                          leaf
                        )
                        (W20.wn01039 b)
                        leaf
                      )
                      (W04.wn00527 b)
                      (node
                        (node
                          leaf
                          (W49.wn02575 b)
                          leaf
                        )
                        (W29.wn01551 b)
                        leaf
                      )
                    )
                    (W02.wn00271 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02319 b)
                          leaf
                        )
                        (W25.wn01295 b)
                        leaf
                      )
                      (W10.wn00783 b)
                      (node
                        leaf
                        (W37.wn01807 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00143 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02191 b)
                          leaf
                        )
                        (W22.wn01167 b)
                        leaf
                      )
                      (W07.wn00655 b)
                      (node
                        leaf
                        (W34.wn01679 b)
                        leaf
                      )
                    )
                    (W02.wn00399 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02447 b)
                          leaf
                        )
                        (W28.wn01423 b)
                        leaf
                      )
                      (W15.wn00911 b)
                      (node
                        leaf
                        (W41.wn01935 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00079 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02127 b)
                          leaf
                        )
                        (W21.wn01103 b)
                        leaf
                      )
                      (W06.wn00591 b)
                      (node
                        leaf
                        (W32.wn01615 b)
                        leaf
                      )
                    )
                    (W02.wn00335 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02383 b)
                          leaf
                        )
                        (W27.wn01359 b)
                        leaf
                      )
                      (W13.wn00847 b)
                      (node
                        leaf
                        (W38.wn01871 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00207 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02255 b)
                          leaf
                        )
                        (W24.wn01231 b)
                        leaf
                      )
                      (W09.wn00719 b)
                      (node
                        leaf
                        (W35.wn01743 b)
                        leaf
                      )
                    )
                    (W03.wn00463 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02511 b)
                          leaf
                        )
                        (W28.wn01487 b)
                        leaf
                      )
                      (W19.wn00975 b)
                      (node
                        leaf
                        (W42.wn01999 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00047 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02095 b)
                          leaf
                        )
                        (W20.wn01071 b)
                        leaf
                      )
                      (W04.wn00559 b)
                      (node
                        leaf
                        (W30.wn01583 b)
                        leaf
                      )
                    )
                    (W02.wn00303 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02351 b)
                          leaf
                        )
                        (W26.wn01327 b)
                        leaf
                      )
                      (W11.wn00815 b)
                      (node
                        leaf
                        (W37.wn01839 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00175 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02223 b)
                          leaf
                        )
                        (W23.wn01199 b)
                        leaf
                      )
                      (W08.wn00687 b)
                      (node
                        leaf
                        (W35.wn01711 b)
                        leaf
                      )
                    )
                    (W03.wn00431 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02479 b)
                          leaf
                        )
                        (W28.wn01455 b)
                        leaf
                      )
                      (W17.wn00943 b)
                      (node
                        leaf
                        (W41.wn01967 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00111 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02159 b)
                          leaf
                        )
                        (W22.wn01135 b)
                        leaf
                      )
                      (W06.wn00623 b)
                      (node
                        leaf
                        (W33.wn01647 b)
                        leaf
                      )
                    )
                    (W02.wn00367 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02415 b)
                          leaf
                        )
                        (W27.wn01391 b)
                        leaf
                      )
                      (W14.wn00879 b)
                      (node
                        leaf
                        (W39.wn01903 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00239 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02287 b)
                          leaf
                        )
                        (W25.wn01263 b)
                        leaf
                      )
                      (W10.wn00751 b)
                      (node
                        leaf
                        (W36.wn01775 b)
                        leaf
                      )
                    )
                    (W03.wn00495 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02543 b)
                          leaf
                        )
                        (W29.wn01519 b)
                        leaf
                      )
                      (W20.wn01007 b)
                      (node
                        leaf
                        (W43.wn02031 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
          (W01.wn00007 b)
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02055 b)
                          leaf
                        )
                        (W20.wn01031 b)
                        leaf
                      )
                      (W04.wn00519 b)
                      (node
                        (node
                          leaf
                          (W48.wn02567 b)
                          leaf
                        )
                        (W29.wn01543 b)
                        leaf
                      )
                    )
                    (W02.wn00263 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02311 b)
                          leaf
                        )
                        (W25.wn01287 b)
                        leaf
                      )
                      (W10.wn00775 b)
                      (node
                        leaf
                        (W37.wn01799 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00135 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02183 b)
                          leaf
                        )
                        (W22.wn01159 b)
                        leaf
                      )
                      (W07.wn00647 b)
                      (node
                        leaf
                        (W34.wn01671 b)
                        leaf
                      )
                    )
                    (W02.wn00391 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02439 b)
                          leaf
                        )
                        (W27.wn01415 b)
                        leaf
                      )
                      (W15.wn00903 b)
                      (node
                        leaf
                        (W40.wn01927 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00071 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02119 b)
                          leaf
                        )
                        (W21.wn01095 b)
                        leaf
                      )
                      (W05.wn00583 b)
                      (node
                        leaf
                        (W31.wn01607 b)
                        leaf
                      )
                    )
                    (W02.wn00327 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02375 b)
                          leaf
                        )
                        (W27.wn01351 b)
                        leaf
                      )
                      (W13.wn00839 b)
                      (node
                        leaf
                        (W38.wn01863 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00199 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02247 b)
                          leaf
                        )
                        (W24.wn01223 b)
                        leaf
                      )
                      (W09.wn00711 b)
                      (node
                        leaf
                        (W35.wn01735 b)
                        leaf
                      )
                    )
                    (W03.wn00455 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02503 b)
                          leaf
                        )
                        (W28.wn01479 b)
                        leaf
                      )
                      (W18.wn00967 b)
                      (node
                        leaf
                        (W42.wn01991 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00039 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02087 b)
                          leaf
                        )
                        (W20.wn01063 b)
                        leaf
                      )
                      (W04.wn00551 b)
                      (node
                        leaf
                        (W29.wn01575 b)
                        leaf
                      )
                    )
                    (W02.wn00295 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02343 b)
                          leaf
                        )
                        (W26.wn01319 b)
                        leaf
                      )
                      (W11.wn00807 b)
                      (node
                        leaf
                        (W37.wn01831 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00167 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02215 b)
                          leaf
                        )
                        (W23.wn01191 b)
                        leaf
                      )
                      (W08.wn00679 b)
                      (node
                        leaf
                        (W35.wn01703 b)
                        leaf
                      )
                    )
                    (W03.wn00423 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02471 b)
                          leaf
                        )
                        (W28.wn01447 b)
                        leaf
                      )
                      (W16.wn00935 b)
                      (node
                        leaf
                        (W41.wn01959 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00103 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02151 b)
                          leaf
                        )
                        (W22.wn01127 b)
                        leaf
                      )
                      (W06.wn00615 b)
                      (node
                        leaf
                        (W33.wn01639 b)
                        leaf
                      )
                    )
                    (W02.wn00359 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02407 b)
                          leaf
                        )
                        (W27.wn01383 b)
                        leaf
                      )
                      (W14.wn00871 b)
                      (node
                        leaf
                        (W39.wn01895 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00231 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02279 b)
                          leaf
                        )
                        (W25.wn01255 b)
                        leaf
                      )
                      (W10.wn00743 b)
                      (node
                        leaf
                        (W35.wn01767 b)
                        leaf
                      )
                    )
                    (W03.wn00487 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02535 b)
                          leaf
                        )
                        (W28.wn01511 b)
                        leaf
                      )
                      (W20.wn00999 b)
                      (node
                        leaf
                        (W42.wn02023 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00023 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02071 b)
                          leaf
                        )
                        (W20.wn01047 b)
                        leaf
                      )
                      (W04.wn00535 b)
                      (node
                        (node
                          leaf
                          (W49.wn02583 b)
                          leaf
                        )
                        (W29.wn01559 b)
                        leaf
                      )
                    )
                    (W02.wn00279 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02327 b)
                          leaf
                        )
                        (W26.wn01303 b)
                        leaf
                      )
                      (W11.wn00791 b)
                      (node
                        leaf
                        (W37.wn01815 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00151 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02199 b)
                          leaf
                        )
                        (W23.wn01175 b)
                        leaf
                      )
                      (W07.wn00663 b)
                      (node
                        leaf
                        (W34.wn01687 b)
                        leaf
                      )
                    )
                    (W02.wn00407 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02455 b)
                          leaf
                        )
                        (W28.wn01431 b)
                        leaf
                      )
                      (W15.wn00919 b)
                      (node
                        leaf
                        (W41.wn01943 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00087 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02135 b)
                          leaf
                        )
                        (W21.wn01111 b)
                        leaf
                      )
                      (W06.wn00599 b)
                      (node
                        leaf
                        (W32.wn01623 b)
                        leaf
                      )
                    )
                    (W02.wn00343 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02391 b)
                          leaf
                        )
                        (W27.wn01367 b)
                        leaf
                      )
                      (W13.wn00855 b)
                      (node
                        leaf
                        (W38.wn01879 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00215 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02263 b)
                          leaf
                        )
                        (W25.wn01239 b)
                        leaf
                      )
                      (W09.wn00727 b)
                      (node
                        leaf
                        (W35.wn01751 b)
                        leaf
                      )
                    )
                    (W03.wn00471 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02519 b)
                          leaf
                        )
                        (W28.wn01495 b)
                        leaf
                      )
                      (W19.wn00983 b)
                      (node
                        leaf
                        (W42.wn02007 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00055 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02103 b)
                          leaf
                        )
                        (W20.wn01079 b)
                        leaf
                      )
                      (W05.wn00567 b)
                      (node
                        leaf
                        (W30.wn01591 b)
                        leaf
                      )
                    )
                    (W02.wn00311 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02359 b)
                          leaf
                        )
                        (W27.wn01335 b)
                        leaf
                      )
                      (W12.wn00823 b)
                      (node
                        leaf
                        (W38.wn01847 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00183 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02231 b)
                          leaf
                        )
                        (W24.wn01207 b)
                        leaf
                      )
                      (W08.wn00695 b)
                      (node
                        leaf
                        (W35.wn01719 b)
                        leaf
                      )
                    )
                    (W03.wn00439 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02487 b)
                          leaf
                        )
                        (W28.wn01463 b)
                        leaf
                      )
                      (W17.wn00951 b)
                      (node
                        leaf
                        (W42.wn01975 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00119 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02167 b)
                          leaf
                        )
                        (W22.wn01143 b)
                        leaf
                      )
                      (W06.wn00631 b)
                      (node
                        leaf
                        (W34.wn01655 b)
                        leaf
                      )
                    )
                    (W02.wn00375 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02423 b)
                          leaf
                        )
                        (W27.wn01399 b)
                        leaf
                      )
                      (W14.wn00887 b)
                      (node
                        leaf
                        (W40.wn01911 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00247 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02295 b)
                          leaf
                        )
                        (W25.wn01271 b)
                        leaf
                      )
                      (W10.wn00759 b)
                      (node
                        leaf
                        (W36.wn01783 b)
                        leaf
                      )
                    )
                    (W03.wn00503 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02551 b)
                          leaf
                        )
                        (W29.wn01527 b)
                        leaf
                      )
                      (W20.wn01015 b)
                      (node
                        leaf
                        (W43.wn02039 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
        )
        (W01.wn00003 b)
        (node
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02051 b)
                          leaf
                        )
                        (W20.wn01027 b)
                        leaf
                      )
                      (W04.wn00515 b)
                      (node
                        (node
                          leaf
                          (W48.wn02563 b)
                          leaf
                        )
                        (W29.wn01539 b)
                        leaf
                      )
                    )
                    (W02.wn00259 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02307 b)
                          leaf
                        )
                        (W25.wn01283 b)
                        leaf
                      )
                      (W10.wn00771 b)
                      (node
                        leaf
                        (W36.wn01795 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00131 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02179 b)
                          leaf
                        )
                        (W22.wn01155 b)
                        leaf
                      )
                      (W07.wn00643 b)
                      (node
                        leaf
                        (W34.wn01667 b)
                        leaf
                      )
                    )
                    (W02.wn00387 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02435 b)
                          leaf
                        )
                        (W27.wn01411 b)
                        leaf
                      )
                      (W15.wn00899 b)
                      (node
                        leaf
                        (W40.wn01923 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00067 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02115 b)
                          leaf
                        )
                        (W21.wn01091 b)
                        leaf
                      )
                      (W05.wn00579 b)
                      (node
                        leaf
                        (W31.wn01603 b)
                        leaf
                      )
                    )
                    (W02.wn00323 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02371 b)
                          leaf
                        )
                        (W27.wn01347 b)
                        leaf
                      )
                      (W12.wn00835 b)
                      (node
                        leaf
                        (W38.wn01859 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00195 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02243 b)
                          leaf
                        )
                        (W24.wn01219 b)
                        leaf
                      )
                      (W09.wn00707 b)
                      (node
                        leaf
                        (W35.wn01731 b)
                        leaf
                      )
                    )
                    (W03.wn00451 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02499 b)
                          leaf
                        )
                        (W28.wn01475 b)
                        leaf
                      )
                      (W18.wn00963 b)
                      (node
                        leaf
                        (W42.wn01987 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00035 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02083 b)
                          leaf
                        )
                        (W20.wn01059 b)
                        leaf
                      )
                      (W04.wn00547 b)
                      (node
                        leaf
                        (W29.wn01571 b)
                        leaf
                      )
                    )
                    (W02.wn00291 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02339 b)
                          leaf
                        )
                        (W26.wn01315 b)
                        leaf
                      )
                      (W11.wn00803 b)
                      (node
                        leaf
                        (W37.wn01827 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00163 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02211 b)
                          leaf
                        )
                        (W23.wn01187 b)
                        leaf
                      )
                      (W08.wn00675 b)
                      (node
                        leaf
                        (W35.wn01699 b)
                        leaf
                      )
                    )
                    (W03.wn00419 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02467 b)
                          leaf
                        )
                        (W28.wn01443 b)
                        leaf
                      )
                      (W16.wn00931 b)
                      (node
                        leaf
                        (W41.wn01955 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00099 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02147 b)
                          leaf
                        )
                        (W21.wn01123 b)
                        leaf
                      )
                      (W06.wn00611 b)
                      (node
                        leaf
                        (W33.wn01635 b)
                        leaf
                      )
                    )
                    (W02.wn00355 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02403 b)
                          leaf
                        )
                        (W27.wn01379 b)
                        leaf
                      )
                      (W14.wn00867 b)
                      (node
                        leaf
                        (W38.wn01891 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00227 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02275 b)
                          leaf
                        )
                        (W25.wn01251 b)
                        leaf
                      )
                      (W10.wn00739 b)
                      (node
                        leaf
                        (W35.wn01763 b)
                        leaf
                      )
                    )
                    (W03.wn00483 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02531 b)
                          leaf
                        )
                        (W28.wn01507 b)
                        leaf
                      )
                      (W20.wn00995 b)
                      (node
                        leaf
                        (W42.wn02019 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00019 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02067 b)
                          leaf
                        )
                        (W20.wn01043 b)
                        leaf
                      )
                      (W04.wn00531 b)
                      (node
                        (node
                          leaf
                          (W49.wn02579 b)
                          leaf
                        )
                        (W29.wn01555 b)
                        leaf
                      )
                    )
                    (W02.wn00275 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02323 b)
                          leaf
                        )
                        (W26.wn01299 b)
                        leaf
                      )
                      (W11.wn00787 b)
                      (node
                        leaf
                        (W37.wn01811 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00147 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02195 b)
                          leaf
                        )
                        (W23.wn01171 b)
                        leaf
                      )
                      (W07.wn00659 b)
                      (node
                        leaf
                        (W34.wn01683 b)
                        leaf
                      )
                    )
                    (W02.wn00403 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02451 b)
                          leaf
                        )
                        (W28.wn01427 b)
                        leaf
                      )
                      (W15.wn00915 b)
                      (node
                        leaf
                        (W41.wn01939 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00083 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02131 b)
                          leaf
                        )
                        (W21.wn01107 b)
                        leaf
                      )
                      (W06.wn00595 b)
                      (node
                        leaf
                        (W32.wn01619 b)
                        leaf
                      )
                    )
                    (W02.wn00339 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02387 b)
                          leaf
                        )
                        (W27.wn01363 b)
                        leaf
                      )
                      (W13.wn00851 b)
                      (node
                        leaf
                        (W38.wn01875 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00211 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02259 b)
                          leaf
                        )
                        (W24.wn01235 b)
                        leaf
                      )
                      (W09.wn00723 b)
                      (node
                        leaf
                        (W35.wn01747 b)
                        leaf
                      )
                    )
                    (W03.wn00467 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02515 b)
                          leaf
                        )
                        (W28.wn01491 b)
                        leaf
                      )
                      (W19.wn00979 b)
                      (node
                        leaf
                        (W42.wn02003 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00051 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02099 b)
                          leaf
                        )
                        (W20.wn01075 b)
                        leaf
                      )
                      (W05.wn00563 b)
                      (node
                        leaf
                        (W30.wn01587 b)
                        leaf
                      )
                    )
                    (W02.wn00307 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02355 b)
                          leaf
                        )
                        (W26.wn01331 b)
                        leaf
                      )
                      (W12.wn00819 b)
                      (node
                        leaf
                        (W37.wn01843 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00179 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02227 b)
                          leaf
                        )
                        (W23.wn01203 b)
                        leaf
                      )
                      (W08.wn00691 b)
                      (node
                        leaf
                        (W35.wn01715 b)
                        leaf
                      )
                    )
                    (W03.wn00435 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02483 b)
                          leaf
                        )
                        (W28.wn01459 b)
                        leaf
                      )
                      (W17.wn00947 b)
                      (node
                        leaf
                        (W41.wn01971 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00115 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02163 b)
                          leaf
                        )
                        (W22.wn01139 b)
                        leaf
                      )
                      (W06.wn00627 b)
                      (node
                        leaf
                        (W34.wn01651 b)
                        leaf
                      )
                    )
                    (W02.wn00371 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02419 b)
                          leaf
                        )
                        (W27.wn01395 b)
                        leaf
                      )
                      (W14.wn00883 b)
                      (node
                        leaf
                        (W40.wn01907 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00243 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02291 b)
                          leaf
                        )
                        (W25.wn01267 b)
                        leaf
                      )
                      (W10.wn00755 b)
                      (node
                        leaf
                        (W36.wn01779 b)
                        leaf
                      )
                    )
                    (W03.wn00499 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02547 b)
                          leaf
                        )
                        (W29.wn01523 b)
                        leaf
                      )
                      (W20.wn01011 b)
                      (node
                        leaf
                        (W43.wn02035 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
          (W01.wn00011 b)
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02059 b)
                          leaf
                        )
                        (W20.wn01035 b)
                        leaf
                      )
                      (W04.wn00523 b)
                      (node
                        (node
                          leaf
                          (W48.wn02571 b)
                          leaf
                        )
                        (W29.wn01547 b)
                        leaf
                      )
                    )
                    (W02.wn00267 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02315 b)
                          leaf
                        )
                        (W25.wn01291 b)
                        leaf
                      )
                      (W10.wn00779 b)
                      (node
                        leaf
                        (W37.wn01803 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00139 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02187 b)
                          leaf
                        )
                        (W22.wn01163 b)
                        leaf
                      )
                      (W07.wn00651 b)
                      (node
                        leaf
                        (W34.wn01675 b)
                        leaf
                      )
                    )
                    (W02.wn00395 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02443 b)
                          leaf
                        )
                        (W27.wn01419 b)
                        leaf
                      )
                      (W15.wn00907 b)
                      (node
                        leaf
                        (W41.wn01931 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00075 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02123 b)
                          leaf
                        )
                        (W21.wn01099 b)
                        leaf
                      )
                      (W05.wn00587 b)
                      (node
                        leaf
                        (W32.wn01611 b)
                        leaf
                      )
                    )
                    (W02.wn00331 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02379 b)
                          leaf
                        )
                        (W27.wn01355 b)
                        leaf
                      )
                      (W13.wn00843 b)
                      (node
                        leaf
                        (W38.wn01867 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00203 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02251 b)
                          leaf
                        )
                        (W24.wn01227 b)
                        leaf
                      )
                      (W09.wn00715 b)
                      (node
                        leaf
                        (W35.wn01739 b)
                        leaf
                      )
                    )
                    (W03.wn00459 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02507 b)
                          leaf
                        )
                        (W28.wn01483 b)
                        leaf
                      )
                      (W19.wn00971 b)
                      (node
                        leaf
                        (W42.wn01995 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00043 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02091 b)
                          leaf
                        )
                        (W20.wn01067 b)
                        leaf
                      )
                      (W04.wn00555 b)
                      (node
                        leaf
                        (W29.wn01579 b)
                        leaf
                      )
                    )
                    (W02.wn00299 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02347 b)
                          leaf
                        )
                        (W26.wn01323 b)
                        leaf
                      )
                      (W11.wn00811 b)
                      (node
                        leaf
                        (W37.wn01835 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00171 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02219 b)
                          leaf
                        )
                        (W23.wn01195 b)
                        leaf
                      )
                      (W08.wn00683 b)
                      (node
                        leaf
                        (W35.wn01707 b)
                        leaf
                      )
                    )
                    (W03.wn00427 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02475 b)
                          leaf
                        )
                        (W28.wn01451 b)
                        leaf
                      )
                      (W16.wn00939 b)
                      (node
                        leaf
                        (W41.wn01963 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00107 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02155 b)
                          leaf
                        )
                        (W22.wn01131 b)
                        leaf
                      )
                      (W06.wn00619 b)
                      (node
                        leaf
                        (W33.wn01643 b)
                        leaf
                      )
                    )
                    (W02.wn00363 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02411 b)
                          leaf
                        )
                        (W27.wn01387 b)
                        leaf
                      )
                      (W14.wn00875 b)
                      (node
                        leaf
                        (W39.wn01899 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00235 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02283 b)
                          leaf
                        )
                        (W25.wn01259 b)
                        leaf
                      )
                      (W10.wn00747 b)
                      (node
                        leaf
                        (W35.wn01771 b)
                        leaf
                      )
                    )
                    (W03.wn00491 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02539 b)
                          leaf
                        )
                        (W29.wn01515 b)
                        leaf
                      )
                      (W20.wn01003 b)
                      (node
                        leaf
                        (W43.wn02027 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00027 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02075 b)
                          leaf
                        )
                        (W20.wn01051 b)
                        leaf
                      )
                      (W04.wn00539 b)
                      (node
                        leaf
                        (W29.wn01563 b)
                        leaf
                      )
                    )
                    (W02.wn00283 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02331 b)
                          leaf
                        )
                        (W26.wn01307 b)
                        leaf
                      )
                      (W11.wn00795 b)
                      (node
                        leaf
                        (W37.wn01819 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00155 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02203 b)
                          leaf
                        )
                        (W23.wn01179 b)
                        leaf
                      )
                      (W08.wn00667 b)
                      (node
                        leaf
                        (W35.wn01691 b)
                        leaf
                      )
                    )
                    (W03.wn00411 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02459 b)
                          leaf
                        )
                        (W28.wn01435 b)
                        leaf
                      )
                      (W15.wn00923 b)
                      (node
                        leaf
                        (W41.wn01947 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00091 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02139 b)
                          leaf
                        )
                        (W21.wn01115 b)
                        leaf
                      )
                      (W06.wn00603 b)
                      (node
                        leaf
                        (W32.wn01627 b)
                        leaf
                      )
                    )
                    (W02.wn00347 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02395 b)
                          leaf
                        )
                        (W27.wn01371 b)
                        leaf
                      )
                      (W13.wn00859 b)
                      (node
                        leaf
                        (W38.wn01883 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00219 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02267 b)
                          leaf
                        )
                        (W25.wn01243 b)
                        leaf
                      )
                      (W09.wn00731 b)
                      (node
                        leaf
                        (W35.wn01755 b)
                        leaf
                      )
                    )
                    (W03.wn00475 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02523 b)
                          leaf
                        )
                        (W28.wn01499 b)
                        leaf
                      )
                      (W19.wn00987 b)
                      (node
                        leaf
                        (W42.wn02011 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00059 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02107 b)
                          leaf
                        )
                        (W21.wn01083 b)
                        leaf
                      )
                      (W05.wn00571 b)
                      (node
                        leaf
                        (W30.wn01595 b)
                        leaf
                      )
                    )
                    (W02.wn00315 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02363 b)
                          leaf
                        )
                        (W27.wn01339 b)
                        leaf
                      )
                      (W12.wn00827 b)
                      (node
                        leaf
                        (W38.wn01851 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00187 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02235 b)
                          leaf
                        )
                        (W24.wn01211 b)
                        leaf
                      )
                      (W09.wn00699 b)
                      (node
                        leaf
                        (W35.wn01723 b)
                        leaf
                      )
                    )
                    (W03.wn00443 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02491 b)
                          leaf
                        )
                        (W28.wn01467 b)
                        leaf
                      )
                      (W18.wn00955 b)
                      (node
                        leaf
                        (W42.wn01979 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00123 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02171 b)
                          leaf
                        )
                        (W22.wn01147 b)
                        leaf
                      )
                      (W06.wn00635 b)
                      (node
                        leaf
                        (W34.wn01659 b)
                        leaf
                      )
                    )
                    (W02.wn00379 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02427 b)
                          leaf
                        )
                        (W27.wn01403 b)
                        leaf
                      )
                      (W14.wn00891 b)
                      (node
                        leaf
                        (W40.wn01915 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00251 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02299 b)
                          leaf
                        )
                        (W25.wn01275 b)
                        leaf
                      )
                      (W10.wn00763 b)
                      (node
                        leaf
                        (W36.wn01787 b)
                        leaf
                      )
                    )
                    (W03.wn00507 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02555 b)
                          leaf
                        )
                        (W29.wn01531 b)
                        leaf
                      )
                      (W20.wn01019 b)
                      (node
                        leaf
                        (W43.wn02043 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
      (W01.wn00001 b)
      (node
        (node
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02049 b)
                          leaf
                        )
                        (W20.wn01025 b)
                        leaf
                      )
                      (W04.wn00513 b)
                      (node
                        (node
                          leaf
                          (W48.wn02561 b)
                          leaf
                        )
                        (W29.wn01537 b)
                        leaf
                      )
                    )
                    (W02.wn00257 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02305 b)
                          leaf
                        )
                        (W25.wn01281 b)
                        leaf
                      )
                      (W10.wn00769 b)
                      (node
                        leaf
                        (W36.wn01793 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00129 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02177 b)
                          leaf
                        )
                        (W22.wn01153 b)
                        leaf
                      )
                      (W07.wn00641 b)
                      (node
                        leaf
                        (W34.wn01665 b)
                        leaf
                      )
                    )
                    (W02.wn00385 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02433 b)
                          leaf
                        )
                        (W27.wn01409 b)
                        leaf
                      )
                      (W15.wn00897 b)
                      (node
                        leaf
                        (W40.wn01921 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00065 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02113 b)
                          leaf
                        )
                        (W21.wn01089 b)
                        leaf
                      )
                      (W05.wn00577 b)
                      (node
                        leaf
                        (W31.wn01601 b)
                        leaf
                      )
                    )
                    (W02.wn00321 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02369 b)
                          leaf
                        )
                        (W27.wn01345 b)
                        leaf
                      )
                      (W12.wn00833 b)
                      (node
                        leaf
                        (W38.wn01857 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00193 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02241 b)
                          leaf
                        )
                        (W24.wn01217 b)
                        leaf
                      )
                      (W09.wn00705 b)
                      (node
                        leaf
                        (W35.wn01729 b)
                        leaf
                      )
                    )
                    (W03.wn00449 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02497 b)
                          leaf
                        )
                        (W28.wn01473 b)
                        leaf
                      )
                      (W18.wn00961 b)
                      (node
                        leaf
                        (W42.wn01985 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00033 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02081 b)
                          leaf
                        )
                        (W20.wn01057 b)
                        leaf
                      )
                      (W04.wn00545 b)
                      (node
                        leaf
                        (W29.wn01569 b)
                        leaf
                      )
                    )
                    (W02.wn00289 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02337 b)
                          leaf
                        )
                        (W26.wn01313 b)
                        leaf
                      )
                      (W11.wn00801 b)
                      (node
                        leaf
                        (W37.wn01825 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00161 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02209 b)
                          leaf
                        )
                        (W23.wn01185 b)
                        leaf
                      )
                      (W08.wn00673 b)
                      (node
                        leaf
                        (W35.wn01697 b)
                        leaf
                      )
                    )
                    (W03.wn00417 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02465 b)
                          leaf
                        )
                        (W28.wn01441 b)
                        leaf
                      )
                      (W16.wn00929 b)
                      (node
                        leaf
                        (W41.wn01953 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00097 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02145 b)
                          leaf
                        )
                        (W21.wn01121 b)
                        leaf
                      )
                      (W06.wn00609 b)
                      (node
                        leaf
                        (W32.wn01633 b)
                        leaf
                      )
                    )
                    (W02.wn00353 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02401 b)
                          leaf
                        )
                        (W27.wn01377 b)
                        leaf
                      )
                      (W14.wn00865 b)
                      (node
                        leaf
                        (W38.wn01889 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00225 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02273 b)
                          leaf
                        )
                        (W25.wn01249 b)
                        leaf
                      )
                      (W09.wn00737 b)
                      (node
                        leaf
                        (W35.wn01761 b)
                        leaf
                      )
                    )
                    (W03.wn00481 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02529 b)
                          leaf
                        )
                        (W28.wn01505 b)
                        leaf
                      )
                      (W19.wn00993 b)
                      (node
                        leaf
                        (W42.wn02017 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00017 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02065 b)
                          leaf
                        )
                        (W20.wn01041 b)
                        leaf
                      )
                      (W04.wn00529 b)
                      (node
                        (node
                          leaf
                          (W49.wn02577 b)
                          leaf
                        )
                        (W29.wn01553 b)
                        leaf
                      )
                    )
                    (W02.wn00273 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02321 b)
                          leaf
                        )
                        (W26.wn01297 b)
                        leaf
                      )
                      (W11.wn00785 b)
                      (node
                        leaf
                        (W37.wn01809 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00145 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02193 b)
                          leaf
                        )
                        (W23.wn01169 b)
                        leaf
                      )
                      (W07.wn00657 b)
                      (node
                        leaf
                        (W34.wn01681 b)
                        leaf
                      )
                    )
                    (W02.wn00401 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02449 b)
                          leaf
                        )
                        (W28.wn01425 b)
                        leaf
                      )
                      (W15.wn00913 b)
                      (node
                        leaf
                        (W41.wn01937 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00081 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02129 b)
                          leaf
                        )
                        (W21.wn01105 b)
                        leaf
                      )
                      (W06.wn00593 b)
                      (node
                        leaf
                        (W32.wn01617 b)
                        leaf
                      )
                    )
                    (W02.wn00337 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02385 b)
                          leaf
                        )
                        (W27.wn01361 b)
                        leaf
                      )
                      (W13.wn00849 b)
                      (node
                        leaf
                        (W38.wn01873 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00209 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02257 b)
                          leaf
                        )
                        (W24.wn01233 b)
                        leaf
                      )
                      (W09.wn00721 b)
                      (node
                        leaf
                        (W35.wn01745 b)
                        leaf
                      )
                    )
                    (W03.wn00465 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02513 b)
                          leaf
                        )
                        (W28.wn01489 b)
                        leaf
                      )
                      (W19.wn00977 b)
                      (node
                        leaf
                        (W42.wn02001 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00049 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02097 b)
                          leaf
                        )
                        (W20.wn01073 b)
                        leaf
                      )
                      (W05.wn00561 b)
                      (node
                        leaf
                        (W30.wn01585 b)
                        leaf
                      )
                    )
                    (W02.wn00305 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02353 b)
                          leaf
                        )
                        (W26.wn01329 b)
                        leaf
                      )
                      (W12.wn00817 b)
                      (node
                        leaf
                        (W37.wn01841 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00177 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02225 b)
                          leaf
                        )
                        (W23.wn01201 b)
                        leaf
                      )
                      (W08.wn00689 b)
                      (node
                        leaf
                        (W35.wn01713 b)
                        leaf
                      )
                    )
                    (W03.wn00433 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02481 b)
                          leaf
                        )
                        (W28.wn01457 b)
                        leaf
                      )
                      (W17.wn00945 b)
                      (node
                        leaf
                        (W41.wn01969 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00113 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02161 b)
                          leaf
                        )
                        (W22.wn01137 b)
                        leaf
                      )
                      (W06.wn00625 b)
                      (node
                        leaf
                        (W33.wn01649 b)
                        leaf
                      )
                    )
                    (W02.wn00369 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02417 b)
                          leaf
                        )
                        (W27.wn01393 b)
                        leaf
                      )
                      (W14.wn00881 b)
                      (node
                        leaf
                        (W39.wn01905 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00241 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02289 b)
                          leaf
                        )
                        (W25.wn01265 b)
                        leaf
                      )
                      (W10.wn00753 b)
                      (node
                        leaf
                        (W36.wn01777 b)
                        leaf
                      )
                    )
                    (W03.wn00497 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02545 b)
                          leaf
                        )
                        (W29.wn01521 b)
                        leaf
                      )
                      (W20.wn01009 b)
                      (node
                        leaf
                        (W43.wn02033 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
          (W01.wn00009 b)
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02057 b)
                          leaf
                        )
                        (W20.wn01033 b)
                        leaf
                      )
                      (W04.wn00521 b)
                      (node
                        (node
                          leaf
                          (W48.wn02569 b)
                          leaf
                        )
                        (W29.wn01545 b)
                        leaf
                      )
                    )
                    (W02.wn00265 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02313 b)
                          leaf
                        )
                        (W25.wn01289 b)
                        leaf
                      )
                      (W10.wn00777 b)
                      (node
                        leaf
                        (W37.wn01801 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00137 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02185 b)
                          leaf
                        )
                        (W22.wn01161 b)
                        leaf
                      )
                      (W07.wn00649 b)
                      (node
                        leaf
                        (W34.wn01673 b)
                        leaf
                      )
                    )
                    (W02.wn00393 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02441 b)
                          leaf
                        )
                        (W27.wn01417 b)
                        leaf
                      )
                      (W15.wn00905 b)
                      (node
                        leaf
                        (W41.wn01929 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00073 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02121 b)
                          leaf
                        )
                        (W21.wn01097 b)
                        leaf
                      )
                      (W05.wn00585 b)
                      (node
                        leaf
                        (W31.wn01609 b)
                        leaf
                      )
                    )
                    (W02.wn00329 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02377 b)
                          leaf
                        )
                        (W27.wn01353 b)
                        leaf
                      )
                      (W13.wn00841 b)
                      (node
                        leaf
                        (W38.wn01865 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00201 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02249 b)
                          leaf
                        )
                        (W24.wn01225 b)
                        leaf
                      )
                      (W09.wn00713 b)
                      (node
                        leaf
                        (W35.wn01737 b)
                        leaf
                      )
                    )
                    (W03.wn00457 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02505 b)
                          leaf
                        )
                        (W28.wn01481 b)
                        leaf
                      )
                      (W19.wn00969 b)
                      (node
                        leaf
                        (W42.wn01993 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00041 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02089 b)
                          leaf
                        )
                        (W20.wn01065 b)
                        leaf
                      )
                      (W04.wn00553 b)
                      (node
                        leaf
                        (W29.wn01577 b)
                        leaf
                      )
                    )
                    (W02.wn00297 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02345 b)
                          leaf
                        )
                        (W26.wn01321 b)
                        leaf
                      )
                      (W11.wn00809 b)
                      (node
                        leaf
                        (W37.wn01833 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00169 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02217 b)
                          leaf
                        )
                        (W23.wn01193 b)
                        leaf
                      )
                      (W08.wn00681 b)
                      (node
                        leaf
                        (W35.wn01705 b)
                        leaf
                      )
                    )
                    (W03.wn00425 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02473 b)
                          leaf
                        )
                        (W28.wn01449 b)
                        leaf
                      )
                      (W16.wn00937 b)
                      (node
                        leaf
                        (W41.wn01961 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00105 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02153 b)
                          leaf
                        )
                        (W22.wn01129 b)
                        leaf
                      )
                      (W06.wn00617 b)
                      (node
                        leaf
                        (W33.wn01641 b)
                        leaf
                      )
                    )
                    (W02.wn00361 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02409 b)
                          leaf
                        )
                        (W27.wn01385 b)
                        leaf
                      )
                      (W14.wn00873 b)
                      (node
                        leaf
                        (W39.wn01897 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00233 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02281 b)
                          leaf
                        )
                        (W25.wn01257 b)
                        leaf
                      )
                      (W10.wn00745 b)
                      (node
                        leaf
                        (W35.wn01769 b)
                        leaf
                      )
                    )
                    (W03.wn00489 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02537 b)
                          leaf
                        )
                        (W29.wn01513 b)
                        leaf
                      )
                      (W20.wn01001 b)
                      (node
                        leaf
                        (W43.wn02025 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00025 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02073 b)
                          leaf
                        )
                        (W20.wn01049 b)
                        leaf
                      )
                      (W04.wn00537 b)
                      (node
                        leaf
                        (W29.wn01561 b)
                        leaf
                      )
                    )
                    (W02.wn00281 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02329 b)
                          leaf
                        )
                        (W26.wn01305 b)
                        leaf
                      )
                      (W11.wn00793 b)
                      (node
                        leaf
                        (W37.wn01817 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00153 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02201 b)
                          leaf
                        )
                        (W23.wn01177 b)
                        leaf
                      )
                      (W07.wn00665 b)
                      (node
                        leaf
                        (W35.wn01689 b)
                        leaf
                      )
                    )
                    (W03.wn00409 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02457 b)
                          leaf
                        )
                        (W28.wn01433 b)
                        leaf
                      )
                      (W15.wn00921 b)
                      (node
                        leaf
                        (W41.wn01945 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00089 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02137 b)
                          leaf
                        )
                        (W21.wn01113 b)
                        leaf
                      )
                      (W06.wn00601 b)
                      (node
                        leaf
                        (W32.wn01625 b)
                        leaf
                      )
                    )
                    (W02.wn00345 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02393 b)
                          leaf
                        )
                        (W27.wn01369 b)
                        leaf
                      )
                      (W13.wn00857 b)
                      (node
                        leaf
                        (W38.wn01881 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00217 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02265 b)
                          leaf
                        )
                        (W25.wn01241 b)
                        leaf
                      )
                      (W09.wn00729 b)
                      (node
                        leaf
                        (W35.wn01753 b)
                        leaf
                      )
                    )
                    (W03.wn00473 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02521 b)
                          leaf
                        )
                        (W28.wn01497 b)
                        leaf
                      )
                      (W19.wn00985 b)
                      (node
                        leaf
                        (W42.wn02009 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00057 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02105 b)
                          leaf
                        )
                        (W20.wn01081 b)
                        leaf
                      )
                      (W05.wn00569 b)
                      (node
                        leaf
                        (W30.wn01593 b)
                        leaf
                      )
                    )
                    (W02.wn00313 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02361 b)
                          leaf
                        )
                        (W27.wn01337 b)
                        leaf
                      )
                      (W12.wn00825 b)
                      (node
                        leaf
                        (W38.wn01849 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00185 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02233 b)
                          leaf
                        )
                        (W24.wn01209 b)
                        leaf
                      )
                      (W09.wn00697 b)
                      (node
                        leaf
                        (W35.wn01721 b)
                        leaf
                      )
                    )
                    (W03.wn00441 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02489 b)
                          leaf
                        )
                        (W28.wn01465 b)
                        leaf
                      )
                      (W17.wn00953 b)
                      (node
                        leaf
                        (W42.wn01977 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00121 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02169 b)
                          leaf
                        )
                        (W22.wn01145 b)
                        leaf
                      )
                      (W06.wn00633 b)
                      (node
                        leaf
                        (W34.wn01657 b)
                        leaf
                      )
                    )
                    (W02.wn00377 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02425 b)
                          leaf
                        )
                        (W27.wn01401 b)
                        leaf
                      )
                      (W14.wn00889 b)
                      (node
                        leaf
                        (W40.wn01913 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00249 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02297 b)
                          leaf
                        )
                        (W25.wn01273 b)
                        leaf
                      )
                      (W10.wn00761 b)
                      (node
                        leaf
                        (W36.wn01785 b)
                        leaf
                      )
                    )
                    (W03.wn00505 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02553 b)
                          leaf
                        )
                        (W29.wn01529 b)
                        leaf
                      )
                      (W20.wn01017 b)
                      (node
                        leaf
                        (W43.wn02041 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
        )
        (W01.wn00005 b)
        (node
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02053 b)
                          leaf
                        )
                        (W20.wn01029 b)
                        leaf
                      )
                      (W04.wn00517 b)
                      (node
                        (node
                          leaf
                          (W48.wn02565 b)
                          leaf
                        )
                        (W29.wn01541 b)
                        leaf
                      )
                    )
                    (W02.wn00261 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02309 b)
                          leaf
                        )
                        (W25.wn01285 b)
                        leaf
                      )
                      (W10.wn00773 b)
                      (node
                        leaf
                        (W36.wn01797 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00133 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02181 b)
                          leaf
                        )
                        (W22.wn01157 b)
                        leaf
                      )
                      (W07.wn00645 b)
                      (node
                        leaf
                        (W34.wn01669 b)
                        leaf
                      )
                    )
                    (W02.wn00389 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02437 b)
                          leaf
                        )
                        (W27.wn01413 b)
                        leaf
                      )
                      (W15.wn00901 b)
                      (node
                        leaf
                        (W40.wn01925 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00069 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02117 b)
                          leaf
                        )
                        (W21.wn01093 b)
                        leaf
                      )
                      (W05.wn00581 b)
                      (node
                        leaf
                        (W31.wn01605 b)
                        leaf
                      )
                    )
                    (W02.wn00325 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02373 b)
                          leaf
                        )
                        (W27.wn01349 b)
                        leaf
                      )
                      (W12.wn00837 b)
                      (node
                        leaf
                        (W38.wn01861 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00197 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02245 b)
                          leaf
                        )
                        (W24.wn01221 b)
                        leaf
                      )
                      (W09.wn00709 b)
                      (node
                        leaf
                        (W35.wn01733 b)
                        leaf
                      )
                    )
                    (W03.wn00453 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02501 b)
                          leaf
                        )
                        (W28.wn01477 b)
                        leaf
                      )
                      (W18.wn00965 b)
                      (node
                        leaf
                        (W42.wn01989 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00037 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02085 b)
                          leaf
                        )
                        (W20.wn01061 b)
                        leaf
                      )
                      (W04.wn00549 b)
                      (node
                        leaf
                        (W29.wn01573 b)
                        leaf
                      )
                    )
                    (W02.wn00293 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02341 b)
                          leaf
                        )
                        (W26.wn01317 b)
                        leaf
                      )
                      (W11.wn00805 b)
                      (node
                        leaf
                        (W37.wn01829 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00165 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02213 b)
                          leaf
                        )
                        (W23.wn01189 b)
                        leaf
                      )
                      (W08.wn00677 b)
                      (node
                        leaf
                        (W35.wn01701 b)
                        leaf
                      )
                    )
                    (W03.wn00421 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02469 b)
                          leaf
                        )
                        (W28.wn01445 b)
                        leaf
                      )
                      (W16.wn00933 b)
                      (node
                        leaf
                        (W41.wn01957 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00101 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02149 b)
                          leaf
                        )
                        (W22.wn01125 b)
                        leaf
                      )
                      (W06.wn00613 b)
                      (node
                        leaf
                        (W33.wn01637 b)
                        leaf
                      )
                    )
                    (W02.wn00357 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02405 b)
                          leaf
                        )
                        (W27.wn01381 b)
                        leaf
                      )
                      (W14.wn00869 b)
                      (node
                        leaf
                        (W39.wn01893 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00229 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02277 b)
                          leaf
                        )
                        (W25.wn01253 b)
                        leaf
                      )
                      (W10.wn00741 b)
                      (node
                        leaf
                        (W35.wn01765 b)
                        leaf
                      )
                    )
                    (W03.wn00485 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02533 b)
                          leaf
                        )
                        (W28.wn01509 b)
                        leaf
                      )
                      (W20.wn00997 b)
                      (node
                        leaf
                        (W42.wn02021 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00021 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02069 b)
                          leaf
                        )
                        (W20.wn01045 b)
                        leaf
                      )
                      (W04.wn00533 b)
                      (node
                        (node
                          leaf
                          (W49.wn02581 b)
                          leaf
                        )
                        (W29.wn01557 b)
                        leaf
                      )
                    )
                    (W02.wn00277 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02325 b)
                          leaf
                        )
                        (W26.wn01301 b)
                        leaf
                      )
                      (W11.wn00789 b)
                      (node
                        leaf
                        (W37.wn01813 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00149 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02197 b)
                          leaf
                        )
                        (W23.wn01173 b)
                        leaf
                      )
                      (W07.wn00661 b)
                      (node
                        leaf
                        (W34.wn01685 b)
                        leaf
                      )
                    )
                    (W02.wn00405 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02453 b)
                          leaf
                        )
                        (W28.wn01429 b)
                        leaf
                      )
                      (W15.wn00917 b)
                      (node
                        leaf
                        (W41.wn01941 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00085 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02133 b)
                          leaf
                        )
                        (W21.wn01109 b)
                        leaf
                      )
                      (W06.wn00597 b)
                      (node
                        leaf
                        (W32.wn01621 b)
                        leaf
                      )
                    )
                    (W02.wn00341 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02389 b)
                          leaf
                        )
                        (W27.wn01365 b)
                        leaf
                      )
                      (W13.wn00853 b)
                      (node
                        leaf
                        (W38.wn01877 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00213 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02261 b)
                          leaf
                        )
                        (W24.wn01237 b)
                        leaf
                      )
                      (W09.wn00725 b)
                      (node
                        leaf
                        (W35.wn01749 b)
                        leaf
                      )
                    )
                    (W03.wn00469 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02517 b)
                          leaf
                        )
                        (W28.wn01493 b)
                        leaf
                      )
                      (W19.wn00981 b)
                      (node
                        leaf
                        (W42.wn02005 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00053 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02101 b)
                          leaf
                        )
                        (W20.wn01077 b)
                        leaf
                      )
                      (W05.wn00565 b)
                      (node
                        leaf
                        (W30.wn01589 b)
                        leaf
                      )
                    )
                    (W02.wn00309 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02357 b)
                          leaf
                        )
                        (W27.wn01333 b)
                        leaf
                      )
                      (W12.wn00821 b)
                      (node
                        leaf
                        (W38.wn01845 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00181 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02229 b)
                          leaf
                        )
                        (W24.wn01205 b)
                        leaf
                      )
                      (W08.wn00693 b)
                      (node
                        leaf
                        (W35.wn01717 b)
                        leaf
                      )
                    )
                    (W03.wn00437 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02485 b)
                          leaf
                        )
                        (W28.wn01461 b)
                        leaf
                      )
                      (W17.wn00949 b)
                      (node
                        leaf
                        (W41.wn01973 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00117 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02165 b)
                          leaf
                        )
                        (W22.wn01141 b)
                        leaf
                      )
                      (W06.wn00629 b)
                      (node
                        leaf
                        (W34.wn01653 b)
                        leaf
                      )
                    )
                    (W02.wn00373 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02421 b)
                          leaf
                        )
                        (W27.wn01397 b)
                        leaf
                      )
                      (W14.wn00885 b)
                      (node
                        leaf
                        (W40.wn01909 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00245 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02293 b)
                          leaf
                        )
                        (W25.wn01269 b)
                        leaf
                      )
                      (W10.wn00757 b)
                      (node
                        leaf
                        (W36.wn01781 b)
                        leaf
                      )
                    )
                    (W03.wn00501 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02549 b)
                          leaf
                        )
                        (W29.wn01525 b)
                        leaf
                      )
                      (W20.wn01013 b)
                      (node
                        leaf
                        (W43.wn02037 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
          (W01.wn00013 b)
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02061 b)
                          leaf
                        )
                        (W20.wn01037 b)
                        leaf
                      )
                      (W04.wn00525 b)
                      (node
                        (node
                          leaf
                          (W49.wn02573 b)
                          leaf
                        )
                        (W29.wn01549 b)
                        leaf
                      )
                    )
                    (W02.wn00269 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02317 b)
                          leaf
                        )
                        (W25.wn01293 b)
                        leaf
                      )
                      (W10.wn00781 b)
                      (node
                        leaf
                        (W37.wn01805 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00141 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02189 b)
                          leaf
                        )
                        (W22.wn01165 b)
                        leaf
                      )
                      (W07.wn00653 b)
                      (node
                        leaf
                        (W34.wn01677 b)
                        leaf
                      )
                    )
                    (W02.wn00397 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02445 b)
                          leaf
                        )
                        (W28.wn01421 b)
                        leaf
                      )
                      (W15.wn00909 b)
                      (node
                        leaf
                        (W41.wn01933 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00077 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02125 b)
                          leaf
                        )
                        (W21.wn01101 b)
                        leaf
                      )
                      (W06.wn00589 b)
                      (node
                        leaf
                        (W32.wn01613 b)
                        leaf
                      )
                    )
                    (W02.wn00333 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02381 b)
                          leaf
                        )
                        (W27.wn01357 b)
                        leaf
                      )
                      (W13.wn00845 b)
                      (node
                        leaf
                        (W38.wn01869 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00205 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02253 b)
                          leaf
                        )
                        (W24.wn01229 b)
                        leaf
                      )
                      (W09.wn00717 b)
                      (node
                        leaf
                        (W35.wn01741 b)
                        leaf
                      )
                    )
                    (W03.wn00461 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02509 b)
                          leaf
                        )
                        (W28.wn01485 b)
                        leaf
                      )
                      (W19.wn00973 b)
                      (node
                        leaf
                        (W42.wn01997 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00045 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02093 b)
                          leaf
                        )
                        (W20.wn01069 b)
                        leaf
                      )
                      (W04.wn00557 b)
                      (node
                        leaf
                        (W30.wn01581 b)
                        leaf
                      )
                    )
                    (W02.wn00301 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02349 b)
                          leaf
                        )
                        (W26.wn01325 b)
                        leaf
                      )
                      (W11.wn00813 b)
                      (node
                        leaf
                        (W37.wn01837 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00173 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02221 b)
                          leaf
                        )
                        (W23.wn01197 b)
                        leaf
                      )
                      (W08.wn00685 b)
                      (node
                        leaf
                        (W35.wn01709 b)
                        leaf
                      )
                    )
                    (W03.wn00429 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02477 b)
                          leaf
                        )
                        (W28.wn01453 b)
                        leaf
                      )
                      (W16.wn00941 b)
                      (node
                        leaf
                        (W41.wn01965 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00109 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02157 b)
                          leaf
                        )
                        (W22.wn01133 b)
                        leaf
                      )
                      (W06.wn00621 b)
                      (node
                        leaf
                        (W33.wn01645 b)
                        leaf
                      )
                    )
                    (W02.wn00365 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02413 b)
                          leaf
                        )
                        (W27.wn01389 b)
                        leaf
                      )
                      (W14.wn00877 b)
                      (node
                        leaf
                        (W39.wn01901 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00237 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02285 b)
                          leaf
                        )
                        (W25.wn01261 b)
                        leaf
                      )
                      (W10.wn00749 b)
                      (node
                        leaf
                        (W36.wn01773 b)
                        leaf
                      )
                    )
                    (W03.wn00493 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02541 b)
                          leaf
                        )
                        (W29.wn01517 b)
                        leaf
                      )
                      (W20.wn01005 b)
                      (node
                        leaf
                        (W43.wn02029 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00029 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02077 b)
                          leaf
                        )
                        (W20.wn01053 b)
                        leaf
                      )
                      (W04.wn00541 b)
                      (node
                        leaf
                        (W29.wn01565 b)
                        leaf
                      )
                    )
                    (W02.wn00285 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02333 b)
                          leaf
                        )
                        (W26.wn01309 b)
                        leaf
                      )
                      (W11.wn00797 b)
                      (node
                        leaf
                        (W37.wn01821 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00157 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02205 b)
                          leaf
                        )
                        (W23.wn01181 b)
                        leaf
                      )
                      (W08.wn00669 b)
                      (node
                        leaf
                        (W35.wn01693 b)
                        leaf
                      )
                    )
                    (W03.wn00413 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02461 b)
                          leaf
                        )
                        (W28.wn01437 b)
                        leaf
                      )
                      (W15.wn00925 b)
                      (node
                        leaf
                        (W41.wn01949 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00093 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02141 b)
                          leaf
                        )
                        (W21.wn01117 b)
                        leaf
                      )
                      (W06.wn00605 b)
                      (node
                        leaf
                        (W32.wn01629 b)
                        leaf
                      )
                    )
                    (W02.wn00349 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02397 b)
                          leaf
                        )
                        (W27.wn01373 b)
                        leaf
                      )
                      (W13.wn00861 b)
                      (node
                        leaf
                        (W38.wn01885 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00221 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02269 b)
                          leaf
                        )
                        (W25.wn01245 b)
                        leaf
                      )
                      (W09.wn00733 b)
                      (node
                        leaf
                        (W35.wn01757 b)
                        leaf
                      )
                    )
                    (W03.wn00477 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02525 b)
                          leaf
                        )
                        (W28.wn01501 b)
                        leaf
                      )
                      (W19.wn00989 b)
                      (node
                        leaf
                        (W42.wn02013 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00061 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02109 b)
                          leaf
                        )
                        (W21.wn01085 b)
                        leaf
                      )
                      (W05.wn00573 b)
                      (node
                        leaf
                        (W31.wn01597 b)
                        leaf
                      )
                    )
                    (W02.wn00317 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02365 b)
                          leaf
                        )
                        (W27.wn01341 b)
                        leaf
                      )
                      (W12.wn00829 b)
                      (node
                        leaf
                        (W38.wn01853 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00189 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02237 b)
                          leaf
                        )
                        (W24.wn01213 b)
                        leaf
                      )
                      (W09.wn00701 b)
                      (node
                        leaf
                        (W35.wn01725 b)
                        leaf
                      )
                    )
                    (W03.wn00445 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02493 b)
                          leaf
                        )
                        (W28.wn01469 b)
                        leaf
                      )
                      (W18.wn00957 b)
                      (node
                        leaf
                        (W42.wn01981 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00125 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02173 b)
                          leaf
                        )
                        (W22.wn01149 b)
                        leaf
                      )
                      (W07.wn00637 b)
                      (node
                        leaf
                        (W34.wn01661 b)
                        leaf
                      )
                    )
                    (W02.wn00381 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02429 b)
                          leaf
                        )
                        (W27.wn01405 b)
                        leaf
                      )
                      (W14.wn00893 b)
                      (node
                        leaf
                        (W40.wn01917 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00253 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02301 b)
                          leaf
                        )
                        (W25.wn01277 b)
                        leaf
                      )
                      (W10.wn00765 b)
                      (node
                        leaf
                        (W36.wn01789 b)
                        leaf
                      )
                    )
                    (W04.wn00509 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02557 b)
                          leaf
                        )
                        (W29.wn01533 b)
                        leaf
                      )
                      (W20.wn01021 b)
                      (node
                        leaf
                        (W43.wn02045 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    refl
    (node
      (node
        (node
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02048 b)
                          leaf
                        )
                        (W20.wn01024 b)
                        leaf
                      )
                      (W04.wn00512 b)
                      (node
                        (node
                          leaf
                          (W48.wn02560 b)
                          leaf
                        )
                        (W29.wn01536 b)
                        leaf
                      )
                    )
                    (W02.wn00256 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02304 b)
                          leaf
                        )
                        (W25.wn01280 b)
                        leaf
                      )
                      (W10.wn00768 b)
                      (node
                        leaf
                        (W36.wn01792 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00128 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02176 b)
                          leaf
                        )
                        (W22.wn01152 b)
                        leaf
                      )
                      (W07.wn00640 b)
                      (node
                        leaf
                        (W34.wn01664 b)
                        leaf
                      )
                    )
                    (W02.wn00384 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02432 b)
                          leaf
                        )
                        (W27.wn01408 b)
                        leaf
                      )
                      (W14.wn00896 b)
                      (node
                        leaf
                        (W40.wn01920 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00064 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02112 b)
                          leaf
                        )
                        (W21.wn01088 b)
                        leaf
                      )
                      (W05.wn00576 b)
                      (node
                        leaf
                        (W31.wn01600 b)
                        leaf
                      )
                    )
                    (W02.wn00320 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02368 b)
                          leaf
                        )
                        (W27.wn01344 b)
                        leaf
                      )
                      (W12.wn00832 b)
                      (node
                        leaf
                        (W38.wn01856 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00192 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02240 b)
                          leaf
                        )
                        (W24.wn01216 b)
                        leaf
                      )
                      (W09.wn00704 b)
                      (node
                        leaf
                        (W35.wn01728 b)
                        leaf
                      )
                    )
                    (W03.wn00448 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02496 b)
                          leaf
                        )
                        (W28.wn01472 b)
                        leaf
                      )
                      (W18.wn00960 b)
                      (node
                        leaf
                        (W42.wn01984 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00032 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02080 b)
                          leaf
                        )
                        (W20.wn01056 b)
                        leaf
                      )
                      (W04.wn00544 b)
                      (node
                        leaf
                        (W29.wn01568 b)
                        leaf
                      )
                    )
                    (W02.wn00288 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02336 b)
                          leaf
                        )
                        (W26.wn01312 b)
                        leaf
                      )
                      (W11.wn00800 b)
                      (node
                        leaf
                        (W37.wn01824 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00160 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02208 b)
                          leaf
                        )
                        (W23.wn01184 b)
                        leaf
                      )
                      (W08.wn00672 b)
                      (node
                        leaf
                        (W35.wn01696 b)
                        leaf
                      )
                    )
                    (W03.wn00416 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02464 b)
                          leaf
                        )
                        (W28.wn01440 b)
                        leaf
                      )
                      (W16.wn00928 b)
                      (node
                        leaf
                        (W41.wn01952 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00096 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02144 b)
                          leaf
                        )
                        (W21.wn01120 b)
                        leaf
                      )
                      (W06.wn00608 b)
                      (node
                        leaf
                        (W32.wn01632 b)
                        leaf
                      )
                    )
                    (W02.wn00352 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02400 b)
                          leaf
                        )
                        (W27.wn01376 b)
                        leaf
                      )
                      (W14.wn00864 b)
                      (node
                        leaf
                        (W38.wn01888 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00224 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02272 b)
                          leaf
                        )
                        (W25.wn01248 b)
                        leaf
                      )
                      (W09.wn00736 b)
                      (node
                        leaf
                        (W35.wn01760 b)
                        leaf
                      )
                    )
                    (W03.wn00480 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02528 b)
                          leaf
                        )
                        (W28.wn01504 b)
                        leaf
                      )
                      (W19.wn00992 b)
                      (node
                        leaf
                        (W42.wn02016 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00016 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02064 b)
                          leaf
                        )
                        (W20.wn01040 b)
                        leaf
                      )
                      (W04.wn00528 b)
                      (node
                        (node
                          leaf
                          (W49.wn02576 b)
                          leaf
                        )
                        (W29.wn01552 b)
                        leaf
                      )
                    )
                    (W02.wn00272 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02320 b)
                          leaf
                        )
                        (W25.wn01296 b)
                        leaf
                      )
                      (W10.wn00784 b)
                      (node
                        leaf
                        (W37.wn01808 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00144 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02192 b)
                          leaf
                        )
                        (W22.wn01168 b)
                        leaf
                      )
                      (W07.wn00656 b)
                      (node
                        leaf
                        (W34.wn01680 b)
                        leaf
                      )
                    )
                    (W02.wn00400 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02448 b)
                          leaf
                        )
                        (W28.wn01424 b)
                        leaf
                      )
                      (W15.wn00912 b)
                      (node
                        leaf
                        (W41.wn01936 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00080 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02128 b)
                          leaf
                        )
                        (W21.wn01104 b)
                        leaf
                      )
                      (W06.wn00592 b)
                      (node
                        leaf
                        (W32.wn01616 b)
                        leaf
                      )
                    )
                    (W02.wn00336 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02384 b)
                          leaf
                        )
                        (W27.wn01360 b)
                        leaf
                      )
                      (W13.wn00848 b)
                      (node
                        leaf
                        (W38.wn01872 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00208 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02256 b)
                          leaf
                        )
                        (W24.wn01232 b)
                        leaf
                      )
                      (W09.wn00720 b)
                      (node
                        leaf
                        (W35.wn01744 b)
                        leaf
                      )
                    )
                    (W03.wn00464 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02512 b)
                          leaf
                        )
                        (W28.wn01488 b)
                        leaf
                      )
                      (W19.wn00976 b)
                      (node
                        leaf
                        (W42.wn02000 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00048 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02096 b)
                          leaf
                        )
                        (W20.wn01072 b)
                        leaf
                      )
                      (W04.wn00560 b)
                      (node
                        leaf
                        (W30.wn01584 b)
                        leaf
                      )
                    )
                    (W02.wn00304 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02352 b)
                          leaf
                        )
                        (W26.wn01328 b)
                        leaf
                      )
                      (W12.wn00816 b)
                      (node
                        leaf
                        (W37.wn01840 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00176 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02224 b)
                          leaf
                        )
                        (W23.wn01200 b)
                        leaf
                      )
                      (W08.wn00688 b)
                      (node
                        leaf
                        (W35.wn01712 b)
                        leaf
                      )
                    )
                    (W03.wn00432 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02480 b)
                          leaf
                        )
                        (W28.wn01456 b)
                        leaf
                      )
                      (W17.wn00944 b)
                      (node
                        leaf
                        (W41.wn01968 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00112 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02160 b)
                          leaf
                        )
                        (W22.wn01136 b)
                        leaf
                      )
                      (W06.wn00624 b)
                      (node
                        leaf
                        (W33.wn01648 b)
                        leaf
                      )
                    )
                    (W02.wn00368 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02416 b)
                          leaf
                        )
                        (W27.wn01392 b)
                        leaf
                      )
                      (W14.wn00880 b)
                      (node
                        leaf
                        (W39.wn01904 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00240 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02288 b)
                          leaf
                        )
                        (W25.wn01264 b)
                        leaf
                      )
                      (W10.wn00752 b)
                      (node
                        leaf
                        (W36.wn01776 b)
                        leaf
                      )
                    )
                    (W03.wn00496 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02544 b)
                          leaf
                        )
                        (W29.wn01520 b)
                        leaf
                      )
                      (W20.wn01008 b)
                      (node
                        leaf
                        (W43.wn02032 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
          (W01.wn00008 b)
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02056 b)
                          leaf
                        )
                        (W20.wn01032 b)
                        leaf
                      )
                      (W04.wn00520 b)
                      (node
                        (node
                          leaf
                          (W48.wn02568 b)
                          leaf
                        )
                        (W29.wn01544 b)
                        leaf
                      )
                    )
                    (W02.wn00264 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02312 b)
                          leaf
                        )
                        (W25.wn01288 b)
                        leaf
                      )
                      (W10.wn00776 b)
                      (node
                        leaf
                        (W37.wn01800 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00136 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02184 b)
                          leaf
                        )
                        (W22.wn01160 b)
                        leaf
                      )
                      (W07.wn00648 b)
                      (node
                        leaf
                        (W34.wn01672 b)
                        leaf
                      )
                    )
                    (W02.wn00392 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02440 b)
                          leaf
                        )
                        (W27.wn01416 b)
                        leaf
                      )
                      (W15.wn00904 b)
                      (node
                        leaf
                        (W40.wn01928 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00072 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02120 b)
                          leaf
                        )
                        (W21.wn01096 b)
                        leaf
                      )
                      (W05.wn00584 b)
                      (node
                        leaf
                        (W31.wn01608 b)
                        leaf
                      )
                    )
                    (W02.wn00328 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02376 b)
                          leaf
                        )
                        (W27.wn01352 b)
                        leaf
                      )
                      (W13.wn00840 b)
                      (node
                        leaf
                        (W38.wn01864 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00200 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02248 b)
                          leaf
                        )
                        (W24.wn01224 b)
                        leaf
                      )
                      (W09.wn00712 b)
                      (node
                        leaf
                        (W35.wn01736 b)
                        leaf
                      )
                    )
                    (W03.wn00456 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02504 b)
                          leaf
                        )
                        (W28.wn01480 b)
                        leaf
                      )
                      (W18.wn00968 b)
                      (node
                        leaf
                        (W42.wn01992 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00040 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02088 b)
                          leaf
                        )
                        (W20.wn01064 b)
                        leaf
                      )
                      (W04.wn00552 b)
                      (node
                        leaf
                        (W29.wn01576 b)
                        leaf
                      )
                    )
                    (W02.wn00296 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02344 b)
                          leaf
                        )
                        (W26.wn01320 b)
                        leaf
                      )
                      (W11.wn00808 b)
                      (node
                        leaf
                        (W37.wn01832 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00168 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02216 b)
                          leaf
                        )
                        (W23.wn01192 b)
                        leaf
                      )
                      (W08.wn00680 b)
                      (node
                        leaf
                        (W35.wn01704 b)
                        leaf
                      )
                    )
                    (W03.wn00424 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02472 b)
                          leaf
                        )
                        (W28.wn01448 b)
                        leaf
                      )
                      (W16.wn00936 b)
                      (node
                        leaf
                        (W41.wn01960 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00104 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02152 b)
                          leaf
                        )
                        (W22.wn01128 b)
                        leaf
                      )
                      (W06.wn00616 b)
                      (node
                        leaf
                        (W33.wn01640 b)
                        leaf
                      )
                    )
                    (W02.wn00360 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02408 b)
                          leaf
                        )
                        (W27.wn01384 b)
                        leaf
                      )
                      (W14.wn00872 b)
                      (node
                        leaf
                        (W39.wn01896 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00232 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02280 b)
                          leaf
                        )
                        (W25.wn01256 b)
                        leaf
                      )
                      (W10.wn00744 b)
                      (node
                        leaf
                        (W35.wn01768 b)
                        leaf
                      )
                    )
                    (W03.wn00488 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02536 b)
                          leaf
                        )
                        (W29.wn01512 b)
                        leaf
                      )
                      (W20.wn01000 b)
                      (node
                        leaf
                        (W42.wn02024 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00024 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02072 b)
                          leaf
                        )
                        (W20.wn01048 b)
                        leaf
                      )
                      (W04.wn00536 b)
                      (node
                        (node
                          leaf
                          (W49.wn02584 b)
                          leaf
                        )
                        (W29.wn01560 b)
                        leaf
                      )
                    )
                    (W02.wn00280 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02328 b)
                          leaf
                        )
                        (W26.wn01304 b)
                        leaf
                      )
                      (W11.wn00792 b)
                      (node
                        leaf
                        (W37.wn01816 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00152 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02200 b)
                          leaf
                        )
                        (W23.wn01176 b)
                        leaf
                      )
                      (W07.wn00664 b)
                      (node
                        leaf
                        (W34.wn01688 b)
                        leaf
                      )
                    )
                    (W02.wn00408 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02456 b)
                          leaf
                        )
                        (W28.wn01432 b)
                        leaf
                      )
                      (W15.wn00920 b)
                      (node
                        leaf
                        (W41.wn01944 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00088 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02136 b)
                          leaf
                        )
                        (W21.wn01112 b)
                        leaf
                      )
                      (W06.wn00600 b)
                      (node
                        leaf
                        (W32.wn01624 b)
                        leaf
                      )
                    )
                    (W02.wn00344 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02392 b)
                          leaf
                        )
                        (W27.wn01368 b)
                        leaf
                      )
                      (W13.wn00856 b)
                      (node
                        leaf
                        (W38.wn01880 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00216 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02264 b)
                          leaf
                        )
                        (W25.wn01240 b)
                        leaf
                      )
                      (W09.wn00728 b)
                      (node
                        leaf
                        (W35.wn01752 b)
                        leaf
                      )
                    )
                    (W03.wn00472 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02520 b)
                          leaf
                        )
                        (W28.wn01496 b)
                        leaf
                      )
                      (W19.wn00984 b)
                      (node
                        leaf
                        (W42.wn02008 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00056 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02104 b)
                          leaf
                        )
                        (W20.wn01080 b)
                        leaf
                      )
                      (W05.wn00568 b)
                      (node
                        leaf
                        (W30.wn01592 b)
                        leaf
                      )
                    )
                    (W02.wn00312 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02360 b)
                          leaf
                        )
                        (W27.wn01336 b)
                        leaf
                      )
                      (W12.wn00824 b)
                      (node
                        leaf
                        (W38.wn01848 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00184 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02232 b)
                          leaf
                        )
                        (W24.wn01208 b)
                        leaf
                      )
                      (W08.wn00696 b)
                      (node
                        leaf
                        (W35.wn01720 b)
                        leaf
                      )
                    )
                    (W03.wn00440 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02488 b)
                          leaf
                        )
                        (W28.wn01464 b)
                        leaf
                      )
                      (W17.wn00952 b)
                      (node
                        leaf
                        (W42.wn01976 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00120 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02168 b)
                          leaf
                        )
                        (W22.wn01144 b)
                        leaf
                      )
                      (W06.wn00632 b)
                      (node
                        leaf
                        (W34.wn01656 b)
                        leaf
                      )
                    )
                    (W02.wn00376 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02424 b)
                          leaf
                        )
                        (W27.wn01400 b)
                        leaf
                      )
                      (W14.wn00888 b)
                      (node
                        leaf
                        (W40.wn01912 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00248 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02296 b)
                          leaf
                        )
                        (W25.wn01272 b)
                        leaf
                      )
                      (W10.wn00760 b)
                      (node
                        leaf
                        (W36.wn01784 b)
                        leaf
                      )
                    )
                    (W03.wn00504 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02552 b)
                          leaf
                        )
                        (W29.wn01528 b)
                        leaf
                      )
                      (W20.wn01016 b)
                      (node
                        leaf
                        (W43.wn02040 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
        )
        (W01.wn00004 b)
        (node
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02052 b)
                          leaf
                        )
                        (W20.wn01028 b)
                        leaf
                      )
                      (W04.wn00516 b)
                      (node
                        (node
                          leaf
                          (W48.wn02564 b)
                          leaf
                        )
                        (W29.wn01540 b)
                        leaf
                      )
                    )
                    (W02.wn00260 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02308 b)
                          leaf
                        )
                        (W25.wn01284 b)
                        leaf
                      )
                      (W10.wn00772 b)
                      (node
                        leaf
                        (W36.wn01796 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00132 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02180 b)
                          leaf
                        )
                        (W22.wn01156 b)
                        leaf
                      )
                      (W07.wn00644 b)
                      (node
                        leaf
                        (W34.wn01668 b)
                        leaf
                      )
                    )
                    (W02.wn00388 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02436 b)
                          leaf
                        )
                        (W27.wn01412 b)
                        leaf
                      )
                      (W15.wn00900 b)
                      (node
                        leaf
                        (W40.wn01924 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00068 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02116 b)
                          leaf
                        )
                        (W21.wn01092 b)
                        leaf
                      )
                      (W05.wn00580 b)
                      (node
                        leaf
                        (W31.wn01604 b)
                        leaf
                      )
                    )
                    (W02.wn00324 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02372 b)
                          leaf
                        )
                        (W27.wn01348 b)
                        leaf
                      )
                      (W12.wn00836 b)
                      (node
                        leaf
                        (W38.wn01860 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00196 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02244 b)
                          leaf
                        )
                        (W24.wn01220 b)
                        leaf
                      )
                      (W09.wn00708 b)
                      (node
                        leaf
                        (W35.wn01732 b)
                        leaf
                      )
                    )
                    (W03.wn00452 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02500 b)
                          leaf
                        )
                        (W28.wn01476 b)
                        leaf
                      )
                      (W18.wn00964 b)
                      (node
                        leaf
                        (W42.wn01988 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00036 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02084 b)
                          leaf
                        )
                        (W20.wn01060 b)
                        leaf
                      )
                      (W04.wn00548 b)
                      (node
                        leaf
                        (W29.wn01572 b)
                        leaf
                      )
                    )
                    (W02.wn00292 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02340 b)
                          leaf
                        )
                        (W26.wn01316 b)
                        leaf
                      )
                      (W11.wn00804 b)
                      (node
                        leaf
                        (W37.wn01828 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00164 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02212 b)
                          leaf
                        )
                        (W23.wn01188 b)
                        leaf
                      )
                      (W08.wn00676 b)
                      (node
                        leaf
                        (W35.wn01700 b)
                        leaf
                      )
                    )
                    (W03.wn00420 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02468 b)
                          leaf
                        )
                        (W28.wn01444 b)
                        leaf
                      )
                      (W16.wn00932 b)
                      (node
                        leaf
                        (W41.wn01956 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00100 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02148 b)
                          leaf
                        )
                        (W22.wn01124 b)
                        leaf
                      )
                      (W06.wn00612 b)
                      (node
                        leaf
                        (W33.wn01636 b)
                        leaf
                      )
                    )
                    (W02.wn00356 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02404 b)
                          leaf
                        )
                        (W27.wn01380 b)
                        leaf
                      )
                      (W14.wn00868 b)
                      (node
                        leaf
                        (W38.wn01892 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00228 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02276 b)
                          leaf
                        )
                        (W25.wn01252 b)
                        leaf
                      )
                      (W10.wn00740 b)
                      (node
                        leaf
                        (W35.wn01764 b)
                        leaf
                      )
                    )
                    (W03.wn00484 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02532 b)
                          leaf
                        )
                        (W28.wn01508 b)
                        leaf
                      )
                      (W20.wn00996 b)
                      (node
                        leaf
                        (W42.wn02020 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00020 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02068 b)
                          leaf
                        )
                        (W20.wn01044 b)
                        leaf
                      )
                      (W04.wn00532 b)
                      (node
                        (node
                          leaf
                          (W49.wn02580 b)
                          leaf
                        )
                        (W29.wn01556 b)
                        leaf
                      )
                    )
                    (W02.wn00276 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02324 b)
                          leaf
                        )
                        (W26.wn01300 b)
                        leaf
                      )
                      (W11.wn00788 b)
                      (node
                        leaf
                        (W37.wn01812 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00148 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02196 b)
                          leaf
                        )
                        (W23.wn01172 b)
                        leaf
                      )
                      (W07.wn00660 b)
                      (node
                        leaf
                        (W34.wn01684 b)
                        leaf
                      )
                    )
                    (W02.wn00404 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02452 b)
                          leaf
                        )
                        (W28.wn01428 b)
                        leaf
                      )
                      (W15.wn00916 b)
                      (node
                        leaf
                        (W41.wn01940 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00084 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02132 b)
                          leaf
                        )
                        (W21.wn01108 b)
                        leaf
                      )
                      (W06.wn00596 b)
                      (node
                        leaf
                        (W32.wn01620 b)
                        leaf
                      )
                    )
                    (W02.wn00340 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02388 b)
                          leaf
                        )
                        (W27.wn01364 b)
                        leaf
                      )
                      (W13.wn00852 b)
                      (node
                        leaf
                        (W38.wn01876 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00212 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02260 b)
                          leaf
                        )
                        (W24.wn01236 b)
                        leaf
                      )
                      (W09.wn00724 b)
                      (node
                        leaf
                        (W35.wn01748 b)
                        leaf
                      )
                    )
                    (W03.wn00468 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02516 b)
                          leaf
                        )
                        (W28.wn01492 b)
                        leaf
                      )
                      (W19.wn00980 b)
                      (node
                        leaf
                        (W42.wn02004 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00052 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02100 b)
                          leaf
                        )
                        (W20.wn01076 b)
                        leaf
                      )
                      (W05.wn00564 b)
                      (node
                        leaf
                        (W30.wn01588 b)
                        leaf
                      )
                    )
                    (W02.wn00308 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02356 b)
                          leaf
                        )
                        (W27.wn01332 b)
                        leaf
                      )
                      (W12.wn00820 b)
                      (node
                        leaf
                        (W37.wn01844 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00180 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02228 b)
                          leaf
                        )
                        (W24.wn01204 b)
                        leaf
                      )
                      (W08.wn00692 b)
                      (node
                        leaf
                        (W35.wn01716 b)
                        leaf
                      )
                    )
                    (W03.wn00436 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02484 b)
                          leaf
                        )
                        (W28.wn01460 b)
                        leaf
                      )
                      (W17.wn00948 b)
                      (node
                        leaf
                        (W41.wn01972 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00116 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02164 b)
                          leaf
                        )
                        (W22.wn01140 b)
                        leaf
                      )
                      (W06.wn00628 b)
                      (node
                        leaf
                        (W34.wn01652 b)
                        leaf
                      )
                    )
                    (W02.wn00372 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02420 b)
                          leaf
                        )
                        (W27.wn01396 b)
                        leaf
                      )
                      (W14.wn00884 b)
                      (node
                        leaf
                        (W40.wn01908 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00244 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02292 b)
                          leaf
                        )
                        (W25.wn01268 b)
                        leaf
                      )
                      (W10.wn00756 b)
                      (node
                        leaf
                        (W36.wn01780 b)
                        leaf
                      )
                    )
                    (W03.wn00500 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02548 b)
                          leaf
                        )
                        (W29.wn01524 b)
                        leaf
                      )
                      (W20.wn01012 b)
                      (node
                        leaf
                        (W43.wn02036 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
          (W01.wn00012 b)
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02060 b)
                          leaf
                        )
                        (W20.wn01036 b)
                        leaf
                      )
                      (W04.wn00524 b)
                      (node
                        (node
                          leaf
                          (W49.wn02572 b)
                          leaf
                        )
                        (W29.wn01548 b)
                        leaf
                      )
                    )
                    (W02.wn00268 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02316 b)
                          leaf
                        )
                        (W25.wn01292 b)
                        leaf
                      )
                      (W10.wn00780 b)
                      (node
                        leaf
                        (W37.wn01804 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00140 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02188 b)
                          leaf
                        )
                        (W22.wn01164 b)
                        leaf
                      )
                      (W07.wn00652 b)
                      (node
                        leaf
                        (W34.wn01676 b)
                        leaf
                      )
                    )
                    (W02.wn00396 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02444 b)
                          leaf
                        )
                        (W27.wn01420 b)
                        leaf
                      )
                      (W15.wn00908 b)
                      (node
                        leaf
                        (W41.wn01932 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00076 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02124 b)
                          leaf
                        )
                        (W21.wn01100 b)
                        leaf
                      )
                      (W06.wn00588 b)
                      (node
                        leaf
                        (W32.wn01612 b)
                        leaf
                      )
                    )
                    (W02.wn00332 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02380 b)
                          leaf
                        )
                        (W27.wn01356 b)
                        leaf
                      )
                      (W13.wn00844 b)
                      (node
                        leaf
                        (W38.wn01868 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00204 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02252 b)
                          leaf
                        )
                        (W24.wn01228 b)
                        leaf
                      )
                      (W09.wn00716 b)
                      (node
                        leaf
                        (W35.wn01740 b)
                        leaf
                      )
                    )
                    (W03.wn00460 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02508 b)
                          leaf
                        )
                        (W28.wn01484 b)
                        leaf
                      )
                      (W19.wn00972 b)
                      (node
                        leaf
                        (W42.wn01996 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00044 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02092 b)
                          leaf
                        )
                        (W20.wn01068 b)
                        leaf
                      )
                      (W04.wn00556 b)
                      (node
                        leaf
                        (W30.wn01580 b)
                        leaf
                      )
                    )
                    (W02.wn00300 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02348 b)
                          leaf
                        )
                        (W26.wn01324 b)
                        leaf
                      )
                      (W11.wn00812 b)
                      (node
                        leaf
                        (W37.wn01836 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00172 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02220 b)
                          leaf
                        )
                        (W23.wn01196 b)
                        leaf
                      )
                      (W08.wn00684 b)
                      (node
                        leaf
                        (W35.wn01708 b)
                        leaf
                      )
                    )
                    (W03.wn00428 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02476 b)
                          leaf
                        )
                        (W28.wn01452 b)
                        leaf
                      )
                      (W16.wn00940 b)
                      (node
                        leaf
                        (W41.wn01964 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00108 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02156 b)
                          leaf
                        )
                        (W22.wn01132 b)
                        leaf
                      )
                      (W06.wn00620 b)
                      (node
                        leaf
                        (W33.wn01644 b)
                        leaf
                      )
                    )
                    (W02.wn00364 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02412 b)
                          leaf
                        )
                        (W27.wn01388 b)
                        leaf
                      )
                      (W14.wn00876 b)
                      (node
                        leaf
                        (W39.wn01900 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00236 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02284 b)
                          leaf
                        )
                        (W25.wn01260 b)
                        leaf
                      )
                      (W10.wn00748 b)
                      (node
                        leaf
                        (W36.wn01772 b)
                        leaf
                      )
                    )
                    (W03.wn00492 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02540 b)
                          leaf
                        )
                        (W29.wn01516 b)
                        leaf
                      )
                      (W20.wn01004 b)
                      (node
                        leaf
                        (W43.wn02028 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00028 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02076 b)
                          leaf
                        )
                        (W20.wn01052 b)
                        leaf
                      )
                      (W04.wn00540 b)
                      (node
                        leaf
                        (W29.wn01564 b)
                        leaf
                      )
                    )
                    (W02.wn00284 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02332 b)
                          leaf
                        )
                        (W26.wn01308 b)
                        leaf
                      )
                      (W11.wn00796 b)
                      (node
                        leaf
                        (W37.wn01820 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00156 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02204 b)
                          leaf
                        )
                        (W23.wn01180 b)
                        leaf
                      )
                      (W08.wn00668 b)
                      (node
                        leaf
                        (W35.wn01692 b)
                        leaf
                      )
                    )
                    (W03.wn00412 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02460 b)
                          leaf
                        )
                        (W28.wn01436 b)
                        leaf
                      )
                      (W15.wn00924 b)
                      (node
                        leaf
                        (W41.wn01948 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00092 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02140 b)
                          leaf
                        )
                        (W21.wn01116 b)
                        leaf
                      )
                      (W06.wn00604 b)
                      (node
                        leaf
                        (W32.wn01628 b)
                        leaf
                      )
                    )
                    (W02.wn00348 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02396 b)
                          leaf
                        )
                        (W27.wn01372 b)
                        leaf
                      )
                      (W13.wn00860 b)
                      (node
                        leaf
                        (W38.wn01884 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00220 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02268 b)
                          leaf
                        )
                        (W25.wn01244 b)
                        leaf
                      )
                      (W09.wn00732 b)
                      (node
                        leaf
                        (W35.wn01756 b)
                        leaf
                      )
                    )
                    (W03.wn00476 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02524 b)
                          leaf
                        )
                        (W28.wn01500 b)
                        leaf
                      )
                      (W19.wn00988 b)
                      (node
                        leaf
                        (W42.wn02012 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00060 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02108 b)
                          leaf
                        )
                        (W21.wn01084 b)
                        leaf
                      )
                      (W05.wn00572 b)
                      (node
                        leaf
                        (W30.wn01596 b)
                        leaf
                      )
                    )
                    (W02.wn00316 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02364 b)
                          leaf
                        )
                        (W27.wn01340 b)
                        leaf
                      )
                      (W12.wn00828 b)
                      (node
                        leaf
                        (W38.wn01852 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00188 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02236 b)
                          leaf
                        )
                        (W24.wn01212 b)
                        leaf
                      )
                      (W09.wn00700 b)
                      (node
                        leaf
                        (W35.wn01724 b)
                        leaf
                      )
                    )
                    (W03.wn00444 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02492 b)
                          leaf
                        )
                        (W28.wn01468 b)
                        leaf
                      )
                      (W18.wn00956 b)
                      (node
                        leaf
                        (W42.wn01980 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00124 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02172 b)
                          leaf
                        )
                        (W22.wn01148 b)
                        leaf
                      )
                      (W06.wn00636 b)
                      (node
                        leaf
                        (W34.wn01660 b)
                        leaf
                      )
                    )
                    (W02.wn00380 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02428 b)
                          leaf
                        )
                        (W27.wn01404 b)
                        leaf
                      )
                      (W14.wn00892 b)
                      (node
                        leaf
                        (W40.wn01916 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00252 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02300 b)
                          leaf
                        )
                        (W25.wn01276 b)
                        leaf
                      )
                      (W10.wn00764 b)
                      (node
                        leaf
                        (W36.wn01788 b)
                        leaf
                      )
                    )
                    (W04.wn00508 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02556 b)
                          leaf
                        )
                        (W29.wn01532 b)
                        leaf
                      )
                      (W20.wn01020 b)
                      (node
                        leaf
                        (W43.wn02044 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
      (W01.wn00002 b)
      (node
        (node
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02050 b)
                          leaf
                        )
                        (W20.wn01026 b)
                        leaf
                      )
                      (W04.wn00514 b)
                      (node
                        (node
                          leaf
                          (W48.wn02562 b)
                          leaf
                        )
                        (W29.wn01538 b)
                        leaf
                      )
                    )
                    (W02.wn00258 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02306 b)
                          leaf
                        )
                        (W25.wn01282 b)
                        leaf
                      )
                      (W10.wn00770 b)
                      (node
                        leaf
                        (W36.wn01794 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00130 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02178 b)
                          leaf
                        )
                        (W22.wn01154 b)
                        leaf
                      )
                      (W07.wn00642 b)
                      (node
                        leaf
                        (W34.wn01666 b)
                        leaf
                      )
                    )
                    (W02.wn00386 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02434 b)
                          leaf
                        )
                        (W27.wn01410 b)
                        leaf
                      )
                      (W15.wn00898 b)
                      (node
                        leaf
                        (W40.wn01922 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00066 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02114 b)
                          leaf
                        )
                        (W21.wn01090 b)
                        leaf
                      )
                      (W05.wn00578 b)
                      (node
                        leaf
                        (W31.wn01602 b)
                        leaf
                      )
                    )
                    (W02.wn00322 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02370 b)
                          leaf
                        )
                        (W27.wn01346 b)
                        leaf
                      )
                      (W12.wn00834 b)
                      (node
                        leaf
                        (W38.wn01858 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00194 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02242 b)
                          leaf
                        )
                        (W24.wn01218 b)
                        leaf
                      )
                      (W09.wn00706 b)
                      (node
                        leaf
                        (W35.wn01730 b)
                        leaf
                      )
                    )
                    (W03.wn00450 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02498 b)
                          leaf
                        )
                        (W28.wn01474 b)
                        leaf
                      )
                      (W18.wn00962 b)
                      (node
                        leaf
                        (W42.wn01986 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00034 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02082 b)
                          leaf
                        )
                        (W20.wn01058 b)
                        leaf
                      )
                      (W04.wn00546 b)
                      (node
                        leaf
                        (W29.wn01570 b)
                        leaf
                      )
                    )
                    (W02.wn00290 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02338 b)
                          leaf
                        )
                        (W26.wn01314 b)
                        leaf
                      )
                      (W11.wn00802 b)
                      (node
                        leaf
                        (W37.wn01826 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00162 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02210 b)
                          leaf
                        )
                        (W23.wn01186 b)
                        leaf
                      )
                      (W08.wn00674 b)
                      (node
                        leaf
                        (W35.wn01698 b)
                        leaf
                      )
                    )
                    (W03.wn00418 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02466 b)
                          leaf
                        )
                        (W28.wn01442 b)
                        leaf
                      )
                      (W16.wn00930 b)
                      (node
                        leaf
                        (W41.wn01954 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00098 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02146 b)
                          leaf
                        )
                        (W21.wn01122 b)
                        leaf
                      )
                      (W06.wn00610 b)
                      (node
                        leaf
                        (W33.wn01634 b)
                        leaf
                      )
                    )
                    (W02.wn00354 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02402 b)
                          leaf
                        )
                        (W27.wn01378 b)
                        leaf
                      )
                      (W14.wn00866 b)
                      (node
                        leaf
                        (W38.wn01890 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00226 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02274 b)
                          leaf
                        )
                        (W25.wn01250 b)
                        leaf
                      )
                      (W09.wn00738 b)
                      (node
                        leaf
                        (W35.wn01762 b)
                        leaf
                      )
                    )
                    (W03.wn00482 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02530 b)
                          leaf
                        )
                        (W28.wn01506 b)
                        leaf
                      )
                      (W19.wn00994 b)
                      (node
                        leaf
                        (W42.wn02018 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00018 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02066 b)
                          leaf
                        )
                        (W20.wn01042 b)
                        leaf
                      )
                      (W04.wn00530 b)
                      (node
                        (node
                          leaf
                          (W49.wn02578 b)
                          leaf
                        )
                        (W29.wn01554 b)
                        leaf
                      )
                    )
                    (W02.wn00274 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02322 b)
                          leaf
                        )
                        (W26.wn01298 b)
                        leaf
                      )
                      (W11.wn00786 b)
                      (node
                        leaf
                        (W37.wn01810 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00146 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02194 b)
                          leaf
                        )
                        (W23.wn01170 b)
                        leaf
                      )
                      (W07.wn00658 b)
                      (node
                        leaf
                        (W34.wn01682 b)
                        leaf
                      )
                    )
                    (W02.wn00402 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02450 b)
                          leaf
                        )
                        (W28.wn01426 b)
                        leaf
                      )
                      (W15.wn00914 b)
                      (node
                        leaf
                        (W41.wn01938 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00082 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02130 b)
                          leaf
                        )
                        (W21.wn01106 b)
                        leaf
                      )
                      (W06.wn00594 b)
                      (node
                        leaf
                        (W32.wn01618 b)
                        leaf
                      )
                    )
                    (W02.wn00338 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02386 b)
                          leaf
                        )
                        (W27.wn01362 b)
                        leaf
                      )
                      (W13.wn00850 b)
                      (node
                        leaf
                        (W38.wn01874 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00210 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02258 b)
                          leaf
                        )
                        (W24.wn01234 b)
                        leaf
                      )
                      (W09.wn00722 b)
                      (node
                        leaf
                        (W35.wn01746 b)
                        leaf
                      )
                    )
                    (W03.wn00466 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02514 b)
                          leaf
                        )
                        (W28.wn01490 b)
                        leaf
                      )
                      (W19.wn00978 b)
                      (node
                        leaf
                        (W42.wn02002 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00050 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02098 b)
                          leaf
                        )
                        (W20.wn01074 b)
                        leaf
                      )
                      (W05.wn00562 b)
                      (node
                        leaf
                        (W30.wn01586 b)
                        leaf
                      )
                    )
                    (W02.wn00306 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02354 b)
                          leaf
                        )
                        (W26.wn01330 b)
                        leaf
                      )
                      (W12.wn00818 b)
                      (node
                        leaf
                        (W37.wn01842 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00178 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02226 b)
                          leaf
                        )
                        (W23.wn01202 b)
                        leaf
                      )
                      (W08.wn00690 b)
                      (node
                        leaf
                        (W35.wn01714 b)
                        leaf
                      )
                    )
                    (W03.wn00434 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02482 b)
                          leaf
                        )
                        (W28.wn01458 b)
                        leaf
                      )
                      (W17.wn00946 b)
                      (node
                        leaf
                        (W41.wn01970 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00114 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02162 b)
                          leaf
                        )
                        (W22.wn01138 b)
                        leaf
                      )
                      (W06.wn00626 b)
                      (node
                        leaf
                        (W34.wn01650 b)
                        leaf
                      )
                    )
                    (W02.wn00370 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02418 b)
                          leaf
                        )
                        (W27.wn01394 b)
                        leaf
                      )
                      (W14.wn00882 b)
                      (node
                        leaf
                        (W40.wn01906 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00242 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02290 b)
                          leaf
                        )
                        (W25.wn01266 b)
                        leaf
                      )
                      (W10.wn00754 b)
                      (node
                        leaf
                        (W36.wn01778 b)
                        leaf
                      )
                    )
                    (W03.wn00498 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02546 b)
                          leaf
                        )
                        (W29.wn01522 b)
                        leaf
                      )
                      (W20.wn01010 b)
                      (node
                        leaf
                        (W43.wn02034 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
          (W01.wn00010 b)
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02058 b)
                          leaf
                        )
                        (W20.wn01034 b)
                        leaf
                      )
                      (W04.wn00522 b)
                      (node
                        (node
                          leaf
                          (W48.wn02570 b)
                          leaf
                        )
                        (W29.wn01546 b)
                        leaf
                      )
                    )
                    (W02.wn00266 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02314 b)
                          leaf
                        )
                        (W25.wn01290 b)
                        leaf
                      )
                      (W10.wn00778 b)
                      (node
                        leaf
                        (W37.wn01802 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00138 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02186 b)
                          leaf
                        )
                        (W22.wn01162 b)
                        leaf
                      )
                      (W07.wn00650 b)
                      (node
                        leaf
                        (W34.wn01674 b)
                        leaf
                      )
                    )
                    (W02.wn00394 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02442 b)
                          leaf
                        )
                        (W27.wn01418 b)
                        leaf
                      )
                      (W15.wn00906 b)
                      (node
                        leaf
                        (W41.wn01930 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00074 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02122 b)
                          leaf
                        )
                        (W21.wn01098 b)
                        leaf
                      )
                      (W05.wn00586 b)
                      (node
                        leaf
                        (W31.wn01610 b)
                        leaf
                      )
                    )
                    (W02.wn00330 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02378 b)
                          leaf
                        )
                        (W27.wn01354 b)
                        leaf
                      )
                      (W13.wn00842 b)
                      (node
                        leaf
                        (W38.wn01866 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00202 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02250 b)
                          leaf
                        )
                        (W24.wn01226 b)
                        leaf
                      )
                      (W09.wn00714 b)
                      (node
                        leaf
                        (W35.wn01738 b)
                        leaf
                      )
                    )
                    (W03.wn00458 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02506 b)
                          leaf
                        )
                        (W28.wn01482 b)
                        leaf
                      )
                      (W19.wn00970 b)
                      (node
                        leaf
                        (W42.wn01994 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00042 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02090 b)
                          leaf
                        )
                        (W20.wn01066 b)
                        leaf
                      )
                      (W04.wn00554 b)
                      (node
                        leaf
                        (W29.wn01578 b)
                        leaf
                      )
                    )
                    (W02.wn00298 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02346 b)
                          leaf
                        )
                        (W26.wn01322 b)
                        leaf
                      )
                      (W11.wn00810 b)
                      (node
                        leaf
                        (W37.wn01834 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00170 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02218 b)
                          leaf
                        )
                        (W23.wn01194 b)
                        leaf
                      )
                      (W08.wn00682 b)
                      (node
                        leaf
                        (W35.wn01706 b)
                        leaf
                      )
                    )
                    (W03.wn00426 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02474 b)
                          leaf
                        )
                        (W28.wn01450 b)
                        leaf
                      )
                      (W16.wn00938 b)
                      (node
                        leaf
                        (W41.wn01962 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00106 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02154 b)
                          leaf
                        )
                        (W22.wn01130 b)
                        leaf
                      )
                      (W06.wn00618 b)
                      (node
                        leaf
                        (W33.wn01642 b)
                        leaf
                      )
                    )
                    (W02.wn00362 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02410 b)
                          leaf
                        )
                        (W27.wn01386 b)
                        leaf
                      )
                      (W14.wn00874 b)
                      (node
                        leaf
                        (W39.wn01898 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00234 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02282 b)
                          leaf
                        )
                        (W25.wn01258 b)
                        leaf
                      )
                      (W10.wn00746 b)
                      (node
                        leaf
                        (W35.wn01770 b)
                        leaf
                      )
                    )
                    (W03.wn00490 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02538 b)
                          leaf
                        )
                        (W29.wn01514 b)
                        leaf
                      )
                      (W20.wn01002 b)
                      (node
                        leaf
                        (W43.wn02026 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00026 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02074 b)
                          leaf
                        )
                        (W20.wn01050 b)
                        leaf
                      )
                      (W04.wn00538 b)
                      (node
                        leaf
                        (W29.wn01562 b)
                        leaf
                      )
                    )
                    (W02.wn00282 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02330 b)
                          leaf
                        )
                        (W26.wn01306 b)
                        leaf
                      )
                      (W11.wn00794 b)
                      (node
                        leaf
                        (W37.wn01818 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00154 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02202 b)
                          leaf
                        )
                        (W23.wn01178 b)
                        leaf
                      )
                      (W08.wn00666 b)
                      (node
                        leaf
                        (W35.wn01690 b)
                        leaf
                      )
                    )
                    (W03.wn00410 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02458 b)
                          leaf
                        )
                        (W28.wn01434 b)
                        leaf
                      )
                      (W15.wn00922 b)
                      (node
                        leaf
                        (W41.wn01946 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00090 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02138 b)
                          leaf
                        )
                        (W21.wn01114 b)
                        leaf
                      )
                      (W06.wn00602 b)
                      (node
                        leaf
                        (W32.wn01626 b)
                        leaf
                      )
                    )
                    (W02.wn00346 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02394 b)
                          leaf
                        )
                        (W27.wn01370 b)
                        leaf
                      )
                      (W13.wn00858 b)
                      (node
                        leaf
                        (W38.wn01882 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00218 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02266 b)
                          leaf
                        )
                        (W25.wn01242 b)
                        leaf
                      )
                      (W09.wn00730 b)
                      (node
                        leaf
                        (W35.wn01754 b)
                        leaf
                      )
                    )
                    (W03.wn00474 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02522 b)
                          leaf
                        )
                        (W28.wn01498 b)
                        leaf
                      )
                      (W19.wn00986 b)
                      (node
                        leaf
                        (W42.wn02010 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00058 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02106 b)
                          leaf
                        )
                        (W20.wn01082 b)
                        leaf
                      )
                      (W05.wn00570 b)
                      (node
                        leaf
                        (W30.wn01594 b)
                        leaf
                      )
                    )
                    (W02.wn00314 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02362 b)
                          leaf
                        )
                        (W27.wn01338 b)
                        leaf
                      )
                      (W12.wn00826 b)
                      (node
                        leaf
                        (W38.wn01850 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00186 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02234 b)
                          leaf
                        )
                        (W24.wn01210 b)
                        leaf
                      )
                      (W09.wn00698 b)
                      (node
                        leaf
                        (W35.wn01722 b)
                        leaf
                      )
                    )
                    (W03.wn00442 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02490 b)
                          leaf
                        )
                        (W28.wn01466 b)
                        leaf
                      )
                      (W17.wn00954 b)
                      (node
                        leaf
                        (W42.wn01978 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00122 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02170 b)
                          leaf
                        )
                        (W22.wn01146 b)
                        leaf
                      )
                      (W06.wn00634 b)
                      (node
                        leaf
                        (W34.wn01658 b)
                        leaf
                      )
                    )
                    (W02.wn00378 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02426 b)
                          leaf
                        )
                        (W27.wn01402 b)
                        leaf
                      )
                      (W14.wn00890 b)
                      (node
                        leaf
                        (W40.wn01914 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00250 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02298 b)
                          leaf
                        )
                        (W25.wn01274 b)
                        leaf
                      )
                      (W10.wn00762 b)
                      (node
                        leaf
                        (W36.wn01786 b)
                        leaf
                      )
                    )
                    (W03.wn00506 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02554 b)
                          leaf
                        )
                        (W29.wn01530 b)
                        leaf
                      )
                      (W20.wn01018 b)
                      (node
                        leaf
                        (W43.wn02042 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
        )
        (W01.wn00006 b)
        (node
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02054 b)
                          leaf
                        )
                        (W20.wn01030 b)
                        leaf
                      )
                      (W04.wn00518 b)
                      (node
                        (node
                          leaf
                          (W48.wn02566 b)
                          leaf
                        )
                        (W29.wn01542 b)
                        leaf
                      )
                    )
                    (W02.wn00262 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02310 b)
                          leaf
                        )
                        (W25.wn01286 b)
                        leaf
                      )
                      (W10.wn00774 b)
                      (node
                        leaf
                        (W37.wn01798 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00134 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02182 b)
                          leaf
                        )
                        (W22.wn01158 b)
                        leaf
                      )
                      (W07.wn00646 b)
                      (node
                        leaf
                        (W34.wn01670 b)
                        leaf
                      )
                    )
                    (W02.wn00390 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02438 b)
                          leaf
                        )
                        (W27.wn01414 b)
                        leaf
                      )
                      (W15.wn00902 b)
                      (node
                        leaf
                        (W40.wn01926 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00070 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02118 b)
                          leaf
                        )
                        (W21.wn01094 b)
                        leaf
                      )
                      (W05.wn00582 b)
                      (node
                        leaf
                        (W31.wn01606 b)
                        leaf
                      )
                    )
                    (W02.wn00326 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02374 b)
                          leaf
                        )
                        (W27.wn01350 b)
                        leaf
                      )
                      (W13.wn00838 b)
                      (node
                        leaf
                        (W38.wn01862 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00198 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02246 b)
                          leaf
                        )
                        (W24.wn01222 b)
                        leaf
                      )
                      (W09.wn00710 b)
                      (node
                        leaf
                        (W35.wn01734 b)
                        leaf
                      )
                    )
                    (W03.wn00454 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02502 b)
                          leaf
                        )
                        (W28.wn01478 b)
                        leaf
                      )
                      (W18.wn00966 b)
                      (node
                        leaf
                        (W42.wn01990 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00038 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02086 b)
                          leaf
                        )
                        (W20.wn01062 b)
                        leaf
                      )
                      (W04.wn00550 b)
                      (node
                        leaf
                        (W29.wn01574 b)
                        leaf
                      )
                    )
                    (W02.wn00294 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02342 b)
                          leaf
                        )
                        (W26.wn01318 b)
                        leaf
                      )
                      (W11.wn00806 b)
                      (node
                        leaf
                        (W37.wn01830 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00166 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02214 b)
                          leaf
                        )
                        (W23.wn01190 b)
                        leaf
                      )
                      (W08.wn00678 b)
                      (node
                        leaf
                        (W35.wn01702 b)
                        leaf
                      )
                    )
                    (W03.wn00422 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02470 b)
                          leaf
                        )
                        (W28.wn01446 b)
                        leaf
                      )
                      (W16.wn00934 b)
                      (node
                        leaf
                        (W41.wn01958 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00102 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02150 b)
                          leaf
                        )
                        (W22.wn01126 b)
                        leaf
                      )
                      (W06.wn00614 b)
                      (node
                        leaf
                        (W33.wn01638 b)
                        leaf
                      )
                    )
                    (W02.wn00358 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02406 b)
                          leaf
                        )
                        (W27.wn01382 b)
                        leaf
                      )
                      (W14.wn00870 b)
                      (node
                        leaf
                        (W39.wn01894 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00230 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02278 b)
                          leaf
                        )
                        (W25.wn01254 b)
                        leaf
                      )
                      (W10.wn00742 b)
                      (node
                        leaf
                        (W35.wn01766 b)
                        leaf
                      )
                    )
                    (W03.wn00486 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02534 b)
                          leaf
                        )
                        (W28.wn01510 b)
                        leaf
                      )
                      (W20.wn00998 b)
                      (node
                        leaf
                        (W42.wn02022 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00022 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02070 b)
                          leaf
                        )
                        (W20.wn01046 b)
                        leaf
                      )
                      (W04.wn00534 b)
                      (node
                        (node
                          leaf
                          (W49.wn02582 b)
                          leaf
                        )
                        (W29.wn01558 b)
                        leaf
                      )
                    )
                    (W02.wn00278 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02326 b)
                          leaf
                        )
                        (W26.wn01302 b)
                        leaf
                      )
                      (W11.wn00790 b)
                      (node
                        leaf
                        (W37.wn01814 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00150 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02198 b)
                          leaf
                        )
                        (W23.wn01174 b)
                        leaf
                      )
                      (W07.wn00662 b)
                      (node
                        leaf
                        (W34.wn01686 b)
                        leaf
                      )
                    )
                    (W02.wn00406 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02454 b)
                          leaf
                        )
                        (W28.wn01430 b)
                        leaf
                      )
                      (W15.wn00918 b)
                      (node
                        leaf
                        (W41.wn01942 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00086 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02134 b)
                          leaf
                        )
                        (W21.wn01110 b)
                        leaf
                      )
                      (W06.wn00598 b)
                      (node
                        leaf
                        (W32.wn01622 b)
                        leaf
                      )
                    )
                    (W02.wn00342 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02390 b)
                          leaf
                        )
                        (W27.wn01366 b)
                        leaf
                      )
                      (W13.wn00854 b)
                      (node
                        leaf
                        (W38.wn01878 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00214 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02262 b)
                          leaf
                        )
                        (W24.wn01238 b)
                        leaf
                      )
                      (W09.wn00726 b)
                      (node
                        leaf
                        (W35.wn01750 b)
                        leaf
                      )
                    )
                    (W03.wn00470 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02518 b)
                          leaf
                        )
                        (W28.wn01494 b)
                        leaf
                      )
                      (W19.wn00982 b)
                      (node
                        leaf
                        (W42.wn02006 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00054 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02102 b)
                          leaf
                        )
                        (W20.wn01078 b)
                        leaf
                      )
                      (W05.wn00566 b)
                      (node
                        leaf
                        (W30.wn01590 b)
                        leaf
                      )
                    )
                    (W02.wn00310 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02358 b)
                          leaf
                        )
                        (W27.wn01334 b)
                        leaf
                      )
                      (W12.wn00822 b)
                      (node
                        leaf
                        (W38.wn01846 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00182 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02230 b)
                          leaf
                        )
                        (W24.wn01206 b)
                        leaf
                      )
                      (W08.wn00694 b)
                      (node
                        leaf
                        (W35.wn01718 b)
                        leaf
                      )
                    )
                    (W03.wn00438 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02486 b)
                          leaf
                        )
                        (W28.wn01462 b)
                        leaf
                      )
                      (W17.wn00950 b)
                      (node
                        leaf
                        (W41.wn01974 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00118 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02166 b)
                          leaf
                        )
                        (W22.wn01142 b)
                        leaf
                      )
                      (W06.wn00630 b)
                      (node
                        leaf
                        (W34.wn01654 b)
                        leaf
                      )
                    )
                    (W02.wn00374 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02422 b)
                          leaf
                        )
                        (W27.wn01398 b)
                        leaf
                      )
                      (W14.wn00886 b)
                      (node
                        leaf
                        (W40.wn01910 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00246 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02294 b)
                          leaf
                        )
                        (W25.wn01270 b)
                        leaf
                      )
                      (W10.wn00758 b)
                      (node
                        leaf
                        (W36.wn01782 b)
                        leaf
                      )
                    )
                    (W03.wn00502 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02550 b)
                          leaf
                        )
                        (W29.wn01526 b)
                        leaf
                      )
                      (W20.wn01014 b)
                      (node
                        leaf
                        (W43.wn02038 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
          (W01.wn00014 b)
          (node
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02062 b)
                          leaf
                        )
                        (W20.wn01038 b)
                        leaf
                      )
                      (W04.wn00526 b)
                      (node
                        (node
                          leaf
                          (W49.wn02574 b)
                          leaf
                        )
                        (W29.wn01550 b)
                        leaf
                      )
                    )
                    (W02.wn00270 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02318 b)
                          leaf
                        )
                        (W25.wn01294 b)
                        leaf
                      )
                      (W10.wn00782 b)
                      (node
                        leaf
                        (W37.wn01806 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00142 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02190 b)
                          leaf
                        )
                        (W22.wn01166 b)
                        leaf
                      )
                      (W07.wn00654 b)
                      (node
                        leaf
                        (W34.wn01678 b)
                        leaf
                      )
                    )
                    (W02.wn00398 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02446 b)
                          leaf
                        )
                        (W28.wn01422 b)
                        leaf
                      )
                      (W15.wn00910 b)
                      (node
                        leaf
                        (W41.wn01934 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00078 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02126 b)
                          leaf
                        )
                        (W21.wn01102 b)
                        leaf
                      )
                      (W06.wn00590 b)
                      (node
                        leaf
                        (W32.wn01614 b)
                        leaf
                      )
                    )
                    (W02.wn00334 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02382 b)
                          leaf
                        )
                        (W27.wn01358 b)
                        leaf
                      )
                      (W13.wn00846 b)
                      (node
                        leaf
                        (W38.wn01870 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00206 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02254 b)
                          leaf
                        )
                        (W24.wn01230 b)
                        leaf
                      )
                      (W09.wn00718 b)
                      (node
                        leaf
                        (W35.wn01742 b)
                        leaf
                      )
                    )
                    (W03.wn00462 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02510 b)
                          leaf
                        )
                        (W28.wn01486 b)
                        leaf
                      )
                      (W19.wn00974 b)
                      (node
                        leaf
                        (W42.wn01998 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00046 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02094 b)
                          leaf
                        )
                        (W20.wn01070 b)
                        leaf
                      )
                      (W04.wn00558 b)
                      (node
                        leaf
                        (W30.wn01582 b)
                        leaf
                      )
                    )
                    (W02.wn00302 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02350 b)
                          leaf
                        )
                        (W26.wn01326 b)
                        leaf
                      )
                      (W11.wn00814 b)
                      (node
                        leaf
                        (W37.wn01838 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00174 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02222 b)
                          leaf
                        )
                        (W23.wn01198 b)
                        leaf
                      )
                      (W08.wn00686 b)
                      (node
                        leaf
                        (W35.wn01710 b)
                        leaf
                      )
                    )
                    (W03.wn00430 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02478 b)
                          leaf
                        )
                        (W28.wn01454 b)
                        leaf
                      )
                      (W17.wn00942 b)
                      (node
                        leaf
                        (W41.wn01966 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00110 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02158 b)
                          leaf
                        )
                        (W22.wn01134 b)
                        leaf
                      )
                      (W06.wn00622 b)
                      (node
                        leaf
                        (W33.wn01646 b)
                        leaf
                      )
                    )
                    (W02.wn00366 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02414 b)
                          leaf
                        )
                        (W27.wn01390 b)
                        leaf
                      )
                      (W14.wn00878 b)
                      (node
                        leaf
                        (W39.wn01902 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00238 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02286 b)
                          leaf
                        )
                        (W25.wn01262 b)
                        leaf
                      )
                      (W10.wn00750 b)
                      (node
                        leaf
                        (W36.wn01774 b)
                        leaf
                      )
                    )
                    (W03.wn00494 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02542 b)
                          leaf
                        )
                        (W29.wn01518 b)
                        leaf
                      )
                      (W20.wn01006 b)
                      (node
                        leaf
                        (W43.wn02030 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
            (W01.wn00030 b)
            (node
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W43.wn02078 b)
                          leaf
                        )
                        (W20.wn01054 b)
                        leaf
                      )
                      (W04.wn00542 b)
                      (node
                        leaf
                        (W29.wn01566 b)
                        leaf
                      )
                    )
                    (W02.wn00286 b)
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02334 b)
                          leaf
                        )
                        (W26.wn01310 b)
                        leaf
                      )
                      (W11.wn00798 b)
                      (node
                        leaf
                        (W37.wn01822 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00158 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02206 b)
                          leaf
                        )
                        (W23.wn01182 b)
                        leaf
                      )
                      (W08.wn00670 b)
                      (node
                        leaf
                        (W35.wn01694 b)
                        leaf
                      )
                    )
                    (W03.wn00414 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02462 b)
                          leaf
                        )
                        (W28.wn01438 b)
                        leaf
                      )
                      (W15.wn00926 b)
                      (node
                        leaf
                        (W41.wn01950 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00094 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02142 b)
                          leaf
                        )
                        (W21.wn01118 b)
                        leaf
                      )
                      (W06.wn00606 b)
                      (node
                        leaf
                        (W32.wn01630 b)
                        leaf
                      )
                    )
                    (W02.wn00350 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02398 b)
                          leaf
                        )
                        (W27.wn01374 b)
                        leaf
                      )
                      (W13.wn00862 b)
                      (node
                        leaf
                        (W38.wn01886 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00222 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02270 b)
                          leaf
                        )
                        (W25.wn01246 b)
                        leaf
                      )
                      (W09.wn00734 b)
                      (node
                        leaf
                        (W35.wn01758 b)
                        leaf
                      )
                    )
                    (W03.wn00478 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02526 b)
                          leaf
                        )
                        (W28.wn01502 b)
                        leaf
                      )
                      (W19.wn00990 b)
                      (node
                        leaf
                        (W42.wn02014 b)
                        leaf
                      )
                    )
                  )
                )
              )
              (W01.wn00062 b)
              (node
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W44.wn02110 b)
                          leaf
                        )
                        (W21.wn01086 b)
                        leaf
                      )
                      (W05.wn00574 b)
                      (node
                        leaf
                        (W31.wn01598 b)
                        leaf
                      )
                    )
                    (W02.wn00318 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02366 b)
                          leaf
                        )
                        (W27.wn01342 b)
                        leaf
                      )
                      (W12.wn00830 b)
                      (node
                        leaf
                        (W38.wn01854 b)
                        leaf
                      )
                    )
                  )
                  (W01.wn00190 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02238 b)
                          leaf
                        )
                        (W24.wn01214 b)
                        leaf
                      )
                      (W09.wn00702 b)
                      (node
                        leaf
                        (W35.wn01726 b)
                        leaf
                      )
                    )
                    (W03.wn00446 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02494 b)
                          leaf
                        )
                        (W28.wn01470 b)
                        leaf
                      )
                      (W18.wn00958 b)
                      (node
                        leaf
                        (W42.wn01982 b)
                        leaf
                      )
                    )
                  )
                )
                (W01.wn00126 b)
                (node
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W45.wn02174 b)
                          leaf
                        )
                        (W22.wn01150 b)
                        leaf
                      )
                      (W07.wn00638 b)
                      (node
                        leaf
                        (W34.wn01662 b)
                        leaf
                      )
                    )
                    (W02.wn00382 b)
                    (node
                      (node
                        (node
                          leaf
                          (W47.wn02430 b)
                          leaf
                        )
                        (W27.wn01406 b)
                        leaf
                      )
                      (W14.wn00894 b)
                      (node
                        leaf
                        (W40.wn01918 b)
                        leaf
                      )
                    )
                  )
                  (W02.wn00254 b)
                  (node
                    (node
                      (node
                        (node
                          leaf
                          (W46.wn02302 b)
                          leaf
                        )
                        (W25.wn01278 b)
                        leaf
                      )
                      (W10.wn00766 b)
                      (node
                        leaf
                        (W36.wn01790 b)
                        leaf
                      )
                    )
                    (W04.wn00510 b)
                    (node
                      (node
                        (node
                          leaf
                          (W48.wn02558 b)
                          leaf
                        )
                        (W29.wn01534 b)
                        leaf
                      )
                      (W20.wn01022 b)
                      (node
                        leaf
                        (W43.wn02046 b)
                        leaf
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  where
  b : Base 3
  b = record { facts = facts ; complete = complete₃ }
