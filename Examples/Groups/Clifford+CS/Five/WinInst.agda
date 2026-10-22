------------------------------------------------------------------------
-- Presentations of groups
--
-- The windows of the five-wire derivations, as a record
--
-- Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Examples.Groups.Clifford+CS.Five.WinInst where

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain using (refl)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; WsL ; pleaf ; pnode)
open import Examples.Groups.Clifford+CS.Five.WinInstL using (wsL)
import Examples.Groups.Clifford+CS.Five.Wins.WP01 as WP01
import Examples.Groups.Clifford+CS.Five.Wins.WP02 as WP02
import Examples.Groups.Clifford+CS.Five.Wins.WP03 as WP03
import Examples.Groups.Clifford+CS.Five.Wins.WP04 as WP04
import Examples.Groups.Clifford+CS.Five.Wins.WP05 as WP05
import Examples.Groups.Clifford+CS.Five.Wins.WP06 as WP06
import Examples.Groups.Clifford+CS.Five.Wins.WP07 as WP07
import Examples.Groups.Clifford+CS.Five.Wins.WP08 as WP08

ws : Complete 4 → Ws
ws c4 = record
  { lit = L
  ; pl  =
      (pnode
        (pnode
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1023 c4 L)
                            pleaf
                          )
                          (WP03.wp0511 c4 L)
                          pleaf
                        )
                        (WP01.wp0255 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1279 c4 L)
                            pleaf
                          )
                          (WP04.wp0767 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0127 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1151 c4 L)
                            pleaf
                          )
                          (WP03.wp0639 c4 L)
                          pleaf
                        )
                        (WP02.wp0383 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1407 c4 L)
                            pleaf
                          )
                          (WP04.wp0895 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0063 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1087 c4 L)
                            pleaf
                          )
                          (WP03.wp0575 c4 L)
                          pleaf
                        )
                        (WP02.wp0319 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1343 c4 L)
                            pleaf
                          )
                          (WP04.wp0831 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0191 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1215 c4 L)
                            pleaf
                          )
                          (WP04.wp0703 c4 L)
                          pleaf
                        )
                        (WP02.wp0447 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1471 c4 L)
                            pleaf
                          )
                          (WP05.wp0959 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0031 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1055 c4 L)
                            pleaf
                          )
                          (WP03.wp0543 c4 L)
                          pleaf
                        )
                        (WP02.wp0287 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1311 c4 L)
                            pleaf
                          )
                          (WP04.wp0799 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0159 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1183 c4 L)
                            pleaf
                          )
                          (WP03.wp0671 c4 L)
                          pleaf
                        )
                        (WP02.wp0415 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1439 c4 L)
                            pleaf
                          )
                          (WP05.wp0927 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0095 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1119 c4 L)
                            pleaf
                          )
                          (WP03.wp0607 c4 L)
                          pleaf
                        )
                        (WP02.wp0351 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1375 c4 L)
                            pleaf
                          )
                          (WP04.wp0863 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0223 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1247 c4 L)
                            pleaf
                          )
                          (WP04.wp0735 c4 L)
                          pleaf
                        )
                        (WP03.wp0479 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1503 c4 L)
                            pleaf
                          )
                          (WP05.wp0991 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0015 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1039 c4 L)
                            pleaf
                          )
                          (WP03.wp0527 c4 L)
                          pleaf
                        )
                        (WP02.wp0271 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1295 c4 L)
                            pleaf
                          )
                          (WP04.wp0783 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0143 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1167 c4 L)
                            pleaf
                          )
                          (WP03.wp0655 c4 L)
                          pleaf
                        )
                        (WP02.wp0399 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1423 c4 L)
                            pleaf
                          )
                          (WP04.wp0911 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0079 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1103 c4 L)
                            pleaf
                          )
                          (WP03.wp0591 c4 L)
                          pleaf
                        )
                        (WP02.wp0335 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1359 c4 L)
                            pleaf
                          )
                          (WP04.wp0847 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0207 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1231 c4 L)
                            pleaf
                          )
                          (WP04.wp0719 c4 L)
                          pleaf
                        )
                        (WP02.wp0463 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1487 c4 L)
                            pleaf
                          )
                          (WP05.wp0975 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0047 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1071 c4 L)
                            pleaf
                          )
                          (WP03.wp0559 c4 L)
                          pleaf
                        )
                        (WP02.wp0303 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1327 c4 L)
                            pleaf
                          )
                          (WP04.wp0815 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0175 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1199 c4 L)
                            pleaf
                          )
                          (WP04.wp0687 c4 L)
                          pleaf
                        )
                        (WP02.wp0431 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1455 c4 L)
                            pleaf
                          )
                          (WP05.wp0943 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0111 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1135 c4 L)
                            pleaf
                          )
                          (WP03.wp0623 c4 L)
                          pleaf
                        )
                        (WP02.wp0367 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1391 c4 L)
                            pleaf
                          )
                          (WP04.wp0879 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0239 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1263 c4 L)
                            pleaf
                          )
                          (WP04.wp0751 c4 L)
                          pleaf
                        )
                        (WP03.wp0495 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1519 c4 L)
                            pleaf
                          )
                          (WP05.wp1007 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
              (WP01.wp0007 c4 L)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1031 c4 L)
                            pleaf
                          )
                          (WP03.wp0519 c4 L)
                          pleaf
                        )
                        (WP02.wp0263 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1287 c4 L)
                            pleaf
                          )
                          (WP04.wp0775 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0135 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1159 c4 L)
                            pleaf
                          )
                          (WP03.wp0647 c4 L)
                          pleaf
                        )
                        (WP02.wp0391 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1415 c4 L)
                            pleaf
                          )
                          (WP04.wp0903 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0071 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1095 c4 L)
                            pleaf
                          )
                          (WP03.wp0583 c4 L)
                          pleaf
                        )
                        (WP02.wp0327 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1351 c4 L)
                            pleaf
                          )
                          (WP04.wp0839 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0199 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1223 c4 L)
                            pleaf
                          )
                          (WP04.wp0711 c4 L)
                          pleaf
                        )
                        (WP02.wp0455 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1479 c4 L)
                            pleaf
                          )
                          (WP05.wp0967 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0039 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1063 c4 L)
                            pleaf
                          )
                          (WP03.wp0551 c4 L)
                          pleaf
                        )
                        (WP02.wp0295 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1319 c4 L)
                            pleaf
                          )
                          (WP04.wp0807 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0167 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1191 c4 L)
                            pleaf
                          )
                          (WP04.wp0679 c4 L)
                          pleaf
                        )
                        (WP02.wp0423 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1447 c4 L)
                            pleaf
                          )
                          (WP05.wp0935 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0103 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1127 c4 L)
                            pleaf
                          )
                          (WP03.wp0615 c4 L)
                          pleaf
                        )
                        (WP02.wp0359 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1383 c4 L)
                            pleaf
                          )
                          (WP04.wp0871 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0231 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1255 c4 L)
                            pleaf
                          )
                          (WP04.wp0743 c4 L)
                          pleaf
                        )
                        (WP03.wp0487 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1511 c4 L)
                            pleaf
                          )
                          (WP05.wp0999 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0023 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1047 c4 L)
                            pleaf
                          )
                          (WP03.wp0535 c4 L)
                          pleaf
                        )
                        (WP02.wp0279 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1303 c4 L)
                            pleaf
                          )
                          (WP04.wp0791 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0151 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1175 c4 L)
                            pleaf
                          )
                          (WP03.wp0663 c4 L)
                          pleaf
                        )
                        (WP02.wp0407 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1431 c4 L)
                            pleaf
                          )
                          (WP05.wp0919 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0087 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1111 c4 L)
                            pleaf
                          )
                          (WP03.wp0599 c4 L)
                          pleaf
                        )
                        (WP02.wp0343 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1367 c4 L)
                            pleaf
                          )
                          (WP04.wp0855 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0215 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1239 c4 L)
                            pleaf
                          )
                          (WP04.wp0727 c4 L)
                          pleaf
                        )
                        (WP02.wp0471 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1495 c4 L)
                            pleaf
                          )
                          (WP05.wp0983 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0055 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1079 c4 L)
                            pleaf
                          )
                          (WP03.wp0567 c4 L)
                          pleaf
                        )
                        (WP02.wp0311 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1335 c4 L)
                            pleaf
                          )
                          (WP04.wp0823 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0183 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1207 c4 L)
                            pleaf
                          )
                          (WP04.wp0695 c4 L)
                          pleaf
                        )
                        (WP02.wp0439 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1463 c4 L)
                            pleaf
                          )
                          (WP05.wp0951 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0119 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1143 c4 L)
                            pleaf
                          )
                          (WP03.wp0631 c4 L)
                          pleaf
                        )
                        (WP02.wp0375 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1399 c4 L)
                            pleaf
                          )
                          (WP04.wp0887 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0247 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1271 c4 L)
                            pleaf
                          )
                          (WP04.wp0759 c4 L)
                          pleaf
                        )
                        (WP03.wp0503 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1015 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
            )
            (WP01.wp0003 c4 L)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1027 c4 L)
                            pleaf
                          )
                          (WP03.wp0515 c4 L)
                          pleaf
                        )
                        (WP01.wp0259 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1283 c4 L)
                            pleaf
                          )
                          (WP04.wp0771 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0131 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1155 c4 L)
                            pleaf
                          )
                          (WP03.wp0643 c4 L)
                          pleaf
                        )
                        (WP02.wp0387 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1411 c4 L)
                            pleaf
                          )
                          (WP04.wp0899 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0067 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1091 c4 L)
                            pleaf
                          )
                          (WP03.wp0579 c4 L)
                          pleaf
                        )
                        (WP02.wp0323 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1347 c4 L)
                            pleaf
                          )
                          (WP04.wp0835 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0195 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1219 c4 L)
                            pleaf
                          )
                          (WP04.wp0707 c4 L)
                          pleaf
                        )
                        (WP02.wp0451 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1475 c4 L)
                            pleaf
                          )
                          (WP05.wp0963 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0035 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1059 c4 L)
                            pleaf
                          )
                          (WP03.wp0547 c4 L)
                          pleaf
                        )
                        (WP02.wp0291 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1315 c4 L)
                            pleaf
                          )
                          (WP04.wp0803 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0163 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1187 c4 L)
                            pleaf
                          )
                          (WP04.wp0675 c4 L)
                          pleaf
                        )
                        (WP02.wp0419 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1443 c4 L)
                            pleaf
                          )
                          (WP05.wp0931 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0099 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1123 c4 L)
                            pleaf
                          )
                          (WP03.wp0611 c4 L)
                          pleaf
                        )
                        (WP02.wp0355 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1379 c4 L)
                            pleaf
                          )
                          (WP04.wp0867 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0227 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1251 c4 L)
                            pleaf
                          )
                          (WP04.wp0739 c4 L)
                          pleaf
                        )
                        (WP03.wp0483 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1507 c4 L)
                            pleaf
                          )
                          (WP05.wp0995 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0019 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1043 c4 L)
                            pleaf
                          )
                          (WP03.wp0531 c4 L)
                          pleaf
                        )
                        (WP02.wp0275 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1299 c4 L)
                            pleaf
                          )
                          (WP04.wp0787 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0147 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1171 c4 L)
                            pleaf
                          )
                          (WP03.wp0659 c4 L)
                          pleaf
                        )
                        (WP02.wp0403 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1427 c4 L)
                            pleaf
                          )
                          (WP04.wp0915 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0083 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1107 c4 L)
                            pleaf
                          )
                          (WP03.wp0595 c4 L)
                          pleaf
                        )
                        (WP02.wp0339 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1363 c4 L)
                            pleaf
                          )
                          (WP04.wp0851 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0211 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1235 c4 L)
                            pleaf
                          )
                          (WP04.wp0723 c4 L)
                          pleaf
                        )
                        (WP02.wp0467 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1491 c4 L)
                            pleaf
                          )
                          (WP05.wp0979 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0051 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1075 c4 L)
                            pleaf
                          )
                          (WP03.wp0563 c4 L)
                          pleaf
                        )
                        (WP02.wp0307 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1331 c4 L)
                            pleaf
                          )
                          (WP04.wp0819 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0179 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1203 c4 L)
                            pleaf
                          )
                          (WP04.wp0691 c4 L)
                          pleaf
                        )
                        (WP02.wp0435 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1459 c4 L)
                            pleaf
                          )
                          (WP05.wp0947 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0115 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1139 c4 L)
                            pleaf
                          )
                          (WP03.wp0627 c4 L)
                          pleaf
                        )
                        (WP02.wp0371 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1395 c4 L)
                            pleaf
                          )
                          (WP04.wp0883 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0243 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1267 c4 L)
                            pleaf
                          )
                          (WP04.wp0755 c4 L)
                          pleaf
                        )
                        (WP03.wp0499 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1011 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
              (WP01.wp0011 c4 L)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1035 c4 L)
                            pleaf
                          )
                          (WP03.wp0523 c4 L)
                          pleaf
                        )
                        (WP02.wp0267 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1291 c4 L)
                            pleaf
                          )
                          (WP04.wp0779 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0139 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1163 c4 L)
                            pleaf
                          )
                          (WP03.wp0651 c4 L)
                          pleaf
                        )
                        (WP02.wp0395 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1419 c4 L)
                            pleaf
                          )
                          (WP04.wp0907 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0075 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1099 c4 L)
                            pleaf
                          )
                          (WP03.wp0587 c4 L)
                          pleaf
                        )
                        (WP02.wp0331 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1355 c4 L)
                            pleaf
                          )
                          (WP04.wp0843 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0203 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1227 c4 L)
                            pleaf
                          )
                          (WP04.wp0715 c4 L)
                          pleaf
                        )
                        (WP02.wp0459 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1483 c4 L)
                            pleaf
                          )
                          (WP05.wp0971 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0043 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1067 c4 L)
                            pleaf
                          )
                          (WP03.wp0555 c4 L)
                          pleaf
                        )
                        (WP02.wp0299 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1323 c4 L)
                            pleaf
                          )
                          (WP04.wp0811 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0171 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1195 c4 L)
                            pleaf
                          )
                          (WP04.wp0683 c4 L)
                          pleaf
                        )
                        (WP02.wp0427 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1451 c4 L)
                            pleaf
                          )
                          (WP05.wp0939 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0107 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1131 c4 L)
                            pleaf
                          )
                          (WP03.wp0619 c4 L)
                          pleaf
                        )
                        (WP02.wp0363 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1387 c4 L)
                            pleaf
                          )
                          (WP04.wp0875 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0235 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1259 c4 L)
                            pleaf
                          )
                          (WP04.wp0747 c4 L)
                          pleaf
                        )
                        (WP03.wp0491 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1515 c4 L)
                            pleaf
                          )
                          (WP05.wp1003 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0027 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1051 c4 L)
                            pleaf
                          )
                          (WP03.wp0539 c4 L)
                          pleaf
                        )
                        (WP02.wp0283 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1307 c4 L)
                            pleaf
                          )
                          (WP04.wp0795 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0155 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1179 c4 L)
                            pleaf
                          )
                          (WP03.wp0667 c4 L)
                          pleaf
                        )
                        (WP02.wp0411 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1435 c4 L)
                            pleaf
                          )
                          (WP05.wp0923 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0091 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1115 c4 L)
                            pleaf
                          )
                          (WP03.wp0603 c4 L)
                          pleaf
                        )
                        (WP02.wp0347 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1371 c4 L)
                            pleaf
                          )
                          (WP04.wp0859 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0219 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1243 c4 L)
                            pleaf
                          )
                          (WP04.wp0731 c4 L)
                          pleaf
                        )
                        (WP03.wp0475 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1499 c4 L)
                            pleaf
                          )
                          (WP05.wp0987 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0059 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1083 c4 L)
                            pleaf
                          )
                          (WP03.wp0571 c4 L)
                          pleaf
                        )
                        (WP02.wp0315 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1339 c4 L)
                            pleaf
                          )
                          (WP04.wp0827 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0187 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1211 c4 L)
                            pleaf
                          )
                          (WP04.wp0699 c4 L)
                          pleaf
                        )
                        (WP02.wp0443 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1467 c4 L)
                            pleaf
                          )
                          (WP05.wp0955 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0123 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1147 c4 L)
                            pleaf
                          )
                          (WP03.wp0635 c4 L)
                          pleaf
                        )
                        (WP02.wp0379 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1403 c4 L)
                            pleaf
                          )
                          (WP04.wp0891 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0251 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1275 c4 L)
                            pleaf
                          )
                          (WP04.wp0763 c4 L)
                          pleaf
                        )
                        (WP03.wp0507 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1019 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
            )
          )
          (WP01.wp0001 c4 L)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1025 c4 L)
                            pleaf
                          )
                          (WP03.wp0513 c4 L)
                          pleaf
                        )
                        (WP01.wp0257 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1281 c4 L)
                            pleaf
                          )
                          (WP04.wp0769 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0129 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1153 c4 L)
                            pleaf
                          )
                          (WP03.wp0641 c4 L)
                          pleaf
                        )
                        (WP02.wp0385 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1409 c4 L)
                            pleaf
                          )
                          (WP04.wp0897 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0065 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1089 c4 L)
                            pleaf
                          )
                          (WP03.wp0577 c4 L)
                          pleaf
                        )
                        (WP02.wp0321 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1345 c4 L)
                            pleaf
                          )
                          (WP04.wp0833 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0193 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1217 c4 L)
                            pleaf
                          )
                          (WP04.wp0705 c4 L)
                          pleaf
                        )
                        (WP02.wp0449 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1473 c4 L)
                            pleaf
                          )
                          (WP05.wp0961 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0033 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1057 c4 L)
                            pleaf
                          )
                          (WP03.wp0545 c4 L)
                          pleaf
                        )
                        (WP02.wp0289 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1313 c4 L)
                            pleaf
                          )
                          (WP04.wp0801 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0161 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1185 c4 L)
                            pleaf
                          )
                          (WP03.wp0673 c4 L)
                          pleaf
                        )
                        (WP02.wp0417 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1441 c4 L)
                            pleaf
                          )
                          (WP05.wp0929 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0097 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1121 c4 L)
                            pleaf
                          )
                          (WP03.wp0609 c4 L)
                          pleaf
                        )
                        (WP02.wp0353 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1377 c4 L)
                            pleaf
                          )
                          (WP04.wp0865 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0225 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1249 c4 L)
                            pleaf
                          )
                          (WP04.wp0737 c4 L)
                          pleaf
                        )
                        (WP03.wp0481 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1505 c4 L)
                            pleaf
                          )
                          (WP05.wp0993 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0017 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1041 c4 L)
                            pleaf
                          )
                          (WP03.wp0529 c4 L)
                          pleaf
                        )
                        (WP02.wp0273 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1297 c4 L)
                            pleaf
                          )
                          (WP04.wp0785 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0145 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1169 c4 L)
                            pleaf
                          )
                          (WP03.wp0657 c4 L)
                          pleaf
                        )
                        (WP02.wp0401 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1425 c4 L)
                            pleaf
                          )
                          (WP04.wp0913 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0081 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1105 c4 L)
                            pleaf
                          )
                          (WP03.wp0593 c4 L)
                          pleaf
                        )
                        (WP02.wp0337 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1361 c4 L)
                            pleaf
                          )
                          (WP04.wp0849 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0209 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1233 c4 L)
                            pleaf
                          )
                          (WP04.wp0721 c4 L)
                          pleaf
                        )
                        (WP02.wp0465 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1489 c4 L)
                            pleaf
                          )
                          (WP05.wp0977 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0049 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1073 c4 L)
                            pleaf
                          )
                          (WP03.wp0561 c4 L)
                          pleaf
                        )
                        (WP02.wp0305 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1329 c4 L)
                            pleaf
                          )
                          (WP04.wp0817 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0177 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1201 c4 L)
                            pleaf
                          )
                          (WP04.wp0689 c4 L)
                          pleaf
                        )
                        (WP02.wp0433 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1457 c4 L)
                            pleaf
                          )
                          (WP05.wp0945 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0113 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1137 c4 L)
                            pleaf
                          )
                          (WP03.wp0625 c4 L)
                          pleaf
                        )
                        (WP02.wp0369 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1393 c4 L)
                            pleaf
                          )
                          (WP04.wp0881 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0241 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1265 c4 L)
                            pleaf
                          )
                          (WP04.wp0753 c4 L)
                          pleaf
                        )
                        (WP03.wp0497 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1009 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
              (WP01.wp0009 c4 L)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1033 c4 L)
                            pleaf
                          )
                          (WP03.wp0521 c4 L)
                          pleaf
                        )
                        (WP02.wp0265 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1289 c4 L)
                            pleaf
                          )
                          (WP04.wp0777 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0137 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1161 c4 L)
                            pleaf
                          )
                          (WP03.wp0649 c4 L)
                          pleaf
                        )
                        (WP02.wp0393 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1417 c4 L)
                            pleaf
                          )
                          (WP04.wp0905 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0073 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1097 c4 L)
                            pleaf
                          )
                          (WP03.wp0585 c4 L)
                          pleaf
                        )
                        (WP02.wp0329 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1353 c4 L)
                            pleaf
                          )
                          (WP04.wp0841 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0201 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1225 c4 L)
                            pleaf
                          )
                          (WP04.wp0713 c4 L)
                          pleaf
                        )
                        (WP02.wp0457 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1481 c4 L)
                            pleaf
                          )
                          (WP05.wp0969 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0041 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1065 c4 L)
                            pleaf
                          )
                          (WP03.wp0553 c4 L)
                          pleaf
                        )
                        (WP02.wp0297 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1321 c4 L)
                            pleaf
                          )
                          (WP04.wp0809 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0169 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1193 c4 L)
                            pleaf
                          )
                          (WP04.wp0681 c4 L)
                          pleaf
                        )
                        (WP02.wp0425 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1449 c4 L)
                            pleaf
                          )
                          (WP05.wp0937 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0105 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1129 c4 L)
                            pleaf
                          )
                          (WP03.wp0617 c4 L)
                          pleaf
                        )
                        (WP02.wp0361 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1385 c4 L)
                            pleaf
                          )
                          (WP04.wp0873 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0233 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1257 c4 L)
                            pleaf
                          )
                          (WP04.wp0745 c4 L)
                          pleaf
                        )
                        (WP03.wp0489 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1513 c4 L)
                            pleaf
                          )
                          (WP05.wp1001 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0025 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1049 c4 L)
                            pleaf
                          )
                          (WP03.wp0537 c4 L)
                          pleaf
                        )
                        (WP02.wp0281 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1305 c4 L)
                            pleaf
                          )
                          (WP04.wp0793 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0153 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1177 c4 L)
                            pleaf
                          )
                          (WP03.wp0665 c4 L)
                          pleaf
                        )
                        (WP02.wp0409 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1433 c4 L)
                            pleaf
                          )
                          (WP05.wp0921 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0089 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1113 c4 L)
                            pleaf
                          )
                          (WP03.wp0601 c4 L)
                          pleaf
                        )
                        (WP02.wp0345 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1369 c4 L)
                            pleaf
                          )
                          (WP04.wp0857 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0217 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1241 c4 L)
                            pleaf
                          )
                          (WP04.wp0729 c4 L)
                          pleaf
                        )
                        (WP02.wp0473 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1497 c4 L)
                            pleaf
                          )
                          (WP05.wp0985 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0057 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1081 c4 L)
                            pleaf
                          )
                          (WP03.wp0569 c4 L)
                          pleaf
                        )
                        (WP02.wp0313 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1337 c4 L)
                            pleaf
                          )
                          (WP04.wp0825 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0185 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1209 c4 L)
                            pleaf
                          )
                          (WP04.wp0697 c4 L)
                          pleaf
                        )
                        (WP02.wp0441 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1465 c4 L)
                            pleaf
                          )
                          (WP05.wp0953 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0121 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1145 c4 L)
                            pleaf
                          )
                          (WP03.wp0633 c4 L)
                          pleaf
                        )
                        (WP02.wp0377 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1401 c4 L)
                            pleaf
                          )
                          (WP04.wp0889 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0249 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1273 c4 L)
                            pleaf
                          )
                          (WP04.wp0761 c4 L)
                          pleaf
                        )
                        (WP03.wp0505 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1017 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
            )
            (WP01.wp0005 c4 L)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1029 c4 L)
                            pleaf
                          )
                          (WP03.wp0517 c4 L)
                          pleaf
                        )
                        (WP02.wp0261 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1285 c4 L)
                            pleaf
                          )
                          (WP04.wp0773 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0133 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1157 c4 L)
                            pleaf
                          )
                          (WP03.wp0645 c4 L)
                          pleaf
                        )
                        (WP02.wp0389 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1413 c4 L)
                            pleaf
                          )
                          (WP04.wp0901 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0069 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1093 c4 L)
                            pleaf
                          )
                          (WP03.wp0581 c4 L)
                          pleaf
                        )
                        (WP02.wp0325 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1349 c4 L)
                            pleaf
                          )
                          (WP04.wp0837 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0197 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1221 c4 L)
                            pleaf
                          )
                          (WP04.wp0709 c4 L)
                          pleaf
                        )
                        (WP02.wp0453 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1477 c4 L)
                            pleaf
                          )
                          (WP05.wp0965 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0037 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1061 c4 L)
                            pleaf
                          )
                          (WP03.wp0549 c4 L)
                          pleaf
                        )
                        (WP02.wp0293 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1317 c4 L)
                            pleaf
                          )
                          (WP04.wp0805 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0165 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1189 c4 L)
                            pleaf
                          )
                          (WP04.wp0677 c4 L)
                          pleaf
                        )
                        (WP02.wp0421 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1445 c4 L)
                            pleaf
                          )
                          (WP05.wp0933 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0101 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1125 c4 L)
                            pleaf
                          )
                          (WP03.wp0613 c4 L)
                          pleaf
                        )
                        (WP02.wp0357 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1381 c4 L)
                            pleaf
                          )
                          (WP04.wp0869 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0229 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1253 c4 L)
                            pleaf
                          )
                          (WP04.wp0741 c4 L)
                          pleaf
                        )
                        (WP03.wp0485 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1509 c4 L)
                            pleaf
                          )
                          (WP05.wp0997 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0021 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1045 c4 L)
                            pleaf
                          )
                          (WP03.wp0533 c4 L)
                          pleaf
                        )
                        (WP02.wp0277 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1301 c4 L)
                            pleaf
                          )
                          (WP04.wp0789 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0149 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1173 c4 L)
                            pleaf
                          )
                          (WP03.wp0661 c4 L)
                          pleaf
                        )
                        (WP02.wp0405 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1429 c4 L)
                            pleaf
                          )
                          (WP04.wp0917 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0085 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1109 c4 L)
                            pleaf
                          )
                          (WP03.wp0597 c4 L)
                          pleaf
                        )
                        (WP02.wp0341 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1365 c4 L)
                            pleaf
                          )
                          (WP04.wp0853 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0213 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1237 c4 L)
                            pleaf
                          )
                          (WP04.wp0725 c4 L)
                          pleaf
                        )
                        (WP02.wp0469 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1493 c4 L)
                            pleaf
                          )
                          (WP05.wp0981 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0053 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1077 c4 L)
                            pleaf
                          )
                          (WP03.wp0565 c4 L)
                          pleaf
                        )
                        (WP02.wp0309 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1333 c4 L)
                            pleaf
                          )
                          (WP04.wp0821 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0181 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1205 c4 L)
                            pleaf
                          )
                          (WP04.wp0693 c4 L)
                          pleaf
                        )
                        (WP02.wp0437 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1461 c4 L)
                            pleaf
                          )
                          (WP05.wp0949 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0117 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1141 c4 L)
                            pleaf
                          )
                          (WP03.wp0629 c4 L)
                          pleaf
                        )
                        (WP02.wp0373 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1397 c4 L)
                            pleaf
                          )
                          (WP04.wp0885 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0245 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1269 c4 L)
                            pleaf
                          )
                          (WP04.wp0757 c4 L)
                          pleaf
                        )
                        (WP03.wp0501 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1013 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
              (WP01.wp0013 c4 L)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1037 c4 L)
                            pleaf
                          )
                          (WP03.wp0525 c4 L)
                          pleaf
                        )
                        (WP02.wp0269 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1293 c4 L)
                            pleaf
                          )
                          (WP04.wp0781 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0141 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1165 c4 L)
                            pleaf
                          )
                          (WP03.wp0653 c4 L)
                          pleaf
                        )
                        (WP02.wp0397 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1421 c4 L)
                            pleaf
                          )
                          (WP04.wp0909 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0077 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1101 c4 L)
                            pleaf
                          )
                          (WP03.wp0589 c4 L)
                          pleaf
                        )
                        (WP02.wp0333 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1357 c4 L)
                            pleaf
                          )
                          (WP04.wp0845 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0205 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1229 c4 L)
                            pleaf
                          )
                          (WP04.wp0717 c4 L)
                          pleaf
                        )
                        (WP02.wp0461 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1485 c4 L)
                            pleaf
                          )
                          (WP05.wp0973 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0045 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1069 c4 L)
                            pleaf
                          )
                          (WP03.wp0557 c4 L)
                          pleaf
                        )
                        (WP02.wp0301 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1325 c4 L)
                            pleaf
                          )
                          (WP04.wp0813 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0173 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1197 c4 L)
                            pleaf
                          )
                          (WP04.wp0685 c4 L)
                          pleaf
                        )
                        (WP02.wp0429 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1453 c4 L)
                            pleaf
                          )
                          (WP05.wp0941 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0109 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1133 c4 L)
                            pleaf
                          )
                          (WP03.wp0621 c4 L)
                          pleaf
                        )
                        (WP02.wp0365 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1389 c4 L)
                            pleaf
                          )
                          (WP04.wp0877 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0237 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1261 c4 L)
                            pleaf
                          )
                          (WP04.wp0749 c4 L)
                          pleaf
                        )
                        (WP03.wp0493 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1517 c4 L)
                            pleaf
                          )
                          (WP05.wp1005 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0029 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1053 c4 L)
                            pleaf
                          )
                          (WP03.wp0541 c4 L)
                          pleaf
                        )
                        (WP02.wp0285 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1309 c4 L)
                            pleaf
                          )
                          (WP04.wp0797 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0157 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1181 c4 L)
                            pleaf
                          )
                          (WP03.wp0669 c4 L)
                          pleaf
                        )
                        (WP02.wp0413 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1437 c4 L)
                            pleaf
                          )
                          (WP05.wp0925 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0093 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1117 c4 L)
                            pleaf
                          )
                          (WP03.wp0605 c4 L)
                          pleaf
                        )
                        (WP02.wp0349 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1373 c4 L)
                            pleaf
                          )
                          (WP04.wp0861 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0221 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1245 c4 L)
                            pleaf
                          )
                          (WP04.wp0733 c4 L)
                          pleaf
                        )
                        (WP03.wp0477 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1501 c4 L)
                            pleaf
                          )
                          (WP05.wp0989 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0061 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1085 c4 L)
                            pleaf
                          )
                          (WP03.wp0573 c4 L)
                          pleaf
                        )
                        (WP02.wp0317 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1341 c4 L)
                            pleaf
                          )
                          (WP04.wp0829 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0189 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1213 c4 L)
                            pleaf
                          )
                          (WP04.wp0701 c4 L)
                          pleaf
                        )
                        (WP02.wp0445 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1469 c4 L)
                            pleaf
                          )
                          (WP05.wp0957 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0125 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1149 c4 L)
                            pleaf
                          )
                          (WP03.wp0637 c4 L)
                          pleaf
                        )
                        (WP02.wp0381 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1405 c4 L)
                            pleaf
                          )
                          (WP04.wp0893 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0253 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1277 c4 L)
                            pleaf
                          )
                          (WP04.wp0765 c4 L)
                          pleaf
                        )
                        (WP03.wp0509 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1021 c4 L)
                          pleaf
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
        (pnode
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1024 c4 L)
                            pleaf
                          )
                          (WP03.wp0512 c4 L)
                          pleaf
                        )
                        (WP01.wp0256 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1280 c4 L)
                            pleaf
                          )
                          (WP04.wp0768 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0128 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1152 c4 L)
                            pleaf
                          )
                          (WP03.wp0640 c4 L)
                          pleaf
                        )
                        (WP02.wp0384 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1408 c4 L)
                            pleaf
                          )
                          (WP04.wp0896 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0064 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1088 c4 L)
                            pleaf
                          )
                          (WP03.wp0576 c4 L)
                          pleaf
                        )
                        (WP02.wp0320 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1344 c4 L)
                            pleaf
                          )
                          (WP04.wp0832 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0192 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1216 c4 L)
                            pleaf
                          )
                          (WP04.wp0704 c4 L)
                          pleaf
                        )
                        (WP02.wp0448 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1472 c4 L)
                            pleaf
                          )
                          (WP05.wp0960 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0032 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1056 c4 L)
                            pleaf
                          )
                          (WP03.wp0544 c4 L)
                          pleaf
                        )
                        (WP02.wp0288 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1312 c4 L)
                            pleaf
                          )
                          (WP04.wp0800 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0160 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1184 c4 L)
                            pleaf
                          )
                          (WP03.wp0672 c4 L)
                          pleaf
                        )
                        (WP02.wp0416 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1440 c4 L)
                            pleaf
                          )
                          (WP05.wp0928 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0096 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1120 c4 L)
                            pleaf
                          )
                          (WP03.wp0608 c4 L)
                          pleaf
                        )
                        (WP02.wp0352 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1376 c4 L)
                            pleaf
                          )
                          (WP04.wp0864 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0224 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1248 c4 L)
                            pleaf
                          )
                          (WP04.wp0736 c4 L)
                          pleaf
                        )
                        (WP03.wp0480 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1504 c4 L)
                            pleaf
                          )
                          (WP05.wp0992 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0016 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1040 c4 L)
                            pleaf
                          )
                          (WP03.wp0528 c4 L)
                          pleaf
                        )
                        (WP02.wp0272 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1296 c4 L)
                            pleaf
                          )
                          (WP04.wp0784 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0144 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1168 c4 L)
                            pleaf
                          )
                          (WP03.wp0656 c4 L)
                          pleaf
                        )
                        (WP02.wp0400 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1424 c4 L)
                            pleaf
                          )
                          (WP04.wp0912 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0080 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1104 c4 L)
                            pleaf
                          )
                          (WP03.wp0592 c4 L)
                          pleaf
                        )
                        (WP02.wp0336 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1360 c4 L)
                            pleaf
                          )
                          (WP04.wp0848 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0208 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1232 c4 L)
                            pleaf
                          )
                          (WP04.wp0720 c4 L)
                          pleaf
                        )
                        (WP02.wp0464 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1488 c4 L)
                            pleaf
                          )
                          (WP05.wp0976 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0048 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1072 c4 L)
                            pleaf
                          )
                          (WP03.wp0560 c4 L)
                          pleaf
                        )
                        (WP02.wp0304 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1328 c4 L)
                            pleaf
                          )
                          (WP04.wp0816 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0176 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1200 c4 L)
                            pleaf
                          )
                          (WP04.wp0688 c4 L)
                          pleaf
                        )
                        (WP02.wp0432 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1456 c4 L)
                            pleaf
                          )
                          (WP05.wp0944 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0112 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1136 c4 L)
                            pleaf
                          )
                          (WP03.wp0624 c4 L)
                          pleaf
                        )
                        (WP02.wp0368 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1392 c4 L)
                            pleaf
                          )
                          (WP04.wp0880 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0240 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1264 c4 L)
                            pleaf
                          )
                          (WP04.wp0752 c4 L)
                          pleaf
                        )
                        (WP03.wp0496 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1008 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
              (WP01.wp0008 c4 L)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1032 c4 L)
                            pleaf
                          )
                          (WP03.wp0520 c4 L)
                          pleaf
                        )
                        (WP02.wp0264 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1288 c4 L)
                            pleaf
                          )
                          (WP04.wp0776 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0136 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1160 c4 L)
                            pleaf
                          )
                          (WP03.wp0648 c4 L)
                          pleaf
                        )
                        (WP02.wp0392 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1416 c4 L)
                            pleaf
                          )
                          (WP04.wp0904 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0072 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1096 c4 L)
                            pleaf
                          )
                          (WP03.wp0584 c4 L)
                          pleaf
                        )
                        (WP02.wp0328 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1352 c4 L)
                            pleaf
                          )
                          (WP04.wp0840 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0200 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1224 c4 L)
                            pleaf
                          )
                          (WP04.wp0712 c4 L)
                          pleaf
                        )
                        (WP02.wp0456 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1480 c4 L)
                            pleaf
                          )
                          (WP05.wp0968 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0040 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1064 c4 L)
                            pleaf
                          )
                          (WP03.wp0552 c4 L)
                          pleaf
                        )
                        (WP02.wp0296 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1320 c4 L)
                            pleaf
                          )
                          (WP04.wp0808 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0168 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1192 c4 L)
                            pleaf
                          )
                          (WP04.wp0680 c4 L)
                          pleaf
                        )
                        (WP02.wp0424 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1448 c4 L)
                            pleaf
                          )
                          (WP05.wp0936 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0104 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1128 c4 L)
                            pleaf
                          )
                          (WP03.wp0616 c4 L)
                          pleaf
                        )
                        (WP02.wp0360 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1384 c4 L)
                            pleaf
                          )
                          (WP04.wp0872 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0232 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1256 c4 L)
                            pleaf
                          )
                          (WP04.wp0744 c4 L)
                          pleaf
                        )
                        (WP03.wp0488 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1512 c4 L)
                            pleaf
                          )
                          (WP05.wp1000 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0024 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1048 c4 L)
                            pleaf
                          )
                          (WP03.wp0536 c4 L)
                          pleaf
                        )
                        (WP02.wp0280 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1304 c4 L)
                            pleaf
                          )
                          (WP04.wp0792 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0152 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1176 c4 L)
                            pleaf
                          )
                          (WP03.wp0664 c4 L)
                          pleaf
                        )
                        (WP02.wp0408 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1432 c4 L)
                            pleaf
                          )
                          (WP05.wp0920 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0088 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1112 c4 L)
                            pleaf
                          )
                          (WP03.wp0600 c4 L)
                          pleaf
                        )
                        (WP02.wp0344 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1368 c4 L)
                            pleaf
                          )
                          (WP04.wp0856 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0216 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1240 c4 L)
                            pleaf
                          )
                          (WP04.wp0728 c4 L)
                          pleaf
                        )
                        (WP02.wp0472 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1496 c4 L)
                            pleaf
                          )
                          (WP05.wp0984 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0056 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1080 c4 L)
                            pleaf
                          )
                          (WP03.wp0568 c4 L)
                          pleaf
                        )
                        (WP02.wp0312 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1336 c4 L)
                            pleaf
                          )
                          (WP04.wp0824 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0184 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1208 c4 L)
                            pleaf
                          )
                          (WP04.wp0696 c4 L)
                          pleaf
                        )
                        (WP02.wp0440 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1464 c4 L)
                            pleaf
                          )
                          (WP05.wp0952 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0120 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1144 c4 L)
                            pleaf
                          )
                          (WP03.wp0632 c4 L)
                          pleaf
                        )
                        (WP02.wp0376 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1400 c4 L)
                            pleaf
                          )
                          (WP04.wp0888 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0248 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1272 c4 L)
                            pleaf
                          )
                          (WP04.wp0760 c4 L)
                          pleaf
                        )
                        (WP03.wp0504 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1016 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
            )
            (WP01.wp0004 c4 L)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1028 c4 L)
                            pleaf
                          )
                          (WP03.wp0516 c4 L)
                          pleaf
                        )
                        (WP02.wp0260 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1284 c4 L)
                            pleaf
                          )
                          (WP04.wp0772 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0132 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1156 c4 L)
                            pleaf
                          )
                          (WP03.wp0644 c4 L)
                          pleaf
                        )
                        (WP02.wp0388 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1412 c4 L)
                            pleaf
                          )
                          (WP04.wp0900 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0068 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1092 c4 L)
                            pleaf
                          )
                          (WP03.wp0580 c4 L)
                          pleaf
                        )
                        (WP02.wp0324 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1348 c4 L)
                            pleaf
                          )
                          (WP04.wp0836 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0196 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1220 c4 L)
                            pleaf
                          )
                          (WP04.wp0708 c4 L)
                          pleaf
                        )
                        (WP02.wp0452 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1476 c4 L)
                            pleaf
                          )
                          (WP05.wp0964 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0036 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1060 c4 L)
                            pleaf
                          )
                          (WP03.wp0548 c4 L)
                          pleaf
                        )
                        (WP02.wp0292 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1316 c4 L)
                            pleaf
                          )
                          (WP04.wp0804 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0164 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1188 c4 L)
                            pleaf
                          )
                          (WP04.wp0676 c4 L)
                          pleaf
                        )
                        (WP02.wp0420 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1444 c4 L)
                            pleaf
                          )
                          (WP05.wp0932 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0100 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1124 c4 L)
                            pleaf
                          )
                          (WP03.wp0612 c4 L)
                          pleaf
                        )
                        (WP02.wp0356 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1380 c4 L)
                            pleaf
                          )
                          (WP04.wp0868 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0228 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1252 c4 L)
                            pleaf
                          )
                          (WP04.wp0740 c4 L)
                          pleaf
                        )
                        (WP03.wp0484 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1508 c4 L)
                            pleaf
                          )
                          (WP05.wp0996 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0020 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1044 c4 L)
                            pleaf
                          )
                          (WP03.wp0532 c4 L)
                          pleaf
                        )
                        (WP02.wp0276 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1300 c4 L)
                            pleaf
                          )
                          (WP04.wp0788 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0148 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1172 c4 L)
                            pleaf
                          )
                          (WP03.wp0660 c4 L)
                          pleaf
                        )
                        (WP02.wp0404 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1428 c4 L)
                            pleaf
                          )
                          (WP04.wp0916 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0084 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1108 c4 L)
                            pleaf
                          )
                          (WP03.wp0596 c4 L)
                          pleaf
                        )
                        (WP02.wp0340 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1364 c4 L)
                            pleaf
                          )
                          (WP04.wp0852 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0212 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1236 c4 L)
                            pleaf
                          )
                          (WP04.wp0724 c4 L)
                          pleaf
                        )
                        (WP02.wp0468 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1492 c4 L)
                            pleaf
                          )
                          (WP05.wp0980 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0052 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1076 c4 L)
                            pleaf
                          )
                          (WP03.wp0564 c4 L)
                          pleaf
                        )
                        (WP02.wp0308 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1332 c4 L)
                            pleaf
                          )
                          (WP04.wp0820 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0180 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1204 c4 L)
                            pleaf
                          )
                          (WP04.wp0692 c4 L)
                          pleaf
                        )
                        (WP02.wp0436 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1460 c4 L)
                            pleaf
                          )
                          (WP05.wp0948 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0116 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1140 c4 L)
                            pleaf
                          )
                          (WP03.wp0628 c4 L)
                          pleaf
                        )
                        (WP02.wp0372 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1396 c4 L)
                            pleaf
                          )
                          (WP04.wp0884 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0244 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1268 c4 L)
                            pleaf
                          )
                          (WP04.wp0756 c4 L)
                          pleaf
                        )
                        (WP03.wp0500 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1012 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
              (WP01.wp0012 c4 L)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1036 c4 L)
                            pleaf
                          )
                          (WP03.wp0524 c4 L)
                          pleaf
                        )
                        (WP02.wp0268 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1292 c4 L)
                            pleaf
                          )
                          (WP04.wp0780 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0140 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1164 c4 L)
                            pleaf
                          )
                          (WP03.wp0652 c4 L)
                          pleaf
                        )
                        (WP02.wp0396 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1420 c4 L)
                            pleaf
                          )
                          (WP04.wp0908 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0076 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1100 c4 L)
                            pleaf
                          )
                          (WP03.wp0588 c4 L)
                          pleaf
                        )
                        (WP02.wp0332 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1356 c4 L)
                            pleaf
                          )
                          (WP04.wp0844 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0204 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1228 c4 L)
                            pleaf
                          )
                          (WP04.wp0716 c4 L)
                          pleaf
                        )
                        (WP02.wp0460 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1484 c4 L)
                            pleaf
                          )
                          (WP05.wp0972 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0044 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1068 c4 L)
                            pleaf
                          )
                          (WP03.wp0556 c4 L)
                          pleaf
                        )
                        (WP02.wp0300 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1324 c4 L)
                            pleaf
                          )
                          (WP04.wp0812 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0172 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1196 c4 L)
                            pleaf
                          )
                          (WP04.wp0684 c4 L)
                          pleaf
                        )
                        (WP02.wp0428 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1452 c4 L)
                            pleaf
                          )
                          (WP05.wp0940 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0108 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1132 c4 L)
                            pleaf
                          )
                          (WP03.wp0620 c4 L)
                          pleaf
                        )
                        (WP02.wp0364 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1388 c4 L)
                            pleaf
                          )
                          (WP04.wp0876 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0236 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1260 c4 L)
                            pleaf
                          )
                          (WP04.wp0748 c4 L)
                          pleaf
                        )
                        (WP03.wp0492 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1516 c4 L)
                            pleaf
                          )
                          (WP05.wp1004 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0028 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1052 c4 L)
                            pleaf
                          )
                          (WP03.wp0540 c4 L)
                          pleaf
                        )
                        (WP02.wp0284 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1308 c4 L)
                            pleaf
                          )
                          (WP04.wp0796 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0156 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1180 c4 L)
                            pleaf
                          )
                          (WP03.wp0668 c4 L)
                          pleaf
                        )
                        (WP02.wp0412 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1436 c4 L)
                            pleaf
                          )
                          (WP05.wp0924 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0092 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1116 c4 L)
                            pleaf
                          )
                          (WP03.wp0604 c4 L)
                          pleaf
                        )
                        (WP02.wp0348 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1372 c4 L)
                            pleaf
                          )
                          (WP04.wp0860 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0220 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1244 c4 L)
                            pleaf
                          )
                          (WP04.wp0732 c4 L)
                          pleaf
                        )
                        (WP03.wp0476 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1500 c4 L)
                            pleaf
                          )
                          (WP05.wp0988 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0060 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1084 c4 L)
                            pleaf
                          )
                          (WP03.wp0572 c4 L)
                          pleaf
                        )
                        (WP02.wp0316 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1340 c4 L)
                            pleaf
                          )
                          (WP04.wp0828 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0188 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1212 c4 L)
                            pleaf
                          )
                          (WP04.wp0700 c4 L)
                          pleaf
                        )
                        (WP02.wp0444 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1468 c4 L)
                            pleaf
                          )
                          (WP05.wp0956 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0124 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1148 c4 L)
                            pleaf
                          )
                          (WP03.wp0636 c4 L)
                          pleaf
                        )
                        (WP02.wp0380 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1404 c4 L)
                            pleaf
                          )
                          (WP04.wp0892 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0252 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1276 c4 L)
                            pleaf
                          )
                          (WP04.wp0764 c4 L)
                          pleaf
                        )
                        (WP03.wp0508 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1020 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
            )
          )
          (WP01.wp0002 c4 L)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1026 c4 L)
                            pleaf
                          )
                          (WP03.wp0514 c4 L)
                          pleaf
                        )
                        (WP01.wp0258 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1282 c4 L)
                            pleaf
                          )
                          (WP04.wp0770 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0130 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1154 c4 L)
                            pleaf
                          )
                          (WP03.wp0642 c4 L)
                          pleaf
                        )
                        (WP02.wp0386 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1410 c4 L)
                            pleaf
                          )
                          (WP04.wp0898 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0066 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1090 c4 L)
                            pleaf
                          )
                          (WP03.wp0578 c4 L)
                          pleaf
                        )
                        (WP02.wp0322 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1346 c4 L)
                            pleaf
                          )
                          (WP04.wp0834 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0194 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1218 c4 L)
                            pleaf
                          )
                          (WP04.wp0706 c4 L)
                          pleaf
                        )
                        (WP02.wp0450 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1474 c4 L)
                            pleaf
                          )
                          (WP05.wp0962 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0034 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1058 c4 L)
                            pleaf
                          )
                          (WP03.wp0546 c4 L)
                          pleaf
                        )
                        (WP02.wp0290 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1314 c4 L)
                            pleaf
                          )
                          (WP04.wp0802 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0162 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1186 c4 L)
                            pleaf
                          )
                          (WP03.wp0674 c4 L)
                          pleaf
                        )
                        (WP02.wp0418 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1442 c4 L)
                            pleaf
                          )
                          (WP05.wp0930 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0098 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1122 c4 L)
                            pleaf
                          )
                          (WP03.wp0610 c4 L)
                          pleaf
                        )
                        (WP02.wp0354 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1378 c4 L)
                            pleaf
                          )
                          (WP04.wp0866 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0226 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1250 c4 L)
                            pleaf
                          )
                          (WP04.wp0738 c4 L)
                          pleaf
                        )
                        (WP03.wp0482 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1506 c4 L)
                            pleaf
                          )
                          (WP05.wp0994 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0018 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1042 c4 L)
                            pleaf
                          )
                          (WP03.wp0530 c4 L)
                          pleaf
                        )
                        (WP02.wp0274 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1298 c4 L)
                            pleaf
                          )
                          (WP04.wp0786 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0146 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1170 c4 L)
                            pleaf
                          )
                          (WP03.wp0658 c4 L)
                          pleaf
                        )
                        (WP02.wp0402 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1426 c4 L)
                            pleaf
                          )
                          (WP04.wp0914 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0082 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1106 c4 L)
                            pleaf
                          )
                          (WP03.wp0594 c4 L)
                          pleaf
                        )
                        (WP02.wp0338 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1362 c4 L)
                            pleaf
                          )
                          (WP04.wp0850 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0210 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1234 c4 L)
                            pleaf
                          )
                          (WP04.wp0722 c4 L)
                          pleaf
                        )
                        (WP02.wp0466 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1490 c4 L)
                            pleaf
                          )
                          (WP05.wp0978 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0050 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1074 c4 L)
                            pleaf
                          )
                          (WP03.wp0562 c4 L)
                          pleaf
                        )
                        (WP02.wp0306 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1330 c4 L)
                            pleaf
                          )
                          (WP04.wp0818 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0178 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1202 c4 L)
                            pleaf
                          )
                          (WP04.wp0690 c4 L)
                          pleaf
                        )
                        (WP02.wp0434 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1458 c4 L)
                            pleaf
                          )
                          (WP05.wp0946 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0114 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1138 c4 L)
                            pleaf
                          )
                          (WP03.wp0626 c4 L)
                          pleaf
                        )
                        (WP02.wp0370 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1394 c4 L)
                            pleaf
                          )
                          (WP04.wp0882 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0242 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1266 c4 L)
                            pleaf
                          )
                          (WP04.wp0754 c4 L)
                          pleaf
                        )
                        (WP03.wp0498 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1010 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
              (WP01.wp0010 c4 L)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1034 c4 L)
                            pleaf
                          )
                          (WP03.wp0522 c4 L)
                          pleaf
                        )
                        (WP02.wp0266 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1290 c4 L)
                            pleaf
                          )
                          (WP04.wp0778 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0138 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1162 c4 L)
                            pleaf
                          )
                          (WP03.wp0650 c4 L)
                          pleaf
                        )
                        (WP02.wp0394 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1418 c4 L)
                            pleaf
                          )
                          (WP04.wp0906 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0074 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1098 c4 L)
                            pleaf
                          )
                          (WP03.wp0586 c4 L)
                          pleaf
                        )
                        (WP02.wp0330 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1354 c4 L)
                            pleaf
                          )
                          (WP04.wp0842 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0202 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1226 c4 L)
                            pleaf
                          )
                          (WP04.wp0714 c4 L)
                          pleaf
                        )
                        (WP02.wp0458 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1482 c4 L)
                            pleaf
                          )
                          (WP05.wp0970 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0042 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1066 c4 L)
                            pleaf
                          )
                          (WP03.wp0554 c4 L)
                          pleaf
                        )
                        (WP02.wp0298 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1322 c4 L)
                            pleaf
                          )
                          (WP04.wp0810 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0170 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1194 c4 L)
                            pleaf
                          )
                          (WP04.wp0682 c4 L)
                          pleaf
                        )
                        (WP02.wp0426 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1450 c4 L)
                            pleaf
                          )
                          (WP05.wp0938 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0106 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1130 c4 L)
                            pleaf
                          )
                          (WP03.wp0618 c4 L)
                          pleaf
                        )
                        (WP02.wp0362 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1386 c4 L)
                            pleaf
                          )
                          (WP04.wp0874 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0234 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1258 c4 L)
                            pleaf
                          )
                          (WP04.wp0746 c4 L)
                          pleaf
                        )
                        (WP03.wp0490 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1514 c4 L)
                            pleaf
                          )
                          (WP05.wp1002 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0026 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1050 c4 L)
                            pleaf
                          )
                          (WP03.wp0538 c4 L)
                          pleaf
                        )
                        (WP02.wp0282 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1306 c4 L)
                            pleaf
                          )
                          (WP04.wp0794 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0154 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1178 c4 L)
                            pleaf
                          )
                          (WP03.wp0666 c4 L)
                          pleaf
                        )
                        (WP02.wp0410 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1434 c4 L)
                            pleaf
                          )
                          (WP05.wp0922 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0090 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1114 c4 L)
                            pleaf
                          )
                          (WP03.wp0602 c4 L)
                          pleaf
                        )
                        (WP02.wp0346 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1370 c4 L)
                            pleaf
                          )
                          (WP04.wp0858 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0218 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1242 c4 L)
                            pleaf
                          )
                          (WP04.wp0730 c4 L)
                          pleaf
                        )
                        (WP03.wp0474 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1498 c4 L)
                            pleaf
                          )
                          (WP05.wp0986 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0058 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1082 c4 L)
                            pleaf
                          )
                          (WP03.wp0570 c4 L)
                          pleaf
                        )
                        (WP02.wp0314 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1338 c4 L)
                            pleaf
                          )
                          (WP04.wp0826 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0186 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1210 c4 L)
                            pleaf
                          )
                          (WP04.wp0698 c4 L)
                          pleaf
                        )
                        (WP02.wp0442 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1466 c4 L)
                            pleaf
                          )
                          (WP05.wp0954 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0122 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1146 c4 L)
                            pleaf
                          )
                          (WP03.wp0634 c4 L)
                          pleaf
                        )
                        (WP02.wp0378 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1402 c4 L)
                            pleaf
                          )
                          (WP04.wp0890 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0250 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1274 c4 L)
                            pleaf
                          )
                          (WP04.wp0762 c4 L)
                          pleaf
                        )
                        (WP03.wp0506 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1018 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
            )
            (WP01.wp0006 c4 L)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1030 c4 L)
                            pleaf
                          )
                          (WP03.wp0518 c4 L)
                          pleaf
                        )
                        (WP02.wp0262 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1286 c4 L)
                            pleaf
                          )
                          (WP04.wp0774 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0134 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1158 c4 L)
                            pleaf
                          )
                          (WP03.wp0646 c4 L)
                          pleaf
                        )
                        (WP02.wp0390 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1414 c4 L)
                            pleaf
                          )
                          (WP04.wp0902 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0070 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1094 c4 L)
                            pleaf
                          )
                          (WP03.wp0582 c4 L)
                          pleaf
                        )
                        (WP02.wp0326 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1350 c4 L)
                            pleaf
                          )
                          (WP04.wp0838 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0198 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1222 c4 L)
                            pleaf
                          )
                          (WP04.wp0710 c4 L)
                          pleaf
                        )
                        (WP02.wp0454 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1478 c4 L)
                            pleaf
                          )
                          (WP05.wp0966 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0038 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1062 c4 L)
                            pleaf
                          )
                          (WP03.wp0550 c4 L)
                          pleaf
                        )
                        (WP02.wp0294 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1318 c4 L)
                            pleaf
                          )
                          (WP04.wp0806 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0166 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1190 c4 L)
                            pleaf
                          )
                          (WP04.wp0678 c4 L)
                          pleaf
                        )
                        (WP02.wp0422 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1446 c4 L)
                            pleaf
                          )
                          (WP05.wp0934 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0102 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1126 c4 L)
                            pleaf
                          )
                          (WP03.wp0614 c4 L)
                          pleaf
                        )
                        (WP02.wp0358 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1382 c4 L)
                            pleaf
                          )
                          (WP04.wp0870 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0230 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1254 c4 L)
                            pleaf
                          )
                          (WP04.wp0742 c4 L)
                          pleaf
                        )
                        (WP03.wp0486 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1510 c4 L)
                            pleaf
                          )
                          (WP05.wp0998 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0022 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1046 c4 L)
                            pleaf
                          )
                          (WP03.wp0534 c4 L)
                          pleaf
                        )
                        (WP02.wp0278 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1302 c4 L)
                            pleaf
                          )
                          (WP04.wp0790 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0150 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1174 c4 L)
                            pleaf
                          )
                          (WP03.wp0662 c4 L)
                          pleaf
                        )
                        (WP02.wp0406 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1430 c4 L)
                            pleaf
                          )
                          (WP04.wp0918 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0086 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1110 c4 L)
                            pleaf
                          )
                          (WP03.wp0598 c4 L)
                          pleaf
                        )
                        (WP02.wp0342 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1366 c4 L)
                            pleaf
                          )
                          (WP04.wp0854 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0214 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1238 c4 L)
                            pleaf
                          )
                          (WP04.wp0726 c4 L)
                          pleaf
                        )
                        (WP02.wp0470 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1494 c4 L)
                            pleaf
                          )
                          (WP05.wp0982 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0054 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1078 c4 L)
                            pleaf
                          )
                          (WP03.wp0566 c4 L)
                          pleaf
                        )
                        (WP02.wp0310 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1334 c4 L)
                            pleaf
                          )
                          (WP04.wp0822 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0182 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1206 c4 L)
                            pleaf
                          )
                          (WP04.wp0694 c4 L)
                          pleaf
                        )
                        (WP02.wp0438 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1462 c4 L)
                            pleaf
                          )
                          (WP05.wp0950 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0118 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1142 c4 L)
                            pleaf
                          )
                          (WP03.wp0630 c4 L)
                          pleaf
                        )
                        (WP02.wp0374 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1398 c4 L)
                            pleaf
                          )
                          (WP04.wp0886 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0246 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1270 c4 L)
                            pleaf
                          )
                          (WP04.wp0758 c4 L)
                          pleaf
                        )
                        (WP03.wp0502 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1014 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
              )
              (WP01.wp0014 c4 L)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1038 c4 L)
                            pleaf
                          )
                          (WP03.wp0526 c4 L)
                          pleaf
                        )
                        (WP02.wp0270 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1294 c4 L)
                            pleaf
                          )
                          (WP04.wp0782 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0142 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1166 c4 L)
                            pleaf
                          )
                          (WP03.wp0654 c4 L)
                          pleaf
                        )
                        (WP02.wp0398 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1422 c4 L)
                            pleaf
                          )
                          (WP04.wp0910 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0078 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1102 c4 L)
                            pleaf
                          )
                          (WP03.wp0590 c4 L)
                          pleaf
                        )
                        (WP02.wp0334 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1358 c4 L)
                            pleaf
                          )
                          (WP04.wp0846 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0206 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1230 c4 L)
                            pleaf
                          )
                          (WP04.wp0718 c4 L)
                          pleaf
                        )
                        (WP02.wp0462 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1486 c4 L)
                            pleaf
                          )
                          (WP05.wp0974 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0046 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1070 c4 L)
                            pleaf
                          )
                          (WP03.wp0558 c4 L)
                          pleaf
                        )
                        (WP02.wp0302 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1326 c4 L)
                            pleaf
                          )
                          (WP04.wp0814 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0174 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1198 c4 L)
                            pleaf
                          )
                          (WP04.wp0686 c4 L)
                          pleaf
                        )
                        (WP02.wp0430 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1454 c4 L)
                            pleaf
                          )
                          (WP05.wp0942 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0110 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1134 c4 L)
                            pleaf
                          )
                          (WP03.wp0622 c4 L)
                          pleaf
                        )
                        (WP02.wp0366 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1390 c4 L)
                            pleaf
                          )
                          (WP04.wp0878 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0238 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1262 c4 L)
                            pleaf
                          )
                          (WP04.wp0750 c4 L)
                          pleaf
                        )
                        (WP03.wp0494 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1518 c4 L)
                            pleaf
                          )
                          (WP05.wp1006 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                )
                (WP01.wp0030 c4 L)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1054 c4 L)
                            pleaf
                          )
                          (WP03.wp0542 c4 L)
                          pleaf
                        )
                        (WP02.wp0286 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1310 c4 L)
                            pleaf
                          )
                          (WP04.wp0798 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0158 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1182 c4 L)
                            pleaf
                          )
                          (WP03.wp0670 c4 L)
                          pleaf
                        )
                        (WP02.wp0414 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1438 c4 L)
                            pleaf
                          )
                          (WP05.wp0926 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0094 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1118 c4 L)
                            pleaf
                          )
                          (WP03.wp0606 c4 L)
                          pleaf
                        )
                        (WP02.wp0350 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1374 c4 L)
                            pleaf
                          )
                          (WP04.wp0862 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0222 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1246 c4 L)
                            pleaf
                          )
                          (WP04.wp0734 c4 L)
                          pleaf
                        )
                        (WP03.wp0478 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1502 c4 L)
                            pleaf
                          )
                          (WP05.wp0990 c4 L)
                          pleaf
                        )
                      )
                    )
                  )
                  (WP01.wp0062 c4 L)
                  (pnode
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP05.wp1086 c4 L)
                            pleaf
                          )
                          (WP03.wp0574 c4 L)
                          pleaf
                        )
                        (WP02.wp0318 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1342 c4 L)
                            pleaf
                          )
                          (WP04.wp0830 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0190 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1214 c4 L)
                            pleaf
                          )
                          (WP04.wp0702 c4 L)
                          pleaf
                        )
                        (WP02.wp0446 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1470 c4 L)
                            pleaf
                          )
                          (WP05.wp0958 c4 L)
                          pleaf
                        )
                      )
                    )
                    (WP01.wp0126 c4 L)
                    (pnode
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP06.wp1150 c4 L)
                            pleaf
                          )
                          (WP03.wp0638 c4 L)
                          pleaf
                        )
                        (WP02.wp0382 c4 L)
                        (pnode
                          (pnode
                            pleaf
                            (WP08.wp1406 c4 L)
                            pleaf
                          )
                          (WP04.wp0894 c4 L)
                          pleaf
                        )
                      )
                      (WP01.wp0254 c4 L)
                      (pnode
                        (pnode
                          (pnode
                            pleaf
                            (WP07.wp1278 c4 L)
                            pleaf
                          )
                          (WP04.wp0766 c4 L)
                          pleaf
                        )
                        (WP03.wp0510 c4 L)
                        (pnode
                          pleaf
                          (WP05.wp1022 c4 L)
                          pleaf
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
  }
  where L = wsL c4
