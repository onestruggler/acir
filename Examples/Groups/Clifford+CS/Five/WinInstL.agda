------------------------------------------------------------------------
-- Presentations of groups
--
-- The literal windows of the five-wire derivations, as a record
--
-- Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Examples.Groups.Clifford+CS.Five.WinInstL where

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain using (refl)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; pleaf ; pnode)
import Examples.Groups.Clifford+CS.Five.Wins.WL01 as WL01
import Examples.Groups.Clifford+CS.Five.Wins.WL02 as WL02
import Examples.Groups.Clifford+CS.Five.Wins.WL03 as WL03
import Examples.Groups.Clifford+CS.Five.Wins.WL04 as WL04
import Examples.Groups.Clifford+CS.Five.Wins.WL05 as WL05
import Examples.Groups.Clifford+CS.Five.Wins.WL06 as WL06
import Examples.Groups.Clifford+CS.Five.Wins.WL07 as WL07
import Examples.Groups.Clifford+CS.Five.Wins.WL08 as WL08
import Examples.Groups.Clifford+CS.Five.Wins.WL09 as WL09

wsL : Complete 4 → WsL
wsL c4 =
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
                        (WL05.wl1023 c4)
                        pleaf
                      )
                      (WL03.wl0511 c4)
                      (pnode
                        pleaf
                        (WL08.wl1535 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0255 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1279 c4)
                        pleaf
                      )
                      (WL04.wl0767 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0127 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1151 c4)
                        pleaf
                      )
                      (WL03.wl0639 c4)
                      (pnode
                        pleaf
                        (WL08.wl1663 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0383 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1407 c4)
                        pleaf
                      )
                      (WL04.wl0895 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0063 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1087 c4)
                        pleaf
                      )
                      (WL03.wl0575 c4)
                      (pnode
                        pleaf
                        (WL08.wl1599 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0319 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1343 c4)
                        pleaf
                      )
                      (WL04.wl0831 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0191 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1215 c4)
                        pleaf
                      )
                      (WL04.wl0703 c4)
                      (pnode
                        pleaf
                        (WL09.wl1727 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0447 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1471 c4)
                        pleaf
                      )
                      (WL05.wl0959 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0031 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1055 c4)
                        pleaf
                      )
                      (WL03.wl0543 c4)
                      (pnode
                        pleaf
                        (WL08.wl1567 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0287 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1311 c4)
                        pleaf
                      )
                      (WL04.wl0799 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0159 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1183 c4)
                        pleaf
                      )
                      (WL03.wl0671 c4)
                      (pnode
                        pleaf
                        (WL08.wl1695 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0415 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1439 c4)
                        pleaf
                      )
                      (WL04.wl0927 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0095 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1119 c4)
                        pleaf
                      )
                      (WL03.wl0607 c4)
                      (pnode
                        pleaf
                        (WL08.wl1631 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0351 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1375 c4)
                        pleaf
                      )
                      (WL04.wl0863 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0223 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1247 c4)
                        pleaf
                      )
                      (WL04.wl0735 c4)
                      pleaf
                    )
                    (WL02.wl0479 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1503 c4)
                        pleaf
                      )
                      (WL05.wl0991 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0015 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1039 c4)
                        pleaf
                      )
                      (WL03.wl0527 c4)
                      (pnode
                        pleaf
                        (WL08.wl1551 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0271 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1295 c4)
                        pleaf
                      )
                      (WL04.wl0783 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0143 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1167 c4)
                        pleaf
                      )
                      (WL03.wl0655 c4)
                      (pnode
                        pleaf
                        (WL08.wl1679 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0399 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1423 c4)
                        pleaf
                      )
                      (WL04.wl0911 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0079 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1103 c4)
                        pleaf
                      )
                      (WL03.wl0591 c4)
                      (pnode
                        pleaf
                        (WL08.wl1615 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0335 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1359 c4)
                        pleaf
                      )
                      (WL04.wl0847 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0207 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1231 c4)
                        pleaf
                      )
                      (WL04.wl0719 c4)
                      pleaf
                    )
                    (WL02.wl0463 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1487 c4)
                        pleaf
                      )
                      (WL05.wl0975 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0047 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1071 c4)
                        pleaf
                      )
                      (WL03.wl0559 c4)
                      (pnode
                        pleaf
                        (WL08.wl1583 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0303 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1327 c4)
                        pleaf
                      )
                      (WL04.wl0815 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0175 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1199 c4)
                        pleaf
                      )
                      (WL03.wl0687 c4)
                      (pnode
                        pleaf
                        (WL08.wl1711 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0431 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1455 c4)
                        pleaf
                      )
                      (WL05.wl0943 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0111 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1135 c4)
                        pleaf
                      )
                      (WL03.wl0623 c4)
                      (pnode
                        pleaf
                        (WL08.wl1647 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0367 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1391 c4)
                        pleaf
                      )
                      (WL04.wl0879 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0239 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1263 c4)
                        pleaf
                      )
                      (WL04.wl0751 c4)
                      pleaf
                    )
                    (WL02.wl0495 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1519 c4)
                        pleaf
                      )
                      (WL05.wl1007 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
          (WL01.wl0007 c4)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1031 c4)
                        pleaf
                      )
                      (WL03.wl0519 c4)
                      (pnode
                        pleaf
                        (WL08.wl1543 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0263 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1287 c4)
                        pleaf
                      )
                      (WL04.wl0775 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0135 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1159 c4)
                        pleaf
                      )
                      (WL03.wl0647 c4)
                      (pnode
                        pleaf
                        (WL08.wl1671 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0391 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1415 c4)
                        pleaf
                      )
                      (WL04.wl0903 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0071 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1095 c4)
                        pleaf
                      )
                      (WL03.wl0583 c4)
                      (pnode
                        pleaf
                        (WL08.wl1607 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0327 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1351 c4)
                        pleaf
                      )
                      (WL04.wl0839 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0199 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1223 c4)
                        pleaf
                      )
                      (WL04.wl0711 c4)
                      (pnode
                        pleaf
                        (WL09.wl1735 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0455 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1479 c4)
                        pleaf
                      )
                      (WL05.wl0967 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0039 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1063 c4)
                        pleaf
                      )
                      (WL03.wl0551 c4)
                      (pnode
                        pleaf
                        (WL08.wl1575 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0295 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1319 c4)
                        pleaf
                      )
                      (WL04.wl0807 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0167 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1191 c4)
                        pleaf
                      )
                      (WL03.wl0679 c4)
                      (pnode
                        pleaf
                        (WL08.wl1703 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0423 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1447 c4)
                        pleaf
                      )
                      (WL05.wl0935 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0103 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1127 c4)
                        pleaf
                      )
                      (WL03.wl0615 c4)
                      (pnode
                        pleaf
                        (WL08.wl1639 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0359 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1383 c4)
                        pleaf
                      )
                      (WL04.wl0871 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0231 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1255 c4)
                        pleaf
                      )
                      (WL04.wl0743 c4)
                      pleaf
                    )
                    (WL02.wl0487 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1511 c4)
                        pleaf
                      )
                      (WL05.wl0999 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0023 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1047 c4)
                        pleaf
                      )
                      (WL03.wl0535 c4)
                      (pnode
                        pleaf
                        (WL08.wl1559 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0279 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1303 c4)
                        pleaf
                      )
                      (WL04.wl0791 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0151 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1175 c4)
                        pleaf
                      )
                      (WL03.wl0663 c4)
                      (pnode
                        pleaf
                        (WL08.wl1687 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0407 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1431 c4)
                        pleaf
                      )
                      (WL04.wl0919 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0087 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1111 c4)
                        pleaf
                      )
                      (WL03.wl0599 c4)
                      (pnode
                        pleaf
                        (WL08.wl1623 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0343 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1367 c4)
                        pleaf
                      )
                      (WL04.wl0855 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0215 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1239 c4)
                        pleaf
                      )
                      (WL04.wl0727 c4)
                      pleaf
                    )
                    (WL02.wl0471 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1495 c4)
                        pleaf
                      )
                      (WL05.wl0983 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0055 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1079 c4)
                        pleaf
                      )
                      (WL03.wl0567 c4)
                      (pnode
                        pleaf
                        (WL08.wl1591 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0311 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1335 c4)
                        pleaf
                      )
                      (WL04.wl0823 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0183 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1207 c4)
                        pleaf
                      )
                      (WL03.wl0695 c4)
                      (pnode
                        pleaf
                        (WL09.wl1719 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0439 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1463 c4)
                        pleaf
                      )
                      (WL05.wl0951 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0119 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1143 c4)
                        pleaf
                      )
                      (WL03.wl0631 c4)
                      (pnode
                        pleaf
                        (WL08.wl1655 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0375 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1399 c4)
                        pleaf
                      )
                      (WL04.wl0887 c4)
                      pleaf
                    )
                  )
                  (WL02.wl0247 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1271 c4)
                        pleaf
                      )
                      (WL04.wl0759 c4)
                      pleaf
                    )
                    (WL02.wl0503 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1527 c4)
                        pleaf
                      )
                      (WL05.wl1015 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
        )
        (WL01.wl0003 c4)
        (pnode
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1027 c4)
                        pleaf
                      )
                      (WL03.wl0515 c4)
                      (pnode
                        pleaf
                        (WL08.wl1539 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0259 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1283 c4)
                        pleaf
                      )
                      (WL04.wl0771 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0131 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1155 c4)
                        pleaf
                      )
                      (WL03.wl0643 c4)
                      (pnode
                        pleaf
                        (WL08.wl1667 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0387 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1411 c4)
                        pleaf
                      )
                      (WL04.wl0899 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0067 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1091 c4)
                        pleaf
                      )
                      (WL03.wl0579 c4)
                      (pnode
                        pleaf
                        (WL08.wl1603 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0323 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1347 c4)
                        pleaf
                      )
                      (WL04.wl0835 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0195 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1219 c4)
                        pleaf
                      )
                      (WL04.wl0707 c4)
                      (pnode
                        pleaf
                        (WL09.wl1731 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0451 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1475 c4)
                        pleaf
                      )
                      (WL05.wl0963 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0035 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1059 c4)
                        pleaf
                      )
                      (WL03.wl0547 c4)
                      (pnode
                        pleaf
                        (WL08.wl1571 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0291 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1315 c4)
                        pleaf
                      )
                      (WL04.wl0803 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0163 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1187 c4)
                        pleaf
                      )
                      (WL03.wl0675 c4)
                      (pnode
                        pleaf
                        (WL08.wl1699 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0419 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1443 c4)
                        pleaf
                      )
                      (WL05.wl0931 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0099 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1123 c4)
                        pleaf
                      )
                      (WL03.wl0611 c4)
                      (pnode
                        pleaf
                        (WL08.wl1635 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0355 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1379 c4)
                        pleaf
                      )
                      (WL04.wl0867 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0227 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1251 c4)
                        pleaf
                      )
                      (WL04.wl0739 c4)
                      pleaf
                    )
                    (WL02.wl0483 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1507 c4)
                        pleaf
                      )
                      (WL05.wl0995 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0019 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1043 c4)
                        pleaf
                      )
                      (WL03.wl0531 c4)
                      (pnode
                        pleaf
                        (WL08.wl1555 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0275 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1299 c4)
                        pleaf
                      )
                      (WL04.wl0787 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0147 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1171 c4)
                        pleaf
                      )
                      (WL03.wl0659 c4)
                      (pnode
                        pleaf
                        (WL08.wl1683 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0403 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1427 c4)
                        pleaf
                      )
                      (WL04.wl0915 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0083 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1107 c4)
                        pleaf
                      )
                      (WL03.wl0595 c4)
                      (pnode
                        pleaf
                        (WL08.wl1619 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0339 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1363 c4)
                        pleaf
                      )
                      (WL04.wl0851 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0211 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1235 c4)
                        pleaf
                      )
                      (WL04.wl0723 c4)
                      pleaf
                    )
                    (WL02.wl0467 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1491 c4)
                        pleaf
                      )
                      (WL05.wl0979 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0051 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1075 c4)
                        pleaf
                      )
                      (WL03.wl0563 c4)
                      (pnode
                        pleaf
                        (WL08.wl1587 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0307 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1331 c4)
                        pleaf
                      )
                      (WL04.wl0819 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0179 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1203 c4)
                        pleaf
                      )
                      (WL03.wl0691 c4)
                      (pnode
                        pleaf
                        (WL09.wl1715 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0435 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1459 c4)
                        pleaf
                      )
                      (WL05.wl0947 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0115 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1139 c4)
                        pleaf
                      )
                      (WL03.wl0627 c4)
                      (pnode
                        pleaf
                        (WL08.wl1651 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0371 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1395 c4)
                        pleaf
                      )
                      (WL04.wl0883 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0243 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1267 c4)
                        pleaf
                      )
                      (WL04.wl0755 c4)
                      pleaf
                    )
                    (WL02.wl0499 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1523 c4)
                        pleaf
                      )
                      (WL05.wl1011 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
          (WL01.wl0011 c4)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1035 c4)
                        pleaf
                      )
                      (WL03.wl0523 c4)
                      (pnode
                        pleaf
                        (WL08.wl1547 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0267 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1291 c4)
                        pleaf
                      )
                      (WL04.wl0779 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0139 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1163 c4)
                        pleaf
                      )
                      (WL03.wl0651 c4)
                      (pnode
                        pleaf
                        (WL08.wl1675 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0395 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1419 c4)
                        pleaf
                      )
                      (WL04.wl0907 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0075 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1099 c4)
                        pleaf
                      )
                      (WL03.wl0587 c4)
                      (pnode
                        pleaf
                        (WL08.wl1611 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0331 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1355 c4)
                        pleaf
                      )
                      (WL04.wl0843 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0203 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1227 c4)
                        pleaf
                      )
                      (WL04.wl0715 c4)
                      (pnode
                        pleaf
                        (WL09.wl1739 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0459 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1483 c4)
                        pleaf
                      )
                      (WL05.wl0971 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0043 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1067 c4)
                        pleaf
                      )
                      (WL03.wl0555 c4)
                      (pnode
                        pleaf
                        (WL08.wl1579 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0299 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1323 c4)
                        pleaf
                      )
                      (WL04.wl0811 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0171 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1195 c4)
                        pleaf
                      )
                      (WL03.wl0683 c4)
                      (pnode
                        pleaf
                        (WL08.wl1707 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0427 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1451 c4)
                        pleaf
                      )
                      (WL05.wl0939 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0107 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1131 c4)
                        pleaf
                      )
                      (WL03.wl0619 c4)
                      (pnode
                        pleaf
                        (WL08.wl1643 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0363 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1387 c4)
                        pleaf
                      )
                      (WL04.wl0875 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0235 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1259 c4)
                        pleaf
                      )
                      (WL04.wl0747 c4)
                      pleaf
                    )
                    (WL02.wl0491 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1515 c4)
                        pleaf
                      )
                      (WL05.wl1003 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0027 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1051 c4)
                        pleaf
                      )
                      (WL03.wl0539 c4)
                      (pnode
                        pleaf
                        (WL08.wl1563 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0283 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1307 c4)
                        pleaf
                      )
                      (WL04.wl0795 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0155 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1179 c4)
                        pleaf
                      )
                      (WL03.wl0667 c4)
                      (pnode
                        pleaf
                        (WL08.wl1691 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0411 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1435 c4)
                        pleaf
                      )
                      (WL04.wl0923 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0091 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1115 c4)
                        pleaf
                      )
                      (WL03.wl0603 c4)
                      (pnode
                        pleaf
                        (WL08.wl1627 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0347 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1371 c4)
                        pleaf
                      )
                      (WL04.wl0859 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0219 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1243 c4)
                        pleaf
                      )
                      (WL04.wl0731 c4)
                      pleaf
                    )
                    (WL02.wl0475 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1499 c4)
                        pleaf
                      )
                      (WL05.wl0987 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0059 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1083 c4)
                        pleaf
                      )
                      (WL03.wl0571 c4)
                      (pnode
                        pleaf
                        (WL08.wl1595 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0315 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1339 c4)
                        pleaf
                      )
                      (WL04.wl0827 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0187 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1211 c4)
                        pleaf
                      )
                      (WL03.wl0699 c4)
                      (pnode
                        pleaf
                        (WL09.wl1723 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0443 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1467 c4)
                        pleaf
                      )
                      (WL05.wl0955 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0123 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1147 c4)
                        pleaf
                      )
                      (WL03.wl0635 c4)
                      (pnode
                        pleaf
                        (WL08.wl1659 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0379 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1403 c4)
                        pleaf
                      )
                      (WL04.wl0891 c4)
                      pleaf
                    )
                  )
                  (WL02.wl0251 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1275 c4)
                        pleaf
                      )
                      (WL04.wl0763 c4)
                      pleaf
                    )
                    (WL03.wl0507 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1531 c4)
                        pleaf
                      )
                      (WL05.wl1019 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (WL01.wl0001 c4)
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
                        (WL05.wl1025 c4)
                        pleaf
                      )
                      (WL03.wl0513 c4)
                      (pnode
                        pleaf
                        (WL08.wl1537 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0257 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1281 c4)
                        pleaf
                      )
                      (WL04.wl0769 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0129 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1153 c4)
                        pleaf
                      )
                      (WL03.wl0641 c4)
                      (pnode
                        pleaf
                        (WL08.wl1665 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0385 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1409 c4)
                        pleaf
                      )
                      (WL04.wl0897 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0065 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1089 c4)
                        pleaf
                      )
                      (WL03.wl0577 c4)
                      (pnode
                        pleaf
                        (WL08.wl1601 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0321 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1345 c4)
                        pleaf
                      )
                      (WL04.wl0833 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0193 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1217 c4)
                        pleaf
                      )
                      (WL04.wl0705 c4)
                      (pnode
                        pleaf
                        (WL09.wl1729 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0449 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1473 c4)
                        pleaf
                      )
                      (WL05.wl0961 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0033 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1057 c4)
                        pleaf
                      )
                      (WL03.wl0545 c4)
                      (pnode
                        pleaf
                        (WL08.wl1569 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0289 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1313 c4)
                        pleaf
                      )
                      (WL04.wl0801 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0161 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1185 c4)
                        pleaf
                      )
                      (WL03.wl0673 c4)
                      (pnode
                        pleaf
                        (WL08.wl1697 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0417 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1441 c4)
                        pleaf
                      )
                      (WL04.wl0929 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0097 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1121 c4)
                        pleaf
                      )
                      (WL03.wl0609 c4)
                      (pnode
                        pleaf
                        (WL08.wl1633 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0353 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1377 c4)
                        pleaf
                      )
                      (WL04.wl0865 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0225 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1249 c4)
                        pleaf
                      )
                      (WL04.wl0737 c4)
                      pleaf
                    )
                    (WL02.wl0481 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1505 c4)
                        pleaf
                      )
                      (WL05.wl0993 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0017 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1041 c4)
                        pleaf
                      )
                      (WL03.wl0529 c4)
                      (pnode
                        pleaf
                        (WL08.wl1553 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0273 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1297 c4)
                        pleaf
                      )
                      (WL04.wl0785 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0145 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1169 c4)
                        pleaf
                      )
                      (WL03.wl0657 c4)
                      (pnode
                        pleaf
                        (WL08.wl1681 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0401 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1425 c4)
                        pleaf
                      )
                      (WL04.wl0913 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0081 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1105 c4)
                        pleaf
                      )
                      (WL03.wl0593 c4)
                      (pnode
                        pleaf
                        (WL08.wl1617 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0337 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1361 c4)
                        pleaf
                      )
                      (WL04.wl0849 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0209 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1233 c4)
                        pleaf
                      )
                      (WL04.wl0721 c4)
                      pleaf
                    )
                    (WL02.wl0465 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1489 c4)
                        pleaf
                      )
                      (WL05.wl0977 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0049 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1073 c4)
                        pleaf
                      )
                      (WL03.wl0561 c4)
                      (pnode
                        pleaf
                        (WL08.wl1585 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0305 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1329 c4)
                        pleaf
                      )
                      (WL04.wl0817 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0177 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1201 c4)
                        pleaf
                      )
                      (WL03.wl0689 c4)
                      (pnode
                        pleaf
                        (WL09.wl1713 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0433 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1457 c4)
                        pleaf
                      )
                      (WL05.wl0945 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0113 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1137 c4)
                        pleaf
                      )
                      (WL03.wl0625 c4)
                      (pnode
                        pleaf
                        (WL08.wl1649 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0369 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1393 c4)
                        pleaf
                      )
                      (WL04.wl0881 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0241 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1265 c4)
                        pleaf
                      )
                      (WL04.wl0753 c4)
                      pleaf
                    )
                    (WL02.wl0497 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1521 c4)
                        pleaf
                      )
                      (WL05.wl1009 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
          (WL01.wl0009 c4)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1033 c4)
                        pleaf
                      )
                      (WL03.wl0521 c4)
                      (pnode
                        pleaf
                        (WL08.wl1545 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0265 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1289 c4)
                        pleaf
                      )
                      (WL04.wl0777 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0137 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1161 c4)
                        pleaf
                      )
                      (WL03.wl0649 c4)
                      (pnode
                        pleaf
                        (WL08.wl1673 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0393 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1417 c4)
                        pleaf
                      )
                      (WL04.wl0905 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0073 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1097 c4)
                        pleaf
                      )
                      (WL03.wl0585 c4)
                      (pnode
                        pleaf
                        (WL08.wl1609 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0329 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1353 c4)
                        pleaf
                      )
                      (WL04.wl0841 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0201 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1225 c4)
                        pleaf
                      )
                      (WL04.wl0713 c4)
                      (pnode
                        pleaf
                        (WL09.wl1737 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0457 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1481 c4)
                        pleaf
                      )
                      (WL05.wl0969 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0041 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1065 c4)
                        pleaf
                      )
                      (WL03.wl0553 c4)
                      (pnode
                        pleaf
                        (WL08.wl1577 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0297 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1321 c4)
                        pleaf
                      )
                      (WL04.wl0809 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0169 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1193 c4)
                        pleaf
                      )
                      (WL03.wl0681 c4)
                      (pnode
                        pleaf
                        (WL08.wl1705 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0425 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1449 c4)
                        pleaf
                      )
                      (WL05.wl0937 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0105 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1129 c4)
                        pleaf
                      )
                      (WL03.wl0617 c4)
                      (pnode
                        pleaf
                        (WL08.wl1641 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0361 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1385 c4)
                        pleaf
                      )
                      (WL04.wl0873 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0233 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1257 c4)
                        pleaf
                      )
                      (WL04.wl0745 c4)
                      pleaf
                    )
                    (WL02.wl0489 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1513 c4)
                        pleaf
                      )
                      (WL05.wl1001 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0025 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1049 c4)
                        pleaf
                      )
                      (WL03.wl0537 c4)
                      (pnode
                        pleaf
                        (WL08.wl1561 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0281 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1305 c4)
                        pleaf
                      )
                      (WL04.wl0793 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0153 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1177 c4)
                        pleaf
                      )
                      (WL03.wl0665 c4)
                      (pnode
                        pleaf
                        (WL08.wl1689 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0409 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1433 c4)
                        pleaf
                      )
                      (WL04.wl0921 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0089 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1113 c4)
                        pleaf
                      )
                      (WL03.wl0601 c4)
                      (pnode
                        pleaf
                        (WL08.wl1625 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0345 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1369 c4)
                        pleaf
                      )
                      (WL04.wl0857 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0217 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1241 c4)
                        pleaf
                      )
                      (WL04.wl0729 c4)
                      pleaf
                    )
                    (WL02.wl0473 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1497 c4)
                        pleaf
                      )
                      (WL05.wl0985 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0057 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1081 c4)
                        pleaf
                      )
                      (WL03.wl0569 c4)
                      (pnode
                        pleaf
                        (WL08.wl1593 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0313 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1337 c4)
                        pleaf
                      )
                      (WL04.wl0825 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0185 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1209 c4)
                        pleaf
                      )
                      (WL03.wl0697 c4)
                      (pnode
                        pleaf
                        (WL09.wl1721 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0441 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1465 c4)
                        pleaf
                      )
                      (WL05.wl0953 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0121 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1145 c4)
                        pleaf
                      )
                      (WL03.wl0633 c4)
                      (pnode
                        pleaf
                        (WL08.wl1657 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0377 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1401 c4)
                        pleaf
                      )
                      (WL04.wl0889 c4)
                      pleaf
                    )
                  )
                  (WL02.wl0249 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1273 c4)
                        pleaf
                      )
                      (WL04.wl0761 c4)
                      pleaf
                    )
                    (WL03.wl0505 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1529 c4)
                        pleaf
                      )
                      (WL05.wl1017 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
        )
        (WL01.wl0005 c4)
        (pnode
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1029 c4)
                        pleaf
                      )
                      (WL03.wl0517 c4)
                      (pnode
                        pleaf
                        (WL08.wl1541 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0261 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1285 c4)
                        pleaf
                      )
                      (WL04.wl0773 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0133 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1157 c4)
                        pleaf
                      )
                      (WL03.wl0645 c4)
                      (pnode
                        pleaf
                        (WL08.wl1669 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0389 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1413 c4)
                        pleaf
                      )
                      (WL04.wl0901 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0069 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1093 c4)
                        pleaf
                      )
                      (WL03.wl0581 c4)
                      (pnode
                        pleaf
                        (WL08.wl1605 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0325 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1349 c4)
                        pleaf
                      )
                      (WL04.wl0837 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0197 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1221 c4)
                        pleaf
                      )
                      (WL04.wl0709 c4)
                      (pnode
                        pleaf
                        (WL09.wl1733 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0453 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1477 c4)
                        pleaf
                      )
                      (WL05.wl0965 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0037 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1061 c4)
                        pleaf
                      )
                      (WL03.wl0549 c4)
                      (pnode
                        pleaf
                        (WL08.wl1573 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0293 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1317 c4)
                        pleaf
                      )
                      (WL04.wl0805 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0165 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1189 c4)
                        pleaf
                      )
                      (WL03.wl0677 c4)
                      (pnode
                        pleaf
                        (WL08.wl1701 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0421 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1445 c4)
                        pleaf
                      )
                      (WL05.wl0933 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0101 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1125 c4)
                        pleaf
                      )
                      (WL03.wl0613 c4)
                      (pnode
                        pleaf
                        (WL08.wl1637 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0357 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1381 c4)
                        pleaf
                      )
                      (WL04.wl0869 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0229 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1253 c4)
                        pleaf
                      )
                      (WL04.wl0741 c4)
                      pleaf
                    )
                    (WL02.wl0485 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1509 c4)
                        pleaf
                      )
                      (WL05.wl0997 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0021 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1045 c4)
                        pleaf
                      )
                      (WL03.wl0533 c4)
                      (pnode
                        pleaf
                        (WL08.wl1557 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0277 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1301 c4)
                        pleaf
                      )
                      (WL04.wl0789 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0149 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1173 c4)
                        pleaf
                      )
                      (WL03.wl0661 c4)
                      (pnode
                        pleaf
                        (WL08.wl1685 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0405 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1429 c4)
                        pleaf
                      )
                      (WL04.wl0917 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0085 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1109 c4)
                        pleaf
                      )
                      (WL03.wl0597 c4)
                      (pnode
                        pleaf
                        (WL08.wl1621 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0341 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1365 c4)
                        pleaf
                      )
                      (WL04.wl0853 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0213 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1237 c4)
                        pleaf
                      )
                      (WL04.wl0725 c4)
                      pleaf
                    )
                    (WL02.wl0469 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1493 c4)
                        pleaf
                      )
                      (WL05.wl0981 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0053 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1077 c4)
                        pleaf
                      )
                      (WL03.wl0565 c4)
                      (pnode
                        pleaf
                        (WL08.wl1589 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0309 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1333 c4)
                        pleaf
                      )
                      (WL04.wl0821 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0181 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1205 c4)
                        pleaf
                      )
                      (WL03.wl0693 c4)
                      (pnode
                        pleaf
                        (WL09.wl1717 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0437 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1461 c4)
                        pleaf
                      )
                      (WL05.wl0949 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0117 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1141 c4)
                        pleaf
                      )
                      (WL03.wl0629 c4)
                      (pnode
                        pleaf
                        (WL08.wl1653 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0373 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1397 c4)
                        pleaf
                      )
                      (WL04.wl0885 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0245 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1269 c4)
                        pleaf
                      )
                      (WL04.wl0757 c4)
                      pleaf
                    )
                    (WL02.wl0501 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1525 c4)
                        pleaf
                      )
                      (WL05.wl1013 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
          (WL01.wl0013 c4)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1037 c4)
                        pleaf
                      )
                      (WL03.wl0525 c4)
                      (pnode
                        pleaf
                        (WL08.wl1549 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0269 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1293 c4)
                        pleaf
                      )
                      (WL04.wl0781 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0141 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1165 c4)
                        pleaf
                      )
                      (WL03.wl0653 c4)
                      (pnode
                        pleaf
                        (WL08.wl1677 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0397 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1421 c4)
                        pleaf
                      )
                      (WL04.wl0909 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0077 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1101 c4)
                        pleaf
                      )
                      (WL03.wl0589 c4)
                      (pnode
                        pleaf
                        (WL08.wl1613 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0333 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1357 c4)
                        pleaf
                      )
                      (WL04.wl0845 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0205 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1229 c4)
                        pleaf
                      )
                      (WL04.wl0717 c4)
                      pleaf
                    )
                    (WL02.wl0461 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1485 c4)
                        pleaf
                      )
                      (WL05.wl0973 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0045 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1069 c4)
                        pleaf
                      )
                      (WL03.wl0557 c4)
                      (pnode
                        pleaf
                        (WL08.wl1581 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0301 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1325 c4)
                        pleaf
                      )
                      (WL04.wl0813 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0173 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1197 c4)
                        pleaf
                      )
                      (WL03.wl0685 c4)
                      (pnode
                        pleaf
                        (WL08.wl1709 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0429 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1453 c4)
                        pleaf
                      )
                      (WL05.wl0941 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0109 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1133 c4)
                        pleaf
                      )
                      (WL03.wl0621 c4)
                      (pnode
                        pleaf
                        (WL08.wl1645 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0365 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1389 c4)
                        pleaf
                      )
                      (WL04.wl0877 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0237 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1261 c4)
                        pleaf
                      )
                      (WL04.wl0749 c4)
                      pleaf
                    )
                    (WL02.wl0493 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1517 c4)
                        pleaf
                      )
                      (WL05.wl1005 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0029 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1053 c4)
                        pleaf
                      )
                      (WL03.wl0541 c4)
                      (pnode
                        pleaf
                        (WL08.wl1565 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0285 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1309 c4)
                        pleaf
                      )
                      (WL04.wl0797 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0157 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1181 c4)
                        pleaf
                      )
                      (WL03.wl0669 c4)
                      (pnode
                        pleaf
                        (WL08.wl1693 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0413 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1437 c4)
                        pleaf
                      )
                      (WL04.wl0925 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0093 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1117 c4)
                        pleaf
                      )
                      (WL03.wl0605 c4)
                      (pnode
                        pleaf
                        (WL08.wl1629 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0349 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1373 c4)
                        pleaf
                      )
                      (WL04.wl0861 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0221 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1245 c4)
                        pleaf
                      )
                      (WL04.wl0733 c4)
                      pleaf
                    )
                    (WL02.wl0477 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1501 c4)
                        pleaf
                      )
                      (WL05.wl0989 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0061 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1085 c4)
                        pleaf
                      )
                      (WL03.wl0573 c4)
                      (pnode
                        pleaf
                        (WL08.wl1597 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0317 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1341 c4)
                        pleaf
                      )
                      (WL04.wl0829 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0189 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1213 c4)
                        pleaf
                      )
                      (WL04.wl0701 c4)
                      (pnode
                        pleaf
                        (WL09.wl1725 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0445 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1469 c4)
                        pleaf
                      )
                      (WL05.wl0957 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0125 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1149 c4)
                        pleaf
                      )
                      (WL03.wl0637 c4)
                      (pnode
                        pleaf
                        (WL08.wl1661 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0381 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1405 c4)
                        pleaf
                      )
                      (WL04.wl0893 c4)
                      pleaf
                    )
                  )
                  (WL02.wl0253 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1277 c4)
                        pleaf
                      )
                      (WL04.wl0765 c4)
                      pleaf
                    )
                    (WL03.wl0509 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1533 c4)
                        pleaf
                      )
                      (WL05.wl1021 c4)
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
                        (WL05.wl1024 c4)
                        pleaf
                      )
                      (WL03.wl0512 c4)
                      (pnode
                        pleaf
                        (WL08.wl1536 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0256 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1280 c4)
                        pleaf
                      )
                      (WL04.wl0768 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0128 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1152 c4)
                        pleaf
                      )
                      (WL03.wl0640 c4)
                      (pnode
                        pleaf
                        (WL08.wl1664 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0384 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1408 c4)
                        pleaf
                      )
                      (WL04.wl0896 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0064 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1088 c4)
                        pleaf
                      )
                      (WL03.wl0576 c4)
                      (pnode
                        pleaf
                        (WL08.wl1600 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0320 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1344 c4)
                        pleaf
                      )
                      (WL04.wl0832 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0192 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1216 c4)
                        pleaf
                      )
                      (WL04.wl0704 c4)
                      (pnode
                        pleaf
                        (WL09.wl1728 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0448 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1472 c4)
                        pleaf
                      )
                      (WL05.wl0960 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0032 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1056 c4)
                        pleaf
                      )
                      (WL03.wl0544 c4)
                      (pnode
                        pleaf
                        (WL08.wl1568 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0288 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1312 c4)
                        pleaf
                      )
                      (WL04.wl0800 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0160 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1184 c4)
                        pleaf
                      )
                      (WL03.wl0672 c4)
                      (pnode
                        pleaf
                        (WL08.wl1696 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0416 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1440 c4)
                        pleaf
                      )
                      (WL04.wl0928 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0096 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1120 c4)
                        pleaf
                      )
                      (WL03.wl0608 c4)
                      (pnode
                        pleaf
                        (WL08.wl1632 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0352 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1376 c4)
                        pleaf
                      )
                      (WL04.wl0864 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0224 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1248 c4)
                        pleaf
                      )
                      (WL04.wl0736 c4)
                      pleaf
                    )
                    (WL02.wl0480 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1504 c4)
                        pleaf
                      )
                      (WL05.wl0992 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0016 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1040 c4)
                        pleaf
                      )
                      (WL03.wl0528 c4)
                      (pnode
                        pleaf
                        (WL08.wl1552 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0272 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1296 c4)
                        pleaf
                      )
                      (WL04.wl0784 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0144 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1168 c4)
                        pleaf
                      )
                      (WL03.wl0656 c4)
                      (pnode
                        pleaf
                        (WL08.wl1680 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0400 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1424 c4)
                        pleaf
                      )
                      (WL04.wl0912 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0080 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1104 c4)
                        pleaf
                      )
                      (WL03.wl0592 c4)
                      (pnode
                        pleaf
                        (WL08.wl1616 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0336 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1360 c4)
                        pleaf
                      )
                      (WL04.wl0848 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0208 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1232 c4)
                        pleaf
                      )
                      (WL04.wl0720 c4)
                      pleaf
                    )
                    (WL02.wl0464 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1488 c4)
                        pleaf
                      )
                      (WL05.wl0976 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0048 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1072 c4)
                        pleaf
                      )
                      (WL03.wl0560 c4)
                      (pnode
                        pleaf
                        (WL08.wl1584 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0304 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1328 c4)
                        pleaf
                      )
                      (WL04.wl0816 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0176 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1200 c4)
                        pleaf
                      )
                      (WL03.wl0688 c4)
                      (pnode
                        pleaf
                        (WL09.wl1712 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0432 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1456 c4)
                        pleaf
                      )
                      (WL05.wl0944 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0112 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1136 c4)
                        pleaf
                      )
                      (WL03.wl0624 c4)
                      (pnode
                        pleaf
                        (WL08.wl1648 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0368 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1392 c4)
                        pleaf
                      )
                      (WL04.wl0880 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0240 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1264 c4)
                        pleaf
                      )
                      (WL04.wl0752 c4)
                      pleaf
                    )
                    (WL02.wl0496 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1520 c4)
                        pleaf
                      )
                      (WL05.wl1008 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
          (WL01.wl0008 c4)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1032 c4)
                        pleaf
                      )
                      (WL03.wl0520 c4)
                      (pnode
                        pleaf
                        (WL08.wl1544 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0264 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1288 c4)
                        pleaf
                      )
                      (WL04.wl0776 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0136 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1160 c4)
                        pleaf
                      )
                      (WL03.wl0648 c4)
                      (pnode
                        pleaf
                        (WL08.wl1672 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0392 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1416 c4)
                        pleaf
                      )
                      (WL04.wl0904 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0072 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1096 c4)
                        pleaf
                      )
                      (WL03.wl0584 c4)
                      (pnode
                        pleaf
                        (WL08.wl1608 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0328 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1352 c4)
                        pleaf
                      )
                      (WL04.wl0840 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0200 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1224 c4)
                        pleaf
                      )
                      (WL04.wl0712 c4)
                      (pnode
                        pleaf
                        (WL09.wl1736 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0456 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1480 c4)
                        pleaf
                      )
                      (WL05.wl0968 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0040 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1064 c4)
                        pleaf
                      )
                      (WL03.wl0552 c4)
                      (pnode
                        pleaf
                        (WL08.wl1576 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0296 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1320 c4)
                        pleaf
                      )
                      (WL04.wl0808 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0168 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1192 c4)
                        pleaf
                      )
                      (WL03.wl0680 c4)
                      (pnode
                        pleaf
                        (WL08.wl1704 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0424 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1448 c4)
                        pleaf
                      )
                      (WL05.wl0936 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0104 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1128 c4)
                        pleaf
                      )
                      (WL03.wl0616 c4)
                      (pnode
                        pleaf
                        (WL08.wl1640 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0360 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1384 c4)
                        pleaf
                      )
                      (WL04.wl0872 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0232 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1256 c4)
                        pleaf
                      )
                      (WL04.wl0744 c4)
                      pleaf
                    )
                    (WL02.wl0488 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1512 c4)
                        pleaf
                      )
                      (WL05.wl1000 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0024 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1048 c4)
                        pleaf
                      )
                      (WL03.wl0536 c4)
                      (pnode
                        pleaf
                        (WL08.wl1560 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0280 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1304 c4)
                        pleaf
                      )
                      (WL04.wl0792 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0152 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1176 c4)
                        pleaf
                      )
                      (WL03.wl0664 c4)
                      (pnode
                        pleaf
                        (WL08.wl1688 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0408 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1432 c4)
                        pleaf
                      )
                      (WL04.wl0920 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0088 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1112 c4)
                        pleaf
                      )
                      (WL03.wl0600 c4)
                      (pnode
                        pleaf
                        (WL08.wl1624 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0344 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1368 c4)
                        pleaf
                      )
                      (WL04.wl0856 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0216 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1240 c4)
                        pleaf
                      )
                      (WL04.wl0728 c4)
                      pleaf
                    )
                    (WL02.wl0472 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1496 c4)
                        pleaf
                      )
                      (WL05.wl0984 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0056 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1080 c4)
                        pleaf
                      )
                      (WL03.wl0568 c4)
                      (pnode
                        pleaf
                        (WL08.wl1592 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0312 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1336 c4)
                        pleaf
                      )
                      (WL04.wl0824 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0184 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1208 c4)
                        pleaf
                      )
                      (WL03.wl0696 c4)
                      (pnode
                        pleaf
                        (WL09.wl1720 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0440 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1464 c4)
                        pleaf
                      )
                      (WL05.wl0952 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0120 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1144 c4)
                        pleaf
                      )
                      (WL03.wl0632 c4)
                      (pnode
                        pleaf
                        (WL08.wl1656 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0376 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1400 c4)
                        pleaf
                      )
                      (WL04.wl0888 c4)
                      pleaf
                    )
                  )
                  (WL02.wl0248 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1272 c4)
                        pleaf
                      )
                      (WL04.wl0760 c4)
                      pleaf
                    )
                    (WL02.wl0504 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1528 c4)
                        pleaf
                      )
                      (WL05.wl1016 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
        )
        (WL01.wl0004 c4)
        (pnode
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1028 c4)
                        pleaf
                      )
                      (WL03.wl0516 c4)
                      (pnode
                        pleaf
                        (WL08.wl1540 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0260 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1284 c4)
                        pleaf
                      )
                      (WL04.wl0772 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0132 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1156 c4)
                        pleaf
                      )
                      (WL03.wl0644 c4)
                      (pnode
                        pleaf
                        (WL08.wl1668 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0388 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1412 c4)
                        pleaf
                      )
                      (WL04.wl0900 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0068 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1092 c4)
                        pleaf
                      )
                      (WL03.wl0580 c4)
                      (pnode
                        pleaf
                        (WL08.wl1604 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0324 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1348 c4)
                        pleaf
                      )
                      (WL04.wl0836 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0196 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1220 c4)
                        pleaf
                      )
                      (WL04.wl0708 c4)
                      (pnode
                        pleaf
                        (WL09.wl1732 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0452 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1476 c4)
                        pleaf
                      )
                      (WL05.wl0964 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0036 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1060 c4)
                        pleaf
                      )
                      (WL03.wl0548 c4)
                      (pnode
                        pleaf
                        (WL08.wl1572 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0292 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1316 c4)
                        pleaf
                      )
                      (WL04.wl0804 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0164 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1188 c4)
                        pleaf
                      )
                      (WL03.wl0676 c4)
                      (pnode
                        pleaf
                        (WL08.wl1700 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0420 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1444 c4)
                        pleaf
                      )
                      (WL05.wl0932 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0100 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1124 c4)
                        pleaf
                      )
                      (WL03.wl0612 c4)
                      (pnode
                        pleaf
                        (WL08.wl1636 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0356 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1380 c4)
                        pleaf
                      )
                      (WL04.wl0868 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0228 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1252 c4)
                        pleaf
                      )
                      (WL04.wl0740 c4)
                      pleaf
                    )
                    (WL02.wl0484 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1508 c4)
                        pleaf
                      )
                      (WL05.wl0996 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0020 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1044 c4)
                        pleaf
                      )
                      (WL03.wl0532 c4)
                      (pnode
                        pleaf
                        (WL08.wl1556 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0276 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1300 c4)
                        pleaf
                      )
                      (WL04.wl0788 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0148 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1172 c4)
                        pleaf
                      )
                      (WL03.wl0660 c4)
                      (pnode
                        pleaf
                        (WL08.wl1684 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0404 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1428 c4)
                        pleaf
                      )
                      (WL04.wl0916 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0084 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1108 c4)
                        pleaf
                      )
                      (WL03.wl0596 c4)
                      (pnode
                        pleaf
                        (WL08.wl1620 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0340 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1364 c4)
                        pleaf
                      )
                      (WL04.wl0852 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0212 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1236 c4)
                        pleaf
                      )
                      (WL04.wl0724 c4)
                      pleaf
                    )
                    (WL02.wl0468 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1492 c4)
                        pleaf
                      )
                      (WL05.wl0980 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0052 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1076 c4)
                        pleaf
                      )
                      (WL03.wl0564 c4)
                      (pnode
                        pleaf
                        (WL08.wl1588 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0308 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1332 c4)
                        pleaf
                      )
                      (WL04.wl0820 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0180 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1204 c4)
                        pleaf
                      )
                      (WL03.wl0692 c4)
                      (pnode
                        pleaf
                        (WL09.wl1716 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0436 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1460 c4)
                        pleaf
                      )
                      (WL05.wl0948 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0116 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1140 c4)
                        pleaf
                      )
                      (WL03.wl0628 c4)
                      (pnode
                        pleaf
                        (WL08.wl1652 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0372 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1396 c4)
                        pleaf
                      )
                      (WL04.wl0884 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0244 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1268 c4)
                        pleaf
                      )
                      (WL04.wl0756 c4)
                      pleaf
                    )
                    (WL02.wl0500 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1524 c4)
                        pleaf
                      )
                      (WL05.wl1012 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
          (WL01.wl0012 c4)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1036 c4)
                        pleaf
                      )
                      (WL03.wl0524 c4)
                      (pnode
                        pleaf
                        (WL08.wl1548 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0268 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1292 c4)
                        pleaf
                      )
                      (WL04.wl0780 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0140 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1164 c4)
                        pleaf
                      )
                      (WL03.wl0652 c4)
                      (pnode
                        pleaf
                        (WL08.wl1676 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0396 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1420 c4)
                        pleaf
                      )
                      (WL04.wl0908 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0076 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1100 c4)
                        pleaf
                      )
                      (WL03.wl0588 c4)
                      (pnode
                        pleaf
                        (WL08.wl1612 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0332 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1356 c4)
                        pleaf
                      )
                      (WL04.wl0844 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0204 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1228 c4)
                        pleaf
                      )
                      (WL04.wl0716 c4)
                      pleaf
                    )
                    (WL02.wl0460 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1484 c4)
                        pleaf
                      )
                      (WL05.wl0972 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0044 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1068 c4)
                        pleaf
                      )
                      (WL03.wl0556 c4)
                      (pnode
                        pleaf
                        (WL08.wl1580 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0300 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1324 c4)
                        pleaf
                      )
                      (WL04.wl0812 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0172 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1196 c4)
                        pleaf
                      )
                      (WL03.wl0684 c4)
                      (pnode
                        pleaf
                        (WL08.wl1708 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0428 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1452 c4)
                        pleaf
                      )
                      (WL05.wl0940 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0108 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1132 c4)
                        pleaf
                      )
                      (WL03.wl0620 c4)
                      (pnode
                        pleaf
                        (WL08.wl1644 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0364 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1388 c4)
                        pleaf
                      )
                      (WL04.wl0876 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0236 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1260 c4)
                        pleaf
                      )
                      (WL04.wl0748 c4)
                      pleaf
                    )
                    (WL02.wl0492 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1516 c4)
                        pleaf
                      )
                      (WL05.wl1004 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0028 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1052 c4)
                        pleaf
                      )
                      (WL03.wl0540 c4)
                      (pnode
                        pleaf
                        (WL08.wl1564 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0284 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1308 c4)
                        pleaf
                      )
                      (WL04.wl0796 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0156 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1180 c4)
                        pleaf
                      )
                      (WL03.wl0668 c4)
                      (pnode
                        pleaf
                        (WL08.wl1692 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0412 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1436 c4)
                        pleaf
                      )
                      (WL04.wl0924 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0092 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1116 c4)
                        pleaf
                      )
                      (WL03.wl0604 c4)
                      (pnode
                        pleaf
                        (WL08.wl1628 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0348 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1372 c4)
                        pleaf
                      )
                      (WL04.wl0860 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0220 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1244 c4)
                        pleaf
                      )
                      (WL04.wl0732 c4)
                      pleaf
                    )
                    (WL02.wl0476 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1500 c4)
                        pleaf
                      )
                      (WL05.wl0988 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0060 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1084 c4)
                        pleaf
                      )
                      (WL03.wl0572 c4)
                      (pnode
                        pleaf
                        (WL08.wl1596 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0316 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1340 c4)
                        pleaf
                      )
                      (WL04.wl0828 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0188 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1212 c4)
                        pleaf
                      )
                      (WL03.wl0700 c4)
                      (pnode
                        pleaf
                        (WL09.wl1724 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0444 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1468 c4)
                        pleaf
                      )
                      (WL05.wl0956 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0124 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1148 c4)
                        pleaf
                      )
                      (WL03.wl0636 c4)
                      (pnode
                        pleaf
                        (WL08.wl1660 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0380 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1404 c4)
                        pleaf
                      )
                      (WL04.wl0892 c4)
                      pleaf
                    )
                  )
                  (WL02.wl0252 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1276 c4)
                        pleaf
                      )
                      (WL04.wl0764 c4)
                      pleaf
                    )
                    (WL03.wl0508 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1532 c4)
                        pleaf
                      )
                      (WL05.wl1020 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
        )
      )
      (WL01.wl0002 c4)
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
                        (WL05.wl1026 c4)
                        pleaf
                      )
                      (WL03.wl0514 c4)
                      (pnode
                        pleaf
                        (WL08.wl1538 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0258 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1282 c4)
                        pleaf
                      )
                      (WL04.wl0770 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0130 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1154 c4)
                        pleaf
                      )
                      (WL03.wl0642 c4)
                      (pnode
                        pleaf
                        (WL08.wl1666 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0386 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1410 c4)
                        pleaf
                      )
                      (WL04.wl0898 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0066 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1090 c4)
                        pleaf
                      )
                      (WL03.wl0578 c4)
                      (pnode
                        pleaf
                        (WL08.wl1602 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0322 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1346 c4)
                        pleaf
                      )
                      (WL04.wl0834 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0194 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1218 c4)
                        pleaf
                      )
                      (WL04.wl0706 c4)
                      (pnode
                        pleaf
                        (WL09.wl1730 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0450 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1474 c4)
                        pleaf
                      )
                      (WL05.wl0962 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0034 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1058 c4)
                        pleaf
                      )
                      (WL03.wl0546 c4)
                      (pnode
                        pleaf
                        (WL08.wl1570 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0290 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1314 c4)
                        pleaf
                      )
                      (WL04.wl0802 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0162 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1186 c4)
                        pleaf
                      )
                      (WL03.wl0674 c4)
                      (pnode
                        pleaf
                        (WL08.wl1698 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0418 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1442 c4)
                        pleaf
                      )
                      (WL05.wl0930 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0098 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1122 c4)
                        pleaf
                      )
                      (WL03.wl0610 c4)
                      (pnode
                        pleaf
                        (WL08.wl1634 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0354 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1378 c4)
                        pleaf
                      )
                      (WL04.wl0866 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0226 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1250 c4)
                        pleaf
                      )
                      (WL04.wl0738 c4)
                      pleaf
                    )
                    (WL02.wl0482 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1506 c4)
                        pleaf
                      )
                      (WL05.wl0994 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0018 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1042 c4)
                        pleaf
                      )
                      (WL03.wl0530 c4)
                      (pnode
                        pleaf
                        (WL08.wl1554 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0274 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1298 c4)
                        pleaf
                      )
                      (WL04.wl0786 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0146 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1170 c4)
                        pleaf
                      )
                      (WL03.wl0658 c4)
                      (pnode
                        pleaf
                        (WL08.wl1682 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0402 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1426 c4)
                        pleaf
                      )
                      (WL04.wl0914 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0082 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1106 c4)
                        pleaf
                      )
                      (WL03.wl0594 c4)
                      (pnode
                        pleaf
                        (WL08.wl1618 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0338 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1362 c4)
                        pleaf
                      )
                      (WL04.wl0850 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0210 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1234 c4)
                        pleaf
                      )
                      (WL04.wl0722 c4)
                      pleaf
                    )
                    (WL02.wl0466 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1490 c4)
                        pleaf
                      )
                      (WL05.wl0978 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0050 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1074 c4)
                        pleaf
                      )
                      (WL03.wl0562 c4)
                      (pnode
                        pleaf
                        (WL08.wl1586 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0306 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1330 c4)
                        pleaf
                      )
                      (WL04.wl0818 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0178 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1202 c4)
                        pleaf
                      )
                      (WL03.wl0690 c4)
                      (pnode
                        pleaf
                        (WL09.wl1714 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0434 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1458 c4)
                        pleaf
                      )
                      (WL05.wl0946 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0114 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1138 c4)
                        pleaf
                      )
                      (WL03.wl0626 c4)
                      (pnode
                        pleaf
                        (WL08.wl1650 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0370 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1394 c4)
                        pleaf
                      )
                      (WL04.wl0882 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0242 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1266 c4)
                        pleaf
                      )
                      (WL04.wl0754 c4)
                      pleaf
                    )
                    (WL02.wl0498 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1522 c4)
                        pleaf
                      )
                      (WL05.wl1010 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
          (WL01.wl0010 c4)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1034 c4)
                        pleaf
                      )
                      (WL03.wl0522 c4)
                      (pnode
                        pleaf
                        (WL08.wl1546 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0266 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1290 c4)
                        pleaf
                      )
                      (WL04.wl0778 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0138 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1162 c4)
                        pleaf
                      )
                      (WL03.wl0650 c4)
                      (pnode
                        pleaf
                        (WL08.wl1674 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0394 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1418 c4)
                        pleaf
                      )
                      (WL04.wl0906 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0074 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1098 c4)
                        pleaf
                      )
                      (WL03.wl0586 c4)
                      (pnode
                        pleaf
                        (WL08.wl1610 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0330 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1354 c4)
                        pleaf
                      )
                      (WL04.wl0842 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0202 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1226 c4)
                        pleaf
                      )
                      (WL04.wl0714 c4)
                      (pnode
                        pleaf
                        (WL09.wl1738 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0458 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1482 c4)
                        pleaf
                      )
                      (WL05.wl0970 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0042 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1066 c4)
                        pleaf
                      )
                      (WL03.wl0554 c4)
                      (pnode
                        pleaf
                        (WL08.wl1578 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0298 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1322 c4)
                        pleaf
                      )
                      (WL04.wl0810 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0170 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1194 c4)
                        pleaf
                      )
                      (WL03.wl0682 c4)
                      (pnode
                        pleaf
                        (WL08.wl1706 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0426 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1450 c4)
                        pleaf
                      )
                      (WL05.wl0938 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0106 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1130 c4)
                        pleaf
                      )
                      (WL03.wl0618 c4)
                      (pnode
                        pleaf
                        (WL08.wl1642 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0362 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1386 c4)
                        pleaf
                      )
                      (WL04.wl0874 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0234 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1258 c4)
                        pleaf
                      )
                      (WL04.wl0746 c4)
                      pleaf
                    )
                    (WL02.wl0490 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1514 c4)
                        pleaf
                      )
                      (WL05.wl1002 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0026 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1050 c4)
                        pleaf
                      )
                      (WL03.wl0538 c4)
                      (pnode
                        pleaf
                        (WL08.wl1562 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0282 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1306 c4)
                        pleaf
                      )
                      (WL04.wl0794 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0154 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1178 c4)
                        pleaf
                      )
                      (WL03.wl0666 c4)
                      (pnode
                        pleaf
                        (WL08.wl1690 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0410 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1434 c4)
                        pleaf
                      )
                      (WL04.wl0922 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0090 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1114 c4)
                        pleaf
                      )
                      (WL03.wl0602 c4)
                      (pnode
                        pleaf
                        (WL08.wl1626 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0346 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1370 c4)
                        pleaf
                      )
                      (WL04.wl0858 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0218 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1242 c4)
                        pleaf
                      )
                      (WL04.wl0730 c4)
                      pleaf
                    )
                    (WL02.wl0474 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1498 c4)
                        pleaf
                      )
                      (WL05.wl0986 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0058 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1082 c4)
                        pleaf
                      )
                      (WL03.wl0570 c4)
                      (pnode
                        pleaf
                        (WL08.wl1594 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0314 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1338 c4)
                        pleaf
                      )
                      (WL04.wl0826 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0186 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1210 c4)
                        pleaf
                      )
                      (WL03.wl0698 c4)
                      (pnode
                        pleaf
                        (WL09.wl1722 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0442 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1466 c4)
                        pleaf
                      )
                      (WL05.wl0954 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0122 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1146 c4)
                        pleaf
                      )
                      (WL03.wl0634 c4)
                      (pnode
                        pleaf
                        (WL08.wl1658 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0378 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1402 c4)
                        pleaf
                      )
                      (WL04.wl0890 c4)
                      pleaf
                    )
                  )
                  (WL02.wl0250 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1274 c4)
                        pleaf
                      )
                      (WL04.wl0762 c4)
                      pleaf
                    )
                    (WL03.wl0506 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1530 c4)
                        pleaf
                      )
                      (WL05.wl1018 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
        )
        (WL01.wl0006 c4)
        (pnode
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1030 c4)
                        pleaf
                      )
                      (WL03.wl0518 c4)
                      (pnode
                        pleaf
                        (WL08.wl1542 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0262 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1286 c4)
                        pleaf
                      )
                      (WL04.wl0774 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0134 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1158 c4)
                        pleaf
                      )
                      (WL03.wl0646 c4)
                      (pnode
                        pleaf
                        (WL08.wl1670 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0390 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1414 c4)
                        pleaf
                      )
                      (WL04.wl0902 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0070 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1094 c4)
                        pleaf
                      )
                      (WL03.wl0582 c4)
                      (pnode
                        pleaf
                        (WL08.wl1606 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0326 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1350 c4)
                        pleaf
                      )
                      (WL04.wl0838 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0198 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1222 c4)
                        pleaf
                      )
                      (WL04.wl0710 c4)
                      (pnode
                        pleaf
                        (WL09.wl1734 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0454 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1478 c4)
                        pleaf
                      )
                      (WL05.wl0966 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0038 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1062 c4)
                        pleaf
                      )
                      (WL03.wl0550 c4)
                      (pnode
                        pleaf
                        (WL08.wl1574 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0294 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1318 c4)
                        pleaf
                      )
                      (WL04.wl0806 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0166 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1190 c4)
                        pleaf
                      )
                      (WL03.wl0678 c4)
                      (pnode
                        pleaf
                        (WL08.wl1702 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0422 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1446 c4)
                        pleaf
                      )
                      (WL05.wl0934 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0102 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1126 c4)
                        pleaf
                      )
                      (WL03.wl0614 c4)
                      (pnode
                        pleaf
                        (WL08.wl1638 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0358 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1382 c4)
                        pleaf
                      )
                      (WL04.wl0870 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0230 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1254 c4)
                        pleaf
                      )
                      (WL04.wl0742 c4)
                      pleaf
                    )
                    (WL02.wl0486 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1510 c4)
                        pleaf
                      )
                      (WL05.wl0998 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0022 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1046 c4)
                        pleaf
                      )
                      (WL03.wl0534 c4)
                      (pnode
                        pleaf
                        (WL08.wl1558 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0278 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1302 c4)
                        pleaf
                      )
                      (WL04.wl0790 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0150 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1174 c4)
                        pleaf
                      )
                      (WL03.wl0662 c4)
                      (pnode
                        pleaf
                        (WL08.wl1686 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0406 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1430 c4)
                        pleaf
                      )
                      (WL04.wl0918 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0086 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1110 c4)
                        pleaf
                      )
                      (WL03.wl0598 c4)
                      (pnode
                        pleaf
                        (WL08.wl1622 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0342 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1366 c4)
                        pleaf
                      )
                      (WL04.wl0854 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0214 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1238 c4)
                        pleaf
                      )
                      (WL04.wl0726 c4)
                      pleaf
                    )
                    (WL02.wl0470 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1494 c4)
                        pleaf
                      )
                      (WL05.wl0982 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0054 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1078 c4)
                        pleaf
                      )
                      (WL03.wl0566 c4)
                      (pnode
                        pleaf
                        (WL08.wl1590 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0310 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1334 c4)
                        pleaf
                      )
                      (WL04.wl0822 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0182 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1206 c4)
                        pleaf
                      )
                      (WL03.wl0694 c4)
                      (pnode
                        pleaf
                        (WL09.wl1718 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0438 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1462 c4)
                        pleaf
                      )
                      (WL05.wl0950 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0118 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1142 c4)
                        pleaf
                      )
                      (WL03.wl0630 c4)
                      (pnode
                        pleaf
                        (WL08.wl1654 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0374 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1398 c4)
                        pleaf
                      )
                      (WL04.wl0886 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0246 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1270 c4)
                        pleaf
                      )
                      (WL04.wl0758 c4)
                      pleaf
                    )
                    (WL02.wl0502 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1526 c4)
                        pleaf
                      )
                      (WL05.wl1014 c4)
                      pleaf
                    )
                  )
                )
              )
            )
          )
          (WL01.wl0014 c4)
          (pnode
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1038 c4)
                        pleaf
                      )
                      (WL03.wl0526 c4)
                      (pnode
                        pleaf
                        (WL08.wl1550 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0270 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1294 c4)
                        pleaf
                      )
                      (WL04.wl0782 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0142 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1166 c4)
                        pleaf
                      )
                      (WL03.wl0654 c4)
                      (pnode
                        pleaf
                        (WL08.wl1678 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0398 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1422 c4)
                        pleaf
                      )
                      (WL04.wl0910 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0078 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1102 c4)
                        pleaf
                      )
                      (WL03.wl0590 c4)
                      (pnode
                        pleaf
                        (WL08.wl1614 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0334 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1358 c4)
                        pleaf
                      )
                      (WL04.wl0846 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0206 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1230 c4)
                        pleaf
                      )
                      (WL04.wl0718 c4)
                      pleaf
                    )
                    (WL02.wl0462 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1486 c4)
                        pleaf
                      )
                      (WL05.wl0974 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0046 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1070 c4)
                        pleaf
                      )
                      (WL03.wl0558 c4)
                      (pnode
                        pleaf
                        (WL08.wl1582 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0302 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1326 c4)
                        pleaf
                      )
                      (WL04.wl0814 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0174 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1198 c4)
                        pleaf
                      )
                      (WL03.wl0686 c4)
                      (pnode
                        pleaf
                        (WL08.wl1710 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0430 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1454 c4)
                        pleaf
                      )
                      (WL05.wl0942 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0110 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1134 c4)
                        pleaf
                      )
                      (WL03.wl0622 c4)
                      (pnode
                        pleaf
                        (WL08.wl1646 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0366 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1390 c4)
                        pleaf
                      )
                      (WL04.wl0878 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0238 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1262 c4)
                        pleaf
                      )
                      (WL04.wl0750 c4)
                      pleaf
                    )
                    (WL02.wl0494 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1518 c4)
                        pleaf
                      )
                      (WL05.wl1006 c4)
                      pleaf
                    )
                  )
                )
              )
            )
            (WL01.wl0030 c4)
            (pnode
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1054 c4)
                        pleaf
                      )
                      (WL03.wl0542 c4)
                      (pnode
                        pleaf
                        (WL08.wl1566 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0286 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1310 c4)
                        pleaf
                      )
                      (WL04.wl0798 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0158 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1182 c4)
                        pleaf
                      )
                      (WL03.wl0670 c4)
                      (pnode
                        pleaf
                        (WL08.wl1694 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0414 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1438 c4)
                        pleaf
                      )
                      (WL04.wl0926 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0094 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1118 c4)
                        pleaf
                      )
                      (WL03.wl0606 c4)
                      (pnode
                        pleaf
                        (WL08.wl1630 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0350 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1374 c4)
                        pleaf
                      )
                      (WL04.wl0862 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0222 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1246 c4)
                        pleaf
                      )
                      (WL04.wl0734 c4)
                      pleaf
                    )
                    (WL02.wl0478 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1502 c4)
                        pleaf
                      )
                      (WL05.wl0990 c4)
                      pleaf
                    )
                  )
                )
              )
              (WL01.wl0062 c4)
              (pnode
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL05.wl1086 c4)
                        pleaf
                      )
                      (WL03.wl0574 c4)
                      (pnode
                        pleaf
                        (WL08.wl1598 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0318 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1342 c4)
                        pleaf
                      )
                      (WL04.wl0830 c4)
                      pleaf
                    )
                  )
                  (WL01.wl0190 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1214 c4)
                        pleaf
                      )
                      (WL04.wl0702 c4)
                      (pnode
                        pleaf
                        (WL09.wl1726 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0446 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1470 c4)
                        pleaf
                      )
                      (WL05.wl0958 c4)
                      pleaf
                    )
                  )
                )
                (WL01.wl0126 c4)
                (pnode
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1150 c4)
                        pleaf
                      )
                      (WL03.wl0638 c4)
                      (pnode
                        pleaf
                        (WL08.wl1662 c4)
                        pleaf
                      )
                    )
                    (WL02.wl0382 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL07.wl1406 c4)
                        pleaf
                      )
                      (WL04.wl0894 c4)
                      pleaf
                    )
                  )
                  (WL02.wl0254 c4)
                  (pnode
                    (pnode
                      (pnode
                        pleaf
                        (WL06.wl1278 c4)
                        pleaf
                      )
                      (WL04.wl0766 c4)
                      pleaf
                    )
                    (WL03.wl0510 c4)
                    (pnode
                      (pnode
                        pleaf
                        (WL08.wl1534 c4)
                        pleaf
                      )
                      (WL05.wl1022 c4)
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
