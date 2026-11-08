{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Soundness where

open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
import Examples.Groups.CCX+HH-3qubit.Checks.R001 as R001
import Examples.Groups.CCX+HH-3qubit.Checks.R002 as R002
import Examples.Groups.CCX+HH-3qubit.Checks.R003 as R003
import Examples.Groups.CCX+HH-3qubit.Checks.R004 as R004
import Examples.Groups.CCX+HH-3qubit.Checks.R005 as R005
import Examples.Groups.CCX+HH-3qubit.Checks.R006 as R006
import Examples.Groups.CCX+HH-3qubit.Checks.R007 as R007
import Examples.Groups.CCX+HH-3qubit.Checks.R008 as R008
import Examples.Groups.CCX+HH-3qubit.Checks.R009 as R009
import Examples.Groups.CCX+HH-3qubit.Checks.R010 as R010
import Examples.Groups.CCX+HH-3qubit.Checks.R011 as R011
import Examples.Groups.CCX+HH-3qubit.Checks.R012 as R012
import Examples.Groups.CCX+HH-3qubit.Checks.R013 as R013
import Examples.Groups.CCX+HH-3qubit.Checks.R014 as R014
import Examples.Groups.CCX+HH-3qubit.Checks.R015 as R015
import Examples.Groups.CCX+HH-3qubit.Checks.R016 as R016
import Examples.Groups.CCX+HH-3qubit.Checks.R017 as R017
import Examples.Groups.CCX+HH-3qubit.Checks.R018 as R018
import Examples.Groups.CCX+HH-3qubit.Checks.R019 as R019
import Examples.Groups.CCX+HH-3qubit.Checks.R020 as R020
import Examples.Groups.CCX+HH-3qubit.Checks.R021 as R021
import Examples.Groups.CCX+HH-3qubit.Checks.R022 as R022
import Examples.Groups.CCX+HH-3qubit.Checks.R023 as R023
import Examples.Groups.CCX+HH-3qubit.Checks.R024 as R024
import Examples.Groups.CCX+HH-3qubit.Checks.R025 as R025
import Examples.Groups.CCX+HH-3qubit.Checks.R026 as R026
import Examples.Groups.CCX+HH-3qubit.Checks.R027 as R027
import Examples.Groups.CCX+HH-3qubit.Checks.R028 as R028
import Examples.Groups.CCX+HH-3qubit.Checks.R029 as R029
import Examples.Groups.CCX+HH-3qubit.Checks.R030 as R030
import Examples.Groups.CCX+HH-3qubit.Checks.R031 as R031
import Examples.Groups.CCX+HH-3qubit.Checks.R032 as R032
import Examples.Groups.CCX+HH-3qubit.Checks.R033 as R033
import Examples.Groups.CCX+HH-3qubit.Checks.R034 as R034
import Examples.Groups.CCX+HH-3qubit.Checks.R035 as R035
import Examples.Groups.CCX+HH-3qubit.Checks.R036 as R036
import Examples.Groups.CCX+HH-3qubit.Checks.R037 as R037
import Examples.Groups.CCX+HH-3qubit.Checks.R038 as R038
import Examples.Groups.CCX+HH-3qubit.Checks.R039 as R039
import Examples.Groups.CCX+HH-3qubit.Checks.R040 as R040
import Examples.Groups.CCX+HH-3qubit.Checks.R041 as R041
import Examples.Groups.CCX+HH-3qubit.Checks.R042 as R042
import Examples.Groups.CCX+HH-3qubit.Checks.R043 as R043
import Examples.Groups.CCX+HH-3qubit.Checks.R044 as R044
import Examples.Groups.CCX+HH-3qubit.Checks.R045 as R045
import Examples.Groups.CCX+HH-3qubit.Checks.R046 as R046
import Examples.Groups.CCX+HH-3qubit.Checks.R083 as R083
import Examples.Groups.CCX+HH-3qubit.Checks.R084 as R084
import Examples.Groups.CCX+HH-3qubit.Checks.R085 as R085
import Examples.Groups.CCX+HH-3qubit.Checks.R086 as R086
import Examples.Groups.CCX+HH-3qubit.Checks.R087 as R087
import Examples.Groups.CCX+HH-3qubit.Checks.R088 as R088
import Examples.Groups.CCX+HH-3qubit.Checks.R089 as R089
import Examples.Groups.CCX+HH-3qubit.Checks.R090 as R090
import Examples.Groups.CCX+HH-3qubit.Checks.R091 as R091
import Examples.Groups.CCX+HH-3qubit.Checks.R092 as R092
import Examples.Groups.CCX+HH-3qubit.Checks.R093 as R093
import Examples.Groups.CCX+HH-3qubit.Checks.R094 as R094
import Examples.Groups.CCX+HH-3qubit.Checks.R095 as R095
import Examples.Groups.CCX+HH-3qubit.Checks.R096 as R096
import Examples.Groups.CCX+HH-3qubit.Checks.R097 as R097
import Examples.Groups.CCX+HH-3qubit.Checks.R098 as R098
import Examples.Groups.CCX+HH-3qubit.Checks.R099 as R099
import Examples.Groups.CCX+HH-3qubit.Checks.R100 as R100
import Examples.Groups.CCX+HH-3qubit.Checks.R101 as R101
import Examples.Groups.CCX+HH-3qubit.Checks.R102 as R102
import Examples.Groups.CCX+HH-3qubit.Checks.R103 as R103
import Examples.Groups.CCX+HH-3qubit.Checks.R104 as R104
import Examples.Groups.CCX+HH-3qubit.Checks.R105 as R105
import Examples.Groups.CCX+HH-3qubit.Checks.R106 as R106
import Examples.Groups.CCX+HH-3qubit.Checks.R107 as R107
import Examples.Groups.CCX+HH-3qubit.Checks.R108 as R108

axiom-sound : ∀ {w v} → w === v → ⟦ w ⟧ ~ ⟦ v ⟧
axiom-sound r001 = by-matrix R001.checked
axiom-sound r002 = by-matrix R002.checked
axiom-sound r003 = by-matrix R003.checked
axiom-sound r004 = by-matrix R004.checked
axiom-sound r005 = by-matrix R005.checked
axiom-sound r006 = by-matrix R006.checked
axiom-sound r007 = by-matrix R007.checked
axiom-sound r008 = by-matrix R008.checked
axiom-sound r009 = by-matrix R009.checked
axiom-sound r010 = by-matrix R010.checked
axiom-sound r011 = by-matrix R011.checked
axiom-sound r012 = by-matrix R012.checked
axiom-sound r013 = by-matrix R013.checked
axiom-sound r014 = by-matrix R014.checked
axiom-sound r015 = by-matrix R015.checked
axiom-sound r016 = by-matrix R016.checked
axiom-sound r017 = by-matrix R017.checked
axiom-sound r018 = by-matrix R018.checked
axiom-sound r019 = by-matrix R019.checked
axiom-sound r020 = by-matrix R020.checked
axiom-sound r021 = by-matrix R021.checked
axiom-sound r022 = by-matrix R022.checked
axiom-sound r023 = by-matrix R023.checked
axiom-sound r024 = by-matrix R024.checked
axiom-sound r025 = by-matrix R025.checked
axiom-sound r026 = by-matrix R026.checked
axiom-sound r027 = by-matrix R027.checked
axiom-sound r028 = by-matrix R028.checked
axiom-sound r029 = by-matrix R029.checked
axiom-sound r030 = by-matrix R030.checked
axiom-sound r031 = by-matrix R031.checked
axiom-sound r032 = by-matrix R032.checked
axiom-sound r033 = by-matrix R033.checked
axiom-sound r034 = by-matrix R034.checked
axiom-sound r035 = by-matrix R035.checked
axiom-sound r036 = by-matrix R036.checked
axiom-sound r037 = by-matrix R037.checked
axiom-sound r038 = by-matrix R038.checked
axiom-sound r039 = by-matrix R039.checked
axiom-sound r040 = by-matrix R040.checked
axiom-sound r041 = by-matrix R041.checked
axiom-sound r042 = by-matrix R042.checked
axiom-sound r043 = by-matrix R043.checked
axiom-sound r044 = by-matrix R044.checked
axiom-sound r045 = by-matrix R045.checked
axiom-sound r046 = by-matrix R046.checked
axiom-sound r083 = by-matrix R083.checked
axiom-sound r084 = by-matrix R084.checked
axiom-sound r085 = by-matrix R085.checked
axiom-sound r086 = by-matrix R086.checked
axiom-sound r087 = by-matrix R087.checked
axiom-sound r088 = by-matrix R088.checked
axiom-sound r089 = by-matrix R089.checked
axiom-sound r090 = by-matrix R090.checked
axiom-sound r091 = by-matrix R091.checked
axiom-sound r092 = by-matrix R092.checked
axiom-sound r093 = by-matrix R093.checked
axiom-sound r094 = by-matrix R094.checked
axiom-sound r095 = by-matrix R095.checked
axiom-sound r096 = by-matrix R096.checked
axiom-sound r097 = by-matrix R097.checked
axiom-sound r098 = by-matrix R098.checked
axiom-sound r099 = by-matrix R099.checked
axiom-sound r100 = by-matrix R100.checked
axiom-sound r101 = by-matrix R101.checked
axiom-sound r102 = by-matrix R102.checked
axiom-sound r103 = by-matrix R103.checked
axiom-sound r104 = by-matrix R104.checked
axiom-sound r105 = by-matrix R105.checked
axiom-sound r106 = by-matrix R106.checked
axiom-sound r107 = by-matrix R107.checked
axiom-sound r108 = by-matrix R108.checked

sound : ∀ {w v} → w ≈ v → ⟦ w ⟧ ~ ⟦ v ⟧
sound = sound-from axiom-sound
