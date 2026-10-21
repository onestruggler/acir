{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; X25 ; X26 ; X27 ; X34 ; X35 ; X36 ; X37 ; X45 ; X46 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00213)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00008)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B018 using (module PE00957 ; module PE00958 ; module PE00959 ; module PE00960 ; module PE00961 ; module PE00962 ; module PE00963 ; module PE00964 ; module PE00965 ; module PE00966 ; module PE00967 ; module PE00968 ; module PE00969 ; module PE00970 ; module PE00971 ; module PE00972 ; module PE00973 ; module PE00974 ; module PE00975 ; module PE00976 ; module PE00977 ; module PE00978 ; module PE00979 ; module PE00980 ; module PE00981 ; module PE00982)

module r1a_ij01 where

  proved : X01 • X01 ≈ ε
  proved = by-assoc-and PE00008.proved Eq.refl Eq.refl

module r1a_ij02 where

  proved : X02 • X02 ≈ ε
  proved = by-assoc-and PE00957.proved Eq.refl Eq.refl

module r1a_ij03 where

  proved : X03 • X03 ≈ ε
  proved = by-assoc-and PE00958.proved Eq.refl Eq.refl

module r1a_ij04 where

  proved : X04 • X04 ≈ ε
  proved = by-assoc-and PE00959.proved Eq.refl Eq.refl

module r1a_ij05 where

  proved : X05 • X05 ≈ ε
  proved = by-assoc-and PE00960.proved Eq.refl Eq.refl

module r1a_ij06 where

  proved : X06 • X06 ≈ ε
  proved = by-assoc-and PE00961.proved Eq.refl Eq.refl

module r1a_ij07 where

  proved : X07 • X07 ≈ ε
  proved = by-assoc-and PE00962.proved Eq.refl Eq.refl

module r1a_ij12 where

  proved : X12 • X12 ≈ ε
  proved = by-assoc-and PE00963.proved Eq.refl Eq.refl

module r1a_ij13 where

  proved : X13 • X13 ≈ ε
  proved = by-assoc-and PE00964.proved Eq.refl Eq.refl

module r1a_ij14 where

  proved : X14 • X14 ≈ ε
  proved = by-assoc-and PE00965.proved Eq.refl Eq.refl

module r1a_ij15 where

  proved : X15 • X15 ≈ ε
  proved = by-assoc-and PE00966.proved Eq.refl Eq.refl

module r1a_ij16 where

  proved : X16 • X16 ≈ ε
  proved = by-assoc-and PE00967.proved Eq.refl Eq.refl

module r1a_ij17 where

  proved : X17 • X17 ≈ ε
  proved = by-assoc-and PE00968.proved Eq.refl Eq.refl

module r1a_ij23 where

  proved : X23 • X23 ≈ ε
  proved = by-assoc-and PE00969.proved Eq.refl Eq.refl

module r1a_ij24 where

  proved : X24 • X24 ≈ ε
  proved = by-assoc-and PE00970.proved Eq.refl Eq.refl

module r1a_ij25 where

  proved : X25 • X25 ≈ ε
  proved = by-assoc-and PE00971.proved Eq.refl Eq.refl

module r1a_ij26 where

  proved : X26 • X26 ≈ ε
  proved = by-assoc-and PE00972.proved Eq.refl Eq.refl

module r1a_ij27 where

  proved : X27 • X27 ≈ ε
  proved = by-assoc-and PE00973.proved Eq.refl Eq.refl

module r1a_ij34 where

  proved : X34 • X34 ≈ ε
  proved = by-assoc-and PE00213.proved Eq.refl Eq.refl

module r1a_ij35 where

  proved : X35 • X35 ≈ ε
  proved = by-assoc-and PE00974.proved Eq.refl Eq.refl

module r1a_ij36 where

  proved : X36 • X36 ≈ ε
  proved = by-assoc-and PE00975.proved Eq.refl Eq.refl

module r1a_ij37 where

  proved : X37 • X37 ≈ ε
  proved = by-assoc-and PE00976.proved Eq.refl Eq.refl

module r1a_ij45 where

  proved : X45 • X45 ≈ ε
  proved = by-assoc-and PE00977.proved Eq.refl Eq.refl

module r1a_ij46 where

  proved : X46 • X46 ≈ ε
  proved = by-assoc-and PE00978.proved Eq.refl Eq.refl

module r1a_ij47 where

  proved : X47 • X47 ≈ ε
  proved = by-assoc-and PE00979.proved Eq.refl Eq.refl

module r1a_ij56 where

  proved : X56 • X56 ≈ ε
  proved = by-assoc-and PE00980.proved Eq.refl Eq.refl

module r1a_ij57 where

  proved : X57 • X57 ≈ ε
  proved = by-assoc-and PE00981.proved Eq.refl Eq.refl

module r1a_ij67 where

  proved : X67 • X67 ≈ ε
  proved = by-assoc-and PE00982.proved Eq.refl Eq.refl
