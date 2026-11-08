{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.GroupLike where

open import Data.Product.Base using (_,_ )
open import Relation.Binary.PropositionalEquality as Eq
open import Presentation.GroupLike using (Grouplike)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Invertible
open import Presentation.Base _===_ hiding (_===_ ; _≈_)
open import Presentation.Properties _===_ using (by-assoc)

iX0 : Invertible X0
iX0 = invol (axiom r021)

iCX01 : Invertible CX01
iCX01 = invol (axiom r022)

iK12 : Invertible K12
iK12 = invol (axiom r023)

iCCX12 : Invertible CCX12
iCCX12 = invol (axiom r024)

iNK : Invertible NK
iNK = invol (axiom r084)

iH2 : Invertible H2
iH2 = invol (axiom r108)

iCZ01 : Invertible CZ01
iCZ01 = along (axiom r001) (product iK12 (product iCX01 iK12))

iX1 : Invertible X1
iX1 = along (axiom r002) (product iCX01 (product iX0 (product iCX01 iX0)))

iZ0 : Invertible Z0
iZ0 = along (axiom r003) (product iCZ01 (product iCX01 (product iCZ01 iCX01)))

iZ1 : Invertible Z1
iZ1 = along (axiom r004) (product iK12 (product iX1 iK12))

iCX20 : Invertible CX20
iCX20 = along (axiom r005) (product iX1 (product iCCX12 (product iX1 iCCX12)))

iCX21 : Invertible CX21
iCX21 = along (axiom r006) (product iCX20 (product iCX01 (product iCX20 iCX01)))

iCX12 : Invertible CX12
iCX12 = along (axiom r007) (product iK12 (product iCX21 iK12))

iSWAP12 : Invertible SWAP12
iSWAP12 = along (axiom r008) (product iCX12 (product iCX21 iCX12))

iCX02 : Invertible CX02
iCX02 = along (axiom r009) (product iSWAP12 (product iCX01 iSWAP12))

iSWAP02 : Invertible SWAP02
iSWAP02 = along (axiom r010) (product iCX02 (product iCX20 iCX02))

iK01 : Invertible K01
iK01 = along (axiom r011) (product iSWAP02 (product iK12 iSWAP02))

iCX10 : Invertible CX10
iCX10 = along (axiom r012) (product iK01 (product iCX01 iK01))

iSWAP01 : Invertible SWAP01
iSWAP01 = along (axiom r013) (product iCX01 (product iCX10 iCX01))

iCCX02 : Invertible CCX02
iCCX02 = along (axiom r014) (product iSWAP01 (product iCCX12 iSWAP01))

iX2 : Invertible X2
iX2 = along (axiom r015) (product iSWAP02 (product iX0 iSWAP02))

iZ2 : Invertible Z2
iZ2 = along (axiom r016) (product iSWAP02 (product iZ0 iSWAP02))

iCCX01 : Invertible CCX01
iCCX01 = along (axiom r017) (product iK12 (product iCCX02 iK12))

iCZ02 : Invertible CZ02
iCZ02 = along (axiom r018) (product iSWAP12 (product iCZ01 iSWAP12))

iCZ12 : Invertible CZ12
iCZ12 = along (axiom r019) (product iSWAP01 (product iCZ02 iSWAP01))

iCCZ : Invertible CCZ
iCCZ = middle
  (product iX0 (product iX1 iX2))
  (product iX2 (product iX1 iX0))
  (along (by-assoc Eq.refl) (invol (axiom r083)))

invertible-gen : (g : Gen) → Invertible [ g ]ʷ
invertible-gen X0-gen = iX0
invertible-gen X1-gen = iX1
invertible-gen X2-gen = iX2
invertible-gen Z0-gen = iZ0
invertible-gen Z1-gen = iZ1
invertible-gen Z2-gen = iZ2
invertible-gen CX01-gen = iCX01
invertible-gen CX02-gen = iCX02
invertible-gen CX10-gen = iCX10
invertible-gen CX12-gen = iCX12
invertible-gen CX20-gen = iCX20
invertible-gen CX21-gen = iCX21
invertible-gen CZ01-gen = iCZ01
invertible-gen CZ02-gen = iCZ02
invertible-gen CZ12-gen = iCZ12
invertible-gen CCX01-gen = iCCX01
invertible-gen CCX02-gen = iCCX02
invertible-gen CCX12-gen = iCCX12
invertible-gen K01-gen = iK01
invertible-gen K12-gen = iK12
invertible-gen SWAP01-gen = iSWAP01
invertible-gen SWAP02-gen = iSWAP02
invertible-gen SWAP12-gen = iSWAP12
invertible-gen CCZ-gen = iCCZ
invertible-gen NK-gen = iNK
invertible-gen H2-gen = iH2

grouplike : Grouplike _===_
grouplike g = Invertible.inverse (invertible-gen g) , Invertible.left (invertible-gen g)
