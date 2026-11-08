{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Core where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Presentation.Base _===_ hiding (_===_ ; _≈_)

data CGen : Set where
  cX0 cCX01 cCCX12 cK12 cCCZ cNK cH2 : CGen

embed : CGen → Gen
embed cX0 = X0-gen
embed cCX01 = CX01-gen
embed cCCX12 = CCX12-gen
embed cK12 = K12-gen
embed cCCZ = CCZ-gen
embed cNK = NK-gen
embed cH2 = H2-gen

⌞_⌟ : Word CGen → Word Gen
⌞ w ⌟ = wmap embed w

wX0 : Word CGen
wX0 = [ cX0 ]ʷ
eX0 : X0 ≈ ⌞ wX0 ⌟
eX0 = refl

wCX01 : Word CGen
wCX01 = [ cCX01 ]ʷ
eCX01 : CX01 ≈ ⌞ wCX01 ⌟
eCX01 = refl

wCCX12 : Word CGen
wCCX12 = [ cCCX12 ]ʷ
eCCX12 : CCX12 ≈ ⌞ wCCX12 ⌟
eCCX12 = refl

wK12 : Word CGen
wK12 = [ cK12 ]ʷ
eK12 : K12 ≈ ⌞ wK12 ⌟
eK12 = refl

wCCZ : Word CGen
wCCZ = [ cCCZ ]ʷ
eCCZ : CCZ ≈ ⌞ wCCZ ⌟
eCCZ = refl

wNK : Word CGen
wNK = [ cNK ]ʷ
eNK : NK ≈ ⌞ wNK ⌟
eNK = refl

wH2 : Word CGen
wH2 = [ cH2 ]ʷ
eH2 : H2 ≈ ⌞ wH2 ⌟
eH2 = refl

wCZ01 : Word CGen
wCZ01 = wK12 • wCX01 • wK12
eCZ01 : CZ01 ≈ ⌞ wCZ01 ⌟
eCZ01 = trans (axiom r001) (cong eK12 (cong eCX01 eK12))

wX1 : Word CGen
wX1 = wCX01 • wX0 • wCX01 • wX0
eX1 : X1 ≈ ⌞ wX1 ⌟
eX1 = trans (axiom r002) (cong eCX01 (cong eX0 (cong eCX01 eX0)))

wZ0 : Word CGen
wZ0 = wCZ01 • wCX01 • wCZ01 • wCX01
eZ0 : Z0 ≈ ⌞ wZ0 ⌟
eZ0 = trans (axiom r003) (cong eCZ01 (cong eCX01 (cong eCZ01 eCX01)))

wZ1 : Word CGen
wZ1 = wK12 • wX1 • wK12
eZ1 : Z1 ≈ ⌞ wZ1 ⌟
eZ1 = trans (axiom r004) (cong eK12 (cong eX1 eK12))

wCX20 : Word CGen
wCX20 = wX1 • wCCX12 • wX1 • wCCX12
eCX20 : CX20 ≈ ⌞ wCX20 ⌟
eCX20 = trans (axiom r005) (cong eX1 (cong eCCX12 (cong eX1 eCCX12)))

wCX21 : Word CGen
wCX21 = wCX20 • wCX01 • wCX20 • wCX01
eCX21 : CX21 ≈ ⌞ wCX21 ⌟
eCX21 = trans (axiom r006) (cong eCX20 (cong eCX01 (cong eCX20 eCX01)))

wCX12 : Word CGen
wCX12 = wK12 • wCX21 • wK12
eCX12 : CX12 ≈ ⌞ wCX12 ⌟
eCX12 = trans (axiom r007) (cong eK12 (cong eCX21 eK12))

wSWAP12 : Word CGen
wSWAP12 = wCX12 • wCX21 • wCX12
eSWAP12 : SWAP12 ≈ ⌞ wSWAP12 ⌟
eSWAP12 = trans (axiom r008) (cong eCX12 (cong eCX21 eCX12))

wCX02 : Word CGen
wCX02 = wSWAP12 • wCX01 • wSWAP12
eCX02 : CX02 ≈ ⌞ wCX02 ⌟
eCX02 = trans (axiom r009) (cong eSWAP12 (cong eCX01 eSWAP12))

wSWAP02 : Word CGen
wSWAP02 = wCX02 • wCX20 • wCX02
eSWAP02 : SWAP02 ≈ ⌞ wSWAP02 ⌟
eSWAP02 = trans (axiom r010) (cong eCX02 (cong eCX20 eCX02))

wK01 : Word CGen
wK01 = wSWAP02 • wK12 • wSWAP02
eK01 : K01 ≈ ⌞ wK01 ⌟
eK01 = trans (axiom r011) (cong eSWAP02 (cong eK12 eSWAP02))

wCX10 : Word CGen
wCX10 = wK01 • wCX01 • wK01
eCX10 : CX10 ≈ ⌞ wCX10 ⌟
eCX10 = trans (axiom r012) (cong eK01 (cong eCX01 eK01))

wSWAP01 : Word CGen
wSWAP01 = wCX01 • wCX10 • wCX01
eSWAP01 : SWAP01 ≈ ⌞ wSWAP01 ⌟
eSWAP01 = trans (axiom r013) (cong eCX01 (cong eCX10 eCX01))

wCCX02 : Word CGen
wCCX02 = wSWAP01 • wCCX12 • wSWAP01
eCCX02 : CCX02 ≈ ⌞ wCCX02 ⌟
eCCX02 = trans (axiom r014) (cong eSWAP01 (cong eCCX12 eSWAP01))

wX2 : Word CGen
wX2 = wSWAP02 • wX0 • wSWAP02
eX2 : X2 ≈ ⌞ wX2 ⌟
eX2 = trans (axiom r015) (cong eSWAP02 (cong eX0 eSWAP02))

wZ2 : Word CGen
wZ2 = wSWAP02 • wZ0 • wSWAP02
eZ2 : Z2 ≈ ⌞ wZ2 ⌟
eZ2 = trans (axiom r016) (cong eSWAP02 (cong eZ0 eSWAP02))

wCCX01 : Word CGen
wCCX01 = wK12 • wCCX02 • wK12
eCCX01 : CCX01 ≈ ⌞ wCCX01 ⌟
eCCX01 = trans (axiom r017) (cong eK12 (cong eCCX02 eK12))

wCZ02 : Word CGen
wCZ02 = wSWAP12 • wCZ01 • wSWAP12
eCZ02 : CZ02 ≈ ⌞ wCZ02 ⌟
eCZ02 = trans (axiom r018) (cong eSWAP12 (cong eCZ01 eSWAP12))

wCZ12 : Word CGen
wCZ12 = wSWAP01 • wCZ02 • wSWAP01
eCZ12 : CZ12 ≈ ⌞ wCZ12 ⌟
eCZ12 = trans (axiom r019) (cong eSWAP01 (cong eCZ02 eSWAP01))

core : Gen → Word CGen
core X0-gen = wX0
core X1-gen = wX1
core X2-gen = wX2
core Z0-gen = wZ0
core Z1-gen = wZ1
core Z2-gen = wZ2
core CX01-gen = wCX01
core CX02-gen = wCX02
core CX10-gen = wCX10
core CX12-gen = wCX12
core CX20-gen = wCX20
core CX21-gen = wCX21
core CZ01-gen = wCZ01
core CZ02-gen = wCZ02
core CZ12-gen = wCZ12
core CCX01-gen = wCCX01
core CCX02-gen = wCCX02
core CCX12-gen = wCCX12
core K01-gen = wK01
core K12-gen = wK12
core SWAP01-gen = wSWAP01
core SWAP02-gen = wSWAP02
core SWAP12-gen = wSWAP12
core CCZ-gen = wCCZ
core NK-gen = wNK
core H2-gen = wH2

expand : Word Gen → Word CGen
expand = core ʷ

gen-expand : (g : Gen) → [ g ]ʷ ≈ ⌞ core g ⌟
gen-expand X0-gen = eX0
gen-expand X1-gen = eX1
gen-expand X2-gen = eX2
gen-expand Z0-gen = eZ0
gen-expand Z1-gen = eZ1
gen-expand Z2-gen = eZ2
gen-expand CX01-gen = eCX01
gen-expand CX02-gen = eCX02
gen-expand CX10-gen = eCX10
gen-expand CX12-gen = eCX12
gen-expand CX20-gen = eCX20
gen-expand CX21-gen = eCX21
gen-expand CZ01-gen = eCZ01
gen-expand CZ02-gen = eCZ02
gen-expand CZ12-gen = eCZ12
gen-expand CCX01-gen = eCCX01
gen-expand CCX02-gen = eCCX02
gen-expand CCX12-gen = eCCX12
gen-expand K01-gen = eK01
gen-expand K12-gen = eK12
gen-expand SWAP01-gen = eSWAP01
gen-expand SWAP02-gen = eSWAP02
gen-expand SWAP12-gen = eSWAP12
gen-expand CCZ-gen = eCCZ
gen-expand NK-gen = eNK
gen-expand H2-gen = eH2

word-expand : (w : Word Gen) → w ≈ ⌞ expand w ⌟
word-expand [ g ]ʷ = gen-expand g
word-expand ε = refl
word-expand (w • v) = cong (word-expand w) (word-expand v)
