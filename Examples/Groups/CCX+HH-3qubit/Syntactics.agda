-- Figures 4, 7 and 8 of arXiv:2407.11152v3. See README.md for corrections.
{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Syntactics where

open import Word.Base public
import Presentation.Base as PB

data Gen : Set where
  X0-gen X1-gen X2-gen Z0-gen Z1-gen Z2-gen CX01-gen CX02-gen CX10-gen CX12-gen CX20-gen CX21-gen CZ01-gen CZ02-gen CZ12-gen CCX01-gen CCX02-gen CCX12-gen K01-gen K12-gen SWAP01-gen SWAP02-gen SWAP12-gen CCZ-gen NK-gen H2-gen : Gen

X0 X1 X2 Z0 Z1 Z2 CX01 CX02 CX10 CX12 CX20 CX21 CZ01 CZ02 CZ12 CCX01 CCX02 CCX12 K01 K12 SWAP01 SWAP02 SWAP12 CCZ NK H2 : Word Gen
X0 = [ X0-gen ]ʷ
X1 = [ X1-gen ]ʷ
X2 = [ X2-gen ]ʷ
Z0 = [ Z0-gen ]ʷ
Z1 = [ Z1-gen ]ʷ
Z2 = [ Z2-gen ]ʷ
CX01 = [ CX01-gen ]ʷ
CX02 = [ CX02-gen ]ʷ
CX10 = [ CX10-gen ]ʷ
CX12 = [ CX12-gen ]ʷ
CX20 = [ CX20-gen ]ʷ
CX21 = [ CX21-gen ]ʷ
CZ01 = [ CZ01-gen ]ʷ
CZ02 = [ CZ02-gen ]ʷ
CZ12 = [ CZ12-gen ]ʷ
CCX01 = [ CCX01-gen ]ʷ
CCX02 = [ CCX02-gen ]ʷ
CCX12 = [ CCX12-gen ]ʷ
K01 = [ K01-gen ]ʷ
K12 = [ K12-gen ]ʷ
SWAP01 = [ SWAP01-gen ]ʷ
SWAP02 = [ SWAP02-gen ]ʷ
SWAP12 = [ SWAP12-gen ]ʷ
CCZ = [ CCZ-gen ]ʷ
NK = [ NK-gen ]ʷ
H2 = [ H2-gen ]ʷ

t01 : Word Gen
t01 = X0 • X1 • CCX01 • X1 • X0

t12 : Word Gen
t12 = X0 • CCX01 • CCX02 • CCX01 • X0

t23 : Word Gen
t23 = X0 • CCX01 • X0

t34 : Word Gen
t34 = X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0

t45 : Word Gen
t45 = X1 • CCX01 • X1

t56 : Word Gen
t56 = CCX01 • CCX02 • CCX01

t67 : Word Gen
t67 = CCX01

m0 : Word Gen
m0 = X0 • X1 • X2 • CCZ • X2 • X1 • X0

t04 : Word Gen
t04 = t01 • t12 • t23 • t34 • t23 • t12 • t01

t13 : Word Gen
t13 = t12 • t23 • t12

m1 : Word Gen
m1 = t01 • m0 • t01

m3 : Word Gen
m3 = t23 • t12 • t01 • m0 • t01 • t12 • t23

m4 : Word Gen
m4 = X0 • m0 • X0

k4567 : Word Gen
k4567 = X0 • NK • X0

t24 : Word Gen
t24 = t23 • t34 • t23

t35 : Word Gen
t35 = t34 • t45 • t34

k1345 : Word Gen
k1345 = t01 • t13 • t24 • t35 • NK • t35 • t24 • t13 • t01

t02 : Word Gen
t02 = t01 • t12 • t01

k2345 : Word Gen
k2345 = t02 • t13 • t24 • t35 • NK • t35 • t24 • t13 • t02

k0124 : Word Gen
k0124 = t34 • NK • t34

rho : Word Gen
rho = k4567 • NK • t34 • NK • k4567

-- Other one-wire Hadamards are words over Σ₂.
H0 H1 : Word Gen
H0 = K01 • K12 • H2
H1 = K12 • H2

infix 4 _===_

data _===_ : WRel Gen where
  r001 : CZ01 === K12 • CX01 • K12
  r002 : X1 === CX01 • X0 • CX01 • X0
  r003 : Z0 === CZ01 • CX01 • CZ01 • CX01
  r004 : Z1 === K12 • X1 • K12
  r005 : CX20 === X1 • CCX12 • X1 • CCX12
  r006 : CX21 === CX20 • CX01 • CX20 • CX01
  r007 : CX12 === K12 • CX21 • K12
  r008 : SWAP12 === CX12 • CX21 • CX12
  r009 : CX02 === SWAP12 • CX01 • SWAP12
  r010 : SWAP02 === CX02 • CX20 • CX02
  r011 : K01 === SWAP02 • K12 • SWAP02
  r012 : CX10 === K01 • CX01 • K01
  r013 : SWAP01 === CX01 • CX10 • CX01
  r014 : CCX02 === SWAP01 • CCX12 • SWAP01
  r015 : X2 === SWAP02 • X0 • SWAP02
  r016 : Z2 === SWAP02 • Z0 • SWAP02
  r017 : CCX01 === K12 • CCX02 • K12
  r018 : CZ02 === SWAP12 • CZ01 • SWAP12
  r019 : CZ12 === SWAP01 • CZ02 • SWAP01
  r020 : SWAP12 === CZ12 • K12 • CZ12 • K12 • CZ12 • K12
  r021 : X0 • X0 === ε
  r022 : CX01 • CX01 === ε
  r023 : K12 • K12 === ε
  r024 : CCX12 • CCX12 === ε
  r025 : K01 • K01 === ε
  r026 : CX12 • X0 === X0 • CX12
  r027 : X0 • K12 === K12 • X0
  r028 : X1 === SWAP01 • X0 • SWAP01
  r029 : CX20 === SWAP02 • CX02 • SWAP02
  r030 : CX12 === SWAP01 • CX02 • SWAP01
  r031 : CX21 === SWAP01 • CX20 • SWAP01
  r032 : CCX01 === SWAP02 • CCX12 • SWAP02
  r033 : CCX01 === SWAP12 • CCX02 • SWAP12
  r034 : Z1 === SWAP01 • Z0 • SWAP01
  r035 : K01 === SWAP01 • K01 • SWAP01
  r036 : CCX12 • CX10 === CX10 • CCX12
  r037 : X0 • CCX12 === CCX12 • X0
  r038 : X0 • CX10 === CX10 • X0
  r039 : K01 • K12 === K12 • K01
  r040 : CZ01 • CZ12 === CZ12 • CZ01
  r041 : K01 • Z0 === X0 • K01
  r042 : X0 • CCX01 === CCX01 • CX12 • X0
  r043 : CX01 • CZ12 === CZ12 • CZ02 • CX01
  r044 : CX12 • CCX12 === CCX12 • CX10 • CX12
  r045 : CCX12 • CX01 === CX01 • CCX02 • CCX12 • CCX02
  r046 : CCX01 • CCX02 === CCX02 • CCX01 • CCX02 • CCX01
  r083 : m0 • m0 === ε
  r084 : NK • NK === ε
  r085 : t12 • m0 === m0 • t12
  r086 : t23 • m0 === m0 • t23
  r087 : t34 • m0 === m0 • t34
  r088 : t45 • m0 === m0 • t45
  r089 : t56 • m0 === m0 • t56
  r090 : t67 • m0 === m0 • t67
  r091 : t45 • NK === NK • t45
  r092 : t56 • NK === NK • t56
  r093 : t67 • NK === NK • t67
  r094 : m4 • NK === NK • m4
  r095 : m0 • m4 === m4 • m0
  r096 : NK • k4567 === k4567 • NK
  r097 : t01 • NK === NK • t13 • m1 • m3
  r098 : t12 • NK === m0 • NK • m0 • NK • m0
  r099 : t23 • NK === NK • t13
  r100 : NK • k1345 === k2345 • k0124
  r101 : m0 • m4 • t04 • rho === rho • t04 • m4 • m0
  r102 : H2 • X0 === X0 • H2
  r103 : H2 • CX01 === CX01 • H2
  r104 : H2 • CCX12 === K01 • K12 • CCZ • K12 • K01 • H2
  r105 : H2 • CCZ === CCX01 • H2
  r106 : H2 • K12 === K12 • H2
  r107 : H2 • NK === NK • H2
  r108 : H2 • H2 === ε

open PB _===_ public using (_≈_)
