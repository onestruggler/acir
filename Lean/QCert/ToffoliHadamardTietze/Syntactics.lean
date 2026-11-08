/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-Tietze`: the relations

Translation of `Syntactics.agda`: Figures 4, 7 and 8 of arXiv:2407.11152v3 over
one alphabet `Σ₂` of 26 letters, and the relation `Rel` of their 72 equations
(`r001`–`r046` Figure 4, `r083`–`r101` Figure 7, `r102`–`r108` Figure 8).  See
`README.md` for the corrections.

Words are the framework's `FreeMonoid`; the Agda's right-nested `•` is written
with the left-associative `*`, the same word.  Words are in matrix-product order:
the rightmost letter acts first.
-/
import QCert.Presentation

namespace QCert.ToffoliHadamardTietze

/-- The letters. -/
inductive Gen : Type
  | X0 | X1 | X2 | Z0 | Z1 | Z2 | CX01 | CX02 | CX10 | CX12 | CX20 | CX21 | CZ01 | CZ02 | CZ12 | CCX01 | CCX02 | CCX12 | K01 | K12 | SWAP01 | SWAP02 | SWAP12 | CCZ | NK | H2
  deriving DecidableEq, Repr

/-- The letter `X0`. -/
abbrev X0 : Word Gen := FreeMonoid.of Gen.X0

/-- The letter `X1`. -/
abbrev X1 : Word Gen := FreeMonoid.of Gen.X1

/-- The letter `X2`. -/
abbrev X2 : Word Gen := FreeMonoid.of Gen.X2

/-- The letter `Z0`. -/
abbrev Z0 : Word Gen := FreeMonoid.of Gen.Z0

/-- The letter `Z1`. -/
abbrev Z1 : Word Gen := FreeMonoid.of Gen.Z1

/-- The letter `Z2`. -/
abbrev Z2 : Word Gen := FreeMonoid.of Gen.Z2

/-- The letter `CX01`. -/
abbrev CX01 : Word Gen := FreeMonoid.of Gen.CX01

/-- The letter `CX02`. -/
abbrev CX02 : Word Gen := FreeMonoid.of Gen.CX02

/-- The letter `CX10`. -/
abbrev CX10 : Word Gen := FreeMonoid.of Gen.CX10

/-- The letter `CX12`. -/
abbrev CX12 : Word Gen := FreeMonoid.of Gen.CX12

/-- The letter `CX20`. -/
abbrev CX20 : Word Gen := FreeMonoid.of Gen.CX20

/-- The letter `CX21`. -/
abbrev CX21 : Word Gen := FreeMonoid.of Gen.CX21

/-- The letter `CZ01`. -/
abbrev CZ01 : Word Gen := FreeMonoid.of Gen.CZ01

/-- The letter `CZ02`. -/
abbrev CZ02 : Word Gen := FreeMonoid.of Gen.CZ02

/-- The letter `CZ12`. -/
abbrev CZ12 : Word Gen := FreeMonoid.of Gen.CZ12

/-- The letter `CCX01`. -/
abbrev CCX01 : Word Gen := FreeMonoid.of Gen.CCX01

/-- The letter `CCX02`. -/
abbrev CCX02 : Word Gen := FreeMonoid.of Gen.CCX02

/-- The letter `CCX12`. -/
abbrev CCX12 : Word Gen := FreeMonoid.of Gen.CCX12

/-- The letter `K01`. -/
abbrev K01 : Word Gen := FreeMonoid.of Gen.K01

/-- The letter `K12`. -/
abbrev K12 : Word Gen := FreeMonoid.of Gen.K12

/-- The letter `SWAP01`. -/
abbrev SWAP01 : Word Gen := FreeMonoid.of Gen.SWAP01

/-- The letter `SWAP02`. -/
abbrev SWAP02 : Word Gen := FreeMonoid.of Gen.SWAP02

/-- The letter `SWAP12`. -/
abbrev SWAP12 : Word Gen := FreeMonoid.of Gen.SWAP12

/-- The letter `CCZ`. -/
abbrev CCZ : Word Gen := FreeMonoid.of Gen.CCZ

/-- The letter `NK`. -/
abbrev NK : Word Gen := FreeMonoid.of Gen.NK

/-- The letter `H2`. -/
abbrev H2 : Word Gen := FreeMonoid.of Gen.H2

def t01 : Word Gen := X0 * X1 * CCX01 * X1 * X0

def t12 : Word Gen := X0 * CCX01 * CCX02 * CCX01 * X0

def t23 : Word Gen := X0 * CCX01 * X0

def t34 : Word Gen := X0 * X2 * CCX01 * X0 * CCX12 * CCX02 * CCX12 * X0 * CCX01 * X2 * X0

def t45 : Word Gen := X1 * CCX01 * X1

def t56 : Word Gen := CCX01 * CCX02 * CCX01

def t67 : Word Gen := CCX01

def m0 : Word Gen := X0 * X1 * X2 * CCZ * X2 * X1 * X0

def t04 : Word Gen := t01 * t12 * t23 * t34 * t23 * t12 * t01

def t13 : Word Gen := t12 * t23 * t12

def m1 : Word Gen := t01 * m0 * t01

def m3 : Word Gen := t23 * t12 * t01 * m0 * t01 * t12 * t23

def m4 : Word Gen := X0 * m0 * X0

def k4567 : Word Gen := X0 * NK * X0

def t24 : Word Gen := t23 * t34 * t23

def t35 : Word Gen := t34 * t45 * t34

def k1345 : Word Gen := t01 * t13 * t24 * t35 * NK * t35 * t24 * t13 * t01

def t02 : Word Gen := t01 * t12 * t01

def k2345 : Word Gen := t02 * t13 * t24 * t35 * NK * t35 * t24 * t13 * t02

def k0124 : Word Gen := t34 * NK * t34

def rho : Word Gen := k4567 * NK * t34 * NK * k4567

def H0 : Word Gen := K01 * K12 * H2

def H1 : Word Gen := K12 * H2

/-- The 72 equations of Figures 4, 7 and 8. -/
inductive Rel : WRel Gen
  | r001 : Rel (CZ01) (K12 * CX01 * K12)
  | r002 : Rel (X1) (CX01 * X0 * CX01 * X0)
  | r003 : Rel (Z0) (CZ01 * CX01 * CZ01 * CX01)
  | r004 : Rel (Z1) (K12 * X1 * K12)
  | r005 : Rel (CX20) (X1 * CCX12 * X1 * CCX12)
  | r006 : Rel (CX21) (CX20 * CX01 * CX20 * CX01)
  | r007 : Rel (CX12) (K12 * CX21 * K12)
  | r008 : Rel (SWAP12) (CX12 * CX21 * CX12)
  | r009 : Rel (CX02) (SWAP12 * CX01 * SWAP12)
  | r010 : Rel (SWAP02) (CX02 * CX20 * CX02)
  | r011 : Rel (K01) (SWAP02 * K12 * SWAP02)
  | r012 : Rel (CX10) (K01 * CX01 * K01)
  | r013 : Rel (SWAP01) (CX01 * CX10 * CX01)
  | r014 : Rel (CCX02) (SWAP01 * CCX12 * SWAP01)
  | r015 : Rel (X2) (SWAP02 * X0 * SWAP02)
  | r016 : Rel (Z2) (SWAP02 * Z0 * SWAP02)
  | r017 : Rel (CCX01) (K12 * CCX02 * K12)
  | r018 : Rel (CZ02) (SWAP12 * CZ01 * SWAP12)
  | r019 : Rel (CZ12) (SWAP01 * CZ02 * SWAP01)
  | r020 : Rel (SWAP12) (CZ12 * K12 * CZ12 * K12 * CZ12 * K12)
  | r021 : Rel (X0 * X0) (1)
  | r022 : Rel (CX01 * CX01) (1)
  | r023 : Rel (K12 * K12) (1)
  | r024 : Rel (CCX12 * CCX12) (1)
  | r025 : Rel (K01 * K01) (1)
  | r026 : Rel (CX12 * X0) (X0 * CX12)
  | r027 : Rel (X0 * K12) (K12 * X0)
  | r028 : Rel (X1) (SWAP01 * X0 * SWAP01)
  | r029 : Rel (CX20) (SWAP02 * CX02 * SWAP02)
  | r030 : Rel (CX12) (SWAP01 * CX02 * SWAP01)
  | r031 : Rel (CX21) (SWAP01 * CX20 * SWAP01)
  | r032 : Rel (CCX01) (SWAP02 * CCX12 * SWAP02)
  | r033 : Rel (CCX01) (SWAP12 * CCX02 * SWAP12)
  | r034 : Rel (Z1) (SWAP01 * Z0 * SWAP01)
  | r035 : Rel (K01) (SWAP01 * K01 * SWAP01)
  | r036 : Rel (CCX12 * CX10) (CX10 * CCX12)
  | r037 : Rel (X0 * CCX12) (CCX12 * X0)
  | r038 : Rel (X0 * CX10) (CX10 * X0)
  | r039 : Rel (K01 * K12) (K12 * K01)
  | r040 : Rel (CZ01 * CZ12) (CZ12 * CZ01)
  | r041 : Rel (K01 * Z0) (X0 * K01)
  | r042 : Rel (X0 * CCX01) (CCX01 * CX12 * X0)
  | r043 : Rel (CX01 * CZ12) (CZ12 * CZ02 * CX01)
  | r044 : Rel (CX12 * CCX12) (CCX12 * CX10 * CX12)
  | r045 : Rel (CCX12 * CX01) (CX01 * CCX02 * CCX12 * CCX02)
  | r046 : Rel (CCX01 * CCX02) (CCX02 * CCX01 * CCX02 * CCX01)
  | r083 : Rel (m0 * m0) (1)
  | r084 : Rel (NK * NK) (1)
  | r085 : Rel (t12 * m0) (m0 * t12)
  | r086 : Rel (t23 * m0) (m0 * t23)
  | r087 : Rel (t34 * m0) (m0 * t34)
  | r088 : Rel (t45 * m0) (m0 * t45)
  | r089 : Rel (t56 * m0) (m0 * t56)
  | r090 : Rel (t67 * m0) (m0 * t67)
  | r091 : Rel (t45 * NK) (NK * t45)
  | r092 : Rel (t56 * NK) (NK * t56)
  | r093 : Rel (t67 * NK) (NK * t67)
  | r094 : Rel (m4 * NK) (NK * m4)
  | r095 : Rel (m0 * m4) (m4 * m0)
  | r096 : Rel (NK * k4567) (k4567 * NK)
  | r097 : Rel (t01 * NK) (NK * t13 * m1 * m3)
  | r098 : Rel (t12 * NK) (m0 * NK * m0 * NK * m0)
  | r099 : Rel (t23 * NK) (NK * t13)
  | r100 : Rel (NK * k1345) (k2345 * k0124)
  | r101 : Rel (m0 * m4 * t04 * rho) (rho * t04 * m4 * m0)
  | r102 : Rel (H2 * X0) (X0 * H2)
  | r103 : Rel (H2 * CX01) (CX01 * H2)
  | r104 : Rel (H2 * CCX12) (K01 * K12 * CCZ * K12 * K01 * H2)
  | r105 : Rel (H2 * CCZ) (CCX01 * H2)
  | r106 : Rel (H2 * K12) (K12 * H2)
  | r107 : Rel (H2 * NK) (NK * H2)
  | r108 : Rel (H2 * H2) (1)

/-- Derivability from `Rel` (the Agda's `_≈_`). -/
infix:50 (priority := high) " ≈ " => Derivable Rel

end QCert.ToffoliHadamardTietze
