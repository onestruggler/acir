/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Kernel replay of the permutation equations

The proof DAG is the independent Lean Toffoli-Hadamard development's
permutation calculation, with its required Figure 4 equations proved
inside the Clifford+CS syntactic quotient.
-/
import QCert.CliffordCS3.Three.PermutationTransport
import QCert.ToffoliHadamard.Engine

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QCert.CliffordCS3.Three.PermutationCert
open ToffoliHadamard ToffoliHadamard.Engine
open PermutationBase

def R : WRel Sym1 := fun a b => Derivable Rel (D a) (D b)

theorem transfer {a b : Word Sym1} (h : Derivable R a b) : Derivable Rel (D a) (D b) :=
  Derivable.map D (fun _ _ h => h) h

theorem involutions (g : Sym1) : Derivable R (FreeMonoid.ofList [g,g]) 1 :=
  Derivable.of (generator_involution g)

def replay (E : List (Rule R)) (l r : List Sym1) (n code : Nat)
    (hc : rrun (E.map fun e => (e.lhs, e.rhs)) l (decodeRot n code) = some r) : Rule R where
  lhs := l
  rhs := r
  sound := rrun_sound involutions (by
    intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact x.sound) hc


def r0 : Rule R := Rule.ofDerivable _ _ (involutions .X0)

def r2 : Rule R := Rule.ofDerivable _ _ (involutions .X2)

def r9 : Rule R := Rule.ofDerivable _ _ (involutions .CCX01)

def r25 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CZ01])
  (FreeMonoid.ofList [Sym1.K12, Sym1.CX01, Sym1.K12]) (Derivable.of PermutationBase.r1)

def r26 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.X1])
  (FreeMonoid.ofList [Sym1.CX01, Sym1.X0, Sym1.CX01, Sym1.X0]) (Derivable.of PermutationBase.r2)

def r28 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.Z1])
  (FreeMonoid.ofList [Sym1.K12, Sym1.X1, Sym1.K12]) (Derivable.of PermutationBase.r4)

def r29 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX20])
  (FreeMonoid.ofList [Sym1.X1, Sym1.CCX12, Sym1.X1, Sym1.CCX12]) (Derivable.of PermutationBase.r5)

def r30 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX21])
  (FreeMonoid.ofList [Sym1.CX20, Sym1.CX01, Sym1.CX20, Sym1.CX01]) (Derivable.of PermutationBase.r6)

def r31 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX12])
  (FreeMonoid.ofList [Sym1.K12, Sym1.CX21, Sym1.K12]) (Derivable.of PermutationBase.r7)

def r32 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.S12])
  (FreeMonoid.ofList [Sym1.CX12, Sym1.CX21, Sym1.CX12]) (Derivable.of PermutationBase.r8)

def r33 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX02])
  (FreeMonoid.ofList [Sym1.S12, Sym1.CX01, Sym1.S12]) (Derivable.of PermutationBase.r9)

def r34 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.S02])
  (FreeMonoid.ofList [Sym1.CX02, Sym1.CX20, Sym1.CX02]) (Derivable.of PermutationBase.r10)

def r35 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.K01])
  (FreeMonoid.ofList [Sym1.S02, Sym1.K12, Sym1.S02]) (Derivable.of PermutationBase.r11)

def r36 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX10])
  (FreeMonoid.ofList [Sym1.K01, Sym1.CX01, Sym1.K01]) (Derivable.of PermutationBase.r12)

def r37 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.S01])
  (FreeMonoid.ofList [Sym1.CX01, Sym1.CX10, Sym1.CX01]) (Derivable.of PermutationBase.r13)

def r38 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CCX02])
  (FreeMonoid.ofList [Sym1.S01, Sym1.CCX12, Sym1.S01]) (Derivable.of PermutationBase.r14)

def r39 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.X2])
  (FreeMonoid.ofList [Sym1.S02, Sym1.X0, Sym1.S02]) (Derivable.of PermutationBase.r15)

def r40 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.Z2])
  (FreeMonoid.ofList [Sym1.S02, Sym1.Z0, Sym1.S02]) (Derivable.of PermutationBase.r16)

def r41 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CCX01])
  (FreeMonoid.ofList [Sym1.K12, Sym1.CCX02, Sym1.K12]) (Derivable.of PermutationBase.r17)

def r42 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CZ02])
  (FreeMonoid.ofList [Sym1.S12, Sym1.CZ01, Sym1.S12]) (Derivable.of PermutationBase.r18)

def r43 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CZ12])
  (FreeMonoid.ofList [Sym1.S01, Sym1.CZ02, Sym1.S01]) (Derivable.of PermutationBase.r19)

def r44 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.S12])
  (FreeMonoid.ofList [Sym1.CZ12, Sym1.K12, Sym1.CZ12, Sym1.K12, Sym1.CZ12, Sym1.K12]) (Derivable.of PermutationBase.r20)

def r50 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX12, Sym1.X0])
  (FreeMonoid.ofList [Sym1.X0, Sym1.CX12]) (Derivable.of PermutationBase.r26)

def r51 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.X0, Sym1.K12])
  (FreeMonoid.ofList [Sym1.K12, Sym1.X0]) (Derivable.of PermutationBase.r27)

def r52 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.X1])
  (FreeMonoid.ofList [Sym1.S01, Sym1.X0, Sym1.S01]) (Derivable.of PermutationBase.r28)

def r53 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX20])
  (FreeMonoid.ofList [Sym1.S02, Sym1.CX02, Sym1.S02]) (Derivable.of PermutationBase.r29)

def r54 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX12])
  (FreeMonoid.ofList [Sym1.S01, Sym1.CX02, Sym1.S01]) (Derivable.of PermutationBase.r30)

def r55 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX21])
  (FreeMonoid.ofList [Sym1.S01, Sym1.CX20, Sym1.S01]) (Derivable.of PermutationBase.r31)

def r56 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CCX01])
  (FreeMonoid.ofList [Sym1.S02, Sym1.CCX12, Sym1.S02]) (Derivable.of PermutationBase.r32)

def r57 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CCX01])
  (FreeMonoid.ofList [Sym1.S12, Sym1.CCX02, Sym1.S12]) (Derivable.of PermutationBase.r33)

def r58 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.Z1])
  (FreeMonoid.ofList [Sym1.S01, Sym1.Z0, Sym1.S01]) (Derivable.of PermutationBase.r34)

def r59 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.K01])
  (FreeMonoid.ofList [Sym1.S01, Sym1.K01, Sym1.S01]) (Derivable.of PermutationBase.r35)

def r60 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CCX12, Sym1.CX10])
  (FreeMonoid.ofList [Sym1.CX10, Sym1.CCX12]) (Derivable.of PermutationBase.r36)

def r61 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.X0, Sym1.CCX12])
  (FreeMonoid.ofList [Sym1.CCX12, Sym1.X0]) (Derivable.of PermutationBase.r37)

def r62 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.X0, Sym1.CX10])
  (FreeMonoid.ofList [Sym1.CX10, Sym1.X0]) (Derivable.of PermutationBase.r38)

def r63 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.K01, Sym1.K12])
  (FreeMonoid.ofList [Sym1.K12, Sym1.K01]) (Derivable.of PermutationBase.r39)

def r65 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.K01, Sym1.Z0])
  (FreeMonoid.ofList [Sym1.X0, Sym1.K01]) (Derivable.of PermutationBase.r41)

def r66 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.X0, Sym1.CCX01])
  (FreeMonoid.ofList [Sym1.CCX01, Sym1.CX12, Sym1.X0]) (Derivable.of PermutationBase.r42)

def r67 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX01, Sym1.CZ12])
  (FreeMonoid.ofList [Sym1.CZ12, Sym1.CZ02, Sym1.CX01]) (Derivable.of PermutationBase.r43)

def r68 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CX12, Sym1.CCX12])
  (FreeMonoid.ofList [Sym1.CCX12, Sym1.CX10, Sym1.CX12]) (Derivable.of PermutationBase.r44)

def r69 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CCX12, Sym1.CX01])
  (FreeMonoid.ofList [Sym1.CX01, Sym1.CCX02, Sym1.CCX12, Sym1.CCX02]) (Derivable.of PermutationBase.r45)

def r70 : Rule R := Rule.ofDerivable (FreeMonoid.ofList [Sym1.CCX01, Sym1.CCX02])
  (FreeMonoid.ofList [Sym1.CCX02, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01]) (Derivable.of PermutationBase.r46)

def r71 : Rule R := replay [r26]
  [Sym1.X0, Sym1.X1] [Sym1.X1, Sym1.X0]
  2 123145302313989 (by decide +kernel)

def r72 : Rule R := replay [r29, r61, r71]
  [Sym1.X0, Sym1.CX20] [Sym1.CX20, Sym1.X0]
  6 15164970100804612925640593232930719492496941767534506468631778426882 (by decide +kernel)

def r73 : Rule R := replay [r31, r50, r51]
  [Sym1.X0, Sym1.CX21] [Sym1.CX21, Sym1.X0]
  5 822852712958976311272479781962438309394719032485583794807504898 (by decide +kernel)

def r74 : Rule R := replay [r28, r51, r71]
  [Sym1.X0, Sym1.Z1] [Sym1.Z1, Sym1.X0]
  5 822802496145093217815218723047949912682101624890417056945012738 (by decide +kernel)

def r75 : Rule R := replay [r32, r50, r73]
  [Sym1.X0, Sym1.S12] [Sym1.S12, Sym1.X0]
  5 822802594224807833232105657982159650301889376489720876695553026 (by decide +kernel)

def r76 : Rule R := replay [r26]
  [Sym1.X1, Sym1.CX01] [Sym1.CX01, Sym1.X1]
  2 18137543811796997 (by decide +kernel)

def r77 : Rule R := replay [r50, r52, r54]
  [Sym1.X1, Sym1.CX02] [Sym1.CX02, Sym1.X1]
  5 822802496145093223535359866470729913019704896523361123761127426 (by decide +kernel)

def r78 : Rule R := replay [r29]
  [Sym1.X1, Sym1.CX20] [Sym1.CX20, Sym1.X1]
  2 158338264338435 (by decide +kernel)

def r79 : Rule R := replay [r38, r52, r61]
  [Sym1.X1, Sym1.CCX02] [Sym1.CCX02, Sym1.X1]
  5 822802496145093217815218723047949912682101624890417056945012738 (by decide +kernel)

def r80 : Rule R := replay [r52, r58, r59, r65]
  [Sym1.X1, Sym1.K01] [Sym1.K01, Sym1.Z1]
  5 100434298232986037811424003940338935657186510113023915458562 (by decide +kernel)

def r81 : Rule R := replay [r34, r77, r78]
  [Sym1.X1, Sym1.S02] [Sym1.S02, Sym1.X1]
  5 822802496145093217815218723047949912682101624890417056945012738 (by decide +kernel)

def r82 : Rule R := replay [r39, r53, r72]
  [Sym1.X2, Sym1.CX02] [Sym1.CX02, Sym1.X2]
  5 822752279331210127234753794743749325038112613341576632060608514 (by decide +kernel)

def r83 : Rule R := replay [r39, r56, r61]
  [Sym1.X2, Sym1.CCX01] [Sym1.CCX01, Sym1.X2]
  5 822752279331210127223603422144484013467344754169223654288654338 (by decide +kernel)

def r84 : Rule R := replay [r35, r39, r51]
  [Sym1.X2, Sym1.K01] [Sym1.K01, Sym1.X2]
  5 822802496145093217815218723047949912682101624890417056945012738 (by decide +kernel)

def r85 : Rule R := replay [r35, r39, r40, r65]
  [Sym1.X2, Sym1.K12] [Sym1.K12, Sym1.Z2]
  5 196829896032833859306653508253629147000143971548483553282 (by decide +kernel)

def r86 : Rule R := replay [r36, r37, r59]
  [Sym1.CX01, Sym1.CX10] [Sym1.CX10, Sym1.S01]
  5 670466799134439678773579503061223329186573478090768386 (by decide +kernel)

def r87 : Rule R := replay [r30]
  [Sym1.CX01, Sym1.CX21] [Sym1.CX21, Sym1.CX01]
  2 123145302313989 (by decide +kernel)

def r88 : Rule R := replay [r67]
  [Sym1.CX01, Sym1.CZ02] [Sym1.CZ02, Sym1.CX01]
  2 36187135283299331 (by decide +kernel)

def r89 : Rule R := replay [r37, r86]
  [Sym1.CX01, Sym1.S01] [Sym1.S01, Sym1.CX10]
  2 123153892771842 (by decide +kernel)

def r90 : Rule R := replay [r34, r53]
  [Sym1.CX02, Sym1.CX20] [Sym1.CX20, Sym1.S02]
  2 36151950911733762 (by decide +kernel)

def r91 : Rule R := replay [r29, r53, r56]
  [Sym1.CX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CX02]
  6 1766858859755101523552365711658670386401578235757112611163257013510602754 (by decide +kernel)

def r92 : Rule R := replay [r68]
  [Sym1.CX10, Sym1.CX12] [Sym1.CX12, Sym1.CX10]
  2 54166340830757893 (by decide +kernel)

def r93 : Rule R := replay [r55, r87, r89]
  [Sym1.CX10, Sym1.CX20] [Sym1.CX20, Sym1.CX10]
  5 822852909118405542106253651830858101546944592741541808484386818 (by decide +kernel)

def r94 : Rule R := replay [r43, r88, r89]
  [Sym1.CX10, Sym1.CZ12] [Sym1.CZ12, Sym1.CX10]
  5 822852909118405542095103279231592789976176733569188830712432642 (by decide +kernel)

def r95 : Rule R := replay [r31, r32, r44]
  [Sym1.CX12, Sym1.CX21] [Sym1.CX21, Sym1.S12]
  6 14475778023635082332539017244199429836727364183368138486404121858964579155970 (by decide +kernel)

def r96 : Rule R := replay [r66]
  [Sym1.CX12, Sym1.CCX01] [Sym1.CCX01, Sym1.CX12]
  2 18172736773816323 (by decide +kernel)

def r97 : Rule R := replay [r32, r95]
  [Sym1.CX12, Sym1.S12] [Sym1.S12, Sym1.CX21]
  2 123153892771842 (by decide +kernel)

def r98 : Rule R := replay [r29]
  [Sym1.CX20, Sym1.CCX12] [Sym1.CCX12, Sym1.CX20]
  2 72215932302265347 (by decide +kernel)

def r99 : Rule R := replay [r28, r41, r79]
  [Sym1.CCX01, Sym1.Z1] [Sym1.Z1, Sym1.CCX01]
  5 822802496145093217815218723047949595769451567833066682769211394 (by decide +kernel)

def r100 : Rule R := replay [r41, r83, r85]
  [Sym1.CCX02, Sym1.Z2] [Sym1.Z2, Sym1.CCX02]
  5 822752475490639360923023050023925986204780794241804628995868674 (by decide +kernel)

def r101 : Rule R := replay [r65, r71, r80]
  [Sym1.Z0, Sym1.Z1] [Sym1.Z1, Sym1.Z0]
  5 822752573570353976339909984958136040737218602898458822922208258 (by decide +kernel)

def r102 : Rule R := replay [r51, r63, r65]
  [Sym1.Z0, Sym1.K12] [Sym1.K12, Sym1.Z0]
  5 822853007198120160360910413277927374650323290341286893186974722 (by decide +kernel)

def r103 : Rule R := replay [r25, r28, r76]
  [Sym1.Z1, Sym1.CZ01] [Sym1.CZ01, Sym1.Z1]
  5 822802496145093217815218723047949912682101624890417056945012738 (by decide +kernel)

def r104 : Rule R := replay [r28, r35, r80, r81]
  [Sym1.Z1, Sym1.S02] [Sym1.S02, Sym1.Z1]
  5 822852909118405544944023478344204414861023178868186604485214210 (by decide +kernel)

def r105 : Rule R := replay [r44]
  [Sym1.CZ12, Sym1.S12] [Sym1.S12, Sym1.CZ12]
  2 228707008518147 (by decide +kernel)

def r106 : Rule R := replay [r44]
  [Sym1.K12, Sym1.S12] [Sym1.S12, Sym1.K12]
  2 193514046493701 (by decide +kernel)

def r107 : Rule R := replay [r32, r34, r54, r55]
  [Sym1.S01, Sym1.S02] [Sym1.S12, Sym1.S01]
  5 822853007198120160366485599578046491353544793736915705073239042 (by decide +kernel)

def r108 : Rule R := replay [r26, r37, r52, r76]
  [Sym1.X0, Sym1.X1] [Sym1.CX10, Sym1.X1, Sym1.CX10]
  5 1645554970965125475446618324959855743304984255012607508277627909 (by decide +kernel)

def r109 : Rule R := replay [r30, r37, r55, r87]
  [Sym1.CX10, Sym1.CX20] [Sym1.CX21, Sym1.CX10, Sym1.CX21]
  5 1645504656167308737882163571057700493037019784758375551523620866 (by decide +kernel)

def r110 : Rule R := replay [r71, r77]
  [Sym1.X0, Sym1.X1, Sym1.X0] [Sym1.CX02, Sym1.X1, Sym1.CX02]
  2 9241439211922391046 (by decide +kernel)

def r111 : Rule R := replay [r71, r79]
  [Sym1.X0, Sym1.X1, Sym1.X0] [Sym1.CCX02, Sym1.X1, Sym1.CCX02]
  2 9241439211922391046 (by decide +kernel)

def r112 : Rule R := replay [r52, r71]
  [Sym1.X0, Sym1.X1, Sym1.X0] [Sym1.S01, Sym1.X0, Sym1.S01]
  2 54095972087103494 (by decide +kernel)

def r113 : Rule R := replay [r71, r81]
  [Sym1.X0, Sym1.X1, Sym1.X0] [Sym1.S02, Sym1.X1, Sym1.S02]
  2 9241439211922391046 (by decide +kernel)

def r114 : Rule R := replay [r39, r81]
  [Sym1.X0, Sym1.X1, Sym1.S02] [Sym1.S02, Sym1.X2, Sym1.X1]
  2 18102368030162948 (by decide +kernel)

def r115 : Rule R := replay [r39, r113]
  [Sym1.X0, Sym1.X1, Sym1.S02] [Sym1.S02, Sym1.X1, Sym1.X2]
  2 9277573579237493762 (by decide +kernel)

def r116 : Rule R := replay [r71, r75]
  [Sym1.X0, Sym1.X1, Sym1.S12] [Sym1.X1, Sym1.S12, Sym1.X0]
  2 18137560992187394 (by decide +kernel)

def r117 : Rule R := replay [r51, r85]
  [Sym1.X0, Sym1.X2, Sym1.K12] [Sym1.K12, Sym1.X0, Sym1.Z2]
  2 18102368030162948 (by decide +kernel)

def r118 : Rule R := replay [r26, r37, r108]
  [Sym1.X0, Sym1.CX01, Sym1.CX10] [Sym1.S01, Sym1.CX01, Sym1.X1]
  3 162260824254262488289666998992899 (by decide +kernel)

def r119 : Rule R := replay [r33, r75]
  [Sym1.X0, Sym1.CX01, Sym1.S12] [Sym1.S12, Sym1.X0, Sym1.CX02]
  2 9241474404884416516 (by decide +kernel)

def r120 : Rule R := replay [r34, r39, r82]
  [Sym1.X0, Sym1.CX02, Sym1.CX20] [Sym1.S02, Sym1.CX02, Sym1.X2]
  3 162578356176589071857949410853892 (by decide +kernel)

def r121 : Rule R := replay [r36, r62]
  [Sym1.X0, Sym1.CX10, Sym1.X0] [Sym1.K01, Sym1.CX01, Sym1.K01]
  2 54095972087103494 (by decide +kernel)

def r122 : Rule R := replay [r39, r62]
  [Sym1.X0, Sym1.CX10, Sym1.S02] [Sym1.CX10, Sym1.S02, Sym1.X2]
  2 9241509597846440962 (by decide +kernel)

def r123 : Rule R := replay [r52, r54]
  [Sym1.X0, Sym1.CX12, Sym1.S01] [Sym1.S01, Sym1.X1, Sym1.CX02]
  2 18102368030162948 (by decide +kernel)

def r124 : Rule R := replay [r39, r73]
  [Sym1.X0, Sym1.CX21, Sym1.S02] [Sym1.CX21, Sym1.S02, Sym1.X2]
  2 9241509597846440962 (by decide +kernel)

def r125 : Rule R := replay [r39, r56]
  [Sym1.X0, Sym1.CCX01, Sym1.S02] [Sym1.S02, Sym1.X2, Sym1.CCX12]
  2 18102368030162948 (by decide +kernel)

def r126 : Rule R := replay [r57, r75]
  [Sym1.X0, Sym1.CCX01, Sym1.S12] [Sym1.S12, Sym1.X0, Sym1.CCX02]
  2 9241474404884414468 (by decide +kernel)

def r127 : Rule R := replay [r38, r52]
  [Sym1.X0, Sym1.CCX02, Sym1.S01] [Sym1.S01, Sym1.X1, Sym1.CCX12]
  2 9241474404884414468 (by decide +kernel)

def r128 : Rule R := replay [r56, r61]
  [Sym1.X0, Sym1.CCX12, Sym1.X0] [Sym1.S02, Sym1.CCX01, Sym1.S02]
  2 18067175068139526 (by decide +kernel)

def r129 : Rule R := replay [r38, r52]
  [Sym1.X0, Sym1.CCX12, Sym1.S01] [Sym1.S01, Sym1.X1, Sym1.CCX02]
  2 9241474404884416516 (by decide +kernel)

def r130 : Rule R := replay [r39, r128]
  [Sym1.X0, Sym1.CCX12, Sym1.S02] [Sym1.S02, Sym1.CCX01, Sym1.X2]
  2 9277573579237493762 (by decide +kernel)

def r131 : Rule R := replay [r74, r75]
  [Sym1.X0, Sym1.Z1, Sym1.S12] [Sym1.Z1, Sym1.S12, Sym1.X0]
  2 18137560992187394 (by decide +kernel)

def r132 : Rule R := replay [r42, r75]
  [Sym1.X0, Sym1.CZ01, Sym1.S12] [Sym1.S12, Sym1.X0, Sym1.CZ02]
  2 9241474404884416516 (by decide +kernel)

def r133 : Rule R := replay [r52, r107]
  [Sym1.X0, Sym1.S01, Sym1.X1] [Sym1.S02, Sym1.S01, Sym1.S12]
  2 9277468008941357062 (by decide +kernel)

def r134 : Rule R := replay [r52, r114, r115]
  [Sym1.X0, Sym1.S01, Sym1.X2] [Sym1.S01, Sym1.X2, Sym1.X1]
  3 319079347366539243091781487618 (by decide +kernel)

def r135 : Rule R := replay [r37, r118]
  [Sym1.X0, Sym1.S01, Sym1.CX01] [Sym1.S01, Sym1.CX01, Sym1.X1]
  2 87960930751495 (by decide +kernel)

def r136 : Rule R := replay [r52, r77]
  [Sym1.X0, Sym1.S01, Sym1.CX02] [Sym1.S01, Sym1.CX02, Sym1.X1]
  2 18137560992187394 (by decide +kernel)

def r137 : Rule R := replay [r52, r78]
  [Sym1.X0, Sym1.S01, Sym1.CX20] [Sym1.S01, Sym1.CX20, Sym1.X1]
  2 18137560992187394 (by decide +kernel)

def r138 : Rule R := replay [r52, r81]
  [Sym1.X0, Sym1.S01, Sym1.S02] [Sym1.S01, Sym1.S02, Sym1.X1]
  2 18137560992187394 (by decide +kernel)

def r139 : Rule R := replay [r81, r115]
  [Sym1.X0, Sym1.S02, Sym1.X1] [Sym1.S02, Sym1.X1, Sym1.X2]
  2 18102359440233479 (by decide +kernel)

def r140 : Rule R := replay [r34, r120]
  [Sym1.X0, Sym1.S02, Sym1.CX02] [Sym1.S02, Sym1.CX02, Sym1.X2]
  2 87960930751495 (by decide +kernel)

def r141 : Rule R := replay [r39, r83]
  [Sym1.X0, Sym1.S02, Sym1.CCX01] [Sym1.S02, Sym1.CCX01, Sym1.X2]
  2 18137560992187394 (by decide +kernel)

def r142 : Rule R := replay [r139, r141]
  [Sym1.X1, Sym1.X2, Sym1.X1] [Sym1.CCX01, Sym1.X2, Sym1.CCX01]
  2 9295552776195016710 (by decide +kernel)

def r143 : Rule R := replay [r134, r135]
  [Sym1.X1, Sym1.X2, Sym1.CX01] [Sym1.X2, Sym1.CX01, Sym1.X1]
  2 36222328245848066 (by decide +kernel)

def r144 : Rule R := replay [r37, r76]
  [Sym1.X1, Sym1.CX01, Sym1.X1] [Sym1.S01, Sym1.CX01, Sym1.CX10]
  2 52776558657542 (by decide +kernel)

def r145 : Rule R := replay [r33, r76]
  [Sym1.X1, Sym1.CX01, Sym1.X1] [Sym1.S12, Sym1.CX02, Sym1.S12]
  2 18067175068139526 (by decide +kernel)

def r146 : Rule R := replay [r33, r77]
  [Sym1.X1, Sym1.CX02, Sym1.X1] [Sym1.S12, Sym1.CX01, Sym1.S12]
  2 54095972087103494 (by decide +kernel)

def r147 : Rule R := replay [r28, r77]
  [Sym1.X1, Sym1.CX02, Sym1.K12] [Sym1.CX02, Sym1.K12, Sym1.Z1]
  2 9241509597846440962 (by decide +kernel)

def r148 : Rule R := replay [r28, r31]
  [Sym1.X1, Sym1.CX12, Sym1.K12] [Sym1.K12, Sym1.Z1, Sym1.CX21]
  2 18102368030162948 (by decide +kernel)

def r149 : Rule R := replay [r56, r81]
  [Sym1.X1, Sym1.CCX01, Sym1.S02] [Sym1.S02, Sym1.X1, Sym1.CCX12]
  2 9241474404884414468 (by decide +kernel)

def r150 : Rule R := replay [r57, r79]
  [Sym1.X1, Sym1.CCX02, Sym1.X1] [Sym1.S12, Sym1.CCX01, Sym1.S12]
  2 18067175068139526 (by decide +kernel)

def r151 : Rule R := replay [r79, r81]
  [Sym1.X1, Sym1.CCX02, Sym1.S02] [Sym1.CCX02, Sym1.S02, Sym1.X1]
  2 18137560992187394 (by decide +kernel)

def r152 : Rule R := replay [r33, r82]
  [Sym1.X2, Sym1.CX02, Sym1.X2] [Sym1.S12, Sym1.CX01, Sym1.S12]
  2 54095972087103494 (by decide +kernel)

def r153 : Rule R := replay [r63, r84]
  [Sym1.X2, Sym1.K01, Sym1.X2] [Sym1.K12, Sym1.K01, Sym1.K12]
  2 18067175068139526 (by decide +kernel)

def r154 : Rule R := replay [r85, r153]
  [Sym1.X2, Sym1.K01, Sym1.K12] [Sym1.K12, Sym1.K01, Sym1.Z2]
  2 9277573579237491714 (by decide +kernel)

def r155 : Rule R := replay [r63, r154]
  [Sym1.X2, Sym1.K12, Sym1.K01] [Sym1.K12, Sym1.K01, Sym1.Z2]
  2 18102359440233479 (by decide +kernel)

def r156 : Rule R := replay [r33]
  [Sym1.CX01, Sym1.CX02, Sym1.S12] [Sym1.S12, Sym1.CX02, Sym1.CX01]
  2 18102368029638660 (by decide +kernel)

def r157 : Rule R := replay [r37, r38]
  [Sym1.CX01, Sym1.CX10, Sym1.CX01] [Sym1.CCX12, Sym1.S01, Sym1.CCX02]
  2 9259453610431874054 (by decide +kernel)

def r158 : Rule R := replay [r37, r107]
  [Sym1.CX01, Sym1.CX10, Sym1.CX01] [Sym1.S12, Sym1.S01, Sym1.S02]
  2 9241439211922392070 (by decide +kernel)

def r159 : Rule R := replay [r38, r60, r86]
  [Sym1.CX01, Sym1.CX10, Sym1.CCX02] [Sym1.CCX12, Sym1.CX10, Sym1.S01]
  3 5316912302218708626663415716108042244 (by decide +kernel)

def r160 : Rule R := replay [r86, r107]
  [Sym1.CX01, Sym1.CX10, Sym1.S02] [Sym1.CX10, Sym1.S12, Sym1.S01]
  2 54166358011151362 (by decide +kernel)

def r161 : Rule R := replay [r33, r158]
  [Sym1.CX01, Sym1.CX10, Sym1.S12] [Sym1.S02, Sym1.S01, Sym1.CX02]
  2 9277573579237493762 (by decide +kernel)

def r162 : Rule R := replay [r54, r161]
  [Sym1.CX01, Sym1.CX10, Sym1.S12] [Sym1.S02, Sym1.CX12, Sym1.S01]
  2 151115727539789577584646 (by decide +kernel)

def r163 : Rule R := replay [r33, r87, r95]
  [Sym1.CX01, Sym1.CX12, Sym1.CX21] [Sym1.CX21, Sym1.S12, Sym1.CX02]
  3 162578356176570661142672721313796 (by decide +kernel)

def r164 : Rule R := replay [r32, r33]
  [Sym1.CX01, Sym1.CX12, Sym1.CX21] [Sym1.S12, Sym1.CX02, Sym1.CX12]
  2 9241474404884415492 (by decide +kernel)

def r165 : Rule R := replay [r32, r163]
  [Sym1.CX01, Sym1.CX21, Sym1.S12] [Sym1.S12, Sym1.CX12, Sym1.CX02]
  2 87960930751495 (by decide +kernel)

def r166 : Rule R := replay [r33, r97]
  [Sym1.CX01, Sym1.CX21, Sym1.S12] [Sym1.S12, Sym1.CX02, Sym1.CX12]
  2 18102368030164996 (by decide +kernel)

def r167 : Rule R := replay [r33, r57]
  [Sym1.CX01, Sym1.CCX01, Sym1.S12] [Sym1.S12, Sym1.CX02, Sym1.CCX02]
  2 18102368030162948 (by decide +kernel)

def r168 : Rule R := replay [r89, r100, r157, r159]
  [Sym1.CX01, Sym1.CCX02, Sym1.CX01] [Sym1.Z2, Sym1.CCX02, Sym1.Z2]
  4 2860086905265490412247462007033649911010689026 (by decide +kernel)

def r169 : Rule R := replay [r37, r89, r159]
  [Sym1.CX01, Sym1.CCX02, Sym1.CX01] [Sym1.S01, Sym1.CCX12, Sym1.S01]
  3 2166546202959745750745481218 (by decide +kernel)

def r170 : Rule R := replay [r38, r57, r169]
  [Sym1.CX01, Sym1.CCX02, Sym1.CX01] [Sym1.S12, Sym1.CCX01, Sym1.S12]
  3 162577117934299884900303663792134 (by decide +kernel)

def r171 : Rule R := replay [r86, r100, r168]
  [Sym1.CX01, Sym1.CCX02, Sym1.CX10] [Sym1.CCX02, Sym1.CX10, Sym1.S01]
  3 2658456943855206975327882575193571332 (by decide +kernel)

def r172 : Rule R := replay [r69, r86, r171]
  [Sym1.CX01, Sym1.CCX02, Sym1.CCX12] [Sym1.CCX12, Sym1.CCX02, Sym1.CX01]
  3 2658780829821656442934712319153800198 (by decide +kernel)

def r173 : Rule R := replay [r33, r170]
  [Sym1.CX01, Sym1.CCX02, Sym1.S12] [Sym1.S12, Sym1.CCX01, Sym1.CX02]
  2 9277573579237493762 (by decide +kernel)

def r174 : Rule R := replay [r36, r37]
  [Sym1.CX01, Sym1.K01, Sym1.CX01] [Sym1.S01, Sym1.CX01, Sym1.K01]
  2 9223460006374933508 (by decide +kernel)

def r175 : Rule R := replay [r35, r36]
  [Sym1.CX01, Sym1.K01, Sym1.CX10] [Sym1.S02, Sym1.K12, Sym1.S02]
  2 54095972087105542 (by decide +kernel)

def r176 : Rule R := replay [r36, r93]
  [Sym1.CX01, Sym1.K01, Sym1.CX20] [Sym1.K01, Sym1.CX20, Sym1.CX10]
  2 18137560992187394 (by decide +kernel)

def r177 : Rule R := replay [r160, r162, r175]
  [Sym1.CX01, Sym1.K01, Sym1.S02] [Sym1.S02, Sym1.K12, Sym1.CX12]
  3 324521029840736842677702514704387 (by decide +kernel)

def r178 : Rule R := replay [r35, r177]
  [Sym1.CX01, Sym1.K01, Sym1.S02] [Sym1.K01, Sym1.S02, Sym1.CX12]
  2 87960930746374 (by decide +kernel)

def r179 : Rule R := replay [r31, r177]
  [Sym1.CX01, Sym1.K01, Sym1.S02] [Sym1.S02, Sym1.CX21, Sym1.K12]
  2 151115763568586596548614 (by decide +kernel)

def r180 : Rule R := replay [r25, r106]
  [Sym1.CX01, Sym1.K12, Sym1.CZ01] [Sym1.S12, Sym1.K12, Sym1.S12]
  2 9241439211922393094 (by decide +kernel)

def r181 : Rule R := replay [r42, r180]
  [Sym1.CX01, Sym1.K12, Sym1.S12] [Sym1.S12, Sym1.K12, Sym1.CZ02]
  2 9223512791523003394 (by decide +kernel)

def r182 : Rule R := replay [r33, r106]
  [Sym1.CX01, Sym1.K12, Sym1.S12] [Sym1.S12, Sym1.CX02, Sym1.K12]
  2 18102368030162948 (by decide +kernel)

def r183 : Rule R := replay [r37, r162]
  [Sym1.CX01, Sym1.S01, Sym1.S02] [Sym1.S12, Sym1.S01, Sym1.CX12]
  2 9295552776195017732 (by decide +kernel)

def r184 : Rule R := replay [r174, r177, r179]
  [Sym1.CX01, Sym1.S01, Sym1.S02] [Sym1.S02, Sym1.CX12, Sym1.CX21]
  3 163529712794530075129032639250435 (by decide +kernel)

def r185 : Rule R := replay [r95, r184]
  [Sym1.CX01, Sym1.S01, Sym1.S02] [Sym1.S02, Sym1.CX21, Sym1.S12]
  2 151115781582985106030598 (by decide +kernel)

def r186 : Rule R := replay [r35, r107, r179]
  [Sym1.CX01, Sym1.S01, Sym1.S12] [Sym1.S02, Sym1.CX21, Sym1.S01]
  3 952904345258458370639378515972 (by decide +kernel)

def r187 : Rule R := replay [r33, r185, r186]
  [Sym1.CX01, Sym1.S01, Sym1.S12] [Sym1.S12, Sym1.CX02, Sym1.S02]
  3 318460226231187097923418589189 (by decide +kernel)

def r188 : Rule R := replay [r107, r184]
  [Sym1.CX01, Sym1.S02, Sym1.CX12] [Sym1.S12, Sym1.S01, Sym1.CX21]
  2 18102359440233479 (by decide +kernel)

def r189 : Rule R := replay [r55, r188]
  [Sym1.CX01, Sym1.S02, Sym1.CX12] [Sym1.S12, Sym1.CX20, Sym1.S01]
  2 151115763568586596548614 (by decide +kernel)

def r190 : Rule R := replay [r54, r189]
  [Sym1.CX01, Sym1.S02, Sym1.S01] [Sym1.S12, Sym1.CX20, Sym1.CX02]
  2 9223512791523001346 (by decide +kernel)

def r191 : Rule R := replay [r35, r55, r179]
  [Sym1.CX01, Sym1.S02, Sym1.S01] [Sym1.S02, Sym1.S01, Sym1.CX20]
  3 952904345258458405832340538370 (by decide +kernel)

def r192 : Rule R := replay [r107, r187]
  [Sym1.CX01, Sym1.S02, Sym1.S01] [Sym1.S12, Sym1.CX02, Sym1.S02]
  2 9223477598560977924 (by decide +kernel)

def r193 : Rule R := replay [r32, r188]
  [Sym1.CX01, Sym1.S02, Sym1.S12] [Sym1.S12, Sym1.S01, Sym1.CX12]
  2 9223512791523000322 (by decide +kernel)

def r194 : Rule R := replay [r156, r187]
  [Sym1.CX01, Sym1.S02, Sym1.S12] [Sym1.S12, Sym1.CX02, Sym1.S01]
  2 140746078816261 (by decide +kernel)

def r195 : Rule R := replay [r97, r165]
  [Sym1.CX01, Sym1.S12, Sym1.CX12] [Sym1.S12, Sym1.CX12, Sym1.CX02]
  2 18102359440233479 (by decide +kernel)

def r196 : Rule R := replay [r33, r53]
  [Sym1.CX01, Sym1.S12, Sym1.S02] [Sym1.S12, Sym1.S02, Sym1.CX20]
  2 18137560992189442 (by decide +kernel)

def r197 : Rule R := replay [r92, r165, r166]
  [Sym1.CX02, Sym1.CX10, Sym1.CX12] [Sym1.CX12, Sym1.CX02, Sym1.CX10]
  3 162896506615569741162373181341700 (by decide +kernel)

def r198 : Rule R := replay [r90, r176, r178]
  [Sym1.CX02, Sym1.CX10, Sym1.CX20] [Sym1.CX20, Sym1.CX12, Sym1.S02]
  3 952904647489895295082534800388 (by decide +kernel)

def r199 : Rule R := replay [r53, r198]
  [Sym1.CX02, Sym1.CX10, Sym1.S02] [Sym1.CX20, Sym1.CX12, Sym1.CX02]
  2 9223512791523001346 (by decide +kernel)

def r200 : Rule R := replay [r34, r160, r162]
  [Sym1.CX02, Sym1.CX10, Sym1.S02] [Sym1.CX20, Sym1.CX02, Sym1.CX12]
  3 635372876288244501082742456323 (by decide +kernel)

def r201 : Rule R := replay [r31, r33, r195]
  [Sym1.CX02, Sym1.CX12, Sym1.CX02] [Sym1.K12, Sym1.CX21, Sym1.K12]
  3 951666405219173078316819677186 (by decide +kernel)

def r202 : Rule R := replay [r33, r54, r195]
  [Sym1.CX02, Sym1.CX12, Sym1.CX02] [Sym1.S01, Sym1.CX02, Sym1.S01]
  3 163210943234432536469894829441026 (by decide +kernel)

def r203 : Rule R := replay [r34, r199]
  [Sym1.CX02, Sym1.CX12, Sym1.CX02] [Sym1.S02, Sym1.CX10, Sym1.S02]
  2 123153892770821 (by decide +kernel)

def r204 : Rule R := replay [r31, r181, r182]
  [Sym1.CX02, Sym1.CX12, Sym1.K12] [Sym1.K12, Sym1.CZ02, Sym1.CX21]
  3 163846315959595685750440426733572 (by decide +kernel)

def r205 : Rule R := replay [r54, r202]
  [Sym1.CX02, Sym1.CX12, Sym1.S01] [Sym1.S01, Sym1.CX02, Sym1.CX12]
  2 9277573579237493762 (by decide +kernel)

def r206 : Rule R := replay [r54, r205]
  [Sym1.CX02, Sym1.CX12, Sym1.S01] [Sym1.CX12, Sym1.S01, Sym1.CX12]
  2 87960930746374 (by decide +kernel)

def r207 : Rule R := replay [r195, r196]
  [Sym1.CX02, Sym1.CX12, Sym1.S02] [Sym1.CX12, Sym1.S02, Sym1.CX20]
  2 36222328245848066 (by decide +kernel)

def r208 : Rule R := replay [r34, r56]
  [Sym1.CX02, Sym1.CX20, Sym1.CX02] [Sym1.CCX12, Sym1.S02, Sym1.CCX01]
  2 9259453610431874054 (by decide +kernel)

def r209 : Rule R := replay [r34, r40]
  [Sym1.CX02, Sym1.CX20, Sym1.CX02] [Sym1.Z2, Sym1.S02, Sym1.Z0]
  2 9223424813412910086 (by decide +kernel)

def r210 : Rule R := replay [r33, r190]
  [Sym1.CX02, Sym1.CX20, Sym1.CX02] [Sym1.S12, Sym1.S02, Sym1.S01]
  2 54166349421216773 (by decide +kernel)

def r211 : Rule R := replay [r34, r91]
  [Sym1.CX02, Sym1.CX20, Sym1.CCX01] [Sym1.S02, Sym1.CCX01, Sym1.CX02]
  2 123162482705410 (by decide +kernel)

def r212 : Rule R := replay [r56, r211]
  [Sym1.CX02, Sym1.CX20, Sym1.CCX01] [Sym1.CCX12, Sym1.S02, Sym1.CX02]
  2 36116757949710342 (by decide +kernel)

def r213 : Rule R := replay [r53, r212]
  [Sym1.CX02, Sym1.CX20, Sym1.CCX01] [Sym1.CCX12, Sym1.CX20, Sym1.S02]
  2 151115727539789577584646 (by decide +kernel)

def r214 : Rule R := replay [r56, r90]
  [Sym1.CX02, Sym1.CX20, Sym1.CCX01] [Sym1.CX20, Sym1.CCX12, Sym1.S02]
  2 9277538394865401858 (by decide +kernel)

def r215 : Rule R := replay [r33, r189]
  [Sym1.CX02, Sym1.CX20, Sym1.S01] [Sym1.S12, Sym1.S02, Sym1.CX12]
  2 54166349421216773 (by decide +kernel)

def r216 : Rule R := replay [r161, r191]
  [Sym1.CX02, Sym1.CX20, Sym1.S01] [Sym1.S12, Sym1.CX10, Sym1.S02]
  2 54183941607263236 (by decide +kernel)

def r217 : Rule R := replay [r90, r98]
  [Sym1.CX02, Sym1.CX20, Sym1.S02] [Sym1.CCX12, Sym1.CX20, Sym1.CCX12]
  2 9241439211922391046 (by decide +kernel)

def r218 : Rule R := replay [r33, r173]
  [Sym1.CX02, Sym1.CCX01, Sym1.CX02] [Sym1.S12, Sym1.CCX02, Sym1.S12]
  2 54166349421216773 (by decide +kernel)

def r219 : Rule R := replay [r31, r41, r204]
  [Sym1.CX02, Sym1.CCX01, Sym1.K12] [Sym1.K12, Sym1.CZ02, Sym1.CCX02]
  3 952904345258458370639378513924 (by decide +kernel)

def r220 : Rule R := replay [r91, r219]
  [Sym1.CX02, Sym1.CCX01, Sym1.K12] [Sym1.K12, Sym1.CCX02, Sym1.CZ02]
  2 9295552776195014660 (by decide +kernel)

def r221 : Rule R := replay [r34, r213]
  [Sym1.CX02, Sym1.CCX01, Sym1.S02] [Sym1.S02, Sym1.CCX12, Sym1.CX20]
  2 123153892771844 (by decide +kernel)

def r222 : Rule R := replay [r34, r214]
  [Sym1.CX02, Sym1.CCX01, Sym1.S02] [Sym1.S02, Sym1.CX20, Sym1.CCX12]
  2 123153892771844 (by decide +kernel)

def r223 : Rule R := replay [r54, r58]
  [Sym1.CX02, Sym1.Z1, Sym1.S01] [Sym1.S01, Sym1.CX12, Sym1.Z0]
  2 18102368030162948 (by decide +kernel)

def r224 : Rule R := replay [r41, r220]
  [Sym1.CX02, Sym1.K12, Sym1.CCX02] [Sym1.K12, Sym1.CCX02, Sym1.CZ02]
  2 54131156459197447 (by decide +kernel)

def r225 : Rule R := replay [r147, r148, r204]
  [Sym1.CX02, Sym1.K12, Sym1.Z1] [Sym1.K12, Sym1.Z1, Sym1.CZ02]
  3 1270436267566541274806445670405 (by decide +kernel)

def r226 : Rule R := replay [r31, r43, r204]
  [Sym1.CX02, Sym1.K12, Sym1.S01] [Sym1.K12, Sym1.S01, Sym1.CZ12]
  3 952904345258458405832340540418 (by decide +kernel)

def r227 : Rule R := replay [r34, r215]
  [Sym1.CX02, Sym1.S01, Sym1.CX12] [Sym1.S02, Sym1.S12, Sym1.S02]
  2 123153892771844 (by decide +kernel)

def r228 : Rule R := replay [r33, r193]
  [Sym1.CX02, Sym1.S01, Sym1.CX12] [Sym1.S12, Sym1.S02, Sym1.S12]
  2 54166349421216773 (by decide +kernel)

def r229 : Rule R := replay [r54, r96]
  [Sym1.CX02, Sym1.S01, Sym1.CCX01] [Sym1.S01, Sym1.CCX01, Sym1.CX12]
  2 18137560992187394 (by decide +kernel)

def r230 : Rule R := replay [r34, r217]
  [Sym1.CX02, Sym1.S02, Sym1.CCX12] [Sym1.S02, Sym1.CCX12, Sym1.CX20]
  2 123153892771844 (by decide +kernel)

def r231 : Rule R := replay [r197, r203]
  [Sym1.CX10, Sym1.CX12, Sym1.CX10] [Sym1.S02, Sym1.CX10, Sym1.S02]
  2 9277538377685533702 (by decide +kernel)

def r232 : Rule R := replay [r160, r164, r216]
  [Sym1.CX10, Sym1.CX12, Sym1.CX21] [Sym1.S12, Sym1.CX20, Sym1.CX12]
  3 1587658402633491992659012092932 (by decide +kernel)

def r233 : Rule R := replay [r92, r94]
  [Sym1.CX10, Sym1.CX12, Sym1.CZ12] [Sym1.CX12, Sym1.CZ12, Sym1.CX10]
  2 18137560992187394 (by decide +kernel)

def r234 : Rule R := replay [r200]
  [Sym1.CX10, Sym1.CX12, Sym1.S02] [Sym1.S02, Sym1.CX12, Sym1.CX10]
  2 72215932302264325 (by decide +kernel)

def r235 : Rule R := replay [r92, r234]
  [Sym1.CX10, Sym1.CX12, Sym1.S02] [Sym1.S02, Sym1.CX10, Sym1.CX12]
  2 9241509580666568708 (by decide +kernel)

def r236 : Rule R := replay [r92, r232]
  [Sym1.CX10, Sym1.CX12, Sym1.S12] [Sym1.CX21, Sym1.CX12, Sym1.CX20]
  2 9295552776195014660 (by decide +kernel)

def r237 : Rule R := replay [r32, r236]
  [Sym1.CX10, Sym1.CX12, Sym1.S12] [Sym1.CX12, Sym1.S12, Sym1.CX20]
  2 18102359440228358 (by decide +kernel)

def r238 : Rule R := replay [r32, r236]
  [Sym1.CX10, Sym1.CX21, Sym1.CX12] [Sym1.CX21, Sym1.CX12, Sym1.CX20]
  2 36116757949715463 (by decide +kernel)

def r239 : Rule R := replay [r200, r208]
  [Sym1.CX10, Sym1.CCX01, Sym1.S02] [Sym1.S02, Sym1.CX12, Sym1.CCX12]
  2 72215932302789636 (by decide +kernel)

def r240 : Rule R := replay [r69, r86, r159]
  [Sym1.CX10, Sym1.CCX02, Sym1.CX10] [Sym1.CCX02, Sym1.CCX12, Sym1.CCX02]
  3 1269816995306202312168524745733 (by decide +kernel)

def r241 : Rule R := replay [r60, r240]
  [Sym1.CX10, Sym1.CCX02, Sym1.CX10] [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12]
  3 2166697309499871923152622596 (by decide +kernel)

def r242 : Rule R := replay [r60, r241]
  [Sym1.CX10, Sym1.CCX02, Sym1.CCX12] [Sym1.CCX12, Sym1.CCX02, Sym1.CX10]
  2 123153892773892 (by decide +kernel)

def r243 : Rule R := replay [r105, r233, r237]
  [Sym1.CX10, Sym1.CZ12, Sym1.S12] [Sym1.S12, Sym1.CZ12, Sym1.CX20]
  3 318460075115423670082900854786 (by decide +kernel)

def r244 : Rule R := replay [r94, r243]
  [Sym1.CX10, Sym1.CZ12, Sym1.S12] [Sym1.S12, Sym1.CX20, Sym1.CZ12]
  2 9295552776195014660 (by decide +kernel)

def r245 : Rule R := replay [r68, r109, r238]
  [Sym1.CX12, Sym1.CX20, Sym1.CCX12] [Sym1.CX20, Sym1.CCX12, Sym1.CX12]
  3 162895578009424513734510861356035 (by decide +kernel)

def r246 : Rule R := replay [r183, r184]
  [Sym1.CX12, Sym1.CX21, Sym1.CX12] [Sym1.S02, Sym1.S12, Sym1.S01]
  2 9241579966590618626 (by decide +kernel)

def r247 : Rule R := replay [r107, r246]
  [Sym1.CX12, Sym1.CX21, Sym1.CX12] [Sym1.S02, Sym1.S01, Sym1.S02]
  2 54131156459195399 (by decide +kernel)

def r248 : Rule R := replay [r38, r98]
  [Sym1.CX20, Sym1.CCX12, Sym1.CX20] [Sym1.S01, Sym1.CCX02, Sym1.S01]
  2 18067175068139526 (by decide +kernel)

def r249 : Rule R := replay [r57]
  [Sym1.CCX01, Sym1.CCX02, Sym1.S12] [Sym1.S12, Sym1.CCX02, Sym1.CCX01]
  2 54131165048604676 (by decide +kernel)

def r250 : Rule R := replay [r99, r104]
  [Sym1.CCX01, Sym1.Z1, Sym1.CCX01] [Sym1.S02, Sym1.Z1, Sym1.S02]
  2 9241439211922391046 (by decide +kernel)

def r251 : Rule R := replay [r56, r250]
  [Sym1.CCX01, Sym1.Z1, Sym1.S02] [Sym1.S02, Sym1.Z1, Sym1.CCX12]
  2 9277573579237491714 (by decide +kernel)

def r252 : Rule R := replay [r38, r57, r107]
  [Sym1.CCX01, Sym1.S01, Sym1.S02] [Sym1.S12, Sym1.S01, Sym1.CCX12]
  3 163212181476684739814624053952516 (by decide +kernel)

def r253 : Rule R := replay [r107, r252]
  [Sym1.CCX01, Sym1.S01, Sym1.S02] [Sym1.S01, Sym1.S02, Sym1.CCX12]
  2 87960930746374 (by decide +kernel)

def r254 : Rule R := replay [r34, r210, r253]
  [Sym1.CCX01, Sym1.S01, Sym1.S02] [Sym1.S02, Sym1.S12, Sym1.CCX12]
  3 2166395078026901082201915398 (by decide +kernel)

def r255 : Rule R := replay [r57, r107]
  [Sym1.CCX01, Sym1.S01, Sym1.S02] [Sym1.S12, Sym1.CCX02, Sym1.S01]
  2 54131165049126916 (by decide +kernel)

def r256 : Rule R := replay [r56, r253, r255]
  [Sym1.CCX01, Sym1.S01, Sym1.S12] [Sym1.S02, Sym1.S01, Sym1.CCX02]
  3 325788370653732965141705159344130 (by decide +kernel)

def r257 : Rule R := replay [r32, r247, r256]
  [Sym1.CCX01, Sym1.S01, Sym1.S12] [Sym1.S12, Sym1.S02, Sym1.CCX02]
  3 2166395077972875478859513862 (by decide +kernel)

def r258 : Rule R := replay [r56, r107]
  [Sym1.CCX01, Sym1.S01, Sym1.S12] [Sym1.S02, Sym1.CCX12, Sym1.S01]
  2 54131165049128964 (by decide +kernel)

def r259 : Rule R := replay [r208, r210]
  [Sym1.CCX01, Sym1.S02, Sym1.CCX12] [Sym1.S12, Sym1.S02, Sym1.S01]
  2 9223477589971045382 (by decide +kernel)

def r260 : Rule R := replay [r104, r251]
  [Sym1.CCX01, Sym1.S02, Sym1.Z1] [Sym1.S02, Sym1.Z1, Sym1.CCX12]
  2 18102359440233479 (by decide +kernel)

def r261 : Rule R := replay [r38, r56]
  [Sym1.CCX01, Sym1.S02, Sym1.S01] [Sym1.S02, Sym1.S01, Sym1.CCX02]
  2 9277538394865404930 (by decide +kernel)

def r262 : Rule R := replay [r167, r192]
  [Sym1.CCX01, Sym1.S02, Sym1.S01] [Sym1.S12, Sym1.CCX02, Sym1.S02]
  2 72215932302787588 (by decide +kernel)

def r263 : Rule R := replay [r107, r254]
  [Sym1.CCX01, Sym1.S02, Sym1.S12] [Sym1.S12, Sym1.S01, Sym1.CCX12]
  2 18102359440233479 (by decide +kernel)

def r264 : Rule R := replay [r167, r194]
  [Sym1.CCX01, Sym1.S02, Sym1.S12] [Sym1.S12, Sym1.CCX02, Sym1.S01]
  2 72215932302787588 (by decide +kernel)

def r265 : Rule R := replay [r32, r246, r257]
  [Sym1.CCX01, Sym1.S12, Sym1.S02] [Sym1.S12, Sym1.S02, Sym1.CCX02]
  3 2166395078026901082201920519 (by decide +kernel)

def r266 : Rule R := replay [r240, r241]
  [Sym1.CCX02, Sym1.CCX12, Sym1.CCX02] [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12]
  2 36187135283825668 (by decide +kernel)

def r267 : Rule R := replay [r38]
  [Sym1.CCX02, Sym1.CCX12, Sym1.S01] [Sym1.S01, Sym1.CCX12, Sym1.CCX02]
  2 54131165048604676 (by decide +kernel)

def r268 : Rule R := replay [r58, r260, r261]
  [Sym1.CCX02, Sym1.Z0, Sym1.S01] [Sym1.S01, Sym1.Z1, Sym1.CCX12]
  3 2658619521283230738720440080011365378 (by decide +kernel)

def r269 : Rule R := replay [r58, r268]
  [Sym1.CCX02, Sym1.Z0, Sym1.S01] [Sym1.Z0, Sym1.S01, Sym1.CCX12]
  2 36116757949710342 (by decide +kernel)

def r270 : Rule R := replay [r259, r262, r269]
  [Sym1.CCX02, Sym1.Z0, Sym1.S02] [Sym1.Z0, Sym1.S02, Sym1.CCX02]
  3 5317075830074744204242390963855556612 (by decide +kernel)

def r271 : Rule R := replay [r40, r100, r270]
  [Sym1.CCX02, Sym1.Z0, Sym1.S02] [Sym1.S02, Sym1.CCX02, Sym1.Z2]
  3 319079347366503108724466384902 (by decide +kernel)

def r272 : Rule R := replay [r224, r226]
  [Sym1.CCX02, Sym1.CZ02, Sym1.CCX02] [Sym1.S01, Sym1.CZ12, Sym1.S01]
  2 9295552776195016710 (by decide +kernel)

def r273 : Rule R := replay [r38, r272]
  [Sym1.CCX02, Sym1.CZ02, Sym1.S01] [Sym1.S01, Sym1.CZ12, Sym1.CCX12]
  2 9277573579237491714 (by decide +kernel)

def r274 : Rule R := replay [r35, r57, r265]
  [Sym1.CCX02, Sym1.K01, Sym1.S02] [Sym1.S02, Sym1.CCX02, Sym1.K12]
  3 5316912619131358693016266089920202754 (by decide +kernel)

def r275 : Rule R := replay [r57, r263]
  [Sym1.CCX02, Sym1.S01, Sym1.CCX12] [Sym1.S12, Sym1.S02, Sym1.S12]
  2 18137552402252805 (by decide +kernel)

def r276 : Rule R := replay [r43, r273]
  [Sym1.CCX02, Sym1.S01, Sym1.CZ12] [Sym1.S01, Sym1.CZ12, Sym1.CCX12]
  2 18102359440233479 (by decide +kernel)

def r277 : Rule R := replay [r259, r264]
  [Sym1.CCX02, Sym1.S01, Sym1.S12] [Sym1.S02, Sym1.S01, Sym1.CCX12]
  2 90177545664201735 (by decide +kernel)

def r278 : Rule R := replay [r107, r277]
  [Sym1.CCX02, Sym1.S01, Sym1.S12] [Sym1.S01, Sym1.S12, Sym1.CCX12]
  2 36116757949710342 (by decide +kernel)

def r279 : Rule R := replay [r56, r57]
  [Sym1.CCX02, Sym1.S12, Sym1.S02] [Sym1.S12, Sym1.S02, Sym1.CCX12]
  2 9241509597846438914 (by decide +kernel)

def r280 : Rule R := replay [r38, r105, r276]
  [Sym1.CCX12, Sym1.CZ12, Sym1.CCX12] [Sym1.S12, Sym1.CZ12, Sym1.S12]
  3 162577117934318421769146477840386 (by decide +kernel)

def r281 : Rule R := replay [r38, r278, r280]
  [Sym1.CCX12, Sym1.CZ12, Sym1.S12] [Sym1.S12, Sym1.CZ12, Sym1.CCX12]
  3 2658782097472105555526804348501755906 (by decide +kernel)

def r282 : Rule R := replay [r105, r281]
  [Sym1.CCX12, Sym1.CZ12, Sym1.S12] [Sym1.CZ12, Sym1.S12, Sym1.CCX12]
  2 87960930746374 (by decide +kernel)

def r283 : Rule R := replay [r280, r282]
  [Sym1.CCX12, Sym1.CZ12, Sym1.S12] [Sym1.S12, Sym1.CCX12, Sym1.CZ12]
  2 54236726755332098 (by decide +kernel)

def r284 : Rule R := replay [r101, r104]
  [Sym1.Z0, Sym1.Z1, Sym1.Z0] [Sym1.S02, Sym1.Z1, Sym1.S02]
  2 9241439211922391046 (by decide +kernel)

def r285 : Rule R := replay [r40, r284]
  [Sym1.Z0, Sym1.Z1, Sym1.S02] [Sym1.S02, Sym1.Z1, Sym1.Z2]
  2 9277573579237493762 (by decide +kernel)

def r286 : Rule R := replay [r58, r225, r226]
  [Sym1.Z0, Sym1.CZ12, Sym1.S01] [Sym1.S01, Sym1.CZ02, Sym1.Z1]
  3 2658619204370278468672944520759871490 (by decide +kernel)

def r287 : Rule R := replay [r35, r102]
  [Sym1.Z0, Sym1.K12, Sym1.Z0] [Sym1.S02, Sym1.K01, Sym1.S02]
  2 18067175068139526 (by decide +kernel)

def r288 : Rule R := replay [r40, r287]
  [Sym1.Z0, Sym1.K12, Sym1.S02] [Sym1.S02, Sym1.K01, Sym1.Z2]
  2 9277573579237493762 (by decide +kernel)

def r289 : Rule R := replay [r58, r107]
  [Sym1.Z0, Sym1.S01, Sym1.Z1] [Sym1.S12, Sym1.S01, Sym1.S02]
  2 9241439211922393094 (by decide +kernel)

def r290 : Rule R := replay [r223, r227]
  [Sym1.Z0, Sym1.S01, Sym1.Z1] [Sym1.S02, Sym1.S12, Sym1.S02]
  2 9277538377685534727 (by decide +kernel)

def r291 : Rule R := replay [r223, r228]
  [Sym1.Z0, Sym1.S01, Sym1.Z1] [Sym1.S12, Sym1.S02, Sym1.S12]
  2 9277538377685534727 (by decide +kernel)

def r292 : Rule R := replay [r58, r103]
  [Sym1.Z0, Sym1.S01, Sym1.CZ01] [Sym1.S01, Sym1.CZ01, Sym1.Z1]
  2 18137560992187394 (by decide +kernel)

def r293 : Rule R := replay [r43, r286]
  [Sym1.Z0, Sym1.S01, Sym1.CZ02] [Sym1.S01, Sym1.CZ02, Sym1.Z1]
  2 54131156459197447 (by decide +kernel)

def r294 : Rule R := replay [r58, r104]
  [Sym1.Z0, Sym1.S01, Sym1.S02] [Sym1.S01, Sym1.S02, Sym1.Z1]
  2 18137560992187394 (by decide +kernel)

def r295 : Rule R := replay [r104, r290]
  [Sym1.Z0, Sym1.S01, Sym1.S02] [Sym1.S02, Sym1.S12, Sym1.Z1]
  2 9223512791523001346 (by decide +kernel)

def r296 : Rule R := replay [r289, r294]
  [Sym1.Z0, Sym1.S01, Sym1.S02] [Sym1.S12, Sym1.Z0, Sym1.S01]
  2 18137543812317190 (by decide +kernel)

def r297 : Rule R := replay [r209, r210]
  [Sym1.Z0, Sym1.S01, Sym1.S02] [Sym1.S02, Sym1.Z2, Sym1.S12]
  2 36187135283825668 (by decide +kernel)

def r298 : Rule R := replay [r296, r297]
  [Sym1.Z0, Sym1.S01, Sym1.S12] [Sym1.S12, Sym1.S02, Sym1.Z2]
  2 18207929736367106 (by decide +kernel)

def r299 : Rule R := replay [r38, r275, r298]
  [Sym1.Z0, Sym1.S01, Sym1.S12] [Sym1.S01, Sym1.S12, Sym1.Z2]
  3 952904345249144926601386917894 (by decide +kernel)

def r300 : Rule R := replay [r289, r295]
  [Sym1.Z0, Sym1.S01, Sym1.S12] [Sym1.S12, Sym1.Z0, Sym1.S02]
  2 175939040841730 (by decide +kernel)

def r301 : Rule R := replay [r104, r285]
  [Sym1.Z0, Sym1.S02, Sym1.Z1] [Sym1.S02, Sym1.Z1, Sym1.Z2]
  2 18102359440233479 (by decide +kernel)

def r302 : Rule R := replay [r35, r288]
  [Sym1.Z0, Sym1.S02, Sym1.K01] [Sym1.S02, Sym1.K01, Sym1.Z2]
  2 18102359440233479 (by decide +kernel)

def r303 : Rule R := replay [r291, r300]
  [Sym1.Z0, Sym1.S02, Sym1.S12] [Sym1.S02, Sym1.S12, Sym1.Z1]
  2 90177545664201735 (by decide +kernel)

def r304 : Rule R := replay [r301, r303]
  [Sym1.Z1, Sym1.Z2, Sym1.Z1] [Sym1.S12, Sym1.Z1, Sym1.S12]
  2 9295552776195016710 (by decide +kernel)

def r305 : Rule R := replay [r304]
  [Sym1.Z1, Sym1.Z2, Sym1.S12] [Sym1.S12, Sym1.Z2, Sym1.Z1]
  2 54236726754808834 (by decide +kernel)

def r306 : Rule R := replay [r42, r292, r299]
  [Sym1.Z1, Sym1.CZ01, Sym1.S12] [Sym1.S12, Sym1.CZ02, Sym1.Z2]
  3 318460075115423670082900854786 (by decide +kernel)

def r307 : Rule R := replay [r103, r306]
  [Sym1.Z1, Sym1.CZ01, Sym1.S12] [Sym1.S12, Sym1.Z2, Sym1.CZ02]
  2 9295552776195014660 (by decide +kernel)

def r308 : Rule R := replay [r42, r293, r299]
  [Sym1.Z1, Sym1.CZ02, Sym1.S12] [Sym1.S12, Sym1.CZ01, Sym1.Z2]
  3 952285375229538370831252457474 (by decide +kernel)

def r309 : Rule R := replay [r305, r307]
  [Sym1.Z1, Sym1.CZ02, Sym1.S12] [Sym1.S12, Sym1.Z2, Sym1.CZ01]
  2 140746078816261 (by decide +kernel)

def r310 : Rule R := replay [r42, r308]
  [Sym1.Z1, Sym1.S12, Sym1.CZ01] [Sym1.S12, Sym1.CZ01, Sym1.Z2]
  2 54131156459197447 (by decide +kernel)

def r311 : Rule R := replay [r302, r303]
  [Sym1.Z1, Sym1.S12, Sym1.K01] [Sym1.S12, Sym1.K01, Sym1.Z2]
  2 9259594365100099586 (by decide +kernel)

def r312 : Rule R := replay [r310, r311]
  [Sym1.Z2, Sym1.CZ01, Sym1.K01] [Sym1.CZ01, Sym1.K01, Sym1.Z2]
  2 36222328245848066 (by decide +kernel)

def r313 : Rule R := replay [r38, r169]
  [Sym1.CX01, Sym1.CCX02] [Sym1.CCX02, Sym1.CX01]
  2 123145302835204 (by decide +kernel)

def r314 : Rule R := replay [r35, r179]
  [Sym1.CX01, Sym1.S02] [Sym1.S02, Sym1.CX21]
  2 54166340831286277 (by decide +kernel)

def r315 : Rule R := replay [r31, r201]
  [Sym1.CX02, Sym1.CX12] [Sym1.CX12, Sym1.CX02]
  2 123145302835204 (by decide +kernel)

def r316 : Rule R := replay [r34, r200]
  [Sym1.CX10, Sym1.S02] [Sym1.S02, Sym1.CX12]
  2 123145302836228 (by decide +kernel)

def r317 : Rule R := replay [r252, r258]
  [Sym1.CCX01, Sym1.S01] [Sym1.S01, Sym1.CCX01]
  2 90265515184361475 (by decide +kernel)

def r318 : Rule R := replay [r35, r274]
  [Sym1.CCX02, Sym1.S02] [Sym1.S02, Sym1.CCX02]
  2 54166340831286277 (by decide +kernel)

def r319 : Rule R := replay [r105, r283]
  [Sym1.CCX12, Sym1.S12] [Sym1.S12, Sym1.CCX12]
  2 18137543812321284 (by decide +kernel)

def r320 : Rule R := replay [r42, r309]
  [Sym1.Z1, Sym1.S12] [Sym1.S12, Sym1.Z2]
  2 54166340831286277 (by decide +kernel)

def r321 : Rule R := replay [r34, r210]
  [Sym1.S01, Sym1.S02] [Sym1.S02, Sym1.S12]
  2 123145302838276 (by decide +kernel)

def r322 : Rule R := replay [r112, r134]
  [Sym1.X0, Sym1.X1, Sym1.X0] [Sym1.X2, Sym1.X1, Sym1.X2]
  2 9295552776195014662 (by decide +kernel)

def r323 : Rule R := replay [r50, r315]
  [Sym1.X0, Sym1.CX02, Sym1.CX12] [Sym1.CX12, Sym1.X0, Sym1.CX02]
  2 87969520680964 (by decide +kernel)

def r324 : Rule R := replay [r121, r178]
  [Sym1.X0, Sym1.CX10, Sym1.X0] [Sym1.S02, Sym1.CX12, Sym1.S02]
  2 9295552776195014662 (by decide +kernel)

def r325 : Rule R := replay [r122, r316]
  [Sym1.X0, Sym1.CX10, Sym1.S02] [Sym1.S02, Sym1.CX12, Sym1.X2]
  2 9277503193313443846 (by decide +kernel)

def r326 : Rule R := replay [r39, r316]
  [Sym1.X0, Sym1.CX10, Sym1.S02] [Sym1.S02, Sym1.X2, Sym1.CX12]
  2 18102368030162948 (by decide +kernel)

def r327 : Rule R := replay [r203, r323]
  [Sym1.X0, Sym1.CX12, Sym1.X0] [Sym1.S02, Sym1.CX10, Sym1.S02]
  2 54166340831285254 (by decide +kernel)

def r328 : Rule R := replay [r39, r316]
  [Sym1.X0, Sym1.CX12, Sym1.S02] [Sym1.S02, Sym1.X2, Sym1.CX10]
  2 18102368030164996 (by decide +kernel)

def r329 : Rule R := replay [r124, r314]
  [Sym1.X0, Sym1.CX21, Sym1.S02] [Sym1.S02, Sym1.CX01, Sym1.X2]
  2 9241474396294479878 (by decide +kernel)

def r330 : Rule R := replay [r52, r317]
  [Sym1.X0, Sym1.CCX01, Sym1.S01] [Sym1.S01, Sym1.X1, Sym1.CCX01]
  2 18102368030162948 (by decide +kernel)

def r331 : Rule R := replay [r131, r320]
  [Sym1.X0, Sym1.Z1, Sym1.S12] [Sym1.S12, Sym1.Z2, Sym1.X0]
  2 9277503193313443846 (by decide +kernel)

def r332 : Rule R := replay [r132, r308, r331]
  [Sym1.X0, Sym1.Z2, Sym1.X0] [Sym1.CZ01, Sym1.Z2, Sym1.CZ01]
  3 1587968038749817435111715505157 (by decide +kernel)

def r333 : Rule R := replay [r312, r332]
  [Sym1.X0, Sym1.Z2, Sym1.X0] [Sym1.K01, Sym1.Z2, Sym1.K01]
  2 72180739340763142 (by decide +kernel)

def r334 : Rule R := replay [r155, r333]
  [Sym1.X0, Sym1.Z2, Sym1.X0] [Sym1.K12, Sym1.X2, Sym1.K12]
  2 18137543812317190 (by decide +kernel)

def r335 : Rule R := replay [r138, r321]
  [Sym1.X0, Sym1.S01, Sym1.S02] [Sym1.S02, Sym1.S12, Sym1.X1]
  2 9277503193313443846 (by decide +kernel)

def r336 : Rule R := replay [r39, r321]
  [Sym1.X0, Sym1.S01, Sym1.S02] [Sym1.S02, Sym1.X2, Sym1.S12]
  2 18102368030162948 (by decide +kernel)

def r337 : Rule R := replay [r133, r335, r336]
  [Sym1.X0, Sym1.S01, Sym1.S12] [Sym1.S02, Sym1.S01, Sym1.X2]
  3 2476182319303237786330467330 (by decide +kernel)

def r338 : Rule R := replay [r107, r337]
  [Sym1.X0, Sym1.S01, Sym1.S12] [Sym1.S01, Sym1.S12, Sym1.X2]
  2 36116757949710342 (by decide +kernel)

def r339 : Rule R := replay [r314, r329]
  [Sym1.X0, Sym1.S02, Sym1.CX01] [Sym1.S02, Sym1.CX01, Sym1.X2]
  2 18102359440233479 (by decide +kernel)

def r340 : Rule R := replay [r316, r325]
  [Sym1.X0, Sym1.S02, Sym1.CX12] [Sym1.S02, Sym1.CX12, Sym1.X2]
  2 54131156459197447 (by decide +kernel)

def r341 : Rule R := replay [r107, r337]
  [Sym1.X0, Sym1.S02, Sym1.S01] [Sym1.S02, Sym1.S01, Sym1.X2]
  2 54131156459197447 (by decide +kernel)

def r342 : Rule R := replay [r139, r339]
  [Sym1.X1, Sym1.X2, Sym1.X1] [Sym1.CX01, Sym1.X2, Sym1.CX01]
  2 9295552776195016710 (by decide +kernel)

def r343 : Rule R := replay [r143, r342]
  [Sym1.X1, Sym1.X2, Sym1.CX01] [Sym1.CX01, Sym1.X1, Sym1.X2]
  2 9277608763609583618 (by decide +kernel)

def r344 : Rule R := replay [r33, r135, r338]
  [Sym1.X1, Sym1.CX01, Sym1.S12] [Sym1.S12, Sym1.CX02, Sym1.X2]
  3 318460075115423670082900854786 (by decide +kernel)

def r345 : Rule R := replay [r33, r344]
  [Sym1.X1, Sym1.CX01, Sym1.S12] [Sym1.CX01, Sym1.S12, Sym1.X2]
  2 36116757949710342 (by decide +kernel)

def r346 : Rule R := replay [r152, r345]
  [Sym1.X1, Sym1.CX01, Sym1.S12] [Sym1.S12, Sym1.X2, Sym1.CX02]
  2 18137543812317190 (by decide +kernel)

def r347 : Rule R := replay [r146, r195]
  [Sym1.X1, Sym1.CX02, Sym1.X1] [Sym1.CX12, Sym1.CX02, Sym1.CX12]
  2 9295552776195014662 (by decide +kernel)

def r348 : Rule R := replay [r33, r136, r338]
  [Sym1.X1, Sym1.CX02, Sym1.S12] [Sym1.S12, Sym1.CX01, Sym1.X2]
  3 952285375229538370831252457474 (by decide +kernel)

def r349 : Rule R := replay [r81, r316]
  [Sym1.X1, Sym1.CX10, Sym1.S02] [Sym1.S02, Sym1.X1, Sym1.CX12]
  2 18102368030162948 (by decide +kernel)

def r350 : Rule R := replay [r164, r346]
  [Sym1.X1, Sym1.CX12, Sym1.CX21] [Sym1.S12, Sym1.X2, Sym1.CX12]
  2 9223512782933066756 (by decide +kernel)

def r351 : Rule R := replay [r167, r346]
  [Sym1.X1, Sym1.CCX01, Sym1.S12] [Sym1.S12, Sym1.X2, Sym1.CCX02]
  2 9223512782933066756 (by decide +kernel)

def r352 : Rule R := replay [r150, r265]
  [Sym1.X1, Sym1.CCX02, Sym1.X1] [Sym1.S02, Sym1.CCX02, Sym1.S02]
  2 9295552776195014662 (by decide +kernel)

def r353 : Rule R := replay [r81, r352]
  [Sym1.X1, Sym1.CCX02, Sym1.S02] [Sym1.S02, Sym1.CCX02, Sym1.X1]
  2 18137552402255876 (by decide +kernel)

def r354 : Rule R := replay [r33, r348]
  [Sym1.X1, Sym1.S12, Sym1.CX01] [Sym1.S12, Sym1.CX01, Sym1.X2]
  2 54131156459197447 (by decide +kernel)

def r355 : Rule R := replay [r144, r343]
  [Sym1.X2, Sym1.CX01, Sym1.X2] [Sym1.S01, Sym1.CX01, Sym1.CX10]
  2 105553116791814 (by decide +kernel)

def r356 : Rule R := replay [r39, r341, r355]
  [Sym1.X2, Sym1.CX01, Sym1.CX10] [Sym1.S01, Sym1.CX01, Sym1.X2]
  3 2658782097472105555526804348501753858 (by decide +kernel)

def r357 : Rule R := replay [r37, r356]
  [Sym1.X2, Sym1.CX01, Sym1.CX10] [Sym1.CX01, Sym1.CX10, Sym1.X2]
  2 54131156459192326 (by decide +kernel)

def r358 : Rule R := replay [r355, r357]
  [Sym1.X2, Sym1.CX01, Sym1.CX10] [Sym1.S01, Sym1.X2, Sym1.CX01]
  2 18137543812317190 (by decide +kernel)

def r359 : Rule R := replay [r152, r195]
  [Sym1.X2, Sym1.CX02, Sym1.X2] [Sym1.CX12, Sym1.CX02, Sym1.CX12]
  2 9295552776195014662 (by decide +kernel)

def r360 : Rule R := replay [r140, r340]
  [Sym1.X2, Sym1.CX02, Sym1.CX12] [Sym1.CX02, Sym1.CX12, Sym1.X2]
  2 36222328245848066 (by decide +kernel)

def r361 : Rule R := replay [r359, r360]
  [Sym1.X2, Sym1.CX02, Sym1.CX12] [Sym1.CX12, Sym1.X2, Sym1.CX02]
  2 54236726755332098 (by decide +kernel)

def r362 : Rule R := replay [r201, r361]
  [Sym1.X2, Sym1.CX12, Sym1.X2] [Sym1.K12, Sym1.CX21, Sym1.K12]
  2 54166340831285254 (by decide +kernel)

def r363 : Rule R := replay [r157, r358]
  [Sym1.X2, Sym1.CCX02, Sym1.S01] [Sym1.S01, Sym1.X2, Sym1.CCX12]
  2 9241544773628595204 (by decide +kernel)

def r364 : Rule R := replay [r69, r240]
  [Sym1.CX01, Sym1.CX10, Sym1.CCX02] [Sym1.CCX12, Sym1.CX01, Sym1.CX10]
  2 158338264858628 (by decide +kernel)

def r365 : Rule R := replay [r241, r364]
  [Sym1.CX01, Sym1.CCX12, Sym1.CX01] [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12]
  2 54166340831285254 (by decide +kernel)

def r366 : Rule R := replay [r33, r319]
  [Sym1.CX01, Sym1.CCX12, Sym1.S12] [Sym1.S12, Sym1.CX02, Sym1.CCX12]
  2 18102368030162948 (by decide +kernel)

def r367 : Rule R := replay [r209, r271]
  [Sym1.CX02, Sym1.CX20, Sym1.CX02] [Sym1.CCX02, Sym1.S02, Sym1.CCX02]
  2 9259523979176050694 (by decide +kernel)

def r368 : Rule R := replay [r229, r317]
  [Sym1.CX02, Sym1.CCX01, Sym1.S01] [Sym1.S01, Sym1.CCX01, Sym1.CX12]
  2 90195146440179716 (by decide +kernel)

def r369 : Rule R := replay [r200, r367]
  [Sym1.CX10, Sym1.CCX02, Sym1.S02] [Sym1.S02, Sym1.CX12, Sym1.CCX02]
  2 72215932302789636 (by decide +kernel)

def r370 : Rule R := replay [r244, r283]
  [Sym1.CX10, Sym1.CCX12, Sym1.S12] [Sym1.S12, Sym1.CX20, Sym1.CCX12]
  2 140746078818308 (by decide +kernel)

def r371 : Rule R := replay [r98, r245]
  [Sym1.CX12, Sym1.CX20, Sym1.CCX12] [Sym1.CCX12, Sym1.CX20, Sym1.CX12]
  2 18102359440228358 (by decide +kernel)

def r372 : Rule R := replay [r56, r318]
  [Sym1.CCX01, Sym1.CCX02, Sym1.S02] [Sym1.S02, Sym1.CCX12, Sym1.CCX02]
  2 54131165049126916 (by decide +kernel)

def r373 : Rule R := replay [r51, r117, r334]
  [Sym1.X0, Sym1.X2] [Sym1.X2, Sym1.X0]
  3 2658618254250996085742687889544708098 (by decide +kernel)

def r374 : Rule R := replay [r32, r350]
  [Sym1.X1, Sym1.S12] [Sym1.S12, Sym1.X2]
  2 123145302840325 (by decide +kernel)

def r375 : Rule R := replay [r31, r362]
  [Sym1.X2, Sym1.CX12] [Sym1.CX12, Sym1.X2]
  2 123145302835204 (by decide +kernel)

def r376 : Rule R := replay [r37, r358]
  [Sym1.X2, Sym1.S01] [Sym1.S01, Sym1.X2]
  2 123145302839300 (by decide +kernel)

def r377 : Rule R := replay [r71, r373]
  [Sym1.X0, Sym1.X1, Sym1.X2] [Sym1.X1, Sym1.X2, Sym1.X0]
  2 18137560992187394 (by decide +kernel)

def r378 : Rule R := replay [r322, r377]
  [Sym1.X0, Sym1.X1, Sym1.X2] [Sym1.X2, Sym1.X0, Sym1.X1]
  2 54236726755332098 (by decide +kernel)

def r379 : Rule R := replay [r116, r374]
  [Sym1.X0, Sym1.X1, Sym1.S12] [Sym1.S12, Sym1.X2, Sym1.X0]
  2 9277503193313443846 (by decide +kernel)

def r380 : Rule R := replay [r83, r373]
  [Sym1.X0, Sym1.X2, Sym1.X0] [Sym1.CCX01, Sym1.X2, Sym1.CCX01]
  2 18067175068139526 (by decide +kernel)

def r381 : Rule R := replay [r66]
  [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.CCX01] [Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.X0]
  2 72180756520110085 (by decide +kernel)

def r382 : Rule R := replay [r330, r381]
  [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01] [Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1]
  5 295101312892167245913791590990947790934906264784161735685 (by decide +kernel)

def r383 : Rule R := replay [r29, r66, r81, r114, r125, r149, r207, r222]
  [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.CCX01] [Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0]
  11 48780298249982135551579969871480672078433137261810915094253329873435912643110928550699247045396054847694470884382069937539069967336413723099140 (by decide +kernel)

def r384 : Rule R := replay [r66, r125, r241, r328, r369, r372]
  [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.CCX01] [Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0]
  7 60827017403468246477129275355032920376457736476998942537086507193137889086055907332 (by decide +kernel)

def r385 : Rule R := replay [r383]
  [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.CCX01, Sym1.X0]
  1 4108 (by decide +kernel)

def r386 : Rule R := replay [r384]
  [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.X0]
  1 4108 (by decide +kernel)

def r387 : Rule R := replay [r9, r70]
  [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01]
  2 151124950947027983794180 (by decide +kernel)

def r388 : Rule R := replay [r0, r382]
  [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0]
  3 5316911983449299626387537947195867140 (by decide +kernel)

def r389 : Rule R := replay [r71, r381]
  [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0]
  5 1645504655688450643699391045554884966037249657866911545642975236 (by decide +kernel)

def r390 : Rule R := replay [r71, r111, r381, r383, r384]
  [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0]
  9 157622463744643218170713288137941142682373590427958399528896889317555690152406808384803481076600874189643363068149772 (by decide +kernel)

def r391 : Rule R := replay [r29, r52, r66, r123, r127, r206, r315, r330, r368, r371, r384]
  [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0]
  21 4226412684902901801138029006551626379612547479417344421689271963954728120170832269001416775377352959824486679207001612602337965171833429130310223131393993218735262999718757232858491786534666163346226649459261805498445814291342978371729002779322580464031320015787982323722 (by decide +kernel)

def r392 : Rule R := replay [r70, r126, r249, r384]
  [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0]
  11 48781789740075513394596310588953367466734676206083035929456172350243500712291763873448319148459628955915850686848688678364459817629979642429452 (by decide +kernel)

def r393 : Rule R := replay [r70, r79, r382]
  [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01]
  7 254645068954692855356729905397160543766357504316091386066028301805138297125900977986601986 (by decide +kernel)

def r394 : Rule R := replay [r0, r66, r70]
  [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0]
  5 1645504557417220853721065630506767339231615599637964985765201927 (by decide +kernel)

def r395 : Rule R := replay [r0, r142, r373, r378, r382]
  [Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0]
  5 822953244953800030354018277332694297188018705171588536849138692 (by decide +kernel)

def r396 : Rule R := replay [r0, r83, r373, r380]
  [Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.X2, Sym1.CCX02, Sym1.X2, Sym1.X0]
  4 140307017287016132748349255807281603005410356233220 (by decide +kernel)

def r397 : Rule R := replay [r0, r373, r380]
  [Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.CCX01, Sym1.X0]
  3 2658782098401467270042071329963246596 (by decide +kernel)

def r398 : Rule R := replay [r142, r373, r378, r383]
  [Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0] [Sym1.X1, Sym1.CCX01, Sym1.X1]
  4 8585884916048568252473179682507350040767890436 (by decide +kernel)

def r399 : Rule R := replay [r373, r380, r381]
  [Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0] [Sym1.CCX01]
  3 324522886901920703539989668955140 (by decide +kernel)

def r400 : Rule R := replay [r68, r71, r108, r239, r241, r242, r324, r352]
  [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0] [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12]
  17 88251025509234530271951846681751370936234555355104748794384892281984050616788391115430126906156591245871115392932846329982733290572277451129145507515706174687919168187324779928056440866922536287521239869269120793971718 (by decide +kernel)

def r401 : Rule R := replay [r26, r29, r66, r110, r116, r126, r145, r173, r218, r242, r347, r351, r354, r365, r366, r370, r371, r373, r379]
  [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.X2, Sym1.CCX02, Sym1.X2, Sym1.X0] [Sym1.X0, Sym1.X2, Sym1.CCX02, Sym1.X2, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12]
  29 659134040085764227399676146465961822039290089905205901139051590610965377922766920194363800824263148173134788270270277511422970212494629150428090264830316218332018142582372634895444207663928382813990214239388064845866912537296463912572330536545060086246885974605386313024581993352391288186540195119771369806322302775959007665283834106077927848651823890033210174388723752678984710 (by decide +kernel)

def r402 : Rule R := replay [r29, r53, r79, r149, r151, r172, r230, r266, r279, r366]
  [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.CCX02, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX02] [Sym1.CCX02, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX02, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12]
  17 2168930971145137033198749528559062342725040577822295311471736187681912800113007123625221756174897393584646025388055144739695613517413564891382493884555871603999745697977885008143303602653825028581579780510757587561416754182 (by decide +kernel)

def r403 : Rule R := replay [r68, r239, r241, r242, r369]
  [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12]
  9 78813660269936954853658758731827920556565187595095412300368195594264493042373856506586865177795956516607246948371462 (by decide +kernel)

def r404 : Rule R := replay [r66, r68, r231, r235, r239, r240, r241, r318, r327, r369, r403]
  [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X0] [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12]
  17 265010444087233719319775218366945824519430128954604013676136431482348590702122368098801728478502558788216874456891712574447004803572371093991702784843381687040730769167504589288693717808538674169862425190708191116134407 (by decide +kernel)

def r405 : Rule R := replay [r29, r127, r129, r137, r248, r266, r267, r330, r404]
  [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X1, Sym1.CCX01, Sym1.X1]
  18 25436456433140563818845684781937615666397763394824634656243677970216887849229004454461186882962165922150644757415883368399813010842096724290414225993923266711784856607151083671585203594238923153803740588806266773023825132985058855486470 (by decide +kernel)

def r406 : Rule R := replay [r83, r380, r384]
  [Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0] [Sym1.CCX01, Sym1.X2, Sym1.CCX02, Sym1.X2, Sym1.CCX01]
  5 98558759776094688203074681274901734747787140589265881094 (by decide +kernel)

def r407 : Rule R := replay [r79, r108, r130, r141, r151, r240, r241, r353, r372]
  [Sym1.CCX01, Sym1.X2, Sym1.CCX02, Sym1.X2, Sym1.CCX01] [Sym1.CCX02, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX02]
  11 10425797379166001104964759256735625774934640092363362682282913061899360885757530818965580832623459294432529154789415110369352897613675366404 (by decide +kernel)

def r408 : Rule R := replay [r0, r2, r9, r395, r400]
  [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0]
  11 390218568803718665533614225108214250933307375392084780336120981345867200777108974754647547721261498731685742123547305921514806008164323145285633 (by decide +kernel)

def r409 : Rule R := replay [r0, r2, r9, r396, r401]
  [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0]
  11 390218568803718665533614225108214250933307375392084780336120981345867200777108974754647547721261498731685742123547305921514806008164323145285633 (by decide +kernel)

def r410 : Rule R := replay [r0, r2, r9, r402, r406, r407]
  [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0]
  13 3515205478027955041034573003001049403983361704419031178317734636439734965448090930207767044290817507573984732766996483128709264629313173891596918357121690501120 (by decide +kernel)

def r411 : Rule R := replay [r0, r2, r9, r399, r403]
  [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.CCX01] [Sym1.CCX01, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0]
  11 11358241486581727797501960551041090593428951997821176592756986205191888463271219302176868844693331709502288895961249000723526333759488 (by decide +kernel)

def r412 : Rule R := replay [r0, r2, r9, r397, r404]
  [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0]
  12 3003427538031464655941364369963818961473108605432897687829242318601847911642592995842408174963662929202791933397276760334095380184733739106295429915136229376 (by decide +kernel)

def r413 : Rule R := replay [r0, r2, r9, r398, r405]
  [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1]
  12 7293847514089003726766958378792941908991547325126935773891572992809075632267740583007310416938987891835076651132584460808465984927189832162893724001787969558 (by decide +kernel)

def r414 : Rule R := replay [r0, r393]
  [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0] [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0]
  5 7404770507945614261906939679740225600499348025625075483683061764 (by decide +kernel)

def r415 : Rule R := replay [r66, r71, r108, r113, r326, r349, r373, r375]
  [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01]
  9 236416856415277669551377518614065220878697571188837236018541266310872582495932965067442338419822157143826841941835780 (by decide +kernel)

def r416 : Rule R := replay [r415]
  [Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] [Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0]
  1 9225 (by decide +kernel)

def r417 : Rule R := replay [r266]
  [Sym1.CCX12] [Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12]
  1 1025 (by decide +kernel)

def r418 : Rule R := replay [r26, r33, r75, r119, r374]
  [Sym1.X2] [Sym1.CX02, Sym1.X0, Sym1.CX02, Sym1.X0]
  5 50217484443437243245065635367210789165264461988035305670658 (by decide +kernel)

def r419 : Rule R := replay [r29, r81, r91, r149, r221]
  [Sym1.CX02] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01]
  5 50217484443437259970624534265178145014840212410694936559618 (by decide +kernel)

def r420 : Rule R := replay [r173, r313, r351, r374, r419]
  [Sym1.CX01] [Sym1.X2, Sym1.CCX02, Sym1.X2, Sym1.CCX02]
  5 150847271638852137051112439688641838792202321098649513754626 (by decide +kernel)

def r421 : Rule R := replay [r382, r393, r407]
  [Sym1.X2, Sym1.CCX02, Sym1.X2] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1]
  3 162265157346631441989084887652359 (by decide +kernel)

def r422 : Rule R := replay [r108]
  [Sym1.X0] [Sym1.CX10, Sym1.X1, Sym1.CX10, Sym1.X1]
  1 2 (by decide +kernel)

def r423 : Rule R := replay [r38, r89, r363, r376, r420]
  [Sym1.CX10] [Sym1.X2, Sym1.CCX12, Sym1.X2, Sym1.CCX12]
  5 150651112209621303277242571269166599518930523298695219775490 (by decide +kernel)

def r425 : Rule R := replay []
  [Sym1.CCX01] [Sym1.CCX01]
  0 0 (by decide +kernel)

def r427 : Rule R := replay [r9]
  [Sym1.CCX02] [Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01]
  2 453347182355485940514816 (by decide +kernel)

def r428 : Rule R := replay [r0, r2, r9, r415, r416, r417]
  [Sym1.CCX12] [Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01]
  23 428607366876181101794049036270676344040342909340312522518454079634498517397968890781711980489960906357385519370562223498411867813926659032593565699235027046209505435413092030845187840369050727032537439434271428994712394189119701642845380699981457241479975397023864315143934346026465754587711042000257026 (by decide +kernel)

def r429 : Rule R := replay [r0, r418, r419]
  [Sym1.X2] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0]
  4 374144419156711147384662490106064724188127576981506 (by decide +kernel)

def r430 : Rule R := replay [r0, r9, r26, r420, r421]
  [Sym1.X1] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0]
  14 4780241935351137873876632806549452527579487272625485486111204821172210987523890455644939243349187034425099765556157458778681849775097458508673238004333730039893835165028581124074373122 (by decide +kernel)

def r431 : Rule R := replay [r419]
  [Sym1.CX02] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01]
  1 2 (by decide +kernel)

def r432 : Rule R := replay [r422, r423]
  [Sym1.X0] [Sym1.X2, Sym1.CCX12, Sym1.X2, Sym1.CCX12, Sym1.X1, Sym1.X2, Sym1.CCX12, Sym1.X2, Sym1.CCX12, Sym1.X1]
  3 162259896101473684392593980391426 (by decide +kernel)

def r433 : Rule R := replay [r420]
  [Sym1.CX01] [Sym1.X2, Sym1.CCX02, Sym1.X2, Sym1.CCX02]
  1 2 (by decide +kernel)

def r434 : Rule R := replay [r423]
  [Sym1.CX10] [Sym1.X2, Sym1.CCX12, Sym1.X2, Sym1.CCX12]
  1 2 (by decide +kernel)

def r435 : Rule R := replay [r29]
  [Sym1.CX20] [Sym1.X1, Sym1.CCX12, Sym1.X1, Sym1.CCX12]
  1 2 (by decide +kernel)

def r436 : Rule R := replay [r30]
  [Sym1.CX21] [Sym1.CX20, Sym1.CX01, Sym1.CX20, Sym1.CX01]
  1 2 (by decide +kernel)

def r437 : Rule R := replay [r37]
  [Sym1.S01] [Sym1.CX01, Sym1.CX10, Sym1.CX01]
  1 2 (by decide +kernel)

def r438 : Rule R := replay [r34]
  [Sym1.S02] [Sym1.CX02, Sym1.CX20, Sym1.CX02]
  1 2 (by decide +kernel)

def r439 : Rule R := replay [r54]
  [Sym1.CX12] [Sym1.S01, Sym1.CX02, Sym1.S01]
  1 2 (by decide +kernel)

def r440 : Rule R := replay [r32]
  [Sym1.S12] [Sym1.CX12, Sym1.CX21, Sym1.CX12]
  1 2 (by decide +kernel)

theorem far26 : PermutationBase.Eqn [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.CCX01] [Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.X0] := transfer r381.sound

theorem far46 : PermutationBase.Eqn [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01] [Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1] := transfer r382.sound

theorem far06 : PermutationBase.Eqn [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.CCX01] [Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0] := transfer r383.sound

theorem far16 : PermutationBase.Eqn [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.CCX01] [Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0] := transfer r384.sound

theorem far24 : PermutationBase.Eqn [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.CCX01, Sym1.X0] := transfer r385.sound

theorem far25 : PermutationBase.Eqn [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.X0] := transfer r386.sound

theorem braid5 : PermutationBase.Eqn [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01] := transfer r387.sound

theorem far02 : PermutationBase.Eqn [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0] := transfer r388.sound

theorem far04 : PermutationBase.Eqn [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0] := transfer r389.sound

theorem far05 : PermutationBase.Eqn [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0] := transfer r390.sound

theorem far14 : PermutationBase.Eqn [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0] := transfer r391.sound

theorem far15 : PermutationBase.Eqn [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0] := transfer r392.sound

theorem braid4 : PermutationBase.Eqn [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] := transfer r393.sound

theorem braid1 : PermutationBase.Eqn [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0] := transfer r394.sound

theorem far03 : PermutationBase.Eqn [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0] := transfer r408.sound

theorem far13 : PermutationBase.Eqn [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0] := transfer r409.sound

theorem far35 : PermutationBase.Eqn [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01] [Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] := transfer r410.sound

theorem far36 : PermutationBase.Eqn [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.CCX01] [Sym1.CCX01, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] := transfer r411.sound

theorem braid2 : PermutationBase.Eqn [Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0] [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] := transfer r412.sound

theorem braid3 : PermutationBase.Eqn [Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1] := transfer r413.sound

theorem braid0 : PermutationBase.Eqn [Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0] [Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0] := transfer r414.sound

theorem route_CCX01 : PermutationBase.Eqn [Sym1.CCX01] [Sym1.CCX01] := transfer r425.sound

theorem route_CCX02 : PermutationBase.Eqn [Sym1.CCX02] [Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01] := transfer r427.sound

theorem route_CCX12 : PermutationBase.Eqn [Sym1.CCX12] [Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.X2, Sym1.CCX01, Sym1.X0, Sym1.CCX12, Sym1.CCX02, Sym1.CCX12, Sym1.X0, Sym1.CCX01, Sym1.X2, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01] := transfer r428.sound

theorem route_X2 : PermutationBase.Eqn [Sym1.X2] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0] := transfer r429.sound

theorem route_X1 : PermutationBase.Eqn [Sym1.X1] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.CCX01, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.CCX02, Sym1.CCX01, Sym1.X0, Sym1.X0, Sym1.CCX01, Sym1.X0] := transfer r430.sound

theorem route_CX02 : PermutationBase.Eqn [Sym1.CX02] [Sym1.X1, Sym1.CCX01, Sym1.X1, Sym1.CCX01] := transfer r431.sound

theorem route_X0 : PermutationBase.Eqn [Sym1.X0] [Sym1.X2, Sym1.CCX12, Sym1.X2, Sym1.CCX12, Sym1.X1, Sym1.X2, Sym1.CCX12, Sym1.X2, Sym1.CCX12, Sym1.X1] := transfer r432.sound

theorem route_CX01 : PermutationBase.Eqn [Sym1.CX01] [Sym1.X2, Sym1.CCX02, Sym1.X2, Sym1.CCX02] := transfer r433.sound

theorem route_CX10 : PermutationBase.Eqn [Sym1.CX10] [Sym1.X2, Sym1.CCX12, Sym1.X2, Sym1.CCX12] := transfer r434.sound

theorem route_CX20 : PermutationBase.Eqn [Sym1.CX20] [Sym1.X1, Sym1.CCX12, Sym1.X1, Sym1.CCX12] := transfer r435.sound

theorem route_CX21 : PermutationBase.Eqn [Sym1.CX21] [Sym1.CX20, Sym1.CX01, Sym1.CX20, Sym1.CX01] := transfer r436.sound

theorem route_S01 : PermutationBase.Eqn [Sym1.S01] [Sym1.CX01, Sym1.CX10, Sym1.CX01] := transfer r437.sound

theorem route_S02 : PermutationBase.Eqn [Sym1.S02] [Sym1.CX02, Sym1.CX20, Sym1.CX02] := transfer r438.sound

theorem route_CX12 : PermutationBase.Eqn [Sym1.CX12] [Sym1.S01, Sym1.CX02, Sym1.S01] := transfer r439.sound

theorem route_S12 : PermutationBase.Eqn [Sym1.S12] [Sym1.CX12, Sym1.CX21, Sym1.CX12] := transfer r440.sound

end QCert.CliffordCS3.Three.PermutationCert
