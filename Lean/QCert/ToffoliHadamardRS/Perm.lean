/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: permutations

Translation of `Perm.agda`: permutations of the basis states as circuits,
`CoxeterFrames` with the circuits `T d` of Figure 7 for the transpositions
of adjacent basis states, at every level `k`.  A Coxeter word is read with
`T d` for its letter `d` (`Pc`).  Given the Coxeter relations for the
circuits `T d` (`Coxeter`), two Coxeter words with the same permutation have
equivalent circuits (`Pc_complete`), and a circuit those `T i` commute with,
conjugated by a Coxeter word, depends only on where the word sends the
states below `j` (`frame_eqW`); `frame ts` sends `0, 1, …` to the distinct
states `ts`.  The circuit `Pc w` sends the basis state `x` to `act w x`.
-/
import QCert.ToffoliHadamardRS.CoxeterFrames
import QCert.ToffoliHadamardRS.Syntactics

namespace QCert.ToffoliHadamardRS

open CoxeterFrames

variable {k : ℕ}

/-- The Coxeter relations for the circuits `T d` of Figure 7. -/
abbrev Coxeter (Γ : WRel (Gate k)) : Prop := CoxeterFrames.Coxeter (T (k := k)) Γ

/-- A Coxeter word read as a circuit. -/
abbrev Pc (w : CW) : Word (Gate k) := CoxeterFrames.Pc T w

/-- A circuit conjugated by a Coxeter word. -/
abbrev Fr (b : Word (Gate k)) (p : CW) : Word (Gate k) := CoxeterFrames.Fr T b p

end QCert.ToffoliHadamardRS
